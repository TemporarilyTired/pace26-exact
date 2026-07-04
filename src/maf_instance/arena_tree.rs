use super::arena_vertex::{ArenaVertexTopDown, Idx, Label, Node, NodeData::*, Status::*};
use super::performed_reduction::PerformedReduction::{self, *};
use crate::common::reading::PrintableSolution;
use crate::common::validity::assert_validity;
use pace26io::{
    binary_tree::{IndexedBinTree, TopDownCursor},
    newick::NewickWriter,
};
use rustc_hash::{FxHashMap, FxHashSet};

// Arena representation of tree, storing a vector of ArenaVertex enums
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ArenaTree {
    pub arena: Vec<Node>,
    pub roots: FxHashSet<Idx>,
    pub leaf_map: FxHashMap<Label, Idx>,
}

impl ArenaTree {
    #[inline]
    pub fn get_lca(&self, leaf_a: Idx, leaf_b: Idx) -> Option<Idx> {
        let path_a = self.path_to_root(leaf_a);
        let path_b = self.path_to_root(leaf_b);

        let path_a_rev = path_a.into_iter().rev();
        let path_b_rev = path_b.into_iter().rev();

        let mut lca = None;
        for (a, b) in path_a_rev.zip(path_b_rev) {
            if a != b {
                break;
            }
            lca = Some(a);
        }
        lca
    }

    pub fn max_label_value(&self) -> Idx {
        self.leaf_map.keys().max().unwrap_or(&Label(0)).0
    }

    #[inline]
    pub fn path_to_root(&self, mut idx: Idx) -> Vec<Idx> {
        // start with self, then iterate all ancestors
        let mut path = vec![idx];
        while let Some(parent) = self.get(idx).parent {
            idx = parent;
            path.push(idx);
        }
        path
    }

    #[inline]
    pub fn ancestors_incl(&self, idx: Idx) -> impl Iterator<Item = Idx> + '_ {
        std::iter::successors(Some(idx), move |&current| self.get(current).parent)
    }

    #[inline]
    pub fn find_root_of(&self, mut idx: Idx) -> Idx {
        // start with self, then iterate all ancestors
        while let Some(parent) = self.get(idx).parent {
            idx = parent;
        }
        idx
    }

    #[inline]
    pub fn apply_merge(&mut self, parent: Idx, leaf_a: Idx, leaf_b: Idx, new_label: Label) {
        // remove label index entries of old labels
        let label_a = self.get(leaf_a).label().unwrap();
        self.leaf_map.remove(&label_a);
        let label_b = self.get(leaf_b).label().unwrap();
        self.leaf_map.remove(&label_b);

        // convert the parent to a leaf with the new merged label
        self.get_mut(leaf_a).status = MergedIntoParent;
        self.get_mut(leaf_b).status = MergedIntoParent;
        self.get_mut(parent).convert_to_leaf(new_label);

        self.leaf_map.insert(new_label, parent);
    }

    #[inline]
    pub fn remove_svt(&mut self, label: Label) {
        let idx = self.leaf_map[&label];
        debug_assert_eq!(self.get_mut(idx).parent, None);
        debug_assert_eq!(self.get_mut(idx).label(), Some(label));

        self.get_mut(idx).status = Removed;

        self.roots.remove(&idx);
        self.leaf_map.remove(&label);
    }

    pub fn undo_reduction(&mut self, performed_reduction: PerformedReduction) {
        match performed_reduction {
            SvtRemoved { label } => {
                let new_svt = Node {
                    status: Present,
                    data: Leaf { label },
                    parent: None,
                };
                let inserted_idx = self.arena.len();
                self.arena.push(new_svt);
                self.leaf_map.insert(label, inserted_idx as Idx);
                self.roots.insert(inserted_idx as Idx);
            }
            LabelsMerged {
                original1,
                original2,
                new_label,
            } => {
                let new_label_idx = self.leaf_map[&new_label] as Idx;
                let insertion_idx1 = self.arena.len() as Idx;
                let insertion_idx2 = self.arena.len() as Idx + 1;

                self.get_mut(new_label_idx).data = Internal {
                    left: insertion_idx1,
                    right: insertion_idx2,
                };
                self.leaf_map.remove(&new_label);

                let original_leaf1 = Node {
                    status: Present,
                    data: Leaf { label: original1 },
                    parent: Some(new_label_idx),
                };
                self.arena.push(original_leaf1);
                self.leaf_map.insert(original1, insertion_idx1 as Idx);

                let original_leaf2 = Node {
                    status: Present,
                    data: Leaf { label: original2 },
                    parent: Some(new_label_idx),
                };
                self.arena.push(original_leaf2);
                self.leaf_map.insert(original2, insertion_idx2 as Idx);
            }
        };
    }

    // return the index of the leaf with the specified label
    // assumes it exists, otherwise panics
    #[inline]
    pub fn locate_label(&self, target_label: Label) -> Idx {
        let leaf_idx = *self
            .leaf_map
            .get(&target_label)
            .expect("label to be present");
        debug_assert!(
            matches!(self.get(leaf_idx), Node{ status: Present, data: Leaf {label}, ..} if *label==target_label)
        );
        leaf_idx
    }

    // return the index of the leaf with the specified label
    // if label is not present, returns None
    #[inline]
    pub fn try_locate_label(&self, target_label: Label) -> Option<Idx> {
        self.leaf_map.get(&target_label).copied()
    }

    #[inline]
    pub fn find_sibling(&self, idx: Idx) -> Option<Idx> {
        let parent_idx = self.get(idx).parent?;
        let Internal { left, right } = self.get(parent_idx).data else {
            unreachable!("parent must have children");
        };
        Some(if left != idx {
            debug_assert_eq!(right, idx);
            left
        } else {
            right
        })
    }

    #[inline]
    pub fn find_uncle(&self, idx: Idx) -> Option<Idx> {
        let parent_idx = self.get(idx).parent?;
        self.find_sibling(parent_idx)
    }

    #[inline]
    pub fn iterate_cherries(&self) -> impl Iterator<Item = (Idx, Label, Label)> {
        self.roots
            .iter()
            .flat_map(|&root| self.dfs_from(root).cherries())
    }

    #[inline]
    pub fn iterate_all(&self) -> impl Iterator<Item = (Idx, &Node)> {
        self.roots.iter().flat_map(|&root| self.dfs_from(root))
    }

    #[inline]
    pub fn ord(&self) -> usize {
        self.roots.len()
    }

    #[inline]
    pub fn get(&self, idx: Idx) -> &Node {
        &self.arena[idx as usize]
    }

    #[inline]
    pub fn get_mut(&mut self, idx: Idx) -> &mut Node {
        &mut self.arena[idx as usize]
    }

    pub fn cut_branch(&mut self, cut: Idx) {
        assert_validity!(self);

        // find parent
        let parent = self
            .get(cut)
            .parent
            .expect("Branch cut failed: tried to cut off a vertex without a parent");
        debug_assert_eq!(self.get(parent).status, Present);
        debug_assert_eq!(self.get(cut).status, Present);

        // find grand_parent (may be None)
        let grand_parent_opt = self.get(parent).parent;

        // find other child of the parent
        let sibling = self.get(parent).children().find(|&v| v != cut).expect(
            "One of the two children of the parent of the cut must be different from the cut",
        );

        // cut off the branch
        self.get_mut(cut).parent = None;
        self.roots.insert(cut);

        // contract parent vertex
        self.get_mut(parent).status = Contracted;
        self.get_mut(sibling).parent = grand_parent_opt;

        if let Some(grand_parent) = grand_parent_opt {
            self.get_mut(grand_parent)
                .replace_child(parent, sibling)
                .expect(
                "Branch cut failed (not cleanly): couldn't contract parent vertex because parent
                is not a child of grand_parent (tree representation is invalid)",
            );
        } else {
            // if contracted vertex was a root: make their child a root instead
            debug_assert!(self.roots.contains(&(parent))); // must return true, otherwise tree representation invalid
            self.roots.remove(&(parent)); // must return true, otherwise tree representation invalid
            self.roots.insert(sibling);
        }
        assert_validity!(self);
    }

    // Add a dummy leaf as sibling of the given sibling (or as root if sibling is None)
    pub fn add_dummy_leaf_as_sibling_of(&mut self, dummy_label: Label, sibling: Option<Idx>) {
        debug_assert!(!self.leaf_map.contains_key(&dummy_label));

        let dummy_leaf = Node {
            status: Present,
            data: Leaf { label: dummy_label },
            parent: None,
        };

        // insert dummy leaf
        let dummy_idx = self.arena.len() as Idx;
        self.leaf_map.insert(dummy_label, dummy_idx);
        self.arena.push(dummy_leaf);

        if let Some(sibling) = sibling {
            let grandparent = self.get(sibling).parent;

            // insert parent to subdivide edge above sibling
            let new_parent_idx = self.arena.len() as Idx;
            let new_parent = Node {
                status: Present,
                data: Internal {
                    left: dummy_idx,
                    right: sibling,
                },
                parent: grandparent,
            };

            match grandparent {
                Some(grandparent) => {
                    self.get_mut(grandparent)
                        .replace_child(sibling, new_parent_idx)
                        .unwrap();
                }
                None => {
                    // sibling was a root: sibling is not a root anymore, new_parent is
                    self.roots.insert(new_parent_idx);
                    self.roots.remove(&sibling);
                }
            }
            self.get_mut(sibling).parent = Some(new_parent_idx);
            self.get_mut(dummy_idx).parent = Some(new_parent_idx);
            self.arena.push(new_parent);
        } else {
            self.roots.insert(dummy_idx);
        }
    }

    // Join two disjoin forests together into one
    // Assumes labels are mutually disjoint
    pub fn join_with(mut self, other: ArenaTree) -> ArenaTree {
        let offset = self.arena.len() as Idx;

        for node in other.arena.iter() {
            let mut new_node = node.clone();
            new_node.parent = new_node.parent.map(|parent| parent + offset);
            new_node.data = match new_node.data.clone() {
                Internal { left, right } => Internal {
                    left: left + offset,
                    right: right + offset,
                },
                leaf => leaf,
            };
            self.arena.push(new_node);
        }

        self.roots
            .extend(other.roots.iter().map(|&root| root + offset));
        self.leaf_map.extend(
            other
                .leaf_map
                .iter()
                .map(|(&label, &idx)| (label, idx + offset)),
        );
        self
    }

    // Join this forest with another that was split from it as a subtree
    // Assumes the used dummy labels are present in the respective forests
    // We assume other below has the dummy as a child of a root.
    // Thus after cutting the dummy its original sibling is a root
    pub fn join_at_dummy(
        mut self,
        mut other_below: ArenaTree,
        used_dummy_above: Label,
        used_dummy_below: Label,
    ) -> ArenaTree {
        // remove the dummy labes of both parts
        let dummy_in_other = other_below.leaf_map[&used_dummy_below];
        let mut sibling_of_dummy = other_below
            .find_sibling(dummy_in_other)
            .expect("dummy label to have a parent");
        other_below.cut_branch(dummy_in_other);
        debug_assert_eq!(other_below.get(sibling_of_dummy).parent, None);

        other_below.remove_svt(used_dummy_below);

        // remove dummy of cluster above; but leave dangling reference from parent to removed dummy
        let dummy_idx = self.leaf_map[&used_dummy_above];
        let parent_of_dummy = self
            .get(dummy_idx)
            .parent
            .expect("dummy label to have parent");
        let dummy = self.get_mut(dummy_idx);
        dummy.parent = None;
        self.remove_svt(used_dummy_above);

        // add all nodes, roots, etc. from the cluster below to this one
        let offset = self.arena.len() as Idx;
        sibling_of_dummy += offset;

        for node in other_below.arena.iter() {
            let mut new_node = node.clone();
            new_node.parent = new_node.parent.map(|parent| parent + offset);
            new_node.data = match new_node.data.clone() {
                Internal { left, right } => Internal {
                    left: left + offset,
                    right: right + offset,
                },
                leaf => leaf,
            };
            self.arena.push(new_node);
        }

        self.roots
            .extend(other_below.roots.iter().map(|&root| root + offset));
        self.leaf_map.extend(
            other_below
                .leaf_map
                .iter()
                .map(|(&label, &idx)| (label, idx + offset)),
        );

        // join the clusters:
        // attach the subtree from below to the parent of the dummy label
        let parent = self.get_mut(parent_of_dummy);
        parent
            .replace_child(dummy_idx, sibling_of_dummy)
            .expect("valid forests representation");
        let sibling = self.get_mut(sibling_of_dummy);
        sibling.parent = Some(parent_of_dummy);
        self.roots.remove(&sibling_of_dummy);

        self
    }

    pub fn new_from_indexed_bin_tree(tree: &IndexedBinTree) -> ArenaTree {
        fn build(
            tree: &IndexedBinTree,
            nodes: &mut FxHashMap<Idx, Node>,
            leaf_map: &mut FxHashMap<Label, Idx>,
            parent: Option<Idx>,
            next_idx: &mut usize,
        ) -> Idx {
            let usize_idx = *next_idx;
            *next_idx += 1;

            let idx = Idx::try_from(usize_idx)
                .expect("Expected node_idx to be at most the size of Idx (u16)");

            let children_idx = tree.children().map(|(left, right)| {
                (
                    build(left, nodes, leaf_map, Some(idx), next_idx),
                    build(right, nodes, leaf_map, Some(idx), next_idx),
                )
            });

            let node = Node::new_from_indexed_bin_tree(tree, children_idx, parent);
            if let Some(label) = node.label() {
                leaf_map.insert(label, idx);
            }

            nodes.insert(idx, node);
            idx
        }

        let mut nodes_map: FxHashMap<Idx, Node> = FxHashMap::default();
        let mut leaf_map: FxHashMap<Label, Idx> = FxHashMap::default();

        let root_idx = build(tree, &mut nodes_map, &mut leaf_map, None, &mut 0);

        let mut roots: FxHashSet<Idx> = FxHashSet::default();
        roots.insert(root_idx);

        let mut arena: Vec<Node> = Vec::with_capacity(nodes_map.len());
        for i in 0..(nodes_map.len() as Idx) {
            arena.push(
                nodes_map
                    .remove(&i)
                    .expect("Expected the indices to all be consecutive integers"),
            );
        }
        ArenaTree {
            arena,
            roots,
            leaf_map,
        }
    }

    pub fn top_down_from(&self, root: usize) -> ArenaVertexTopDown<'_> {
        ArenaVertexTopDown {
            idx: root,
            arena: &self.arena,
        }
    }

    #[cfg(feature = "assert_validity")]
    pub fn assert_validity(&self) {
        // test if there are duplicate leaf Labels (previously also NodeIdxs)
        let mut unique_labels: FxHashSet<Label> = FxHashSet::default();
        // let mut unique_nodes: FxHashSet<NodeIdx> = FxHashSet::new();
        for vertex in self.arena.iter() {
            if let Node {
                status: Present,
                data: Leaf { label },
                ..
            } = vertex
            {
                assert!(unique_labels.insert(*label), "duplicate Label: {}", label.0);
            }
        }

        // test if all Present vertices without a parent are a root
        // and test if all other vertices are not a root
        for (idx, vertex) in self.arena.iter().enumerate() {
            let is_root = self.roots.contains(&(u16::try_from(idx)).unwrap());
            let has_parent = vertex.parent.is_none() && vertex.status == Present;
            assert_eq!(is_root, has_parent);
        }

        // test if all children of some Present X are Present and have X as parent
        // test if all Present inner nodes have 2 children
        for (idx, vertex) in self.arena.iter().enumerate() {
            if vertex.status != Present {
                continue;
            }
            for child in vertex.children() {
                assert!(
                    matches!(*self.get(child), Node {status: Present, parent, ..} if parent == Some(idx as Idx))
                )
            }
        }

        // test if no inner node has status MergedIntoParent (reserved for leaves)
        for vertex in self.arena.iter() {
            assert!(!matches!(
                vertex,
                Node {
                    status: MergedIntoParent,
                    data: Internal { .. },
                    ..
                }
            ));
        }
    }
}

impl PrintableSolution for ArenaTree {
    fn print_newick_strings(&self) {
        for root in &self.roots {
            println!("{}", &self.top_down_from(*root as usize).to_newick_string());
        }
    }
}
