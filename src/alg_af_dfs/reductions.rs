use itertools::kmerge;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::common::generation_set::GenerationSet;
use crate::maf_instance::{
    arena_tree::ArenaTree,
    arena_vertex::{Idx, Label, NodeData::*, Status::*},
    instance::Instance,
    performed_reduction::PerformedReduction::{self, *},
    tree_traversal::TreeTraversal,
};

pub trait AfDbsReductionsInstanceExt {
    fn fully_reduce(&mut self) -> Vec<PerformedReduction>;
    fn fully_r1_reduce(&mut self) -> bool;
    fn rr_2_2_1_reduce(&mut self) -> bool;
    fn reduce_svt_and_merge(&mut self) -> (Vec<PerformedReduction>, usize);

    fn split_into_clusters(self) -> Vec<Instance>;
    fn copy_cluster(&self, cluster_labels: &FxHashSet<Label>) -> Instance;

    #[allow(clippy::type_complexity)]
    fn find_clusters_w_dummy(
        &self,
    ) -> Option<(Instance, Instance, (Instance, Label), (Instance, Label))>;
}

impl AfDbsReductionsInstanceExt for Instance {
    /// Exhaustively performs reductions:
    /// - merge common subtrees between all forests
    /// - sync single vertex trees between the forests
    /// - perform reduction rule 2.2.1
    fn fully_reduce(&mut self) -> Vec<PerformedReduction> {
        let (mut performed_reductions, _) = self.reduce_svt_and_merge();

        while self.rr_2_2_1_reduce() || self.fully_r1_reduce() {
            let (new_reductions, _) = self.reduce_svt_and_merge();
            performed_reductions.extend(new_reductions);
        }
        performed_reductions
    }

    // Perform r1-reduction exhaustively, returning true if any cut was performed
    fn fully_r1_reduce(&mut self) -> bool {
        let n_forests = self.forests.len();
        let n_nodes = self
            .forests
            .iter()
            .map(|f| f.arena.len())
            .max()
            .unwrap_or(0);
        let max_label = self.forests[0].max_label_value() as usize;
        let mut done: Vec<Vec<bool>> = vec![vec![false; n_forests]; n_forests];
        let workspace: &mut R1Workspace = &mut R1Workspace::new(max_label, n_nodes);

        let mut has_performed_cut = false;

        loop {
            let mut any_changed = false;

            for i in 1..n_forests {
                for j in 0..i {
                    if done[i][j] {
                        continue;
                    }

                    let [f_i, f_j] = self.forests.get_disjoint_mut([i, j]).unwrap();
                    let (i_changed, j_changed) =
                        ArenaTree::r1_reduce_pair_w_workspace(f_i, f_j, workspace);

                    // mark pair as fully reduced
                    done[i][j] = true;

                    // if a forest changes: invalidate all 'done' pairs involving it
                    if i_changed {
                        any_changed = true;
                        for k in 0..n_forests {
                            if k != j {
                                let (a, b) = if i > k { (i, k) } else { (k, i) };
                                done[a][b] = false;
                            }
                        }
                        debug_assert!(done[i][j]);
                    }
                    if j_changed {
                        any_changed = true;
                        for k in 0..n_forests {
                            if k != i {
                                let (a, b) = if j > k { (j, k) } else { (k, j) };
                                done[a][b] = false;
                            }
                        }
                        debug_assert!(done[i][j]);
                    }
                }
            }

            if !any_changed {
                break;
            }
            has_performed_cut |= any_changed;
        }
        has_performed_cut
    }

    /// Exhaustively performs reductions:
    /// - merges common subtrees between all forests
    /// - syncs single vertex trees between the forests and removes them
    ///
    /// returns the removed svts and the merged labels
    fn reduce_svt_and_merge(&mut self) -> (Vec<PerformedReduction>, usize) {
        let mut performed_reductions: Vec<PerformedReduction> = vec![];
        let mut n_removed_svts: usize = 0;

        let mut to_check: Vec<Label> = self.forests[0].leaf_map.keys().copied().collect();
        let mut to_check_set: FxHashSet<Label> = to_check.iter().copied().collect();

        'outer: while let Some(label) = to_check.pop() {
            to_check_set.remove(&label);

            // check if label is part of a common cherry
            // or if it is a svt that is not yet synced
            let f1 = &self.forests[0];
            let Some(leaf_idx) = f1.try_locate_label(label) else {
                continue 'outer;
            };

            let v = f1.get(leaf_idx);
            debug_assert_eq!(v.status, Present);

            'check_common_cherry: {
                let Some(parent_idx) = v.parent else {
                    break 'check_common_cherry;
                };

                let parent = f1.get(parent_idx);

                let Internal { left, right } = parent.data else {
                    break 'check_common_cherry;
                };

                let Leaf { label: label_left } = f1.get(left).data else {
                    break 'check_common_cherry;
                };
                let Leaf { label: label_right } = f1.get(right).data else {
                    break 'check_common_cherry;
                };

                // check if cherry (left, right) is common to all forests
                for forest in &self.forests[1..] {
                    let leaf1 = forest.locate_label(label_left);
                    let leaf2 = forest.locate_label(label_right);
                    if forest.get(leaf1).parent.is_none()
                        || forest.get(leaf1).parent != forest.get(leaf2).parent
                    {
                        break 'check_common_cherry;
                    }
                }

                // (arbitrarily) assign the new label to be the one with the lowest number
                let new_label = label_left.min(label_right);

                // apply merge in each forest
                self.merge_common_sibling(label_left, label_right, new_label);
                performed_reductions.push(LabelsMerged {
                    original1: label_left,
                    original2: label_right,
                    new_label,
                });

                // NOTE: all cut-opts containing the old-label and new-label should be
                // outdated cut-opts where the other is a s.v.t

                // queue up the new-label for (possibly) syncing svt's
                // or merging the (possibly) newly formed common cherry
                if to_check_set.insert(new_label) {
                    to_check.push(new_label);
                }
                continue 'outer;
            }

            'check_svt: {
                let mut is_svt_in_any = false;
                let mut is_svt_in_all = true;
                for f in self.forests.iter_mut() {
                    let label_idx = f.locate_label(label);
                    let is_svt_in_this_forests = f.get(label_idx).parent.is_none();

                    is_svt_in_all &= is_svt_in_this_forests;
                    is_svt_in_any |= is_svt_in_this_forests;
                }
                match (is_svt_in_any, is_svt_in_all) {
                    (_, true) => {
                        // label is already an svt in every forest
                    }
                    (false, false) => {
                        // label not an svt in any forest
                        break 'check_svt;
                    }
                    (true, false) => {
                        // label is an svt in some forests, but not all:
                        //  - make it an svt in all forests
                        let affected_sibling_labels = self.cut_svt_return_siblings_labels(label);

                        for sibling_label in affected_sibling_labels {
                            // queue up the all affected sibling labels to check them again
                            if to_check_set.insert(sibling_label) {
                                to_check.push(sibling_label);
                            }
                        }
                    }
                }

                // label is an svt in every forest: remove it from the instance
                self.remove_svt(label);
                n_removed_svts += 1;
                performed_reductions.push(SvtRemoved { label });
            }
        }

        (performed_reductions, n_removed_svts)
    }

    /// Find cherries s.t. in each forest
    /// - there are 0 or 1 pendant subtrees between it, and
    /// - the label set of these pendant subtrees is equal
    ///
    /// These pendant subtrees are cut
    /// NOTE: does NOT perform this reduction exhaustively
    ///
    /// Returns true if at least one reduction was applied
    fn rr_2_2_1_reduce(&mut self) -> bool {
        let mut applied_a_reduction = false;

        let cherries: Vec<(Label, Label)> = self
            .iterate_all_cherries()
            .map(|(_, a, b)| (a, b))
            .collect();

        'cherries: for (a, b) in cherries {
            // check if labels still exist (after previous reduction iterations)
            let f1 = &self.forests[0];
            if f1.try_locate_label(a).is_none() || f1.try_locate_label(b).is_none() {
                continue 'cherries;
            }

            // check if label is a cherry or uncle-nephew in every forest with the same label set
            let mut label_set_opt: Option<FxHashSet<Label>> = None;
            for forest in &self.forests {
                let leaf_a = forest.locate_label(a);
                let leaf_b = forest.locate_label(b);

                let Some(parent_a) = forest.get(leaf_a).parent else {
                    continue 'cherries;
                };
                let Some(parent_b) = forest.get(leaf_b).parent else {
                    continue 'cherries;
                };
                let sibling_a = forest.find_sibling(leaf_a).unwrap();
                let sibling_b = forest.find_sibling(leaf_b).unwrap();

                let pendant_subtree = if parent_a == parent_b {
                    // this is a cherry, no further checks needed
                    continue;
                } else if sibling_a == parent_b {
                    // a is the uncle of b: ((b,_), a)
                    sibling_b
                } else if sibling_b == parent_a {
                    // b is the uncle of a: ((a,_), b)
                    sibling_a
                } else {
                    // there is more than 1 pendant subtree between a and b
                    // (or they are in different components)
                    continue 'cherries;
                };

                let new_label_set = forest.dfs_from(pendant_subtree).labels().collect();
                if let Some(label_set) = &label_set_opt {
                    if new_label_set != *label_set {
                        continue 'cherries;
                    }
                } else {
                    label_set_opt = Some(new_label_set);
                }
            }

            // perform the cut in each forest (if not a cherry already)
            for forest in self.forests.iter_mut() {
                let leaf_a = forest.locate_label(a);
                let leaf_b = forest.locate_label(b);

                let parent_a = forest.get(leaf_a).parent.unwrap();
                let parent_b = forest.get(leaf_b).parent.unwrap();
                let sibling_a = forest.find_sibling(leaf_a).unwrap();
                let sibling_b = forest.find_sibling(leaf_b).unwrap();

                let pendant_subtree = if parent_a == parent_b {
                    // this is a cherry, no further checks needed
                    continue;
                } else if sibling_a == parent_b {
                    // a is the uncle of b: ((b,_), a)
                    sibling_b
                } else if sibling_b == parent_a {
                    // b is the uncle of a: ((a,_), b)
                    sibling_a
                } else {
                    // there is more than 1 pendant subtree between a and b
                    // (or they are in different components)
                    unreachable!("this cut should not have been performed");
                };

                forest.cut_branch(pendant_subtree);
            }
            applied_a_reduction = true;
        }
        applied_a_reduction
    }

    fn split_into_clusters(self) -> Vec<Instance> {
        let mut expanded_labels = FxHashSet::<Label>::default();
        let mut clusters: Vec<FxHashSet<Label>> = vec![];

        // loop through all labels, skipping the ones already processed
        for label in self.forests[0]
            .leaf_map
            .keys()
            .cloned()
            .collect::<Vec<Label>>()
        {
            if expanded_labels.contains(&label) {
                continue;
            }

            // collect all labels that are connected via some route
            // (possibly alternating between forests)
            let mut current_cluster = FxHashSet::<Label>::default();

            let mut to_expand = vec![label];
            let mut to_expand_set = FxHashSet::<Label>::from_iter(to_expand.clone());
            while let Some(neighbor) = to_expand.pop() {
                to_expand_set.remove(&neighbor);
                debug_assert_eq!(
                    FxHashSet::<Label>::from_iter(to_expand.clone()),
                    to_expand_set
                );

                if !expanded_labels.insert(neighbor) {
                    continue;
                }
                current_cluster.insert(neighbor);

                for f in self.forests.iter() {
                    let leaf = f.locate_label(neighbor);
                    let comp = f.find_root_of(leaf);
                    for neighbor2 in f.dfs_from(comp).labels() {
                        if !to_expand.contains(&neighbor2) && to_expand_set.insert(neighbor2) {
                            to_expand.push(neighbor2);
                        }
                    }
                }
            }
            clusters.push(current_cluster);
        }

        clusters
            .into_iter()
            .map(|cluster| self.copy_cluster(&cluster))
            .collect()
    }

    fn copy_cluster(&self, cluster_labels: &FxHashSet<Label>) -> Instance {
        Instance {
            num_leaves: cluster_labels.len(),
            forests: self
                .forests
                .iter()
                .map(|f| f.copy_cluster(cluster_labels))
                .collect(),
        }
    }

    fn find_clusters_w_dummy(
        &self,
    ) -> Option<(Instance, Instance, (Instance, Label), (Instance, Label))> {
        const MIN_CLUSTER_SIZE_BELOW: usize = 3;
        const MIN_CLUSTER_SIZE_ABOVE: usize = 3;

        let n = self.forests[0].leaf_map.len();
        let max_cluster_size = n.checked_sub(MIN_CLUSTER_SIZE_ABOVE)?;

        if n < MIN_CLUSTER_SIZE_BELOW + MIN_CLUSTER_SIZE_ABOVE {
            return None;
        }

        let goal = n / 2;

        // build map storing the label set of each subtree as
        // a sorted vec
        let mut clusters: Vec<FxHashMap<Vec<Label>, Idx>> = vec![];

        for f in self.forests.iter() {
            let mut label_sets: FxHashMap<Idx, Vec<Label>> = FxHashMap::default();
            for &root in f.roots.iter() {
                for (idx, node) in f.dfs_postorder(root) {
                    // NOTE: we skip roots here, because they are handled without dummies
                    if node.parent.is_none() {
                        continue;
                    }
                    let label_set = match node.data {
                        Internal { left, right } => {
                            kmerge([&label_sets[&left], &label_sets[&right]])
                                .copied()
                                .collect()
                        }
                        Leaf { label } => vec![label],
                    };

                    label_sets.insert(idx, label_set);
                }
            }

            // invert the map
            let node_of_label_set = label_sets.drain().map(|(k, v)| (v, k)).collect();
            clusters.push(node_of_label_set);
        }

        let Some((f1_clusters, other_clusters)) = clusters.split_first() else {
            unreachable!("can only try to find clusters on two or more trees");
        };

        let mut best_cluster: Option<&Vec<Label>> = None;

        for cluster in f1_clusters.keys() {
            let cluster_size = cluster.len();
            if cluster_size < MIN_CLUSTER_SIZE_BELOW || cluster_size > max_cluster_size {
                // this cluster cuts off too little nodes to be useful
                continue;
            }

            if best_cluster
                .is_some_and(|best| best.len().abs_diff(goal) < cluster_size.abs_diff(goal))
            {
                // this cluster is farther from the goal size than the current best cluster
                continue;
            }

            if other_clusters
                .iter()
                .any(|other| !other.contains_key(cluster))
            {
                // this is not a common cluster
                continue;
            }

            // this is a common cluster, better balanced than the current best
            best_cluster = Some(cluster);
        }

        let cluster = best_cluster?;

        // let dummy_label_above = Label(self.main.forests[0].max_label_value() + 1);
        let dummy_label_above = *cluster.iter().min().expect("at least one label in cluster");
        let dummy_label_below = Label(0);

        let mut cluster_above: Vec<ArenaTree> = vec![];
        let mut cluster_above_w_dummy: Vec<ArenaTree> = vec![];
        let mut cluster_below: Vec<ArenaTree> = vec![];
        let mut cluster_below_w_dummy: Vec<ArenaTree> = vec![];
        for (forest, clusters_f) in self.forests.iter().zip(clusters.iter()) {
            let cluster_subtree = clusters_f[cluster];
            let (forest_above, tree_below, forest_above_w_dummy, tree_below_w_dummy) =
                forest.clone().split_at_subtree_with_dummy(
                    cluster_subtree,
                    (dummy_label_above, dummy_label_below),
                );

            cluster_above.push(forest_above);
            cluster_above_w_dummy.push(forest_above_w_dummy);
            cluster_below.push(tree_below);
            cluster_below_w_dummy.push(tree_below_w_dummy);
        }

        let lsi_instance_above = Instance {
            forests: cluster_above,
            num_leaves: n - cluster.len(),
        };
        let lsi_instance_above_w_dummy = Instance {
            forests: cluster_above_w_dummy,
            num_leaves: n - cluster.len() + 1,
        };
        let lsi_instance_below = Instance {
            forests: cluster_below,
            num_leaves: cluster.len(),
        };
        let lsi_instance_below_w_dummy = Instance {
            forests: cluster_below_w_dummy,
            num_leaves: cluster.len() + 1,
        };

        Some((
            lsi_instance_above,
            lsi_instance_below,
            (lsi_instance_above_w_dummy, dummy_label_above),
            (lsi_instance_below_w_dummy, dummy_label_below),
        ))
    }
}

trait ReductionArenaTreeExt {
    /// exhaustively r1-reduce a pair of forests
    /// returns a tuple denoting for each forests if it changed
    /// uses a workspace to avoid (re)allocation
    fn r1_reduce_pair_w_workspace(
        a: &mut ArenaTree,
        b: &mut ArenaTree,
        workspace: &mut R1Workspace,
    ) -> (bool, bool);

    fn find_r1_target_with_w_workspace(
        &self,
        other: &ArenaTree,
        ws: &mut R1Workspace,
    ) -> Option<Idx>;

    fn copy_cluster(&self, cluster_labels: &FxHashSet<Label>) -> ArenaTree;

    fn split_at_subtree_with_dummy(
        self,
        subtree: Idx,
        dummy_labels: (Label, Label),
    ) -> (ArenaTree, ArenaTree, ArenaTree, ArenaTree)
    where
        Self: std::marker::Sized;
}

impl ReductionArenaTreeExt for ArenaTree {
    /// exhaustively r1-reduce a pair of forests
    /// returns a tuple denoting for each forests if it changed
    /// uses a workspace to avoid (re)allocation
    fn r1_reduce_pair_w_workspace(
        a: &mut ArenaTree,
        b: &mut ArenaTree,
        workspace: &mut R1Workspace,
    ) -> (bool, bool) {
        // keep reducing until it is not applicable in either direction
        let mut a_changed = false;
        let mut b_changed = false;
        loop {
            if let Some(cut) = a.find_r1_target_with_w_workspace(b, workspace) {
                a_changed = true;
                a.cut_branch(cut);
                // a.cut_branch(cut, false);
            } else if let Some(cut) = b.find_r1_target_with_w_workspace(a, workspace) {
                b_changed = true;
                b.cut_branch(cut);
                // b.cut_branch(cut, false);
            } else {
                break;
            }
        }
        (a_changed, b_changed)
    }

    fn find_r1_target_with_w_workspace(
        &self,
        other: &ArenaTree,
        ws: &mut R1Workspace,
    ) -> Option<Idx> {
        for &root_other in other.roots.iter() {
            for label in other.dfs_from(root_other).labels() {
                ws.label_to_root[label.0 as usize] = root_other;
            }
        }

        for &root in self.roots.iter() {
            ws.component_labels.advance();
            for label in self.dfs_from(root).labels() {
                ws.component_labels.insert(label.0 as usize);
            }
            'vertices_in_comp: for v in self.dfs_from(root).indices() {
                if v == root {
                    continue;
                }
                ws.subtree_labels.advance();
                for label in self.dfs_from(v).labels() {
                    ws.subtree_labels.insert(label.0 as usize);
                }

                ws.checked_roots.advance();
                for label in self.dfs_from(v).labels() {
                    let root_other = ws.label_to_root[label.0 as usize];
                    debug_assert!((root_other as usize) < other.arena.len());
                    if ws.checked_roots.contains(root_other as usize) {
                        continue;
                    }
                    ws.checked_roots.insert(root_other as usize);

                    for Label(label_other) in other.dfs_from(root_other).labels() {
                        if ws.component_labels.contains(label_other as usize)
                            && !ws.subtree_labels.contains(label_other as usize)
                        {
                            continue 'vertices_in_comp;
                        }
                    }
                }
                // at this point all components in other overlapping with this subtree
                // have all their labels either not in this component or inside of this subtree
                return Some(v);
            }
        }

        None
    }

    fn copy_cluster(&self, cluster_labels: &FxHashSet<Label>) -> ArenaTree {
        let roots: FxHashSet<Idx> = cluster_labels
            .iter()
            .map(|&label| self.find_root_of(self.locate_label(label)))
            .collect();
        let indices_of_subtree: FxHashSet<Idx> = roots
            .iter()
            .flat_map(|&root| self.dfs_from(root).indices())
            .collect();

        let mut translation: FxHashMap<Idx, Idx> = FxHashMap::default();

        let mut new_arena = vec![];
        for (idx, node) in self.arena.iter().cloned().enumerate() {
            if node.status != Present {
                continue;
            }
            if indices_of_subtree.contains(&(idx as Idx)) {
                let new_idx = new_arena.len() as Idx;
                new_arena.push(node);
                translation.insert(idx as Idx, new_idx);
            }
        }

        let new_roots: FxHashSet<Idx> = new_arena
            .iter()
            .enumerate()
            .filter_map(|(idx, node)| node.parent.is_none().then_some(idx as Idx))
            .collect();

        let new_leaf_map: FxHashMap<Label, Idx> = new_arena
            .iter()
            .enumerate()
            .filter_map(|(idx, node)| node.label().map(|label| (label, idx as Idx)))
            .collect();

        for node in new_arena.iter_mut() {
            node.parent = node.parent.map(|p| translation[&p]);
            node.data = match node.data.clone() {
                Internal { left, right } => Internal {
                    left: translation[&left],
                    right: translation[&right],
                },
                leaf => leaf,
            };
        }

        ArenaTree {
            arena: new_arena,
            roots: new_roots,
            leaf_map: new_leaf_map,
        }
    }

    fn split_at_subtree_with_dummy(
        mut self,
        subtree: Idx,
        (dummy_label_above, dummy_label_below): (Label, Label),
    ) -> (ArenaTree, ArenaTree, ArenaTree, ArenaTree) {
        // store the sibling of the subtree, to later insert the dummy leaf as a sibling again
        let sibling_of_cut = self.find_sibling(subtree);

        if self.get(subtree).parent.is_some() {
            self.cut_branch(subtree);
        }

        let indices_of_subtree: FxHashSet<Idx> = self.dfs_from(subtree).indices().collect();

        let mut translation_above: FxHashMap<Idx, Idx> = FxHashMap::default();
        let mut translation_below: FxHashMap<Idx, Idx> = FxHashMap::default();

        let mut above = vec![];
        let mut below = vec![];
        for (idx, node) in self.arena.iter().cloned().enumerate() {
            if node.status != Present {
                continue;
            }
            if indices_of_subtree.contains(&(idx as Idx)) {
                let new_idx = below.len() as Idx;
                below.push(node);
                translation_below.insert(idx as Idx, new_idx);
            } else {
                let new_idx = above.len() as Idx;
                above.push(node);
                translation_above.insert(idx as Idx, new_idx);
            }
        }

        let roots_above: FxHashSet<Idx> = above
            .iter()
            .enumerate()
            .filter_map(|(idx, node)| node.parent.is_none().then_some(idx as Idx))
            .collect();
        let roots_below: FxHashSet<Idx> = below
            .iter()
            .enumerate()
            .filter_map(|(idx, node)| node.parent.is_none().then_some(idx as Idx))
            .collect();

        let leaf_map_above: FxHashMap<Label, Idx> = above
            .iter()
            .enumerate()
            .filter_map(|(idx, node)| node.label().map(|label| (label, idx as Idx)))
            .collect();
        let leaf_map_below: FxHashMap<Label, Idx> = below
            .iter()
            .enumerate()
            .filter_map(|(idx, node)| node.label().map(|label| (label, idx as Idx)))
            .collect();

        for node in above.iter_mut() {
            node.parent = node.parent.map(|p| translation_above[&p]);
            node.data = match node.data.clone() {
                Internal { left, right } => Internal {
                    left: translation_above[&left],
                    right: translation_above[&right],
                },
                leaf => leaf,
            };
        }
        for node in below.iter_mut() {
            node.parent = node.parent.map(|p| translation_below[&p]);
            node.data = match node.data.clone() {
                Internal { left, right } => Internal {
                    left: translation_below[&left],
                    right: translation_below[&right],
                },
                leaf => leaf,
            };
        }

        let (c_above, c_below) = (
            ArenaTree {
                arena: above,
                roots: roots_above,
                leaf_map: leaf_map_above,
            },
            ArenaTree {
                arena: below,
                roots: roots_below,
                leaf_map: leaf_map_below,
            },
        );

        // add the dummy leaves:
        // - for instance above:
        //  subdivide the edge above the sibling and give it dummy as other child

        // - for instance below:
        //  add a parent to the root (i.e., subtree) and give it dummy as other child
        let mut c_above_dummy = c_above.clone();
        c_above_dummy.add_dummy_leaf_as_sibling_of(
            dummy_label_above,
            sibling_of_cut.map(|sibling| translation_above[&sibling]),
        );
        let mut c_below_dummy = c_below.clone();
        c_below_dummy
            .add_dummy_leaf_as_sibling_of(dummy_label_below, Some(translation_below[&subtree]));

        (c_above, c_below, c_above_dummy, c_below_dummy)
    }
}

pub struct R1Workspace {
    /// label -> root idx in "other" forest; indexed by label.
    pub label_to_root: Vec<Idx>,
    /// component label membership; indexed by label.
    pub component_labels: GenerationSet,
    /// subtree label membership; indexed by label.
    pub subtree_labels: GenerationSet,
    /// whether we've already checked an other-root for the current vertex; indexed by node idx.
    pub checked_roots: GenerationSet,
}

impl R1Workspace {
    pub fn new(max_label: usize, max_node: usize) -> Self {
        Self {
            label_to_root: vec![Idx::MAX; max_label + 1],
            component_labels: GenerationSet::new(max_label + 1),
            subtree_labels: GenerationSet::new(max_label + 1),
            checked_roots: GenerationSet::new(max_node + 1),
        }
    }
}
