use smallvec::SmallVec;

use super::{
    arena_tree::ArenaTree,
    arena_vertex::{Idx, Label, Node, NodeData::*, Status::*},
};

// implement dfs traversal for arena forest
impl ArenaTree {
    pub fn dfs_from(&self, start: Idx) -> Dfs<'_> {
        let mut stack = SmallVec::<[Idx; 16]>::new();
        stack.push(start);
        Dfs { tree: self, stack }
    }
    pub fn dfs_postorder(&self, start: Idx) -> DfsPostOrder<'_> {
        DfsPostOrder::new(self, start)
    }
}

#[allow(unused)]
pub trait TreeTraversal<'a>: Iterator<Item = (Idx, &'a Node)> + Sized {
    fn labels(self) -> impl Iterator<Item = Label> + 'a
    where
        Self: 'a,
    {
        self.filter_map(|(_, node)| match node.data {
            Leaf { label } => Some(label),
            _ => None,
        })
    }

    fn indices(self) -> impl Iterator<Item = Idx> + 'a
    where
        Self: 'a,
    {
        self.map(|(idx, _)| idx)
    }

    fn leaves(self) -> impl Iterator<Item = (Idx, Label)> + 'a
    where
        Self: 'a,
    {
        self.filter_map(|(idx, node)| match node.data {
            Leaf { label } => Some((idx, label)),
            _ => None,
        })
    }

    fn internals(self) -> impl Iterator<Item = (Idx, Idx, Idx)> + 'a
    where
        Self: 'a,
    {
        self.filter_map(|(idx, node)| match node.data {
            Internal { left, right } => Some((idx, left, right)),
            _ => None,
        })
    }
}

/// Blanket impl: anything that iterates (Idx, &Node) gets the extensions.
impl<'a, T> TreeTraversal<'a> for T where T: Iterator<Item = (Idx, &'a Node)> {}

pub struct Dfs<'a> {
    tree: &'a ArenaTree,
    stack: SmallVec<[Idx; 16]>,
}

impl<'a> Iterator for Dfs<'a> {
    type Item = (Idx, &'a Node);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(idx) = self.stack.pop() {
            let node = &self.tree.get(idx);

            debug_assert_eq!(
                node.status, Present,
                "Iterating non-present nodes is undefined behaviour"
            );

            // Push children first (right first so left is visited first)
            if let Internal { left, right } = node.data {
                self.stack.push(right);
                self.stack.push(left);
            }

            return Some((idx, node));
        }

        None
    }
}

pub struct DfsPostOrder<'a> {
    tree: &'a ArenaTree,
    current: Option<Idx>,
    root: Idx,
}

impl<'a> DfsPostOrder<'a> {
    pub fn new(tree: &'a ArenaTree, root: Idx) -> Self {
        Self {
            tree,
            current: Some(Self::leftmost_leaf(tree, root)),
            root,
        }
    }

    /// Descend to the leftmost leaf from `idx`.
    fn leftmost_leaf(tree: &ArenaTree, mut idx: Idx) -> Idx {
        loop {
            match tree.get(idx).data {
                Internal { left, .. } => idx = left,
                Leaf { .. } => return idx,
            }
        }
    }
}

impl<'a> Iterator for DfsPostOrder<'a> {
    type Item = (Idx, &'a Node);

    fn next(&mut self) -> Option<Self::Item> {
        let idx = self.current?;
        let node = self.tree.get(idx);

        // Determine the next node in post-order
        if idx == self.root {
            // We just emitted the root — we're done
            self.current = None;
        } else {
            let parent_idx = node.parent.expect("non-root must have parent");
            let parent = self.tree.get(parent_idx);

            match parent.data {
                Internal { left, right } if left == idx && right != idx => {
                    // We're the left child — next is the leftmost leaf
                    // of the right subtree, then back up to parent
                    self.current = Some(Self::leftmost_leaf(self.tree, right));
                }
                _ => {
                    // We're the right child (or only child) — parent is next
                    self.current = Some(parent_idx);
                }
            }
        }

        Some((idx, node))
    }
}

impl<'a> Dfs<'a> {
    pub fn cherries(self) -> impl Iterator<Item = (Idx, Label, Label)> {
        let tree = self.tree;
        self.filter_map(|(idx, node)| {
            if let &Internal { left, right } = &node.data
                && let Leaf { label: label_left } = tree.get(left).data
                && let Leaf { label: label_right } = tree.get(right).data
            {
                Some((idx, label_left, label_right))
            } else {
                None
            }
        })
    }
}

impl<'a> DfsPostOrder<'a> {
    pub fn cherries(self) -> impl Iterator<Item = (Idx, Label, Label)> {
        let tree = self.tree;
        self.filter_map(|(idx, node)| {
            if let &Internal { left, right } = &node.data
                && let Leaf { label: label_left } = tree.get(left).data
                && let Leaf { label: label_right } = tree.get(right).data
            {
                Some((idx, label_left, label_right))
            } else {
                None
            }
        })
    }
}
