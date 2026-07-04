use pace26io::binary_tree::IndexedBinTreeBuilder;
use pace26io::pace;

use super::arena_tree::ArenaTree;
use super::arena_vertex::{Idx, Label};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instance {
    pub num_leaves: usize,
    pub forests: Vec<ArenaTree>,
}

impl Instance {
    /// Assumes forests are fully cherry merged
    pub fn is_completed(&self) -> bool {
        self.forests[0].iterate_cherries().next().is_none()
    }

    #[inline]
    pub fn iterate_all_cherries(&self) -> impl Iterator<Item = (Idx, Label, Label)> {
        self.forests
            .iter()
            .flat_map(|forest| forest.iterate_cherries())
    }

    pub fn ord(&self) -> usize {
        self.forests
            .iter()
            .map(|forest| forest.ord())
            .max()
            .expect("at least one forest in an instance")
    }

    pub fn remove_svt(&mut self, label: Label) {
        for f in self.forests.iter_mut() {
            f.remove_svt(label);
        }

        self.num_leaves -= 1;
    }

    /// Cut off a single label, making it a single vertex tree in each forest
    /// Returns the labels of all siblings (across the forests) of the cut (may contain duplicates)
    pub fn cut_svt_return_siblings_labels(&mut self, label: Label) -> Vec<Label> {
        let mut sibling_labels = vec![];

        // perform the cut in each forest
        for forest in self.forests.iter_mut() {
            let leaf_a_idx = forest.locate_label(label);
            if forest.get(leaf_a_idx).parent.is_some() {
                // find and store the label of the sibling of the cut
                let sibling = forest
                    .find_sibling(leaf_a_idx)
                    .expect("a sibling when it has a parent");
                if let Some(sibling_label) = forest.get(sibling).label() {
                    sibling_labels.push(sibling_label);
                }

                // perform the cut
                forest.cut_branch(leaf_a_idx);
            }
        }
        sibling_labels
    }

    pub fn merge_common_sibling(&mut self, label_a: Label, label_b: Label, new_label: Label) {
        debug_assert_ne!(label_a, label_b);

        for f in self.forests.iter_mut() {
            let left_idx = f.locate_label(label_a);
            let right_idx = f.locate_label(label_b);
            let parent = f
                .get(left_idx)
                .parent
                .expect("expected sibling pair to have a parent");

            f.apply_merge(parent, left_idx, right_idx, new_label);
        }

        // we merge 2 labels into 1: #leaves decreased by 1 in all forests
        self.num_leaves -= 1;
    }

    pub fn extract_af(&mut self) -> ArenaTree {
        self.forests.swap_remove(0)
    }

    // Create new instance from IndexedBinTreeBuilder instance
    pub fn new_from_instance(
        instance: pace::simplified::Instance<IndexedBinTreeBuilder>,
    ) -> Instance {
        assert!(
            instance.trees.len() >= 2,
            "Instance expects at leats two trees"
        );
        let forests = instance
            .trees
            .iter()
            .map(ArenaTree::new_from_indexed_bin_tree)
            .collect();
        Instance {
            num_leaves: instance.num_leaves,
            forests,
        }
    }

    #[cfg(feature = "assert_validity")]
    pub fn assert_validity(&self) {
        for f in self.forests.iter() {
            f.assert_validity();
        }
    }
}
