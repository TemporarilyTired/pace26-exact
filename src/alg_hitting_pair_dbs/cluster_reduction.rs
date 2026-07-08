use itertools::kmerge;
use rustc_hash::{FxHashMap, FxHashSet};

use super::hitting_pair_dbs::{State, calc_expensive_lb_and_ub, cherry_dbs};
use crate::common::validity::assert_validity;
use crate::maf_instance::{
    arena_tree::ArenaTree,
    arena_vertex::{Idx, Label, NodeData::*, Status::*},
    instance::Instance,
    tree_traversal::TreeTraversal,
};

// Try to find an agreement forest of clusters a and b s.t. ord(a)+ord(b) <= k
// Otherwise returns None
pub fn solve_split(cluster_a: State, cluster_b: State, k: usize) -> Option<(ArenaTree, ArenaTree)> {
    // NOTE: post-submission bug-fix:
    // Removed call to `cluster_a.get_matching_lb()` and its resulting lower bounds
    let (_, lb_a) = calc_expensive_lb_and_ub(cluster_a.clone());
    let remaining_k_for_b = k.checked_sub(lb_a)?;

    let mut sol_b = cherry_dbs(cluster_b.clone(), remaining_k_for_b, false)?;
    let mut ub_b = sol_b.ord();
    let mut maybe_sol_a = cherry_dbs(cluster_a.clone(), k.checked_sub(ub_b).unwrap(), false);
    loop {
        if let Some(sol_a) = maybe_sol_a {
            return Some((sol_a, sol_b));
        }
        sol_b = cherry_dbs(cluster_b.clone(), ub_b.checked_sub(1)?, false)?;
        ub_b = sol_b.ord();
        maybe_sol_a = cherry_dbs(cluster_a.clone(), k.checked_sub(ub_b)?, false);
    }
}

// Try to find an agreement forest of clusters a and b s.t. ord(a)+ord(b) <= k
// Otherwise returns None
pub fn solve_split_with_dummy(
    above: State,
    below: State,
    (above_with_dummy, used_dummy_above): (State, Label),
    (below_with_dummy, used_dummy_below): (State, Label),
    k: usize,
) -> Option<ArenaTree> {
    let ord_a = above.instance.ord();
    let mut sol_b = cherry_dbs(
        below.clone(),
        (k + 1).checked_sub(ord_a)?.min(below.instance.num_leaves),
        false,
    )?;
    let mut ub_b = sol_b.ord();
    let mut maybe_sol_a = cherry_dbs(above.clone(), (k + 1).checked_sub(ub_b).unwrap(), false);
    while maybe_sol_a.is_none() {
        sol_b = cherry_dbs(below.clone(), ub_b.checked_sub(1)?, false)?;
        ub_b = sol_b.ord();
        maybe_sol_a = cherry_dbs(above.clone(), (k + 1).checked_sub(ub_b)?, false);
    }
    // we have found a solution of <= k+1

    let sol_a = maybe_sol_a.unwrap();
    let ord_a = sol_a.ord();
    let ord_b = ub_b;
    debug_assert_eq!(ord_b, sol_b.ord());

    // if we are lucky: we have a solution of <= k already
    if ord_a + ord_b <= k {
        return Some(sol_a.join_with(sol_b));
    }

    // we found a solution of size exactly k+1: try to decrease it to k
    if let Some(smaller_sol_b) = cherry_dbs(below.clone(), ord_b - 1, false) {
        return Some(sol_a.join_with(smaller_sol_b));
    }
    if let Some(smaller_sol_a) = cherry_dbs(above.clone(), ord_a - 1, false) {
        return Some(smaller_sol_a.join_with(sol_b));
    }

    // decreasing to k failed: see if clusters with dummies have the same optimal
    // if so: join them into a solution of size k
    let sol_a_w_dummy = cherry_dbs(above_with_dummy, ord_a, false)?;
    let sol_b_w_dummy = cherry_dbs(below_with_dummy, ord_b, false)?;
    debug_assert!(
        sol_a_w_dummy
            .get(sol_a_w_dummy.locate_label(used_dummy_above))
            .parent
            .is_some()
    );
    debug_assert!(
        sol_b_w_dummy
            .get(sol_b_w_dummy.locate_label(used_dummy_below))
            .parent
            .is_some()
    );
    Some(sol_a_w_dummy.join_at_dummy(sol_b_w_dummy, used_dummy_above, used_dummy_below))
}

impl State {
    pub fn find_clusters_component(&self) -> Option<(State, State)> {
        const MIN_CLUSTER_SIZE_BELOW: usize = 1;
        const MIN_CLUSTER_SIZE_ABOVE: usize = 1;

        let ord = self.instance.ord();
        let n = self.instance.forests[0].leaf_map.len();
        let max_cluster_size = n.checked_sub(MIN_CLUSTER_SIZE_ABOVE)?;
        let corrected_max_cluster_size = max_cluster_size.checked_sub(ord - 1)?;

        if n < MIN_CLUSTER_SIZE_BELOW + corrected_max_cluster_size {
            return None;
        }

        // build map storing the label set of each subtree as
        // a sorted vec
        let mut clusters: Vec<FxHashMap<Vec<Label>, Idx>> = vec![];

        for f in self.instance.forests.iter() {
            let mut label_sets: FxHashMap<Idx, Vec<Label>> = FxHashMap::default();
            for &root in f.roots.iter() {
                for (idx, node) in f.dfs_postorder(root) {
                    let label_set = match node.data {
                        Internal { left, right } => kmerge(vec![
                            label_sets.get(&left).unwrap(),
                            label_sets.get(&right).unwrap(),
                        ])
                        .copied()
                        .collect(),
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

            if cluster_size < MIN_CLUSTER_SIZE_BELOW || cluster_size > corrected_max_cluster_size {
                // this cluster cuts off too little nodes to be useful
                // clusters of size 3 (or n-3) are also useless, because
                // reduction rule 2.2.1 is always applicable on clusters of size 3
                // resulting in zero branches in the clusters
                continue;
            }

            if best_cluster
                .is_some_and(|best| best.len().abs_diff(n / 2) < cluster_size.abs_diff(n / 2))
            {
                // this cluster is farther from size n/2 than the current best cluster
                continue;
            }

            if other_clusters
                .iter()
                .any(|other| !other.contains_key(cluster))
            {
                // this is not a common cluster
                continue;
            }

            if clusters
                .iter()
                .zip(self.instance.forests.iter())
                .all(|(other, f)| f.get(other[cluster]).parent.is_some())
            {
                // this is not a component in any forests
                // i.e., the cluster is part of a larger component in all forests
                continue;
            }

            // this is a common cluster, better balanced than the current best
            best_cluster = Some(cluster);
        }

        let cluster = best_cluster?;

        let mut cluster_above: Vec<ArenaTree> = vec![];
        let mut cluster_below: Vec<ArenaTree> = vec![];
        for (forest, clusters_f) in self.instance.forests.iter().zip(clusters.iter()) {
            let cluster_subtree = clusters_f[cluster];
            let (forest_above, tree_below) = forest
                .clone()
                .split_at_subtree_w_dummy(cluster_subtree, None);

            cluster_above.push(forest_above);
            cluster_below.push(tree_below);
        }

        let instance_above = Instance {
            forests: cluster_above,
            num_leaves: n - cluster.len(),
        };
        let instance_below = Instance {
            forests: cluster_below,
            num_leaves: cluster.len(),
        };
        assert_validity!(instance_above);
        assert_validity!(instance_below);

        let labels_cluster: FxHashSet<Label> = cluster.iter().copied().collect();

        let cut_opts_above: FxHashSet<(Label, Label)> = self
            .cut_opts
            .iter()
            .filter(|(a, b)| !labels_cluster.contains(a) && !labels_cluster.contains(b))
            .copied()
            .collect();
        let cut_opts_below: FxHashSet<(Label, Label)> = self
            .cut_opts
            .iter()
            .filter(|(a, b)| labels_cluster.contains(a) && labels_cluster.contains(b))
            .copied()
            .collect();

        let state_above = State {
            instance: instance_above,
            cut_opts: cut_opts_above,
        };
        let state_below = State {
            instance: instance_below,
            cut_opts: cut_opts_below,
        };

        Some((state_above, state_below))
    }

    #[allow(clippy::type_complexity)]
    pub fn find_clusters_w_dummy(&self) -> Option<(State, State, (State, Label), (State, Label))> {
        const MIN_CLUSTER_SIZE_BELOW: usize = 5;
        const MIN_CLUSTER_SIZE_ABOVE: usize = 5;

        let ord = self.instance.ord();
        let n = self.instance.forests[0].leaf_map.len();

        let max_cluster_size = n.checked_sub(MIN_CLUSTER_SIZE_ABOVE)?;
        let corrected_max_cluster_size = max_cluster_size.checked_sub(ord - 1)?;

        if n < MIN_CLUSTER_SIZE_BELOW + corrected_max_cluster_size {
            return None;
        }

        let goal = (n.checked_sub(ord - 1)? as f64 * 0.5).floor() as usize;
        // let goal = (n.checked_sub(ord - 1)? as f64 * 0.75).floor() as usize;

        // build map storing the label set of each subtree as
        // a sorted vec
        let mut clusters: Vec<FxHashMap<Vec<Label>, Idx>> = vec![];

        for f in self.instance.forests.iter() {
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
            if cluster_size < MIN_CLUSTER_SIZE_BELOW || cluster_size > corrected_max_cluster_size {
                // this cluster cuts off too little nodes to be useful
                // clusters of size 3 are also useless, because
                // reduction rule 2.2.1 is always applicable on clusters of size 3
                // resulting in zero branches in the clusters
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

        // NOTE: We can use any label in the common-cluster as the dummy label for the cluster above
        // NOTE: We can use any designated label as dummy label for the cluster below, because
        // any previous occurence of that label will be cut from it by this procedure.
        //
        // This allows for 'global caching' of the solutions to these clusters as well
        // let dummy_label_above = Label(self.instance.forests[0].max_label_value() + 1);
        let dummy_label_above = *cluster.iter().min().expect("at least one label in cluster");
        let dummy_label_below = Label(0);

        let mut cluster_above: Vec<ArenaTree> = vec![];
        let mut cluster_above_w_dummy: Vec<ArenaTree> = vec![];
        let mut cluster_below: Vec<ArenaTree> = vec![];
        let mut cluster_below_w_dummy: Vec<ArenaTree> = vec![];
        for (forest, clusters_f) in self.instance.forests.iter().zip(clusters.iter()) {
            let cluster_subtree = clusters_f[cluster];
            let (forest_above, tree_below) = forest
                .clone()
                .split_at_subtree_w_dummy(cluster_subtree, None);
            let (forest_above_w_dummy, tree_below_w_dummy) =
                forest.clone().split_at_subtree_w_dummy(
                    cluster_subtree,
                    Some((dummy_label_above, dummy_label_below)),
                );
            debug_assert!(!tree_below.leaf_map.contains_key(&Label(0)));

            cluster_above.push(forest_above);
            cluster_above_w_dummy.push(forest_above_w_dummy);
            cluster_below.push(tree_below);
            cluster_below_w_dummy.push(tree_below_w_dummy);
        }

        let instance_above = Instance {
            forests: cluster_above,
            num_leaves: n - cluster.len(),
        };
        let instance_above_w_dummy = Instance {
            forests: cluster_above_w_dummy,
            num_leaves: n - cluster.len() + 1,
        };
        let instance_below = Instance {
            forests: cluster_below,
            num_leaves: cluster.len(),
        };
        let instance_below_w_dummy = Instance {
            forests: cluster_below_w_dummy,
            num_leaves: cluster.len() + 1,
        };
        assert_validity!(instance_above);
        assert_validity!(instance_above_w_dummy);
        assert_validity!(instance_below);
        assert_validity!(instance_below_w_dummy);

        let labels_cluster: FxHashSet<Label> = cluster.iter().copied().collect();

        // Assert that all cut opts are either fully inside or fully outside the cluster
        // This is true because cut opts must always be a cherry in some forest
        debug_assert!(
            self.cut_opts
                .iter()
                .all(|(a, b)| labels_cluster.contains(a) == labels_cluster.contains(b))
        );
        let cut_opts_above: FxHashSet<(Label, Label)> = self
            .cut_opts
            .iter()
            .filter(|(a, b)| !labels_cluster.contains(a) && !labels_cluster.contains(b))
            .copied()
            .collect();
        let cut_opts_below: FxHashSet<(Label, Label)> = self
            .cut_opts
            .iter()
            .filter(|(a, b)| labels_cluster.contains(a) && labels_cluster.contains(b))
            .copied()
            .collect();

        let state_above = State {
            instance: instance_above,
            cut_opts: cut_opts_above.clone(),
        };
        let state_above_w_dummy = State {
            instance: instance_above_w_dummy,
            cut_opts: cut_opts_above,
        };
        let state_below = State {
            instance: instance_below,
            cut_opts: cut_opts_below.clone(),
        };
        let state_below_w_dummy = State {
            instance: instance_below_w_dummy,
            cut_opts: cut_opts_below,
        };

        Some((
            state_above,
            state_below,
            (state_above_w_dummy, dummy_label_above),
            (state_below_w_dummy, dummy_label_below),
        ))
    }
}

impl ArenaTree {
    pub fn split_at_subtree_w_dummy(
        mut self,
        subtree: Idx,
        dummy_labels_opt: Option<(Label, Label)>,
    ) -> (ArenaTree, ArenaTree) {
        assert_validity!(self);

        // store the sibling of the subtree, to later insert the dummy leaf as a sibling again
        let sibling_of_cut = self.find_sibling(subtree);

        if self.get(subtree).parent.is_some() {
            self.cut_branch(subtree);

            debug_assert_eq!(
                subtree,
                self.find_root_of(
                    self.locate_label(
                        self.dfs_from(subtree)
                            .labels()
                            .next()
                            .expect("at least one label")
                    )
                )
            );
        }

        let indices_of_subtree: FxHashSet<Idx> = self.dfs_from(subtree).indices().collect();

        let mut translation_above: FxHashMap<Idx, Idx> = FxHashMap::default();
        let mut translation_below: FxHashMap<Idx, Idx> = FxHashMap::default();

        let mut above = vec![];
        let mut below = vec![];
        for (idx, node) in self.arena.into_iter().enumerate() {
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

        let (mut c_above, mut c_below) = (
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

        assert_validity!(c_above);
        assert_validity!(c_below);

        // possibly add the dummy leaf:
        // - for instance above:
        //  subdivide the edge above the sibling and give it dummy as other child

        // - for instance below:
        //  add a parent to the root (i.e., subtree) and give it dummy as other child
        if let Some((dummy_label_above, dummy_label_below)) = dummy_labels_opt {
            c_above.add_dummy_leaf_as_sibling_of(
                dummy_label_above,
                sibling_of_cut.map(|sibling| translation_above[&sibling]),
            );
            c_below
                .add_dummy_leaf_as_sibling_of(dummy_label_below, Some(translation_below[&subtree]));
            assert_validity!(c_above);
            assert_validity!(c_below);
        }

        (c_above, c_below)
    }
}
