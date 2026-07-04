use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};

use crate::alg_af_dfs::state::ConstraintHashSet;
use crate::maf_instance::{
    arena_tree::ArenaTree,
    arena_vertex::{Idx, Label, NodeData::*},
    instance::Instance,
    tree_traversal::TreeTraversal,
};

pub trait AfDbsInstanceExt {
    fn calculate_lcas(&self) -> Vec<Vec<Vec<usize>>>;

    fn find_incompatible_triples_and_extensions(
        &self,
        labels: &[Label],
        lcas: &[Vec<Vec<usize>>],
        comp_groups: &[usize],
    ) -> (
        ConstraintHashSet,
        (Option<FxHashMap<u128, ComponentExtensions>>, usize),
    );

    fn find_non_crossing_paths_in_any(
        &self,
        labels: &[Label],
        lcas: &[Vec<Vec<usize>>],
        comp_groups: &[usize],
    ) -> Vec<u64>;
    fn try_find_non_crossing_paths_in_any(
        &self,
        labels: &[Label],
        lcas: &[Vec<Vec<usize>>],
        comp_groups: &[usize],
        max_n_path_pairs: usize,
    ) -> Option<Vec<u64>>;

    fn calculate_comp_groups(&self) -> Vec<usize>;
}

impl AfDbsInstanceExt for Instance {
    /// calculate the 2d map of the lca of two nodes for each forest
    fn calculate_lcas(&self) -> Vec<Vec<Vec<usize>>> {
        // NOTE: this could be way more efficient; but even this takes negligible time
        // since it is only used once per instance
        debug_assert!(!self.forests.is_empty());

        let n_forests = self.forests.len();
        let n_nodes = self
            .forests
            .iter()
            .map(|f| f.arena.len())
            .max()
            .unwrap_or_default();
        let mut lcas: Vec<Vec<Vec<usize>>> =
            vec![vec![vec![usize::MAX; n_nodes]; n_nodes]; n_forests];
        for (lcas_f, f) in lcas.iter_mut().zip_eq(self.forests.iter()) {
            for &root in f.roots.iter() {
                for (node_idx, node) in f.dfs_from(root) {
                    let node_idx_u = node_idx as usize;
                    match node.data {
                        Leaf { .. } => lcas_f[node_idx_u][node_idx_u] = node_idx_u,
                        Internal { left, right } => {
                            let parent: u16 = node_idx;
                            let parent_u: usize = node_idx_u;
                            let left_indices: Vec<Idx> =
                                f.dfs_from(left).indices().chain([parent]).collect();
                            let right_indices: Vec<Idx> =
                                f.dfs_from(right).indices().chain([parent]).collect();
                            for left_idx in left_indices {
                                for &right_idx in right_indices.iter() {
                                    lcas_f[left_idx as usize][right_idx as usize] = parent_u;
                                    lcas_f[right_idx as usize][left_idx as usize] = parent_u;
                                }
                            }
                        }
                    }
                }
            }
        }
        lcas
    }

    /// Calculate a comp-group identifier for each label s.t.
    /// the identifier is equal for labels a and b iff labels
    /// a and b are in the same component in every forest
    fn calculate_comp_groups(&self) -> Vec<usize> {
        let mut comp_groups: Vec<usize> =
            vec![usize::MAX; self.forests[0].max_label_value() as usize + 1];
        let mut comp_identifier: FxHashMap<Vec<Idx>, usize> = FxHashMap::default();
        for label in self.forests[0].iterate_all().labels() {
            let roots_of_label: Vec<Idx> = self
                .forests
                .iter()
                .map(|f| f.find_root_of(f.locate_label(label)))
                .collect();
            if let Some(&comp_group) = comp_identifier.get(&roots_of_label) {
                comp_groups[label.0 as usize] = comp_group;
            } else {
                let ident = comp_identifier.len();
                comp_identifier.insert(roots_of_label, ident);
                comp_groups[label.0 as usize] = ident;
            }
        }
        comp_groups
    }

    /// Find all pairs of pairs of labels that are disjoint in each input tree.
    /// Uses pre-calculated map of lcas of each pair of nodes in each tree
    /// Is the complement of 'find_crossing_paths_in_any', with the same complexity
    /// (when implemented the same way), but returns 50%-95% less pairs.
    /// WARN: result can be over 2BG of memory if trees have >300 labels
    fn find_non_crossing_paths_in_any(
        &self,
        labels: &[Label],
        lcas: &[Vec<Vec<usize>>],
        comp_groups: &[usize],
    ) -> Vec<u64> {
        let n_forests = self.forests.len();
        let max_label = labels.iter().max().unwrap_or(&Label(0)).0 as usize;
        let max_node_idx = self
            .forests
            .iter()
            .map(|f| f.arena.len())
            .max()
            .unwrap_or_default();

        // n^2 is a conservative guess on #non-crossing pairs
        let mut res: Vec<_> = Vec::with_capacity(labels.len() * labels.len());

        // NOTE: pre-calculate lca of each pair of labels in each tree
        let mut label_lcas: Vec<Vec<Vec<usize>>> =
            vec![vec![vec![usize::MAX; max_label + 1]; max_label + 1]; n_forests];
        for ((label_lcas_f, lcas_f), f) in label_lcas
            .iter_mut()
            .zip_eq(lcas.iter())
            .zip_eq(&self.forests)
        {
            for &a in labels.iter() {
                let leaf_a = f.locate_label(a) as usize;
                for &b in labels.iter() {
                    let leaf_b = f.locate_label(b) as usize;
                    label_lcas_f[a.0 as usize][b.0 as usize] = lcas_f[leaf_a][leaf_b];
                }
            }
        }

        // NOTE: pre-calculate depth of each node in each tree
        let mut depth: Vec<Vec<usize>> = vec![vec![usize::MAX; max_node_idx + 1]; n_forests];
        for (depth_f, f) in depth.iter_mut().zip_eq(&self.forests) {
            for &root in f.roots.iter() {
                for (node_idx, node) in f.dfs_from(root) {
                    depth_f[node_idx as usize] = match node.parent {
                        None => 0,
                        Some(parent) => {
                            debug_assert_ne!(depth_f[parent as usize], usize::MAX);
                            depth_f[parent as usize] + 1
                        }
                    };
                }
            }
        }

        // iterate over all pairs of labels (a,b),(c,d) where (a<b) (c<d) and (a<c)
        // and label a lies in the same component as label b in each forest (same with c and d)
        //
        // We can skip instances where a and b (or c and d) are separated in SOME forest
        // because we know that in any AF they must also be separated due to this.
        for &Label(d) in labels.iter() {
            let comp_group_d = comp_groups[d as usize];
            for &Label(c) in labels.iter() {
                if c >= d {
                    break;
                }
                let comp_group_c = comp_groups[c as usize];
                if comp_group_c != comp_group_d {
                    continue;
                }
                for &Label(b) in labels.iter() {
                    let comp_group_b = comp_groups[b as usize];
                    'label_a_loop: for &Label(a) in labels.iter() {
                        if a >= b || a >= c {
                            break;
                        }
                        let comp_group_a = comp_groups[a as usize];
                        if comp_group_a != comp_group_b {
                            continue;
                        }
                        for ((label_lcas_f, depth_f), f) in label_lcas
                            .iter()
                            .zip_eq(depth.iter())
                            .zip_eq(self.forests.iter())
                        {
                            // if pair a,b lies in a different component than pair c,d
                            // there is no need to check if their paths overlap
                            if f.find_root_of(f.locate_label(Label(a)))
                                != f.find_root_of(f.locate_label(Label(c)))
                            {
                                continue;
                            }

                            if f.paths_intersect_using_lca_and_depth(
                                a as usize,
                                b as usize,
                                c as usize,
                                d as usize,
                                label_lcas_f,
                                depth_f,
                            ) {
                                continue 'label_a_loop;
                            }
                        }
                        res.push(quad_key(Label(a), Label(b), Label(c), Label(d)));
                    }
                }
            }
        }
        res
    }

    /// Find all pairs of pairs of labels that are disjoint in each input tree.
    /// Uses pre-calculated map of lcas of each pair of nodes in each tree
    /// Is the complement of 'find_crossing_paths_in_any', with the same complexity
    /// (when implemented the same way), but returns 50%-95% less pairs.
    ///
    /// Returns None if the number of compatible path pairs exceeds max_n_path_pairs
    fn try_find_non_crossing_paths_in_any(
        &self,
        labels: &[Label],
        lcas: &[Vec<Vec<usize>>],
        comp_groups: &[usize],
        max_n_path_pairs: usize,
    ) -> Option<Vec<u64>> {
        let n_forests = self.forests.len();
        let max_label = labels.iter().max().unwrap_or(&Label(0)).0 as usize;
        let max_node_idx = self
            .forests
            .iter()
            .map(|f| f.arena.len())
            .max()
            .unwrap_or_default();

        // n^2 is a conservative guess on #non-crossing pairs
        let mut res: Vec<_> = Vec::with_capacity(labels.len() * labels.len());

        // NOTE: pre-calculate lca of each pair of labels in each tree
        let mut label_lcas: Vec<Vec<Vec<usize>>> =
            vec![vec![vec![usize::MAX; max_label + 1]; max_label + 1]; n_forests];
        for ((label_lcas_f, lcas_f), f) in label_lcas
            .iter_mut()
            .zip_eq(lcas.iter())
            .zip_eq(&self.forests)
        {
            for &a in labels.iter() {
                let leaf_a = f.locate_label(a) as usize;
                for &b in labels.iter() {
                    let leaf_b = f.locate_label(b) as usize;
                    label_lcas_f[a.0 as usize][b.0 as usize] = lcas_f[leaf_a][leaf_b];
                }
            }
        }

        // NOTE: pre-calculate depth of each node in each tree
        let mut depth: Vec<Vec<usize>> = vec![vec![usize::MAX; max_node_idx + 1]; n_forests];
        for (depth_f, f) in depth.iter_mut().zip_eq(&self.forests) {
            for &root in f.roots.iter() {
                for (node_idx, node) in f.dfs_from(root) {
                    depth_f[node_idx as usize] = match node.parent {
                        None => 0,
                        Some(parent) => {
                            debug_assert_ne!(depth_f[parent as usize], usize::MAX);
                            depth_f[parent as usize] + 1
                        }
                    };
                }
            }
        }

        // iterate over all pairs of labels (a,b),(c,d) where (a<b) (c<d) and (a<c)
        // and label a lies in the same component as label b in each forest (same with c and d)
        //
        // We can skip instances where a and b (or c and d) are separated in SOME forest
        // because we know that in any AF they must also be separated due to this.
        for &Label(d) in labels.iter() {
            let comp_group_d = comp_groups[d as usize];
            for &Label(c) in labels.iter() {
                if c >= d {
                    break;
                }
                let comp_group_c = comp_groups[c as usize];
                if comp_group_c != comp_group_d {
                    continue;
                }
                for &Label(b) in labels.iter() {
                    let comp_group_b = comp_groups[b as usize];
                    'label_a_loop: for &Label(a) in labels.iter() {
                        if a >= b || a >= c {
                            break;
                        }
                        let comp_group_a = comp_groups[a as usize];
                        if comp_group_a != comp_group_b {
                            continue;
                        }
                        for ((label_lcas_f, depth_f), f) in label_lcas
                            .iter()
                            .zip_eq(depth.iter())
                            .zip_eq(self.forests.iter())
                        {
                            // if pair a,b lies in a different component than pair c,d
                            // there is no need to check if their paths overlap
                            if f.find_root_of(f.locate_label(Label(a)))
                                != f.find_root_of(f.locate_label(Label(c)))
                            {
                                continue;
                            }

                            if f.paths_intersect_using_lca_and_depth(
                                a as usize,
                                b as usize,
                                c as usize,
                                d as usize,
                                label_lcas_f,
                                depth_f,
                            ) {
                                continue 'label_a_loop;
                            }
                        }
                        if res.len() >= max_n_path_pairs {
                            return None;
                        }
                        res.push(quad_key(Label(a), Label(b), Label(c), Label(d)));
                    }
                }
            }
        }
        Some(res)
    }

    /// Find all triples of labels that have a different embedding in at least one
    /// pair of input trees.
    /// Uses pre-calculated map of lcas of each pair of nodes in each tree
    ///
    /// Also tries to calculate set of valid extensions and an upper bound on maximum component size
    fn find_incompatible_triples_and_extensions(
        &self,
        labels: &[Label],
        lcas: &[Vec<Vec<usize>>],
        comp_groups: &[usize],
    ) -> (
        ConstraintHashSet,
        (Option<FxHashMap<u128, ComponentExtensions>>, usize),
    ) {
        let n_forests = self.forests.len();
        let max_label = labels.iter().max().unwrap_or(&Label(0)).0 as usize;
        // guess that around n^2 incompatible triples will be found (at most n^3, but that is a lot of memory)
        let mut res: ConstraintHashSet = FxHashSet::default();

        let mut label_lcas: Vec<Vec<Vec<usize>>> =
            vec![vec![vec![usize::MAX; max_label + 1]; max_label + 1]; n_forests];

        for (label_lcas_f, (lcas_f, f)) in label_lcas
            .iter_mut()
            .zip_eq(lcas.iter().zip_eq(&self.forests))
        {
            for &a in labels.iter() {
                let leaf_a = f.locate_label(a) as usize;
                for &b in labels.iter() {
                    let leaf_b = f.locate_label(b) as usize;
                    label_lcas_f[a.0 as usize][b.0 as usize] = lcas_f[leaf_a][leaf_b];
                }
            }
        }

        let mut compatible_triples: FxHashSet<SmallComponent> = FxHashSet::default();
        // let mut extensions_for_2: FxHashMap<u128, ComponentExtensions> = FxHashMap::default();
        let mut too_many_compatible_triples = false;

        // iterate over all sorted triples of labels (a,b,c) that
        // are in the same component in every forest
        for &Label(c) in labels.iter() {
            let comp_group_c = comp_groups[c as usize];
            for &Label(b) in labels.iter() {
                if b >= c {
                    break;
                }
                let comp_group_b = comp_groups[b as usize];
                if comp_group_b != comp_group_c {
                    continue;
                }
                'label_a_loop: for &Label(a) in labels.iter() {
                    if a >= b {
                        break;
                    }
                    let comp_group_a = comp_groups[a as usize];
                    if comp_group_a != comp_group_b {
                        continue;
                    }

                    let lca_ab = label_lcas[0][a as usize][b as usize];
                    let lca_bc = label_lcas[0][b as usize][c as usize];
                    let lca_ac = label_lcas[0][a as usize][c as usize];

                    for label_lcas_other in label_lcas.iter().skip(1) {
                        let lca_ab_other = label_lcas_other[a as usize][b as usize];
                        let lca_bc_other = label_lcas_other[b as usize][c as usize];
                        let lca_ac_other = label_lcas_other[a as usize][c as usize];

                        if ((lca_ab == lca_ac) != (lca_ab_other == lca_ac_other))
                            || ((lca_ac == lca_bc) != (lca_ac_other == lca_bc_other))
                            || ((lca_ab == lca_bc) != (lca_ab_other == lca_bc_other))
                        {
                            // abc is an incompatible triple (in sorted order)
                            res.insert(triple_key(Label(a), Label(b), Label(c)));
                            continue 'label_a_loop;
                        }
                    }

                    too_many_compatible_triples |= compatible_triples.len() >= 200_000;
                    if !too_many_compatible_triples {
                        compatible_triples.insert(smallvec![Label(a), Label(b), Label(c)]);
                    }
                }
            }
        }

        if too_many_compatible_triples {
            (res, (None, labels.len()))
        } else {
            (res, try_calc_extensions(labels, compatible_triples))
        }
    }
}

trait AfDbsArenaTreeExt {
    fn paths_intersect_using_lca_and_depth(
        &self,
        a: usize,
        b: usize,
        c: usize,
        d: usize,
        label_lcas: &[Vec<usize>],
        depth: &[usize],
    ) -> bool;
}

impl AfDbsArenaTreeExt for ArenaTree {
    /// determine if label pair a,b and c,d have intersecting paths
    /// label_lcas is a map from two labels (as Idx) to their lca
    #[inline]
    fn paths_intersect_using_lca_and_depth(
        &self,
        a: usize,
        b: usize,
        c: usize,
        d: usize,
        label_lcas: &[Vec<usize>],
        depth: &[usize],
    ) -> bool {
        // by case analysis: if the any of the four cross lcas (ac,ad,bc,bd)
        // is deeper in the tree than the deepest normal lca (ab,cd):
        //  then the paths (a--b and c--d) overlap
        let lca_ab = label_lcas[a][b];
        let lca_cd = label_lcas[c][d];
        if lca_ab == lca_cd {
            return true;
        }

        let lca_ac = label_lcas[a][c];
        let lca_ad = label_lcas[a][d];

        let lca_bc = label_lcas[b][c];
        let lca_bd = label_lcas[b][d];

        let max_depth_cross_lca = depth[lca_ac]
            .max(depth[lca_ad])
            .max(depth[lca_bc])
            .max(depth[lca_bd]);
        if max_depth_cross_lca > depth[lca_ab] && max_depth_cross_lca > depth[lca_cd] {
            return true;
        }
        false
    }
}

#[inline(always)]
pub fn pair_key_u128(a: Label, b: Label) -> u128 {
    ((b.0 as u128) << 16) | (a.0 as u128)
}

#[inline(always)]
pub fn triple_key(a: Label, b: Label, c: Label) -> u64 {
    ((c.0 as u64) << 32) | ((b.0 as u64) << 16) | (a.0 as u64)
}

#[inline(always)]
pub fn quad_key(a: Label, b: Label, c: Label, d: Label) -> u64 {
    ((d.0 as u64) << 48) | ((c.0 as u64) << 32) | ((b.0 as u64) << 16) | (a.0 as u64)
}

// Bitshift the individual u16 labels to obtain a u128 identifier
// Only to be used on unique, sorted lists of labels
// Note that component_key() is different for lists of two different sizes,
// because the most significant label is >= 1 due to the sorted input
#[inline(always)]
pub fn component_key(labels: &[Label]) -> u128 {
    let mut key = 0u128;
    for &l in labels.iter().rev() {
        key = (key << 16) | l.0 as u128;
    }
    #[cfg(debug_assertions)]
    {
        if labels.len() == 2 {
            debug_assert_eq!(pair_key_u128(labels[0], labels[1]), key);
        }
        if labels.len() == 3 {
            debug_assert_eq!(triple_key(labels[0], labels[1], labels[2]) as u128, key);
        }
        if labels.len() == 4 {
            debug_assert_eq!(
                quad_key(labels[0], labels[1], labels[2], labels[3]) as u128,
                key
            );
        }
    }
    key
}

type SmallComponent = SmallVec<[Label; 8]>;
pub type ComponentExtensions = SmallVec<[Label; 8]>;

// If succesful, returns a map containing all possible (i.e. valid w.r.t incompatible triples and comp-groups)
// extensions of every component of size<=8
// Also returns an integer containing the maximum possible component size (w.r.t. the same as above) or an upper bound on it
fn try_calc_extensions(
    sorted_labels: &[Label],
    compatible_triples: FxHashSet<SmallComponent>,
) -> (Option<FxHashMap<u128, ComponentExtensions>>, usize) {
    let mut max_comp_size = sorted_labels.len();
    debug_assert!(sorted_labels.is_sorted());

    if compatible_triples.len() > 200_000 {
        return (None, max_comp_size);
    }

    let mut extensions = FxHashMap::<u128, SmallComponent>::default();
    debug_assert!(extensions.values().all(|ls| ls.is_sorted()));

    // base level: compatible triples constitute all valid comps of size 3
    let mut current_valid_comps = compatible_triples;
    for abc in current_valid_comps.iter() {
        debug_assert_eq!(abc.len(), 3);
        let (a, b, c) = (abc[0], abc[1], abc[2]);
        extensions
            .entry(pair_key_u128(a, b))
            // .entry(pair_key_u128(Label(a), Label(b)))
            .or_default()
            .push(c);
    }
    for exts in extensions.values_mut() {
        exts.sort_unstable();
    }

    // build extensions list for every valid component of size 3,4,5,...,8
    for target_size in 3..=8 {
        #[cfg(feature = "logging")]
        println!(
            "# n_comps_of_size_{} = {}",
            target_size,
            current_valid_comps.len()
        );

        if current_valid_comps.len() > 300_000 {
            return (None, max_comp_size);
        }
        if current_valid_comps.is_empty() {
            max_comp_size = target_size;
            break;
        }
        let mut next_valid_comps = FxHashSet::<SmallComponent>::default();

        for comp in &current_valid_comps {
            debug_assert_eq!(comp.len(), target_size);
            debug_assert!(comp.is_sorted());

            let largest = *comp.last().unwrap();
            let first_idx_greater_than_largest = sorted_labels.partition_point(|&l| l <= largest);

            'label_check: for &new_label in &sorted_labels[first_idx_greater_than_largest..] {
                debug_assert!(new_label > largest);
                // Check if every subset of one size smaller is a valid comp
                // If so: this is also a valid component
                for removed in 0..comp.len() {
                    let mut subset = SmallComponent::with_capacity(comp.len());

                    for (i, &x) in comp.iter().enumerate() {
                        if i != removed {
                            subset.push(x);
                        }
                    }
                    subset.push(new_label);

                    if !current_valid_comps.contains(&subset) {
                        continue 'label_check;
                    }
                }

                let mut new_comp = comp.clone();
                new_comp.push(new_label);
                next_valid_comps.insert(new_comp.clone());

                extensions
                    .entry(component_key(comp))
                    .or_default()
                    .push(new_label);
            }
        }

        current_valid_comps = next_valid_comps;
        if current_valid_comps.is_empty() {
            max_comp_size = target_size + 1;
        }
    }

    (Some(extensions), max_comp_size)
}
