use super::instance_ext::AfDbsInstanceExt;
use super::instance_ext::ComponentExtensions;
use super::instance_ext::component_key;
use super::instance_ext::quad_key;
use super::instance_ext::triple_key;
use crate::common::validity::assert_validity;
use crate::maf_instance::arena_tree::ArenaTree;
use crate::maf_instance::arena_vertex::Idx;
use crate::maf_instance::arena_vertex::Label;
use crate::maf_instance::instance::Instance;
use crate::maf_instance::tree_traversal::TreeTraversal;

use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use smallvec::{SmallVec, smallvec};

use std::time::Duration;
use std::time::Instant;

use super::logging::log;
#[cfg(feature = "logging")]
use super::logging::{LOGS, Logs};

pub type ConstraintHashSet = FxHashSet<u64>;

// Initialize the solver by calculating all constraints
// I.E., incompatible triples and incompatible path pairs
pub fn init_bu_state(instance: Instance) -> BuState {
    assert_validity!(instance);

    let f1 = &instance.forests[0];
    let mut sorted_labels: SmallVec<[Label; 256]> = f1.leaf_map.keys().copied().collect();
    sorted_labels.sort_unstable();

    log!(|logs: &mut Logs| logs.n_leaves_after_merging = sorted_labels.len() as u64);
    log!(|logs: &mut Logs| logs.ord_after_merging = instance.ord() as u64);

    // INFO: calcuate all LCAs of pairs of nodes in each tree
    let lcas = instance.calculate_lcas();

    // calculate an identifier s.t. comp_groups[a]=comp_groups[b] means a and b are in the
    // same component in every input forest
    let comp_groups = SmallVec::from_vec(instance.calculate_comp_groups());

    // INFO: find all incompatible triples of labels/leaves
    // and try to calculate the set of all possible extensions of any valid component of size <= 8
    let (bad_triples, (extensions_opt, max_comp_size)): (
        ConstraintHashSet,
        (Option<FxHashMap<u128, ComponentExtensions>>, usize),
    ) = instance.find_incompatible_triples_and_extensions(&sorted_labels, &lcas, &comp_groups);
    log!(|logs: &mut Logs| logs.n_triple_constr = bad_triples.len() as u64);
    log!(|logs: &mut Logs| logs.max_comp_size = max_comp_size as u64);
    log!(|logs: &Logs| logs.print_logs_partial());

    // INFO: find all NON-overlapping paths between pairs of labels
    let good_quads: ConstraintHashSet = instance
        .find_non_crossing_paths_in_any(&sorted_labels, &lcas, &comp_groups)
        .into_iter()
        .collect();
    log!(|logs: &mut Logs| logs.n_non_overlap_pair_constr = good_quads.len() as u64);
    log!(|logs: &Logs| logs.print_logs());

    BuState::new(
        sorted_labels,
        bad_triples,
        extensions_opt,
        max_comp_size,
        good_quads,
        comp_groups,
        instance,
    )
}

// Try to initialize the solver by calculating all constraints
// I.E., incompatible triples and (in)compatible path pairs
// Fails if (in)compatible path pairs set is too large (too much RAM usage expected)
pub fn try_init_bu_state(instance: Instance, max_n_path_pairs: usize) -> Option<BuState> {
    assert_validity!(instance);

    let f1 = &instance.forests[0];
    let mut sorted_labels: SmallVec<[Label; 256]> = f1.leaf_map.keys().copied().collect();
    sorted_labels.sort_unstable();
    log!(|logs: &mut Logs| logs.n_leaves_after_merging = sorted_labels.len() as u64);
    log!(|logs: &mut Logs| logs.ord_after_merging = instance.ord() as u64);

    // INFO: calcuate all LCAs of pairs of nodes in each tree
    let lcas = instance.calculate_lcas();

    // calculate an identifier s.t. comp_groups[a]=comp_groups[b] means a and b are in the
    // same component in every input forest
    let comp_groups = SmallVec::from_vec(instance.calculate_comp_groups());

    // INFO: find all incompatible triples of labels/leaves
    // and try to calculate the set of all possible extensions of any valid component of size <= 8
    let (bad_triples, (extensions_opt, max_comp_size)): (
        ConstraintHashSet,
        (Option<FxHashMap<u128, ComponentExtensions>>, usize),
    ) = instance.find_incompatible_triples_and_extensions(&sorted_labels, &lcas, &comp_groups);
    log!(|logs: &mut Logs| logs.n_triple_constr = bad_triples.len() as u64);
    log!(|logs: &mut Logs| logs.max_comp_size = max_comp_size as u64);
    log!(|logs: &Logs| logs.print_logs_partial());

    // INFO: find all NON-overlapping paths between pairs of labels
    let good_quads: ConstraintHashSet = instance
        .try_find_non_crossing_paths_in_any(&sorted_labels, &lcas, &comp_groups, max_n_path_pairs)?
        .into_iter()
        .collect();
    log!(|logs: &mut Logs| logs.n_non_overlap_pair_constr = good_quads.len() as u64);
    log!(|logs: &Logs| logs.print_logs());

    Some(BuState::new(
        sorted_labels,
        bad_triples,
        extensions_opt,
        max_comp_size,
        good_quads,
        comp_groups,
        instance,
    ))
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OperationFrame {
    Extension(Label),      // extended the last component with one new label
    NewComp(Label, Label), // created a new component consisting of two (sorted) labels
    NoOperation,           // others not applicable
}
use OperationFrame::*;

pub type BuSol = SmallVec<[SmallVec<[Label; 16]>; 16]>;

pub struct BuState {
    // input forests
    instance: Instance,

    // information about labels of input forests
    num_leaves: usize,
    sorted_labels: SmallVec<[Label; 256]>,
    is_label: SmallVec<[bool; 256]>,

    // pre-calculated constraint information
    bad_triples: ConstraintHashSet,
    extensions_opt: Option<FxHashMap<u128, ComponentExtensions>>,
    max_comp_size: usize,
    good_quads: ConstraintHashSet,
    comp_groups: SmallVec<[usize; 256]>,

    // dynamic information on current solution
    sol: BuSol,
    cur_sol_ord: usize,
    cur_sol_label_set: SmallVec<[bool; 256]>,

    best_sol: BuSol,
    best_sol_ord: usize,

    // information about current branching state
    last_undid_operation: OperationFrame,

    // debug logging
    #[cfg(feature = "logging")]
    sol_counts: SmallVec<[usize; 64]>,
}

impl BuState {
    fn new(
        sorted_labels: SmallVec<[Label; 256]>,
        bad_triples: ConstraintHashSet,
        extensions_opt: Option<FxHashMap<u128, ComponentExtensions>>,
        max_comp_size: usize,
        good_quads: ConstraintHashSet,
        comp_groups: SmallVec<[usize; 256]>,
        instance: Instance,
    ) -> BuState {
        let num_leaves = sorted_labels.len();
        let max_label = sorted_labels.last().unwrap_or(&Label(0)).0 as usize;

        let mut is_label: SmallVec<[bool; 256]> = smallvec![false; max_label + 1];
        for &Label(l) in sorted_labels.iter() {
            is_label[l as usize] = true;
        }

        let cur_sol_label_set = smallvec![false; max_label + 1];

        let sol: BuSol = smallvec![];
        let cur_sol_ord: usize = 0;

        let best_sol: BuSol = smallvec![];
        let best_sol_ord: usize = 0;

        let last_undid_operation = if num_leaves > 0 {
            NewComp(sorted_labels[0], sorted_labels[0])
        } else {
            NoOperation
        };

        #[cfg(feature = "logging")]
        let sol_counts = smallvec![1];

        BuState {
            instance,
            num_leaves,
            sorted_labels,
            is_label,
            bad_triples,
            extensions_opt,
            max_comp_size,
            good_quads,
            comp_groups,
            sol,
            cur_sol_ord,
            best_sol,
            best_sol_ord,
            cur_sol_label_set,
            last_undid_operation,

            #[cfg(feature = "logging")]
            sol_counts,
        }
    }

    /// Try to solve the instance in the given time limit (in seconds).
    /// Returns the solution if found in time, otherwise None.
    /// Can be called again later to pick up where this left off.
    pub fn try_solve(&mut self, time_limit_s: u64) -> Option<ArenaTree> {
        if self.num_leaves == 0 {
            return Some(self.construct_solution_forest(self.best_sol.clone()));
        }

        let start_time = Instant::now();
        let end_time = start_time + Duration::new(time_limit_s, 0);

        const ITERS_BETWEEN_TIME_CHECK: u32 = 50_000;

        while Instant::now() < end_time {
            for _ in 0..ITERS_BETWEEN_TIME_CHECK {
                self.update_best();

                if self.try_extend_comp() {
                    continue;
                }
                if self.try_new_comp() {
                    continue;
                }
                if self.backtrack() {
                    continue;
                }

                return Some(self.construct_solution_forest(self.best_sol.clone()));
            }
        }
        None
    }

    /// iterate all agreement forests (represented as partitions of the label set)
    /// in dfs order, where the trivial parition of singletons is the root of the search tree
    /// and its children are the possible labels to add to the 'last' component and the possible
    /// new components consisting of two labels to be added.
    pub fn solve(&mut self) -> ArenaTree {
        if self.num_leaves == 0 {
            return self.construct_solution_forest(self.best_sol.clone());
        }

        #[cfg(feature = "logging")]
        let mut iter: usize = 0;
        loop {
            #[cfg(feature = "logging")]
            {
                iter += 1;
                if iter.is_multiple_of(1_000_000) {
                    println!("#s iterations {}", iter);
                    let (progress, max) = self.estimate_progress();
                    println!("# progress: {} \t/ {}", progress, max);
                    for (k, &count) in self.sol_counts.iter().enumerate() {
                        println!("#s k_{}_sol_count {}", k, count);
                    }
                }
            }

            self.update_best();

            if self.try_extend_comp() {
                continue;
            }
            if self.try_new_comp() {
                continue;
            }
            if self.backtrack() {
                continue;
            }

            break;
        }
        self.construct_solution_forest(self.best_sol.clone())
    }

    fn update_best(&mut self) {
        if self.cur_sol_ord > self.best_sol_ord {
            self.best_sol = self.sol.clone();
            self.best_sol_ord = self.cur_sol_ord;

            #[cfg(feature = "logging")]
            println!("#s best_sol_ord {}", self.best_sol_ord);
        }
    }

    // Tries to find a new label to add to the last component of the solution.
    // Adheres to the ordering of solutions: does nothing if last undid operation was NewComp
    fn try_extend_comp(&mut self) -> bool {
        // find the last tried addition, so that we can start iterating from there
        let Some(last_comp) = self.sol.last() else {
            return false;
        };
        let last_comp_len = last_comp.len();
        let last_comp_key_opt = if (2..=8).contains(&last_comp_len) {
            Some(component_key(last_comp))
        } else {
            None
        };

        // check where the previous search left off and continue from there
        let last_tried_idx = match self.last_undid_operation {
            NoOperation => last_comp.last().unwrap().0 as usize,
            Extension(label) => label.0 as usize,
            NewComp(..) => return false,
        };

        // find the component group of the last comp
        let last_comp_group = self.comp_groups[last_comp[0].0 as usize];

        // checks if:
        //  - if new_label_idx is in the same comp group as the last component
        //  - the new_label is not in any incompatible triples with the last component
        let check_comp_group_and_incomp_triples = |new_label_idx: usize| -> bool {
            debug_assert!(new_label_idx > last_comp.last().unwrap().0 as usize);
            let new_label = Label(new_label_idx as Idx);

            // reject labels that are in a different component in some forest
            let new_label_comp_group = self.comp_groups[new_label.0 as usize];
            if new_label_comp_group != last_comp_group {
                return false;
            }

            // check incompatible triples
            for &i in last_comp.iter() {
                for &j in last_comp.iter() {
                    if j >= i {
                        break;
                    }
                    // let triple = (j, i, new_label);
                    // if self.bad_triples.contains(&triple) {
                    if self.bad_triples.contains(&triple_key(j, i, new_label)) {
                        return false;
                    }
                }
            }

            true
        };

        let check_overlapping_path_pairs = |new_label: Label| -> bool {
            // check overlapping path pairs
            for comp in self.sol[..(self.sol.len() - 1)].iter() {
                debug_assert!(comp.is_sorted());
                // iterate over pairs within this comp
                for &i in comp.iter() {
                    for &j in comp.iter() {
                        if j >= i {
                            break;
                        }
                        // let other_pair = (j, i);
                        // iterate new pairs with new_label in the last comp
                        for &k in last_comp.iter() {
                            // let new_pair = (k, new_label);
                            debug_assert!(k < new_label);
                            // let sorted_pairs = sort_tup((new_pair, other_pair));
                            let quad_key = if k < j {
                                quad_key(k, new_label, j, i)
                            } else {
                                quad_key(j, i, k, new_label)
                            };
                            if !self.good_quads.contains(&quad_key) {
                                return false;
                            }
                        }
                    }
                }
            }
            true
        };

        fn perform_addition(state: &mut BuState, new_label: Label) {
            // addition to solution is valid: perfom it and continue the search
            state.sol.last_mut().unwrap().push(new_label);
            state.cur_sol_ord += 1;
            state.cur_sol_label_set[new_label.0 as usize] = true;
            state.last_undid_operation = NoOperation; // reset operation marker
            #[cfg(feature = "logging")]
            {
                if state.sol_counts.len() <= state.cur_sol_ord {
                    state.sol_counts.resize(state.cur_sol_ord + 1, 0);
                }
                state.sol_counts[state.cur_sol_ord] += 1;
            }
            debug_assert!(state.sol.last().unwrap().is_sorted());
            debug_assert!(state.sol.is_sorted());
        }

        // NOTE: method of iterating label options depends on whether `extensions-map` was pre-calculated
        //
        // If we have the extensions map calculated and the current component is of size <= 8:
        //  - Loop through pre-calculated extension labels
        // Otherwise:
        //  - Verify incompatible triples manually
        if let Some(last_comp_key) = last_comp_key_opt
            && let Some(extensions_map) = &self.extensions_opt
        {
            let Some(extensions) = extensions_map.get(&last_comp_key) else {
                return false;
            };
            debug_assert!(extensions.iter().is_sorted());

            let last_tried_label = Label(last_tried_idx as u16);
            let first_idx_greater_than_last =
                extensions.partition_point(|&l| l <= last_tried_label);

            for &label_to_try in extensions[first_idx_greater_than_last..].iter() {
                // check if it is not in the current solution already
                if self.cur_sol_label_set[label_to_try.0 as usize] {
                    continue;
                }
                debug_assert!(check_comp_group_and_incomp_triples(label_to_try.0 as usize));

                if check_overlapping_path_pairs(label_to_try) {
                    perform_addition(self, label_to_try);
                    return true;
                }
            }
        } else {
            // Loop though all indices and keep the ones that are actually labels in the instance
            for label_idx_to_try in self
                .is_label
                .iter()
                .enumerate()
                .skip(last_tried_idx + 1)
                .filter_map(|(_new_label_idx, &this_is_label)| {
                    if this_is_label {
                        Some(_new_label_idx)
                    } else {
                        None
                    }
                })
            {
                // Verify that the label is not already in another component
                if self.cur_sol_label_set[label_idx_to_try] {
                    continue;
                }
                let label_to_try = Label(label_idx_to_try as u16);

                // Verify the incompatible triples constraints
                // Verify the incompatible path pair constraints
                if check_comp_group_and_incomp_triples(label_idx_to_try)
                    && check_overlapping_path_pairs(label_to_try)
                {
                    perform_addition(self, label_to_try);
                    return true;
                }
            }
        };

        false
    }

    // Tries to find a new pair of labels to add as the new last component of the solution.
    // Adheres to the ordering of solutions
    fn try_new_comp(&mut self) -> bool {
        // find the last tried pair of labels, so that we can start iterating from there
        let (last_tried_lo_idx, mut last_tried_hi_idx) = match self.last_undid_operation {
            NewComp(label_lo, label_hi) => (label_lo.0 as usize, label_hi.0 as usize),
            _ => (
                self.sol
                    .last()
                    .expect("some component if the last undo'd operation was not NewComp")
                    .first()
                    .unwrap()
                    .0 as usize
                    + 1,
                0,
            ),
        };

        // calculate initial number of unused labels after where we left off
        // to use in trivial upper bound calculation
        let mut unused_labels_ge = self
            .is_label
            .iter()
            .zip_eq(&self.cur_sol_label_set)
            .skip(last_tried_lo_idx)
            .filter(|&(&it_is_label, &it_is_in_sol)| it_is_label && !it_is_in_sol)
            .count();

        // loop through all possible first labels for the new component
        'label_lo_loop: for (label_lo_idx, &this_is_label) in
            self.is_label.iter().enumerate().skip(last_tried_lo_idx)
        {
            if !this_is_label {
                continue;
            }
            if self.cur_sol_label_set[label_lo_idx] {
                continue;
            }
            let label_lo = Label(label_lo_idx as Idx);
            let label_lo_comp_group = self.comp_groups[label_lo.0 as usize];

            // check if trivial upper bound can exceed the best solution found
            //
            // in the best case these are all divided over components of size:
            // self.max_comp_size
            // and we need at least:  unused_labels_ge / new_comps_needed  components for this
            // (including the current)
            let min_comps_needed = unused_labels_ge.div_ceil(self.max_comp_size);
            let upper_bound = self.cur_sol_ord + unused_labels_ge - min_comps_needed;
            if upper_bound <= self.best_sol_ord {
                // prune the branch: after breaking, the algorithm will backtrack
                break 'label_lo_loop;
            }

            last_tried_hi_idx = last_tried_hi_idx.max(label_lo_idx);

            // loop through all possible second labels for the new component
            'label_hi_loop: for (label_hi_idx, &this_is_label) in
                self.is_label.iter().enumerate().skip(last_tried_hi_idx + 1)
            {
                if !this_is_label {
                    continue;
                }
                if self.cur_sol_label_set[label_hi_idx] {
                    continue;
                }
                let label_hi = Label(label_hi_idx as Idx);

                // skip labels that are in a different component in some forest
                let label_hi_comp_group = self.comp_groups[label_hi.0 as usize];

                if label_hi_comp_group != label_lo_comp_group {
                    continue 'label_hi_loop;
                }

                // don't check incompatible triples because the new component is of size 2

                // check overlapping path pairs
                // iterate all pairs NOT in the newly joined comp,
                // for each check if the paths overlap in any tree with the new pair
                // let new_pair = (label_lo, label_hi);
                for comp in self.sol.iter() {
                    debug_assert!(comp.is_sorted());
                    // iterate over pairs within this comp
                    for &i in comp.iter() {
                        for &j in comp.iter() {
                            if j >= i {
                                break;
                            }
                            // let other_pair = (j, i);
                            // let sorted_pairs = sort_tup((new_pair, other_pair));
                            let quad_key = if label_lo < j {
                                quad_key(label_lo, label_hi, j, i)
                            } else {
                                quad_key(j, i, label_lo, label_hi)
                            };
                            if !self.good_quads.contains(&quad_key) {
                                // if !self.good_quads.contains(&sorted_pairs) {
                                // check if trivial upper bound can exceed the best solution found
                                // now that we skipped one label in this loop, we know we need
                                // at least one more component after this: one less possbile ord
                                let new_upper_bound = upper_bound - 1;
                                if new_upper_bound <= self.best_sol_ord {
                                    // prune the branch: after breaking, the algorithm will backtrack
                                    break 'label_lo_loop;
                                }
                                continue 'label_hi_loop;
                            }
                        }
                    }
                }

                // solution is valid: create and add it
                let new_comp = smallvec![label_lo, label_hi];
                debug_assert!(new_comp.is_sorted());
                self.sol.push(new_comp);
                self.cur_sol_ord += 1;
                self.cur_sol_label_set[label_lo.0 as usize] = true;
                self.cur_sol_label_set[label_hi.0 as usize] = true;
                self.last_undid_operation = NoOperation; // reset operation marker
                #[cfg(feature = "logging")]
                {
                    if self.sol_counts.len() <= self.cur_sol_ord {
                        self.sol_counts.resize(self.cur_sol_ord + 1, 0);
                    }
                    self.sol_counts[self.cur_sol_ord] += 1;
                }
                return true;
            }

            // we moved past exactly 1 label that is not in the current solution
            unused_labels_ge -= 1;

            // reset the last tried marked after completing an iteration of the lo index
            // so that the next iteration starts at the first possible pair
            last_tried_hi_idx = 0;
        }
        false
    }

    // tries to undo the last operation, returns whether succesful
    // if not succesful this must mean that the entire tree is completed
    fn backtrack(&mut self) -> bool {
        // pop the last operation
        // but if sol is empty, we completed the entire tree
        if self.sol.is_empty() {
            return false;
        }
        let last_comp = self.sol.last_mut().unwrap();
        if last_comp.len() == 2 {
            // remove the component
            let (label_lo, label_hi) = (last_comp[0], last_comp[1]);
            self.last_undid_operation = NewComp(label_lo, label_hi);
            self.cur_sol_label_set[label_lo.0 as usize] = false;
            self.cur_sol_label_set[label_hi.0 as usize] = false;
            self.sol.pop();
        } else {
            // remove the last label from the component
            let last_label = last_comp.pop().unwrap();
            self.last_undid_operation = Extension(last_label);
            self.cur_sol_label_set[last_label.0 as usize] = false;
        }
        self.cur_sol_ord -= 1;
        true
    }

    pub fn estimate_progress(&self) -> (usize, usize) {
        // There are self.num_leaves * (self.num_leaves-1) / 2 sorted pairs of unique labels.
        // Each of these by themselves is a valid agreement forest (unless an input forest has them separated)
        // We want to know how many of these come before (a,b) in lexicographical order
        // to estimate the progress in the current ordered search algorithm
        let n_pairs = self.num_leaves * (self.num_leaves - 1) / 2;
        if self.sol.is_empty() || self.sol[0].len() < 2 {
            return (0, n_pairs);
        }

        let a = self.sol[0][0];
        let b = self.sol[0][1];

        let i = self
            .sorted_labels
            .binary_search(&a)
            .expect("label not found");
        let j = self
            .sorted_labels
            .binary_search(&b)
            .expect("label not found");

        debug_assert!(i < j);

        // Number of pairs whose first label is < a.
        let before_a = if i == 0 {
            0
        } else {
            i * (self.num_leaves - 1) - i * (i - 1) / 2
        };

        // Number of pairs with first label == a and second label < b.
        let within_a = j - i - 1;

        (before_a + within_a, n_pairs)
    }

    pub fn get_best_sol_ord(&self) -> usize {
        self.num_leaves - self.best_sol_ord
    }

    pub fn get_current_best_solution_forest(&self) -> ArenaTree {
        self.construct_solution_forest(self.best_sol.clone())
    }

    pub fn construct_solution_forest(&self, mut sol: BuSol) -> ArenaTree {
        let mut f1 = self.instance.forests[0].clone();

        // add all (previously implicit) singleton components to the solution
        let non_singleton_labels: FxHashSet<Label> = sol.iter().flatten().copied().collect();
        for label in f1.iterate_all().labels() {
            if !non_singleton_labels.contains(&label) {
                sol.push(smallvec![label]);
            }
        }

        for comp in sol {
            // find the lowest common ancestor of all labels in the component and cut it
            let comp_lca = comp
                .iter()
                .map(|&label| f1.locate_label(label))
                .reduce(|a, b| f1.get_lca(a, b).expect("component to be connected"))
                .expect("at least one item to compute lca");

            if f1.get(comp_lca).parent.is_some() {
                f1.cut_branch(comp_lca);
            }
        }

        f1
    }
}
