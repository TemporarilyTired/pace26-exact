use rustc_hash::{FxHashMap, FxHashSet};

use super::cluster_reduction::{solve_split, solve_split_with_dummy};
use crate::common::helpers::sort_tup;
use crate::maf_instance::{
    arena_tree::ArenaTree,
    arena_vertex::{Label, NodeData::*, Status::*},
    instance::Instance,
    performed_reduction::PerformedReduction::{self, *},
    tree_traversal::TreeTraversal,
};

use crate::common::validity::assert_validity;

// import log macro; and only import other logging things if enabled
use super::logging::log;
#[cfg(feature = "logging")]
use super::logging::{LOGS, Logs};

pub fn solve_binary_search_dbs(instance: Instance) -> ArenaTree {
    let approx_state = State {
        instance: instance.clone(),
        cut_opts: FxHashSet::default(),
    };
    let (upper_bound_af, lb) = calc_expensive_lb_and_ub(approx_state);
    let sol = upper_bound_af;

    solve_binary_search_dbs_with_bounds(instance, lb, sol)
}

pub fn solve_binary_search_dbs_with_bounds(
    instance: Instance,
    mut lb: usize,
    mut sol: ArenaTree,
) -> ArenaTree {
    let mut ub = sol.ord();

    #[cfg(feature = "logging")]
    println!(
        "# starting dbs on instance (ord={}) with #leaves = {}",
        instance.ord(),
        instance.num_leaves,
    );
    #[cfg(feature = "logging")]
    println!("# initial bounds = ({}, {})", lb, sol.ord());

    while lb < ub {
        let mid = (lb + ub) / 2;

        // reset all counters
        log!(|logs: &mut Logs| logs.reset_logs_for_new_k());

        let state = State {
            instance: instance.clone(),
            cut_opts: FxHashSet::default(),
        };
        let result = cherry_dbs(state, mid, false);

        // print the call count logs
        log!(|logs: &Logs| logs.print_logs_after_k(mid));

        if let Some(maf) = result {
            ub = maf.ord();
            sol = maf;
        } else {
            lb = mid + 1;
        }
    }
    sol
}

pub fn cherry_dbs(mut state: State, k: usize, is_rr1_and_rr2_reduced: bool) -> Option<ArenaTree> {
    log!(|logs: &mut Logs| logs.total_calls += 1);

    assert_validity!(state);
    assert_validity!(state.instance);

    let ord = state.instance.ord();
    if ord > k {
        return None;
    }

    // INFO: Reduction rule 1 and 2
    if !is_rr1_and_rr2_reduced {
        let (performed_reductions, n_removed_svts) = state.remove_svt_and_merge_safe();

        if !performed_reductions.is_empty() {
            let mut sol = cherry_dbs(state, k.checked_sub(n_removed_svts)?, true)?;

            for reduction in performed_reductions.into_iter().rev() {
                sol.undo_reduction(reduction);
            }
            return Some(sol);
        }
    }

    // After the merge reduction we can quickly check if
    // this instance is completed by checking if it has any cherries
    if state.instance.is_completed() {
        if ord <= k {
            return Some(state.instance.extract_af());
        } else {
            return None;
        }
    }
    debug_assert!(state.instance.iterate_all_cherries().next().is_some());

    // INFO: Reduction rule 3
    if state.rr_2_2_1_reduce() {
        log!(|logs: &mut Logs| logs.rr_2_2_1_succesful += 1);
        return cherry_dbs(state, k, false);
    }

    // Add cut-opt (a,b) for every cherry (a,b) s.t.
    // a is not in the same component as b in every forest
    // INFO: Reduction rule 4
    state.add_cherry_cut_opts();

    // If a label is in a cut-opt with every other label in its component (in some forest):
    // make it a SVT.
    // INFO: Reduction rule 5
    if state.reduce_universal_hitting_pairs() {
        return cherry_dbs(state, k, false);
    }

    #[cfg(feature = "assert_validity")]
    state.assert_cut_opts_exist();
    #[cfg(feature = "assert_validity")]
    state.assert_no_svts();
    #[cfg(feature = "assert_validity")]
    state.assert_cherries_merged();
    assert_validity!(state);

    let ord = state.instance.ord();

    // calculate a somewhat expensive upper and lower bound on the current branch
    if state.instance.ord() + 4 <= k {
        let (upper_bound_af, lb) = calc_expensive_lb_and_ub(state.clone());
        let ub = upper_bound_af.ord();

        if ub <= k {
            log!(|logs: &mut Logs| logs.ub_3_approx_best += 1);
            return Some(upper_bound_af);
        }

        if lb > k {
            log!(|logs: &mut Logs| logs.lb_3_approx_prune += 1);
            return None;
        }
    }

    if state.instance.ord() + 2 < k {
        // if the instance has a useful common cluster that is a complete component in at least one forests:
        // split it into clusters and solve separately
        // The order of the maf will always be the sum of the orders of cluster above and cluster below
        if let Some((above, below)) = state.find_clusters_component() {
            log!(|logs: &mut Logs| logs.comp_clusters += 1);
            #[cfg(feature = "logging")]
            {
                let n_calls = LOGS.with_borrow(|x| x.total_calls);
                if n_calls < 100_000 {
                    eprintln!(
                        "# splitting, k={}, n_leaves={}, ord={}\n # - above: ord={},\tn_leaves={}\n # - below: ord={},\tn_leaves={}",
                        k,
                        state.instance.num_leaves,
                        state.instance.ord(),
                        above.instance.ord(),
                        above.instance.num_leaves,
                        below.instance.ord(),
                        below.instance.num_leaves,
                    );
                }
            }

            let (sol_above, sol_below) = solve_split(above, below, k)?;
            return Some(sol_above.join_with(sol_below));
        }
    }

    if state.instance.ord() + 4 < k {
        // if the instance has a useful common cluster, split it into clusters and solve separately
        // if the addition of the dummy leaf does not increase the MAF in both parts: some component
        // can span the cut edge of the subtree
        // So: test if opt(above)+opt(below) <= k, if so: return Some(_)
        // otherwise: test if opt(above)+opt(below) > k+1, if so: return None
        // At this point opt(above)+opt(below) == k+1,
        // If opt(above with dummy) == opt(above)  (we can just check for   opt(above w dummy) <= opt(above))
        // and opt(below with dummy) == opt(below)  (we can just check for   opt(below w dummy) <= opt(below))
        // Then: return Some(opt(above) + opt(below) - 1)
        // otherwise: return None

        if let Some((
            above,
            below,
            (above_w_dummy, used_dummy_above),
            (below_w_dummy, used_dummy_below),
        )) = state.find_clusters_w_dummy()
        {
            log!(|logs: &mut Logs| logs.subtree_clusters += 1);
            #[cfg(feature = "logging")]
            {
                let n_calls = LOGS.with_borrow(|x| x.total_calls);
                if n_calls < 100_000 {
                    eprintln!(
                        "# subtree splitting, k={}, n_leaves={}, ord={}\n # - above: ord={},\tn_leaves={}\n # - below: ord={},\tn_leaves={}",
                        k,
                        state.instance.num_leaves,
                        state.instance.ord(),
                        above.instance.ord(),
                        above.instance.num_leaves,
                        below.instance.ord(),
                        below.instance.num_leaves,
                    );
                }
            }

            return solve_split_with_dummy(
                above,
                below,
                (above_w_dummy, used_dummy_above),
                (below_w_dummy, used_dummy_below),
                k,
            );
        }
    }

    loop {
        #[cfg(feature = "assert_validity")]
        state.assert_cut_opts_exist();
        #[cfg(feature = "assert_validity")]
        state.assert_no_svts();
        #[cfg(feature = "assert_validity")]
        assert_validity!(state);

        // calculate lb_cuts: lb on number of cuts needed to satisfy cut-opts
        // lb is NOT ord+lb_cuts because some cuts will be useless
        // (i.e., when cutting ALL labels of a component, the last cut is 'free')
        // instead:
        //      lb = #svt's=0 + lb_cuts, or
        //      lb = ord + ceil(lb_cuts / 2)

        let matching_lb_cuts = state.get_matching_lb();
        let matching_lb1 = matching_lb_cuts;
        let matching_lb2 = ord + matching_lb_cuts.div_ceil(2);

        if matching_lb1 > k || matching_lb2 > k {
            return None;
        }

        let (max_degree_label_opt, max_cut_opt_degree) = state.get_max_cut_opt();

        let mut max_degree_cut_lb = ord;
        if let Some(max_degree_label) = max_degree_label_opt {
            // If cutting the label with the most cut-opt entries is guaranteed
            // to be necessary: do it
            let new_lb1 = max_cut_opt_degree;
            let new_lb2 = ord + max_cut_opt_degree.div_ceil(2);
            max_degree_cut_lb = new_lb1.max(new_lb2);
            if max_degree_cut_lb > k {
                state.cut_svt(max_degree_label);
                return cherry_dbs(state, k, false);
            }
        }

        // increase this multiplier to favor the cut-opt branching over the path-cutting branching
        const DEGREE_CUT_MULTIPLIER: f64 = 2_f64;
        // perform a branch: find target with largest increase in ord (heuristic for pruning or better branching)
        if let Some(((a, b), new_ord)) = state.find_path_cut_target_ord_strategy()
            && (max_degree_label_opt.is_none()
                || new_ord > k
                || (new_ord - ord) as f64
                    > (max_degree_cut_lb - ord) as f64 * DEGREE_CUT_MULTIPLIER)
        {
            // INFO: Branching rule 1

            // at this point:
            // - neither a nor b is a single vertex tree anywhere
            // - in some forest(s), a and b are not a cherry
            // - a and b are in the same component in each forest

            // so we branch:
            // - connect a and b in each tree (removing all pendant subtrees), or
            // - add {a,b} as cut-option

            if new_ord <= k {
                log!(|logs: &mut Logs| logs.case_1_b += 1);
                log!(|logs: &mut Logs| logs.total_branches += 1);
                log!(|logs: &mut Logs| logs.total_branches_all_k += 1);

                // cut all pendant subtrees on path a to lca and b to lca
                let mut state2 = state.clone();
                for forest in state2.instance.forests.iter_mut() {
                    let leaf_a = forest.locate_label(a);
                    let leaf_b = forest.locate_label(b);
                    let lca = forest.get_lca(leaf_a, leaf_b);

                    for leaf in [leaf_a, leaf_b] {
                        while forest.get(leaf).parent != lca {
                            let sibling = forest
                                .find_sibling(leaf)
                                .expect("a parent and thus a sibling");
                            forest.cut_branch(sibling);
                        }
                    }
                    debug_assert_eq!(forest.get(leaf_a).parent, forest.get(leaf_b).parent);
                }

                if let Some(maf) = cherry_dbs(state2, k, false) {
                    return Some(maf);
                }
            }

            state.cut_opts.insert(sort_tup((a, b)));

            if state.reduce_universal_hitting_pairs_on_label(a) {
                log!(|logs: &mut Logs| logs.case_1_a += 1);
                return cherry_dbs(state, k, false);
            }

            // NOTE: we do not need to perform the merge and SVT reductions again:
            // loop until we hit another case
        } else {
            // INFO: Branching rule 2

            log!(|logs: &mut Logs| logs.case_2 += 1);
            log!(|logs: &mut Logs| logs.total_branches += 1);
            log!(|logs: &mut Logs| logs.total_branches_all_k += 1);

            // all cherries have been (implicitly) inspected:
            // - choose a cut-opt and branch on it

            // NOTE: we choose the branching target in a smarter way:
            // choose the target that occurs in the most cut-opts,
            // resulting in the branch where target is not cut being a small instance

            // We can only enter this else clause when there was no cherry that is not a cut-opt
            // Since there must always be a cherry, there must also be a cut-opt
            let target = max_degree_label_opt.expect("at least one cut-opt");

            // cut target in each forest
            let mut state2 = state.clone();
            state2.cut_svt(target);
            if let Some(maf) = cherry_dbs(state2, k, false) {
                return Some(maf);
            }

            // or cut all labels that are in a cut-opt with target in each forest
            let mut others = vec![];
            for &(a, b) in state.cut_opts.iter() {
                if a == target {
                    others.push(b);
                } else if b == target {
                    others.push(a);
                }
            }
            for other in others {
                state.cut_svt(other);
            }

            debug_assert!(
                state
                    .cut_opts
                    .iter()
                    .all(|&(a, b)| a != target && b != target)
            );

            return cherry_dbs(state, k, false);
        }
    }
}

pub fn calc_expensive_lb_and_ub(mut state: State) -> (ArenaTree, usize) {
    let (performed_reductions, n_removed_svts) = state.remove_svt_and_merge_safe();

    if !performed_reductions.is_empty() {
        let (mut sol, lb) = calc_expensive_lb_and_ub(state);

        for reduction in performed_reductions.into_iter().rev() {
            sol.undo_reduction(reduction);
        }
        return (sol, lb + n_removed_svts);
    }

    if state.rr_2_2_1_reduce() {
        return calc_expensive_lb_and_ub(state);
    }

    if state.instance.is_completed() {
        return (state.instance.extract_af(), state.instance.ord());
    }
    debug_assert!(state.instance.iterate_all_cherries().next().is_some());

    // Add cut-opt (a,b) for every cherry (a,b) s.t.
    // a is not in the same component as b in every forest
    state.add_cherry_cut_opts();

    // If a cut-opt is a cherry without a parent in any forest: split it
    if state.reduce_universal_hitting_pairs() {
        return calc_expensive_lb_and_ub(state);
    }

    let mut non_forced_cuts: usize = 0;

    #[cfg(feature = "assert_validity")]
    state.assert_cut_opts_exist();
    #[cfg(feature = "assert_validity")]
    state.assert_no_svts();
    #[cfg(feature = "assert_validity")]
    assert_validity!(state);

    // perform a 'branch' but instead apply all options to arrive at an upper bound of MAF
    if let Some(&(a, b)) = state.cut_opts.iter().next() {
        // cut targets in each forest
        state.cut_svt(a);
        state.cut_svt(b);

        // we (possibly) performed one cut too many
        non_forced_cuts += 1;
    } else {
        let Some((_, a, b)) = state
            .instance
            .forests
            .iter()
            .rev()
            .flat_map(|forest| forest.iterate_cherries())
            .next()
        else {
            unreachable!("Some cherry present, otherwise instance is completed");
        };

        // at this point:
        // - neither a nor b is a single vertex tree anywhere
        // - a and b are not a cherry in some forest(s)
        // - a and b are in the same component in each forest

        // so we branch:
        // - connect a and b in each tree (removing all pendant subtrees), or
        // - add {a,b} as cut-option

        // cut ONE pendant subtree on path a to lca and b to lca
        // only in the first forest where they are not sibling
        for forest in state.instance.forests.iter_mut() {
            let leaf_a = forest.locate_label(a);
            let leaf_b = forest.locate_label(b);

            if forest.get(leaf_a).parent == forest.get(leaf_b).parent {
                continue;
            }

            let lca = forest.get_lca(leaf_a, leaf_b);
            'cut_one_branch_on_path: for leaf in [leaf_a, leaf_b] {
                if let Some(parent) = forest.get(leaf).parent
                    && Some(parent) != lca
                {
                    let sibling = forest
                        .find_sibling(leaf)
                        .expect("a parent and thus a sibling");
                    forest.cut_branch(sibling);
                    break 'cut_one_branch_on_path;
                }
            }
            break;
        }

        non_forced_cuts += 1;

        state.cut_opts.insert(sort_tup((a, b)));
    }

    let (sol, lb) = calc_expensive_lb_and_ub(state);
    (sol, lb - non_forced_cuts)
}

pub fn calc_simple_lb(mut state: State) -> usize {
    let (_, n_removed_svts) = state.remove_svt_and_merge_safe();

    if n_removed_svts != 0 {
        let lb = calc_simple_lb(state);
        return lb + n_removed_svts;
    }

    if state.rr_2_2_1_reduce() {
        return calc_simple_lb(state);
    }

    if state.instance.is_completed() {
        return state.instance.ord();
    }
    debug_assert!(state.instance.iterate_all_cherries().next().is_some());

    // Add cut-opt (a,b) for every cherry (a,b) s.t.
    // a is not in the same component as b in every forest
    state.add_cherry_cut_opts();

    // If a cut-opt is a cherry without a parent in any forest: split it
    if state.reduce_universal_hitting_pairs() {
        return calc_simple_lb(state);
    }

    // let ord = state.instance.ord();
    let mut non_forced_cuts: usize = 0;

    #[cfg(feature = "assert_validity")]
    state.assert_cut_opts_exist();
    #[cfg(feature = "assert_validity")]
    state.assert_no_svts();
    #[cfg(feature = "assert_validity")]
    assert_validity!(state);

    // perform a 'branch' but instead apply all options to arrive at an upper bound of MAF
    if let Some(&(a, b)) = state.cut_opts.iter().next() {
        // cut targets in each forest
        state.cut_svt(a);
        state.cut_svt(b);

        // we (possibly) performed one cut too many
        non_forced_cuts += 1;
        let lb = calc_simple_lb(state);

        lb - non_forced_cuts
    } else {
        state.instance.ord() - non_forced_cuts
    }
}

#[derive(Clone)]
pub struct State {
    pub instance: Instance,
    pub cut_opts: FxHashSet<(Label, Label)>,
}

impl State {
    /// Calculate a greedy maximal matching on the cut-opts of the instance
    /// This is a lower bound on the minimum vertex cover of cut-opts,
    /// Which is in turn a lb on the number of cuts needed
    pub fn get_matching_lb(&self) -> usize {
        let mut matched = FxHashSet::default();
        let mut count = 0;
        for &(a, b) in self.cut_opts.iter() {
            if !matched.contains(&a) && !matched.contains(&b) {
                // match a with b
                matched.insert(a);
                matched.insert(b);
                count += 1;
            }
        }
        count
    }

    /// Find cherries s.t. in each forest
    /// - there are 0 or 1 pendant subtrees between it, and
    /// - the label set of these pendant subtrees is equal
    ///
    /// These pendant subtrees are cut
    /// NOTE: does NOT perform this reduction exhaustively
    ///
    /// Returns true if at least one reduction was applied
    pub fn rr_2_2_1_reduce(&mut self) -> bool {
        let mut applied_a_reduction = false;

        // NOTE: the correctness of this reduction rule needs that
        // a and b are not in any cut-opts
        let mut labels_in_a_cut_opt = FxHashSet::default();
        for &(a, b) in self.cut_opts.iter() {
            labels_in_a_cut_opt.insert(a);
            labels_in_a_cut_opt.insert(b);
        }

        let cherries: Vec<(Label, Label)> = self
            .instance
            .iterate_all_cherries()
            .filter_map(|(_, a, b)| {
                if !labels_in_a_cut_opt.contains(&a) && !labels_in_a_cut_opt.contains(&b) {
                    Some((a, b))
                } else {
                    None
                }
            })
            .collect();

        'cherries: for (a, b) in cherries {
            debug_assert!(!self.cut_opts.contains(&sort_tup((a, b))));

            // check if labels still exist (after previous reduction iterations)
            let f1 = &self.instance.forests[0];
            if f1.try_locate_label(a).is_none() || f1.try_locate_label(b).is_none() {
                continue 'cherries;
            }

            // check if label is a cherry or uncle-nephew in every forest with the same label set
            let mut label_set_opt: Option<FxHashSet<Label>> = None;
            for forest in &self.instance.forests {
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
            for forest in self.instance.forests.iter_mut() {
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

            log!(|logs: &mut Logs| logs.rr_2_2_1_cuts += 1);
            applied_a_reduction = true;
        }
        applied_a_reduction
    }

    /// Exhaustively performs reductions:
    /// - merges common subtrees between all forests
    /// - syncs single vertex trees between the forests and removes them
    ///
    /// returns the removed svts and the merged labels
    pub fn remove_svt_and_merge_safe(&mut self) -> (Vec<PerformedReduction>, usize) {
        let mut performed_reductions: Vec<PerformedReduction> = vec![];
        let mut n_removed_svts: usize = 0;

        let mut to_check: Vec<Label> = self.instance.forests[0].iterate_all().labels().collect();
        let mut to_check_set: FxHashSet<Label> = to_check.iter().copied().collect();

        'outer: while let Some(label) = to_check.pop() {
            to_check_set.remove(&label);

            // check if label is part of a common cherry
            // or if it is a svt that is not yet synced
            let f1 = &self.instance.forests[0];
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
                for forest in &self.instance.forests[1..] {
                    let leaf1 = forest.locate_label(label_left);
                    let leaf2 = forest.locate_label(label_right);
                    if forest.get(leaf1).parent.is_none()
                        || forest.get(leaf1).parent != forest.get(leaf2).parent
                    {
                        break 'check_common_cherry;
                    }
                }

                if self.cut_opts.contains(&sort_tup((label_left, label_right))) {
                    // either left or right must be cut, but since it is a cherry everywhere,
                    // cutting left or right is equivalent: cut left (arbitrarily)
                    self.cut_opts.remove(&(label_left, label_right));

                    self.cut_svt(label_left);
                    if to_check_set.insert(label_right) {
                        to_check.push(label_right);
                    }
                    continue 'outer;
                }

                // (arbitrarily) assign the new label to be the one with the lowest number
                let new_label = label_left.min(label_right);

                // apply merge in each forest
                self.instance
                    .merge_common_sibling(label_left, label_right, new_label);
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
                for f in self.instance.forests.iter_mut() {
                    let label_idx = f.locate_label(label);
                    let is_svt_in_this_forests = f.get(label_idx).parent.is_none();

                    is_svt_in_all &= is_svt_in_this_forests;
                    is_svt_in_any |= is_svt_in_this_forests;
                }
                match (is_svt_in_any, is_svt_in_all) {
                    (_, true) => {
                        // WARN: this could be a newly formed s.v.t
                        // So: remove it from the cut-opts
                        self.cut_opts.retain(|&(a, b)| a != label && b != label);
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
                self.instance.remove_svt(label);
                n_removed_svts += 1;
                performed_reductions.push(SvtRemoved { label });
            }
        }

        (performed_reductions, n_removed_svts)
    }

    // for each component:
    // - find a label in it that is in a cut_opts with every other
    //   label from that component
    // if found: cut that label and return true
    // otherwise: return false
    pub fn reduce_universal_hitting_pairs(&mut self) -> bool {
        let (_, max_degree) = self.get_max_cut_opt();
        for f in self.instance.forests.iter() {
            'comps: for &root in f.roots.iter() {
                let mut non_uni_labels = vec![];
                let mut universal_labels = vec![];
                for label in f.dfs_from(root).labels() {
                    if non_uni_labels.len() + universal_labels.len() > max_degree {
                        continue 'comps;
                    }

                    let mut new_label_is_uni = true;

                    universal_labels.retain(|&uni_label| {
                        if self.cut_opts.contains(&sort_tup((uni_label, label))) {
                            true
                        } else {
                            new_label_is_uni = false;
                            non_uni_labels.push(uni_label);
                            false
                        }
                    });

                    new_label_is_uni = new_label_is_uni
                        && non_uni_labels.iter().all(|&non_uni_label| {
                            self.cut_opts.contains(&sort_tup((non_uni_label, label)))
                        });

                    if new_label_is_uni {
                        universal_labels.push(label);
                    } else {
                        non_uni_labels.push(label);
                    }
                }

                if !universal_labels.is_empty()
                    && universal_labels.len() + non_uni_labels.len() >= 2
                {
                    log!(|logs: &mut Logs| logs.universal_cut_opt += 1);

                    let mut universal_labels_iter = universal_labels.into_iter();
                    if non_uni_labels.is_empty() {
                        universal_labels_iter.next();
                    }

                    for label in universal_labels_iter {
                        self.cut_svt(label);
                    }
                    return true;
                }
            }
        }
        false
    }

    // Perform `reduce_universal_hitting_pairs` (as above) but only on label in the same component
    // as label a.
    // Can be used to perform the reduction more efficiently when only one hitting pair (=cut_opt)
    // has been changed
    pub fn reduce_universal_hitting_pairs_on_label(&mut self, a: Label) -> bool {
        let (_, max_degree) = self.get_max_cut_opt();
        'forests: for f in self.instance.forests.iter() {
            let root = f.find_root_of(f.locate_label(a));

            let mut non_uni_labels = vec![];
            let mut universal_labels = vec![];
            for label in f.dfs_from(root).labels() {
                if non_uni_labels.len() + universal_labels.len() > max_degree {
                    continue 'forests;
                }

                let mut new_label_is_uni = true;

                universal_labels.retain(|&uni_label| {
                    if self.cut_opts.contains(&sort_tup((uni_label, label))) {
                        true
                    } else {
                        new_label_is_uni = false;
                        non_uni_labels.push(uni_label);
                        false
                    }
                });

                new_label_is_uni = new_label_is_uni
                    && non_uni_labels.iter().all(|&non_uni_label| {
                        self.cut_opts.contains(&sort_tup((non_uni_label, label)))
                    });

                if new_label_is_uni {
                    universal_labels.push(label);
                } else {
                    non_uni_labels.push(label);
                }
            }

            if !universal_labels.is_empty() && universal_labels.len() + non_uni_labels.len() >= 2 {
                log!(|logs: &mut Logs| logs.universal_cut_opt += 1);
                let mut universal_labels_iter = universal_labels.into_iter();
                if non_uni_labels.is_empty() {
                    universal_labels_iter.next();
                }

                for label in universal_labels_iter {
                    self.cut_svt(label);
                }
                return true;
            }
        }

        false
    }

    /// Find a cherry (a,b) that is not a cut-opt, and maximizes the strategy value:
    /// Maximizes the total number of pendant subtrees between the cherry (summed over forests)
    ///
    /// Returns None if all cherries are also a cut-opt
    #[allow(unused)]
    pub fn find_path_cut_target_total_path_strategy(&self) -> Option<((Label, Label), usize)> {
        let cherries = self
            .instance
            .iterate_all_cherries()
            .filter(|&(_, a, b)| !self.cut_opts.contains(&sort_tup((a, b))));

        let mut target = None;
        let mut max_path_len = 0;

        for (_, a, b) in cherries {
            let mut total_path_len = 0;

            for forest in self.instance.forests.iter() {
                let leaf_a = forest.locate_label(a);
                let leaf_b = forest.locate_label(b);
                let lca = forest
                    .get_lca(leaf_a, leaf_b)
                    .expect("labels in the same comp");

                total_path_len += forest
                    .ancestors_incl(leaf_a)
                    .take_while(|&anc| anc != lca)
                    .count()
                    + forest
                        .ancestors_incl(leaf_b)
                        .take_while(|&anc| anc != lca)
                        .count()
                    + 1;
            }
            if target.is_none() || total_path_len > max_path_len {
                target = Some((a, b));
                max_path_len = total_path_len;
            }
        }
        target.map(|t| (t, max_path_len))
    }

    /// Find a cherry (a,b) that is not a cut-opt, and maximizes the strategy value:
    /// Maximizes the total number of pendant subtrees between the cherry (summed over forests)
    ///
    /// Returns None if all cherries are also a cut-opt
    pub fn find_path_cut_target_total_path_strategy_return_ord(
        &self,
    ) -> Option<((Label, Label), usize, usize)> {
        let cherries = self
            .instance
            .iterate_all_cherries()
            .filter(|&(_, a, b)| !self.cut_opts.contains(&sort_tup((a, b))));

        let mut target = None;
        let mut max_path_len = 0;
        let mut new_ord = self.instance.ord();

        for (_, a, b) in cherries {
            let mut total_path_len = 0;
            let mut cur_ord = 0;
            for forest in self.instance.forests.iter() {
                let leaf_a = forest.locate_label(a);
                let leaf_b = forest.locate_label(b);
                let lca = forest
                    .get_lca(leaf_a, leaf_b)
                    .expect("labels in the same comp");

                let extra_path_len = forest
                    .ancestors_incl(leaf_a)
                    .take_while(|&anc| anc != lca)
                    .count()
                    + forest
                        .ancestors_incl(leaf_b)
                        .take_while(|&anc| anc != lca)
                        .count()
                    + 1;
                total_path_len += extra_path_len;
                cur_ord = cur_ord.max(forest.ord() + extra_path_len - 3)
            }
            if target.is_none() || total_path_len > max_path_len {
                target = Some((a, b));
                max_path_len = total_path_len;
                new_ord = cur_ord;
            }
        }
        target.map(|t| (t, max_path_len, new_ord))
    }

    /// Find a cherry (a,b) that is not a cut-opt, and maximizes the strategy value:
    /// Maximizes the resulting ord of the instance after
    /// cutting all pendant subtrees between the cherry
    ///
    /// Returns None if all cherries are also a cut-opt
    /// Otherwise returns said cherry and the strategy value ord
    pub fn find_path_cut_target_ord_strategy(&self) -> Option<((Label, Label), usize)> {
        let cherries = self
            .instance
            .iterate_all_cherries()
            .filter(|&(_, a, b)| !self.cut_opts.contains(&sort_tup((a, b))));

        let mut target = None;
        let mut max_ord = 0;

        for (_, a, b) in cherries {
            let ord = self
                .instance
                .forests
                .iter()
                .map(|f| {
                    let leaf_a = f.locate_label(a);
                    let leaf_b = f.locate_label(b);
                    let lca = f.get_lca(leaf_a, leaf_b).expect("labels in the same comp");

                    // find the number of pendant subtrees between a and b, add it to the original ord
                    f.ord()
                        + f.ancestors_incl(leaf_a)
                            .take_while(|&anc| anc != lca)
                            .count()
                        + f.ancestors_incl(leaf_b)
                            .take_while(|&anc| anc != lca)
                            .count()
                        - 2
                })
                .max()
                .unwrap();
            if target.is_none() || ord > max_ord {
                target = Some((a, b));
                max_ord = ord;
            }
        }
        target.map(|t| (t, max_ord))
    }

    /// Find the cherry with the largest number of cut-opt entries
    pub fn get_max_cut_opt(&self) -> (Option<Label>, usize) {
        let mut degrees: FxHashMap<Label, usize> = FxHashMap::default();
        for &(a2, b2) in self.cut_opts.iter() {
            degrees
                .entry(a2)
                .and_modify(|degree| *degree += 1)
                .or_insert(1);
            degrees
                .entry(b2)
                .and_modify(|degree| *degree += 1)
                .or_insert(1);
        }

        // TODO: clean up
        if let Some((&max_degree_label, &degree)) = degrees.iter().max_by_key(|&(_, degree)| degree)
        {
            (Some(max_degree_label), degree)
        } else {
            (None, 0)
        }
    }

    /// Adds cut-opts that are definitely needed.
    /// Iterates all cherries (a,b) s.t. in some other forests
    /// a and b are in different components: adds (a,b) as cut-opt
    pub fn add_cherry_cut_opts(&mut self) {
        let mut new_cut_opts = vec![];
        let cherries = self
            .instance
            .iterate_all_cherries()
            .filter(|&(_, a, b)| !self.cut_opts.contains(&sort_tup((a, b))));
        for (_, a, b) in cherries {
            let ab_in_same_comp =
                self.instance.forests.iter().all(|f| {
                    f.find_root_of(f.locate_label(a)) == f.find_root_of(f.locate_label(b))
                });

            if !ab_in_same_comp {
                new_cut_opts.push(sort_tup((a, b)));
            }
        }
        self.cut_opts.extend(new_cut_opts);
    }

    /// Cut off a single label, making it a single vertex tree in each forest
    pub fn cut_svt(&mut self, label: Label) {
        // remove all cutting constraints involving the cut label
        self.cut_opts.retain(|&(a, b)| a != label && b != label);

        // perform the cut in each forest
        for forest in self.instance.forests.iter_mut() {
            let leaf_a_idx = forest.locate_label(label);
            if forest.get(leaf_a_idx).parent.is_some() {
                forest.cut_branch(leaf_a_idx);
            }
        }
    }

    /// Cut off a single label, making it a single vertex tree in each forest
    /// Returns the labels of all siblings (across the forests) of the cut (may contain duplicates)
    pub fn cut_svt_return_siblings_labels(&mut self, label: Label) -> Vec<Label> {
        // remove all cutting constraints involving the cut label
        self.cut_opts.retain(|&(a, b)| a != label && b != label);

        let mut sibling_labels = vec![];

        // perform the cut in each forest
        for forest in self.instance.forests.iter_mut() {
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

    #[cfg(feature = "assert_validity")]
    pub fn assert_validity(&self) {
        let f1 = &self.instance.forests[0];
        for &(a, b) in self.cut_opts.iter() {
            assert_ne!(a, b);
            assert!(a < b);

            assert!(f1.try_locate_label(a).is_some());
            assert!(f1.try_locate_label(b).is_some());
        }

        let labels_f1: FxHashSet<_> = f1.iterate_all().labels().collect();
        assert_eq!(labels_f1.len(), self.instance.num_leaves);

        for f in self.instance.forests.iter() {
            let labels: FxHashSet<_> = f.iterate_all().labels().collect();
            assert_eq!(labels, labels_f1);
        }
    }

    #[cfg(feature = "assert_validity")]
    pub fn assert_svt_synced(&self) {
        let f1 = &self.instance.forests[0];
        for label in f1.iterate_all().labels() {
            let leaf = f1.locate_label(label);
            let is_svt = f1.get(leaf).parent.is_none();

            for f in self.instance.forests[1..].iter() {
                let leaf2 = f.locate_label(label);
                let is_svt_here = f.get(leaf2).parent.is_none();
                assert_eq!(is_svt, is_svt_here);
            }
        }
    }

    #[cfg(feature = "assert_validity")]
    pub fn assert_no_svts(&self) {
        for f in self.instance.forests.iter() {
            for &root in f.roots.iter() {
                assert_eq!(f.get(root).label(), None);
            }
        }
    }

    #[cfg(feature = "assert_validity")]
    pub fn assert_cherries_merged(&self) {
        let f1 = &self.instance.forests[0];
        for &label in f1.leaf_map.keys() {
            // check if label is part of a common cherry
            // or if it is a svt that is not yet synced
            let Some(leaf_idx) = f1.try_locate_label(label) else {
                unreachable!();
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
                for forest in &self.instance.forests[1..] {
                    let leaf1 = forest.locate_label(label_left);
                    let leaf2 = forest.locate_label(label_right);
                    if forest.get(leaf1).parent.is_none()
                        || forest.get(leaf1).parent != forest.get(leaf2).parent
                    {
                        break 'check_common_cherry;
                    }
                }

                unreachable!("there should be no common cherries");
            }
        }
    }

    #[cfg(feature = "assert_validity")]
    pub fn assert_no_cut_opts_svt(&self) {
        let f1 = &self.instance.forests[0];
        let svts: FxHashSet<Label> = f1
            .iterate_all()
            .filter_map(|(_, v)| if v.parent.is_none() { v.label() } else { None })
            .collect();
        for (a, b) in self.cut_opts.iter() {
            assert!(!svts.contains(a));
            assert!(!svts.contains(b));
        }
    }

    #[cfg(feature = "assert_validity")]
    pub fn assert_cut_opts_exist(&self) {
        let f1 = &self.instance.forests[0];
        for (a, b) in self.cut_opts.iter() {
            assert!(f1.leaf_map.contains_key(a));
            assert!(f1.leaf_map.contains_key(b));
        }
    }
}
