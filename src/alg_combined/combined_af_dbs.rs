use rustc_hash::FxHashSet;

use crate::alg_af_dfs::{BuState, try_init_bu_state};
use crate::alg_hitting_pair_dbs::hitting_pair_dbs::solve_binary_search_dbs_with_bounds;
use crate::maf_instance::{arena_tree::ArenaTree, instance::Instance};

pub fn solve_combined(instance: Instance) -> ArenaTree {
    // get an upper and lower bound, to see which algorithm we try first
    let approx_state = crate::alg_hitting_pair_dbs::hitting_pair_dbs::State {
        instance: instance.clone(),
        cut_opts: FxHashSet::default(),
    };
    let (mut upper_bound_af, lb) =
        crate::alg_hitting_pair_dbs::hitting_pair_dbs::calc_expensive_lb_and_ub(approx_state);
    let ub = upper_bound_af.ord();

    // Instances with a low order agreement forest: always use DBS
    if ub < 11 {
        return solve_binary_search_dbs_with_bounds(instance, lb, upper_bound_af);
    }

    // Instances with much slack to the trivial agreement forest
    // (i.e. a large order MAF): don't every try AF-DFS, always use DBS
    let n_connections = instance.num_leaves - ub;
    if n_connections > 20
        || n_connections > 15 && instance.num_leaves > 30
        || n_connections > 13 && instance.num_leaves > 100
    {
        return solve_binary_search_dbs_with_bounds(instance, lb, upper_bound_af);
    }

    // We can safely iterate and store 100M path pairs, because they are stored as
    // u64s in a HashSet, which means at most 3x memory overhead
    const MAX_N_PATH_PAIRS: usize = 100_000_000;
    let Some(mut af_dfs_state) = try_init_bu_state(instance.clone(), MAX_N_PATH_PAIRS) else {
        return solve_binary_search_dbs_with_bounds(instance, lb, upper_bound_af);
    };

    // We run the AF-DFS for some iterations and see how far along it is
    let mut time_limit_s = 2;
    let mut total_time_ran_s = time_limit_s;
    loop {
        total_time_ran_s += time_limit_s;
        if let Some(sol) = af_dfs_state.try_solve(time_limit_s) {
            return sol;
        }

        // NOTE: Look at upper bound on MAF and estimated total runtime to decide (very crudely)
        // when to give up on AF-DFS and default to DBS
        let new_ub = af_dfs_state.get_best_sol_ord();
        let n_connections = instance.num_leaves - ub;
        let est_solve_time_s = estimate_solve_time_s(&af_dfs_state, total_time_ran_s);
        #[cfg(feature = "logging")]
        {
            println!("# total_time_ran_s = {}", total_time_ran_s);
            println!("# est_solve_time_s = {}", est_solve_time_s);
            println!("# new_ub = {}", new_ub);
        }
        if total_time_ran_s > 120 && est_solve_time_s > 3600_f64
            || total_time_ran_s > 2 && est_solve_time_s > 60_f64 && new_ub <= 20
            || total_time_ran_s > 10 && est_solve_time_s > 180_f64 && new_ub <= 30
            || total_time_ran_s > 30 && est_solve_time_s > 1800_f64 && new_ub <= 50
            || total_time_ran_s > 30 && est_solve_time_s > 7200_f64 && new_ub <= 100
            || n_connections > 25
            || n_connections > 20 && instance.num_leaves > 30
            || n_connections > 15 && instance.num_leaves > 100
            || n_connections > 13 && instance.num_leaves > 200
            || n_connections > 10 && instance.num_leaves > 300
        {
            break;
        }

        // increase the time limit a bit each iteration
        time_limit_s = (time_limit_s as f64 * 1.4).round() as u64;
    }

    // If we did find a better upper bound in the AF-DFS, pass it on
    if af_dfs_state.get_best_sol_ord() < ub {
        upper_bound_af = af_dfs_state.get_current_best_solution_forest();
    }
    solve_binary_search_dbs_with_bounds(instance, lb, upper_bound_af)
}

fn estimate_solve_time_s(af_dfs_state: &BuState, total_time_ran_s: u64) -> f64 {
    let (progress_i, max_progress) = af_dfs_state.estimate_progress();
    if progress_i == 0 {
        return f64::INFINITY;
    }

    let progress = progress_i as f64 / max_progress as f64;
    let progress_per_s = progress / total_time_ran_s as f64;
    1_f64 / progress_per_s
}
