use crate::alg_af_dfs::reductions::AfDbsReductionsInstanceExt;
use crate::maf_instance::{arena_tree::ArenaTree, arena_vertex::Label, instance::Instance};

use super::combined_af_dbs::solve_combined;

pub fn solve(mut instance: Instance) -> ArenaTree {
    // INFO: apply:
    // - sibling leaf merge,
    // - single vertex tree syncing, and
    // - reduction rule 2.2.1 (from DBS-LSI)
    // - reduction rule 1 (from DBS-LSI)
    // to exhaustively to reduce the input trees to (smaller) forests
    let performed_reductions = instance.fully_reduce();

    let clusters = instance.clone().split_into_clusters();
    let mut cluster_mafs = vec![];

    for cluster in clusters {
        cluster_mafs.push(solve_cluster(cluster));
    }

    let mut maf = cluster_mafs
        .into_iter()
        .reduce(|maf1, maf2| maf1.join_with(maf2))
        .unwrap_or_default();

    for reduction in performed_reductions.iter().rev() {
        maf.undo_reduction(reduction.clone());
    }
    maf
}

/// Solve a fully reduced cluster of an instance
fn solve_cluster(cluster: Instance) -> ArenaTree {
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
    )) = cluster.find_clusters_w_dummy()
    {
        return solve_split_with_dummy(
            above,
            below,
            (above_w_dummy, used_dummy_above),
            (below_w_dummy, used_dummy_below),
        );
    }

    #[cfg(feature = "logging")]
    println!(
        "# solving minimial cluster (ord={}) leaves: \t{}",
        cluster.ord(),
        cluster.num_leaves,
    );

    solve_combined(cluster)
}

/// Solve an instance split into 4 by subtree cluster reduction
fn solve_split_with_dummy(
    above: Instance,
    below: Instance,
    (above_with_dummy, used_dummy_above): (Instance, Label),
    (below_with_dummy, used_dummy_below): (Instance, Label),
) -> ArenaTree {
    let mut a_dummy = solve(above_with_dummy);
    if a_dummy
        .get(a_dummy.locate_label(used_dummy_above))
        .parent
        .is_some()
    {
        let mut b_dummy = solve(below_with_dummy);
        if b_dummy
            .get(b_dummy.locate_label(used_dummy_below))
            .parent
            .is_some()
        {
            // NOTE: check which of a and b is likely to be the quickest to solve:
            // solve that one first
            let difficulty_a = above.num_leaves + 1;
            let difficulty_b = below.num_leaves + 1;

            if difficulty_a < difficulty_b {
                // We can construct a solution of order |a_dummy| + |b_dummy| -1
                // But this can still be one larger than |a| + |b| in the case:
                //      |a_dummy| = |a|+1 and |b_dummy| = |b|+1
                // So we need to calculate |a| and |b| too
                let a = solve(above);
                if a.ord() == a_dummy.ord() {
                    // |a_dummy| = |a|, thus |a_dummy| + |b_dummy| - 1 <= |a| + |b|
                    return a_dummy.join_at_dummy(b_dummy, used_dummy_above, used_dummy_below);
                }
                let b = solve(below);
                if b.ord() == b_dummy.ord() {
                    // |b_dummy| = |b|, thus |a_dummy| + |b_dummy| - 1 <= |a| + |b|
                    return a_dummy.join_at_dummy(b_dummy, used_dummy_above, used_dummy_below);
                }
                return a.join_with(b);
            }

            // We can construct a solution of order |a_dummy| + |b_dummy| -1
            // But this can still be one larger than |a| + |b| in the case:
            //      |a_dummy| = |a|+1 and |b_dummy| = |b|+1
            // So we need to calculate |a| and |b| too
            let b = solve(below);
            if b.ord() == b_dummy.ord() {
                // |b_dummy| = |b|, thus |a_dummy| + |b_dummy| - 1 <= |a| + |b|
                return a_dummy.join_at_dummy(b_dummy, used_dummy_above, used_dummy_below);
            }
            let a = solve(above);
            if a.ord() == a_dummy.ord() {
                // |a_dummy| = |a|, thus |a_dummy| + |b_dummy| - 1 <= |a| + |b|
                return a_dummy.join_at_dummy(b_dummy, used_dummy_above, used_dummy_below);
            }
            return a.join_with(b);
        }
        // b_dummy contains an optimal solution for below
        b_dummy.remove_svt(used_dummy_below);
        let a = solve(above);
        return a.join_with(b_dummy);
    }

    // a_dummy contains an optimal solution for above
    a_dummy.remove_svt(used_dummy_above);
    let b = solve(below);
    a_dummy.join_with(b)
}
