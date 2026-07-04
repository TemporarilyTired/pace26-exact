use pace26_exact::alg_hitting_pair_dbs::solve_binary_search_dbs;
use pace26_exact::common::reading::PrintableSolution;
use pace26_exact::common::reading::read_to_my_instance;

fn main() {
    println!("# Starting hitting pair depth bounded search");
    let instance = read_to_my_instance();

    println!(
        "# Succesfully read {} forests with {} leaves",
        instance.forests.len(),
        instance.num_leaves
    );

    println!("# Calling solve method");

    let maf = solve_binary_search_dbs(instance);

    maf.print_newick_strings();
}
