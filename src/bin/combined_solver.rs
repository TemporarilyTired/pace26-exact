use pace26_exact::alg_combined::solve;
use pace26_exact::common::reading::PrintableSolution;
use pace26_exact::common::reading::read_to_my_instance;

fn main() {
    println!("# Starting combined agreement forest dfs + hitting pair dbs");

    let instance = read_to_my_instance();

    println!(
        "# Succesfully read {} forests with {} leaves",
        instance.forests.len(),
        instance.num_leaves
    );

    println!("# Calling combined hitting pair DBS + AF-DFS method");
    let maf = solve(instance);
    maf.print_newick_strings();
}
