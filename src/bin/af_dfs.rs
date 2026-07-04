use pace26_exact::alg_af_dfs::solve;
use pace26_exact::common::reading::PrintableSolution;
use pace26_exact::common::reading::read_to_my_instance;

fn main() {
    println!("# Starting agreement forest dfs");
    println!("#s alg 3");

    let instance = read_to_my_instance();

    println!(
        "# Succesfully read {} forests with {} leaves",
        instance.forests.len(),
        instance.num_leaves
    );

    println!("# Calling solve method");

    let maf = solve(instance);

    maf.print_newick_strings();
}
