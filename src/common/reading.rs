use pace26io::binary_tree::IndexedBinTreeBuilder;
use pace26io::pace::simplified::*;
use std::io::stdin;

use crate::maf_instance::instance;

type Builder = IndexedBinTreeBuilder;
// type Node = <Builder as TreeBuilder>::Node;

pub fn read_instance_from_std_in() -> Instance<Builder> {
    let mut input = stdin().lock();

    let mut tree_builder = Builder::default();

    Instance::try_read(&mut input, &mut tree_builder).expect("Valid PACE26 Instance")
}

#[inline]
pub fn read_to_my_instance() -> instance::Instance {
    instance::Instance::new_from_instance(read_instance_from_std_in())
}

pub trait PrintableSolution {
    fn print_newick_strings(&self);
}
