#[cfg(feature = "logging")]
use std::cell::RefCell;

#[cfg(feature = "logging")]
#[derive(Default)]
pub struct Logs {
    pub n_leaves_after_merging: u64,
    pub ord_after_merging: u64,
    pub n_triple_constr: u64,
    pub max_comp_size: u64,
    // pub n_overlap_pair_constr: u64,
    pub n_non_overlap_pair_constr: u64,
    // pub n_incomp_pair_constr: u64,
}

#[cfg(feature = "logging")]
impl Logs {
    pub fn print_logs(&self) {
        for (name, val) in [
            ("n_leaves_after_merging", self.n_leaves_after_merging),
            ("ord_after_merging", self.ord_after_merging),
            ("n_triple_constr", self.n_triple_constr),
            // ("n_overlap_pair_constr", self.n_overlap_pair_constr),
            ("n_non_overlap_pair_constr", self.n_non_overlap_pair_constr),
            ("max_comp_size", self.max_comp_size),
            // ("n_path_pair_constr", self.n_incomp_pair_constr),
        ] {
            println!("#s {} {}", name, val);
        }
    }
    pub fn print_logs_partial(&self) {
        for (name, val) in [
            ("n_leaves_after_merging", self.n_leaves_after_merging),
            ("ord_after_merging", self.ord_after_merging),
            ("n_triple_constr", self.n_triple_constr),
            // ("n_overlap_pair_constr", self.n_overlap_pair_constr),
            ("n_non_overlap_pair_constr", self.n_non_overlap_pair_constr),
            ("max_comp_size", self.max_comp_size),
            // ("n_path_pair_constr", self.n_incomp_pair_constr),
        ] {
            if val > 0 {
                println!("#s {} {}", name, val);
            }
        }
    }
}

#[cfg(feature = "logging")]
thread_local! {
    pub static LOGS: RefCell<Logs> = RefCell::new(Logs::default());
}

#[cfg(feature = "logging")]
macro_rules! log {
    ($body:expr) => {
        LOGS.with(|s| $body(&mut *s.borrow_mut()))
    };
}

#[cfg(not(feature = "logging"))]
macro_rules! log {
    ($body:expr) => {};
}

pub(crate) use log;
