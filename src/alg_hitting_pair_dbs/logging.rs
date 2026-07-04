#[cfg(feature = "logging")]
use std::cell::RefCell;

#[cfg(feature = "logging")]
#[derive(Default)]
pub struct Logs {
    pub total_calls: u64,
    pub prunes_at_merge: u64,
    pub case_1_total: u64,
    pub case_1_a: u64,
    pub case_1_b: u64,
    pub case_1_c: u64,
    pub case_2: u64,
    pub rr_2_2_1_succesful: u64,
    pub rr_2_2_1_cuts: u64,
    pub rr_2_2_1_termination: u64,
    pub universal_cut_opt: u64,
    pub comp_clusters: u64,
    pub subtree_clusters: u64,
    pub total_branches: u64,
    pub total_branches_all_k: u64,
    pub ub_3_approx_best: u64,
    pub lb_3_approx_prune: u64,
}

#[cfg(feature = "logging")]
impl Logs {
    pub fn print_logs_after_k(&self, k: usize) {
        println!("#s total_branches_all_k {}", self.total_branches_all_k);
        for (name, val) in [
            ("total_calls", self.total_calls),
            ("prunes_at_merge", self.prunes_at_merge),
            ("ub_3_approx_best", self.ub_3_approx_best),
            ("lb_3_approx_prune", self.lb_3_approx_prune),
            ("case_1_total", self.case_1_total),
            ("case_1_a", self.case_1_a),
            ("case_1_b_branch", self.case_1_b),
            ("case_1_c", self.case_1_c),
            ("case_2___branch", self.case_2),
            ("rr_2_2_1_succesful", self.rr_2_2_1_succesful),
            ("rr_2_2_1_cuts", self.rr_2_2_1_cuts),
            ("rr_2_2_1_termination", self.rr_2_2_1_termination),
            ("universal_cut_opt", self.universal_cut_opt),
            ("comp_clusters", self.comp_clusters),
            ("subtree_clusters", self.subtree_clusters),
            ("total_branches", self.total_branches),
        ] {
            println!("#s k{}_{} {}", k, name, val);
        }
    }

    pub fn reset_logs_for_new_k(&mut self) {
        *self = Logs {
            total_branches_all_k: self.total_branches_all_k,
            ..Default::default()
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
