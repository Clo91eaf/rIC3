use giputils::statistic::{Average, AverageDuration};
use std::ops::AddAssign;

#[derive(Debug, Default, Clone, Copy)]
pub struct SolverStatistic {
    pub num_solve: usize,
    pub avg_solve_time: AverageDuration,
    pub avg_decide_var: Average,
    pub num_simplify_subsume: usize,
    pub num_simplify_self_subsume: usize,
    /// solves that reused a trail prefix from the previous solve (ILB)
    pub num_ilb: usize,
    /// average number of reused decision levels on ILB solves
    pub avg_ilb_reuse: Average,
    /// average shared-assumption-prefix length BEFORE soundness clamps
    pub avg_ilb_prefix: Average,
    /// reuse depth on constrained (mic-style) fast solves
    pub avg_ilb_reuse_con: Average,
    /// reuse depth as a fraction of the reusable maximum, constrained solves
    pub avg_ilb_frac_con: Average,
    /// reuse depth on unconstrained fast solves
    pub avg_ilb_reuse_unc: Average,
    /// constrained (mic-style) fast solves
    pub num_ilb_con: usize,
    /// clamp events: kept ¬act assignment below the shared prefix
    pub num_ilb_clamp_act: usize,
    /// clamp events: locked temporary clause below the shared prefix
    pub num_ilb_clamp_locked: usize,
}

impl AddAssign for SolverStatistic {
    fn add_assign(&mut self, rhs: Self) {
        self.num_solve += rhs.num_solve;
        self.avg_solve_time += rhs.avg_solve_time;
        self.avg_decide_var += rhs.avg_decide_var;
        self.num_simplify_subsume += rhs.num_simplify_subsume;
        self.num_simplify_self_subsume += rhs.num_simplify_self_subsume;
        self.num_ilb += rhs.num_ilb;
        self.avg_ilb_reuse += rhs.avg_ilb_reuse;
        self.avg_ilb_prefix += rhs.avg_ilb_prefix;
        self.avg_ilb_reuse_con += rhs.avg_ilb_reuse_con;
        self.avg_ilb_frac_con += rhs.avg_ilb_frac_con;
        self.avg_ilb_reuse_unc += rhs.avg_ilb_reuse_unc;
        self.num_ilb_con += rhs.num_ilb_con;
        self.num_ilb_clamp_act += rhs.num_ilb_clamp_act;
        self.num_ilb_clamp_locked += rhs.num_ilb_clamp_locked;
    }
}
