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
    }
}
