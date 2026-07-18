use giputils::statistic::{Average, AverageDuration};
use std::ops::AddAssign;

#[derive(Debug, Default, Clone, Copy)]
pub struct SolverStatistic {
    pub num_solve: usize,
    pub avg_solve_time: AverageDuration,
    pub avg_decide_var: Average,
    pub num_simplify_subsume: usize,
    pub num_simplify_self_subsume: usize,
    /// watch events resolved by the blocker (no clause fetch)
    pub num_prop_blocker: usize,
    /// watch events fetching a short (<=3 lit) clause
    pub num_prop_short: usize,
    /// watch events fetching a long (>3 lit) clause
    pub num_prop_long: usize,
    /// learnt clauses shortened by vivification
    pub num_vivify_shrunk: usize,
    /// literals removed by vivification
    pub num_vivify_lits: usize,
    /// total time spent in vivification
    pub vivify_time: std::time::Duration,
}

impl AddAssign for SolverStatistic {
    fn add_assign(&mut self, rhs: Self) {
        self.num_solve += rhs.num_solve;
        self.avg_solve_time += rhs.avg_solve_time;
        self.avg_decide_var += rhs.avg_decide_var;
        self.num_simplify_subsume += rhs.num_simplify_subsume;
        self.num_simplify_self_subsume += rhs.num_simplify_self_subsume;
        self.num_prop_blocker += rhs.num_prop_blocker;
        self.num_prop_short += rhs.num_prop_short;
        self.num_prop_long += rhs.num_prop_long;
        self.num_vivify_shrunk += rhs.num_vivify_shrunk;
        self.num_vivify_lits += rhs.num_vivify_lits;
        self.vivify_time += rhs.vivify_time;
    }
}
