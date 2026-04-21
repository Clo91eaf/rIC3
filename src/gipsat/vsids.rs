use super::{DagCnfSolver, cdb::CREF_NONE};
use giputils::{OptionU32, gvec::Gvec};
use logicrs::{Lbool, Lit, LitVec, Var, VarMap};
use rand::RngExt;
use std::ops::{Index, MulAssign};

#[derive(Clone)]
pub struct VmtfQueue {
    pub queue: Vec<Var>,      // ordered list, front = highest priority
    pos: VarMap<u32>,         // var -> position in queue
    enabled: bool,
}

impl VmtfQueue {
    pub fn new() -> Self {
        Self {
            queue: Vec::new(),
            pos: Default::default(),
            enabled: false,
        }
    }

    pub fn init_from_scores(&mut self, scores: &VarMap<f64>, num_vars: usize) {
        let mut vars: Vec<(Var, f64)> = (0..num_vars)
            .map(|i| {
                let v = Var::new(i);
                let s = if (v.0 as usize) < scores.len() { scores[v] } else { 0.0 };
                (v, s)
            })
            .collect();
        vars.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        self.queue = vars.into_iter().map(|(v, _)| v).collect();
        self.pos = Default::default();
        for (i, &v) in self.queue.iter().enumerate() {
            self.pos.reserve(v);
            self.pos[v] = i as u32;
        }
        self.enabled = true;
    }

    pub fn move_to_front(&mut self, var: Var) {
        if !self.enabled || var.0 as usize >= self.pos.len() {
            return;
        }
        let old_pos = self.pos[var] as usize;
        if old_pos == 0 { return; }
        // Shift everything from 0..old_pos right by 1
        for i in (0..old_pos).rev() {
            self.queue[i + 1] = self.queue[i];
            self.pos[self.queue[i + 1]] = (i + 1) as u32;
        }
        self.queue[0] = var;
        self.pos[var] = 0;
    }

    pub fn is_enabled(&self) -> bool {
        self.enabled
    }
}

#[derive(Default, Clone)]
pub struct BinaryHeap {
    heap: Gvec<Var>,
    pos: VarMap<OptionU32>,
}

impl BinaryHeap {
    #[inline]
    fn reserve(&mut self, var: Var) {
        self.pos.reserve(var);
    }

    #[inline]
    pub fn clear(&mut self) {
        for v in self.heap.iter() {
            self.pos[*v] = OptionU32::NONE;
        }
        self.heap.clear();
    }

    #[inline]
    fn up(&mut self, v: Var, activity: &Activity) {
        let mut idx = match self.pos[v] {
            OptionU32::NONE => return,
            idx => *idx,
        };
        while idx != 0 {
            let pidx = (idx - 1) >> 1;
            if activity[self.heap[pidx]] >= activity[v] {
                break;
            }
            self.heap[idx] = self.heap[pidx];
            *self.pos[self.heap[idx]] = idx;
            idx = pidx;
        }
        self.heap[idx] = v;
        *self.pos[v] = idx;
    }

    #[inline]
    fn down(&mut self, mut idx: u32, activity: &Activity) {
        let v = self.heap[idx];
        loop {
            let left = (idx << 1) + 1;
            if left >= self.heap.len() as u32 {
                break;
            }
            let right = left + 1;
            let child = if right < self.heap.len() as u32
                && activity[self.heap[right]] > activity[self.heap[left]]
            {
                right
            } else {
                left
            };
            if activity[v] >= activity[self.heap[child]] {
                break;
            }
            self.heap[idx] = self.heap[child];
            *self.pos[self.heap[idx]] = idx;
            idx = child;
        }
        self.heap[idx] = v;
        *self.pos[v] = idx;
    }

    #[inline]
    pub fn push(&mut self, var: Var, activity: &Activity) {
        if self.pos[var].is_some() {
            return;
        }
        let idx = self.heap.len() as u32;
        self.heap.push(var);
        *self.pos[var] = idx;
        self.up(var, activity);
    }

    #[inline]
    pub fn pop(&mut self, activity: &Activity) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let value = self.heap[0u32];
        self.heap[0u32] = self.heap[self.heap.len() - 1];
        *self.pos[self.heap[0u32]] = 0;
        self.pos[value] = OptionU32::NONE;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.down(0, activity);
        }
        Some(value)
    }
}

#[derive(Clone)]
pub struct Activity {
    activity: VarMap<f64>,
    pub act_inc: f64,
    bucket_heap: BinaryHeap,
    bucket_table: Gvec<u32>,
    bump_weights: VarMap<f64>,
}

impl Index<Var> for Activity {
    type Output = f64;

    #[inline]
    fn index(&self, index: Var) -> &Self::Output {
        &self.activity[index]
    }
}

impl Activity {
    #[inline]
    pub fn reserve(&mut self, var: Var) {
        let is_new = self.activity.len() <= var.0 as usize;
        self.activity.reserve(var);
        self.bump_weights.reserve(var);
        if is_new {
            self.activity[var] = 1.0;
            self.bump_weights[var] = 1.0;
        }
        self.bucket_heap.reserve(var);
    }

    #[inline]
    fn check(&mut self, var: Var) {
        let act = unsafe { &mut *(self as *mut Activity) };
        if self.bucket_heap.pos[var].is_none() {
            self.bucket_heap.push(var, act);
            let b = self.bucket_table.len() - 1;
            let b = size_of_val(&b) as u32 * 8 - b.leading_zeros();
            *self.bucket_table.last_mut().unwrap() = b;
            self.bucket_table.push(b + 1);
        }
        assert!(self.bucket_heap.pos[var].is_some())
    }

    #[inline]
    fn bucket(&self, var: Var) -> u32 {
        match self.bucket_heap.pos[var] {
            OptionU32::NONE => self.bucket_table[self.bucket_table.len() - 1],
            b => self.bucket_table[*b],
        }
    }

    #[inline]
    pub fn bump(&mut self, var: Var) {
        self.activity[var] += self.act_inc * self.bump_weights[var];
        self.check(var);
        let act = unsafe { &mut *(self as *mut Activity) };
        self.bucket_heap.up(var, act);
        if self.activity[var] > 1e100 {
            self.activity.iter_mut().for_each(|a| a.mul_assign(1e-100));
            self.act_inc *= 1e-100;
        }
    }

    pub fn boost(&mut self, var: Var, factor: f64) {
        self.activity[var] *= factor;
        self.check(var);
        let act = unsafe { &mut *(self as *mut Activity) };
        self.bucket_heap.up(var, act);
    }

    pub fn set_bump_weight(&mut self, var: Var, weight: f64) {
        self.bump_weights.reserve(var);
        self.bump_weights[var] = weight;
    }

    pub fn set(&mut self, var: Var, value: f64) {
        self.activity[var] = value;
        self.check(var);
        let act = unsafe { &mut *(self as *mut Activity) };
        self.bucket_heap.up(var, act);
    }

    const DECAY: f64 = 0.95;

    #[inline]
    pub fn decay(&mut self) {
        self.act_inc *= 1.0 / Self::DECAY
    }

    #[allow(unused)]
    pub fn sort_by_activity(&self, cube: &mut LitVec, ascending: bool) {
        if ascending {
            cube.sort_by(|a, b| self.activity[*a].partial_cmp(&self.activity[*b]).unwrap());
        } else {
            cube.sort_by(|a, b| self.activity[*b].partial_cmp(&self.activity[*a]).unwrap());
        }
    }
}

impl Default for Activity {
    fn default() -> Self {
        let mut bucket_table = Gvec::new();
        bucket_table.push(0);
        Self {
            act_inc: 1.0,
            activity: Default::default(),
            bucket_heap: Default::default(),
            bucket_table,
            bump_weights: Default::default(),
        }
    }
}

#[derive(Clone)]
pub struct Vsids {
    pub activity: Activity,
    pub heap: BinaryHeap,
    pub bucket: Bucket,
    pub enable_bucket: bool,
    pub hint_scores: VarMap<f64>,
}

impl Vsids {
    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.heap.reserve(var);
        self.activity.reserve(var);
        self.bucket.reserve(var);
    }

    #[inline]
    pub fn push(&mut self, var: Var) {
        if self.enable_bucket {
            return self.bucket.push(var, &self.activity);
        }
        self.heap.push(var, &self.activity)
    }

    #[inline]
    pub fn pop(&mut self) -> Option<Var> {
        if self.enable_bucket {
            return self.bucket.pop(&self.hint_scores);
        }
        self.heap.pop(&self.activity)
    }

    #[inline]
    pub fn bump(&mut self, var: Var) {
        self.activity.bump(var);
        if !self.enable_bucket {
            self.heap.up(var, &self.activity);
        }
        self.bucket
            .buckets
            .reserve(self.activity.bucket_table[self.activity.bucket_table.len() - 1] as usize + 1);
    }

    #[inline]
    pub fn decay(&mut self) {
        self.activity.decay();
    }

    /// Boost activity for a variable and ensure bucket array is properly sized.
    /// Used by StructHint to give control variables a head start.
    pub fn boost(&mut self, var: Var, factor: f64) {
        self.activity.boost(var, factor);
        self.bucket
            .buckets
            .reserve(self.activity.bucket_table[self.activity.bucket_table.len() - 1] as usize + 1);
    }

    /// Set persistent bump weight for a variable (used during every conflict).
    pub fn set_bump_weight(&mut self, var: Var, weight: f64) {
        self.activity.set_bump_weight(var, weight);
    }

    /// Directly set initial activity for a variable.
    pub fn set_activity(&mut self, var: Var, value: f64) {
        self.activity.set(var, value);
        self.bucket
            .buckets
            .reserve(self.activity.bucket_table[self.activity.bucket_table.len() - 1] as usize + 1);
    }
}

impl Default for Vsids {
    fn default() -> Self {
        Self {
            activity: Default::default(),
            heap: Default::default(),
            bucket: Bucket::new(),
            enable_bucket: true,
            hint_scores: Default::default(),
        }
    }
}

#[derive(Clone)]
pub struct Bucket {
    buckets: Gvec<Gvec<Var>>,
    in_bucket: VarMap<bool>,
    head: u32,
}

impl Bucket {
    #[inline]
    pub fn new() -> Self {
        let mut buckets: Gvec<_> = Gvec::new();
        buckets.reserve(10);
        Self {
            buckets,
            in_bucket: Default::default(),
            head: Default::default(),
        }
    }

    #[inline]
    pub fn reserve(&mut self, var: Var) {
        self.in_bucket.reserve(var);
    }

    #[inline]
    pub fn push(&mut self, var: Var, activity: &Activity) {
        if self.in_bucket[var] {
            return;
        }
        let bucket = activity.bucket(var);
        if self.head > bucket {
            self.head = bucket;
        }
        self.buckets[bucket].push(var);
        self.in_bucket[var] = true;
    }

    #[inline]
    pub fn pop(&mut self, hint_scores: &VarMap<f64>) -> Option<Var> {
        while self.head < self.buckets.len() as u32 {
            if !self.buckets[self.head].is_empty() {
                if hint_scores.len() == 0 {
                    // No hints: plain LIFO
                    let var = self.buckets[self.head].pop().unwrap();
                    self.in_bucket[var] = false;
                    return Some(var);
                }
                // Hint tiebreak: find variable with highest score in this bucket
                let bucket = &mut self.buckets[self.head];
                let blen = bucket.len();
                let mut best_idx: usize = blen - 1; // default: last (LIFO)
                let mut best_score = -1.0f64;
                for i in 0..blen {
                    let v = bucket[i as u32];
                    let score = if (v.0 as usize) < hint_scores.len() {
                        hint_scores[v]
                    } else {
                        0.0
                    };
                    if score > best_score {
                        best_score = score;
                        best_idx = i;
                    }
                }
                // Swap best to last position, then pop
                let last = blen - 1;
                if best_idx != last {
                    let tmp = bucket[best_idx as u32];
                    bucket[best_idx as u32] = bucket[last as u32];
                    bucket[last as u32] = tmp;
                }
                let var = bucket.pop().unwrap();
                self.in_bucket[var] = false;
                return Some(var);
            }
            self.head += 1;
        }
        None
    }

    #[inline]
    pub fn clear(&mut self) {
        while self.head < self.buckets.len() as u32 {
            while let Some(var) = self.buckets[self.head].pop() {
                self.in_bucket[var] = false;
            }
            self.head += 1;
        }
        for b in self.buckets.iter_mut() {
            b.clear();
        }
        self.head = 0;
    }
}

impl DagCnfSolver {
    #[inline]
    pub fn decide(&mut self) -> bool {
        // Try VMTF queue if enabled
        if self.vmtf.is_enabled() {
            for i in 0..self.vmtf.queue.len() {
                let var = self.vmtf.queue[i];
                if self.value.v(var.lit()).is_none() && self.domain_has(var) {
                    self.total_decisions += 1;
                    if var.0 < self.hinted_vars.len() as u32 && self.hinted_vars[var] {
                        self.boost_decisions += 1;
                    }
                    let decide = if !self.cfg.phase_saving || self.phase_saving[var].is_none() {
                        Lit::new(var, self.rng.random_bool(0.5))
                    } else {
                        Lit::new(var, self.phase_saving[var] != Lbool::FALSE)
                    };
                    self.pos_in_trail.push(self.trail.len() as u32);
                    self.assign(decide, CREF_NONE);
                    return true;
                }
            }
            return false;
        }
        // Original VSIDS decide
        while let Some(decide) = self.vsids.pop() {
            if self.value.v(decide.lit()).is_none() {
                self.total_decisions += 1;
                if decide.0 < self.hinted_vars.len() as u32 && self.hinted_vars[decide] {
                    self.boost_decisions += 1;
                }
                let decide = if !self.cfg.phase_saving || self.phase_saving[decide].is_none() {
                    Lit::new(decide, self.rng.random_bool(0.5))
                } else {
                    Lit::new(decide, self.phase_saving[decide] != Lbool::FALSE)
                };
                self.pos_in_trail.push(self.trail.len() as u32);
                self.assign(decide, CREF_NONE);
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn activity_initializes_to_one() {
        let mut activity = Activity::default();
        let v0 = Var::new(0);
        let v1 = Var::new(1);
        activity.reserve(v0);
        activity.reserve(v1);
        assert_eq!(activity[v0], 1.0);
        assert_eq!(activity[v1], 1.0);
    }

    #[test]
    fn boost_multiplies_from_one() {
        let mut activity = Activity::default();
        let v0 = Var::new(0);
        let v1 = Var::new(1);
        activity.reserve(v0);
        activity.reserve(v1);
        activity.boost(v0, 2.0);
        assert_eq!(activity[v0], 2.0);
        assert_eq!(activity[v1], 1.0);
    }

    #[test]
    fn boost_changes_decision_order() {
        let mut vsids = Vsids::default();
        let control = Var::new(0);
        let datapath = Var::new(1);
        vsids.reserve(control);
        vsids.reserve(datapath);

        // Boost control variable
        vsids.boost(control, 2.0);

        // Push both into decision queue
        vsids.push(control);
        vsids.push(datapath);

        // Control should be decided first (higher activity)
        let first = vsids.pop().unwrap();
        assert_eq!(first, control, "boosted control var should be decided first");
    }

    #[test]
    fn reserve_does_not_reset_bumped_activity() {
        let mut activity = Activity::default();
        let v0 = Var::new(0);
        activity.reserve(v0);
        activity.bump(v0); // activity = 1.0 + 1.0 = 2.0
        activity.reserve(v0); // should NOT reset to 1.0
        assert!(activity[v0] > 1.0, "reserve must not reset existing activity");
    }
}
