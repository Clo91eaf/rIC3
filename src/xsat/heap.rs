use logicrs::Var;

/// Activity-indexed binary heap (max-heap by activity).
/// Corresponds to X-SAT `Heap<GreaterActivity>` (libs/heap.h)
///
/// Stores variable indices, ordered by external activity values.
/// Supports insert, pop, update, erase, and in-heap queries.
pub struct ActHeap {
    heap: Vec<Var>,
    pos: Vec<i32>,
}

impl ActHeap {
    pub fn new() -> Self {
        Self {
            heap: Vec::new(),
            pos: Vec::new(),
        }
    }

    pub fn with_capacity(n: usize) -> Self {
        Self {
            heap: Vec::with_capacity(n),
            pos: vec![-1; n],
        }
    }

    pub fn reserve(&mut self, n: usize) {
        if self.pos.len() < n {
            self.pos.resize(n, -1);
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len()
    }

    #[inline]
    pub fn in_heap(&self, var: Var) -> bool {
        let idx = *var as usize;
        idx < self.pos.len() && self.pos[idx] >= 0
    }

    #[inline]
    pub fn top(&self) -> Option<Var> {
        self.heap.first().copied()
    }

    fn up(&mut self, activity: &[f64], mut idx: usize) {
        let v = self.heap[idx];
        while idx > 0 {
            let pidx = (idx - 1) >> 1;
            if activity[*self.heap[pidx] as usize] >= activity[*v as usize] {
                break;
            }
            self.heap[idx] = self.heap[pidx];
            self.pos[*self.heap[idx] as usize] = idx as i32;
            idx = pidx;
        }
        self.heap[idx] = v;
        self.pos[*v as usize] = idx as i32;
    }

    fn down(&mut self, activity: &[f64], mut idx: usize) {
        let v = self.heap[idx];
        loop {
            let left = (idx << 1) + 1;
            if left >= self.heap.len() {
                break;
            }
            let right = left + 1;
            let child = if right < self.heap.len()
                && activity[*self.heap[right] as usize] > activity[*self.heap[left] as usize]
            {
                right
            } else {
                left
            };
            if activity[*v as usize] >= activity[*self.heap[child] as usize] {
                break;
            }
            self.heap[idx] = self.heap[child];
            self.pos[*self.heap[idx] as usize] = idx as i32;
            idx = child;
        }
        self.heap[idx] = v;
        self.pos[*v as usize] = idx as i32;
    }

    pub fn insert(&mut self, var: Var, activity: &[f64]) {
        let idx = *var as usize;
        if idx >= self.pos.len() {
            self.pos.resize(idx + 1, -1);
        }
        if self.pos[idx] >= 0 {
            return;
        }
        self.pos[idx] = self.heap.len() as i32;
        self.heap.push(var);
        self.up(activity, self.heap.len() - 1);
    }

    pub fn pop(&mut self, activity: &[f64]) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let v = self.heap[0];
        let last = *self.heap.last().unwrap();
        self.heap[0] = last;
        self.pos[*last as usize] = 0;
        self.pos[*v as usize] = -1;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.down(activity, 0);
        }
        Some(v)
    }

    pub fn update(&mut self, var: Var, activity: &[f64]) {
        let idx = self.pos[*var as usize];
        if idx < 0 {
            return;
        }
        self.up(activity, idx as usize);
    }

    pub fn erase(&mut self, var: Var, activity: &[f64]) {
        let p = self.pos[*var as usize];
        if p < 0 {
            return;
        }
        let o = *self.heap.last().unwrap();
        if *var == *o as u32 {
            self.pos[*var as usize] = -1;
            self.heap.pop();
            return;
        }
        self.heap[p as usize] = o;
        self.pos[*o as usize] = p;
        self.pos[*var as usize] = -1;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.up(activity, p as usize);
            self.down(activity, p as usize);
        }
    }

    pub fn clear(&mut self) {
        for &v in &self.heap {
            self.pos[*v as usize] = -1;
        }
        self.heap.clear();
    }
}

impl Default for ActHeap {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_heap_basic() {
        let mut heap = ActHeap::new();
        let activity = [0.0, 3.0, 1.0, 5.0, 2.0];

        heap.insert(Var(1), &activity);
        heap.insert(Var(2), &activity);
        heap.insert(Var(3), &activity);
        heap.insert(Var(4), &activity);

        assert_eq!(heap.pop(&activity), Some(Var(3))); // activity 5.0
        assert_eq!(heap.pop(&activity), Some(Var(1))); // activity 3.0
        assert_eq!(heap.pop(&activity), Some(Var(4))); // activity 2.0
        assert_eq!(heap.pop(&activity), Some(Var(2))); // activity 1.0
        assert_eq!(heap.pop(&activity), None);
    }

    #[test]
    fn test_heap_update() {
        let mut heap = ActHeap::new();
        let mut activity = [0.0, 1.0, 5.0, 3.0];

        heap.insert(Var(1), &activity);
        heap.insert(Var(2), &activity);
        heap.insert(Var(3), &activity);

        activity[1] = 10.0;
        heap.update(Var(1), &activity);

        assert_eq!(heap.pop(&activity), Some(Var(1)));
    }

    #[test]
    fn test_heap_erase() {
        let mut heap = ActHeap::new();
        let activity = [0.0, 1.0, 5.0, 3.0];

        heap.insert(Var(1), &activity);
        heap.insert(Var(2), &activity);
        heap.insert(Var(3), &activity);

        heap.erase(Var(2), &activity);
        assert!(!heap.in_heap(Var(2)));

        assert_eq!(heap.pop(&activity), Some(Var(3)));
        assert_eq!(heap.pop(&activity), Some(Var(1)));
    }

    #[test]
    fn test_heap_duplicate_insert() {
        let mut heap = ActHeap::new();
        let activity = [0.0, 5.0];
        heap.insert(Var(1), &activity);
        heap.insert(Var(1), &activity);
        assert_eq!(heap.len(), 1);
    }
}
