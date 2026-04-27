use logicrs::Lit;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct CRef(u32);

pub const CREF_NONE: CRef = CRef(u32::MAX);

impl CRef {
    #[inline]
    pub fn idx(self) -> usize {
        self.0 as usize
    }
}

impl From<usize> for CRef {
    #[inline]
    fn from(value: usize) -> Self {
        Self(value as _)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct VRef(u32);

pub const VREF_NONE: VRef = VRef(u32::MAX);

impl VRef {
    #[inline]
    pub fn idx(self) -> usize {
        self.0 as usize
    }
}

impl From<usize> for VRef {
    #[inline]
    fn from(value: usize) -> Self {
        Self(value as _)
    }
}

/// A single clause in the SAT solver.
///
/// X-SAT C++ uses a flexible array member (`int data[]`) at the end of Clause,
/// stored inside a flat `int* memory` buffer. Rust can just use a Vec<Lit>.
///
/// Field correspondence with X-SAT `Clause` (clause.hpp:9-41):
///   lbd        → Clause::lbd        — Literal Block Distance, learned clause quality metric
///   activity   → Clause::activity   — clause activity for reduction decisions
///   is_deleted → Clause::is_deleted — soft-delete marker
///   is_learn   → Clause::learn      — whether this is a conflict-learned clause
///   vref       → Clause::vref       — LUT gate mapping during preprocessing (Phase 7)
///   data       → Clause::data[]     — the literal array
#[derive(Clone)]
pub struct Clause {
    pub lbd: u32,
    pub activity: f64,
    pub is_deleted: bool,
    pub is_learn: bool,
    pub vref: VRef,
    pub data: Vec<Lit>,
}

impl Clause {
    pub fn new(size: usize, learn: bool) -> Self {
        Self {
            lbd: 0,
            activity: 0.0,
            is_deleted: false,
            is_learn: learn,
            vref: VREF_NONE,
            data: vec![Lit::new(logicrs::Var::CONST, true); size],
        }
    }

    /// Find a literal and swap it to position 0.
    /// X-SAT: `Clause::find_lit_swap_first` (clause.hpp:19-27)
    ///
    /// Used during watched literal propagation: when a watched literal becomes
    /// false, find a replacement and swap it to the watch position.
    pub fn find_lit_swap_first(&mut self, lit: Lit) -> bool {
        for i in 0..self.data.len() {
            if self.data[i] == lit {
                self.data.swap(0, i);
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use logicrs::Var;

    #[test]
    fn test_clause_new() {
        let cls = Clause::new(3, false);
        assert_eq!(cls.data.len(), 3);
        assert!(!cls.is_learn);
        assert!(!cls.is_deleted);
        assert_eq!(cls.lbd, 0);
        assert_eq!(cls.vref, VREF_NONE);
    }

    #[test]
    fn test_clause_learned() {
        let cls = Clause::new(2, true);
        assert!(cls.is_learn);
    }

    #[test]
    fn test_find_lit_swap_first() {
        let mut cls = Clause::new(3, false);
        cls.data[0] = Var(0).lit();
        cls.data[1] = Var(1).lit();
        cls.data[2] = !Var(2).lit();

        let target = !Var(2).lit();
        assert!(cls.find_lit_swap_first(target));
        assert_eq!(cls.data[0], target);
        assert_eq!(cls.data[1], Var(1).lit());
        assert_eq!(cls.data[2], Var(0).lit());

        assert!(!cls.find_lit_swap_first(Var(5).lit()));
    }

    #[test]
    fn test_clause_fields() {
        let mut cls = Clause::new(2, true);
        cls.activity = 3.14159;
        assert!((cls.activity - 3.14159).abs() < 1e-10);

        cls.lbd = 42;
        assert_eq!(cls.lbd, 42);

        cls.vref = VRef::from(12345);
        assert_eq!(cls.vref, VRef::from(12345));
    }

    #[test]
    fn test_cref() {
        let cr = CRef::from(42);
        assert_eq!(cr.idx(), 42);
        assert_ne!(cr, CREF_NONE);
    }

    #[test]
    fn test_vref() {
        let vr = VRef::from(100);
        assert_eq!(vr.idx(), 100);
        assert_ne!(vr, VREF_NONE);
    }
}
