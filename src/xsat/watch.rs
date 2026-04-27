use logicrs::{Lit, Var};

use super::clause::{CRef, Clause};

/// Watcher for general clauses (size >= 4).
/// Corresponds to X-SAT `Watcher` struct (solver.h:138-141)
///
///   cref    — reference to the watched clause
///   blocker — the other watched literal, used as a quick satisfiability check
///             If blocker is already true, skip the clause entirely.
#[derive(Clone, Copy)]
pub struct Watcher {
    pub cref: CRef,
    pub blocker: Lit,
}

/// Three-layer watched literal data structures.
/// Corresponds to X-SAT's `watches_bin`, `watches_tri`, `watches` (solver.h:147-149)
///
/// Each layer is indexed by literal (Lit encoded as u32).
/// A watch is registered on `~lit`: "when lit becomes false, notify me".
///
/// Layer 1 — Binary clauses (size 2): store the partner literal directly.
///   No CRef needed because binary clause propagation doesn't need the clause body.
///   X-SAT: `vec<int> *watches_bin` (solver.h:148)
///
/// Layer 2 — Ternary clauses (size 3): store CRef only.
///   The two watched literals are always at positions [0] and [1] in the clause.
///   X-SAT: `vec<int> *watches_tri` (solver.h:149)
///
/// Layer 3 — General clauses (size >= 4): store Watcher {cref, blocker}.
///   Blocker is a cheap satisfiability check before touching the clause data.
///   X-SAT: `vec<Watcher> *watches` (solver.h:147)
pub struct Watches {
    bin: Vec<Vec<Lit>>,
    tri: Vec<Vec<CRef>>,
    general: Vec<Vec<Watcher>>,
}

impl Watches {
    pub fn new(num_lits: usize) -> Self {
        Self {
            bin: vec![Vec::new(); num_lits],
            tri: vec![Vec::new(); num_lits],
            general: vec![Vec::new(); num_lits],
        }
    }

    pub fn ensure_size(&mut self, num_lits: usize) {
        if num_lits > self.bin.len() {
            self.bin.resize(num_lits, Vec::new());
            self.tri.resize(num_lits, Vec::new());
            self.general.resize(num_lits, Vec::new());
        }
    }

    // --- Binary watch ---

    /// Register a binary clause `(a, b)`.
    /// Watch `~a → b` and `~b → a`.
    /// X-SAT: watch.cpp:16-17
    pub fn add_bin(&mut self, a: Lit, b: Lit) {
        self.bin[u32::from(!a) as usize].push(b);
        self.bin[u32::from(!b) as usize].push(a);
    }

    #[inline]
    pub fn bin(&self, lit: Lit) -> &[Lit] {
        &self.bin[u32::from(lit) as usize]
    }

    // --- Ternary watch ---

    /// Register a ternary clause, watched on `~a` and `~b`.
    /// X-SAT: watch.cpp:19-20
    pub fn add_tri(&mut self, a: Lit, b: Lit, cref: CRef) {
        self.tri[u32::from(!a) as usize].push(cref);
        self.tri[u32::from(!b) as usize].push(cref);
    }

    #[inline]
    pub fn tri_mut(&mut self, lit: Lit) -> &mut Vec<CRef> {
        &mut self.tri[u32::from(lit) as usize]
    }

    // --- General watch ---

    /// Register a general clause, watched on `~a` (blocker = b) and `~b` (blocker = a).
    /// X-SAT: watch.cpp:22-24
    pub fn add_gen(&mut self, a: Lit, b: Lit, cref: CRef) {
        self.general[u32::from(!a) as usize].push(Watcher { cref, blocker: b });
        self.general[u32::from(!b) as usize].push(Watcher { cref, blocker: a });
    }

    #[inline]
    pub fn general(&self, lit: Lit) -> &[Watcher] {
        &self.general[u32::from(lit) as usize]
    }

    #[inline]
    pub fn general_mut(&mut self, lit: Lit) -> &mut Vec<Watcher> {
        &mut self.general[u32::from(lit) as usize]
    }

    /// Register watches for a newly learned clause.
    /// X-SAT: solver.cpp:174-180 (add_learning_clause)
    pub fn add_learned(&mut self, clauses: &[Clause], cref: CRef) {
        let cls = &clauses[cref.idx()];
        if cls.data.len() == 3 {
            self.add_tri(cls.data[0], cls.data[1], cref);
        } else {
            self.add_gen(cls.data[0], cls.data[1], cref);
        }
    }
}

/// Build watches from circuit gate clauses.
/// Corresponds to X-SAT `CSat::build_watches()` (watch.cpp:6-27)
///
/// For each gate's CNF clauses, register watches based on clause size:
///   size 2 → binary watch (watches_bin)
///   size 3 → ternary watch (watches_tri)
///   size 4+ → general watch (watches)
pub fn build_watches(
    watches: &mut Watches,
    clauses: &[Clause],
    vars: &super::gate::GateVarMap<super::gate::GateVar>,
    num_vars: usize,
) {
    let num_lits = (num_vars + 1) * 2;
    watches.ensure_size(num_lits);

    for v in 1..=num_vars {
        let var = Var(v as u32);
        let gv = &vars[var];
        for &cref in &gv.clauses {
            let cls = &clauses[cref.idx()];
            match cls.data.len() {
                2 => {
                    watches.add_bin(cls.data[0], cls.data[1]);
                }
                3 => {
                    watches.add_tri(cls.data[0], cls.data[1], cref);
                }
                _ => {
                    watches.add_gen(cls.data[0], cls.data[1], cref);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use logicrs::Var;

    #[test]
    fn test_watches_bin() {
        let mut w = Watches::new(20);
        let a = Var(1).lit();
        let b = !Var(2).lit();
        w.add_bin(a, b);

        assert_eq!(w.bin(!a), &[b]);
        assert_eq!(w.bin(!b), &[a]);
    }

    #[test]
    fn test_watches_tri() {
        let mut w = Watches::new(20);
        let a = Var(1).lit();
        let b = Var(2).lit();
        let cref = CRef::from(5);
        w.add_tri(a, b, cref);

        assert_eq!(w.tri_mut(!a), &vec![cref]);
        assert_eq!(w.tri_mut(!b), &vec![cref]);
    }

    #[test]
    fn test_watches_gen() {
        let mut w = Watches::new(20);
        let a = Var(1).lit();
        let b = Var(2).lit();
        let cref = CRef::from(3);
        w.add_gen(a, b, cref);

        let ws = w.general(!a);
        assert_eq!(ws.len(), 1);
        assert_eq!(ws[0].cref, cref);
        assert_eq!(ws[0].blocker, b);
    }

    #[test]
    fn test_ensure_size() {
        let mut w = Watches::new(4);
        w.ensure_size(100);
        assert!(w.bin.len() >= 100);
    }
}
