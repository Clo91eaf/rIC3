//! Demand-driven shared node/context encoding, including single-use AND
//! expansion. Observed JG functions: 0x91fdf0/0x91de70 and 0x8aa8c0.
use crate::transys::{Transys, TransysIf, certify::BlCex};
use cadical::CaDiCaL;
use logicrs::{Lit, LitVec, LitVvec, Var, satif::Satif};

pub(super) struct Encoding<'a> {
    pub ts: &'a Transys,
    pub solver: CaDiCaL,
    pub origins: Vec<Option<Var>>,
    frames: Vec<Vec<Option<Lit>>>,
    ands: Vec<Option<(bool, Vec<Lit>)>>,
    refs: Vec<usize>,
    clauses: usize,
}

impl<'a> Encoding<'a> {
    pub fn new(ts: &'a Transys, solver: CaDiCaL) -> Self {
        let n = usize::from(ts.max_var()) + 1;
        let mut refs = vec![0; n];
        let mut pending: Vec<_> = ts
            .next
            .values()
            .copied()
            .chain(ts.bad.iter().copied())
            .chain(ts.constraint.iter().copied())
            .chain(ts.init.values().copied())
            .collect();
        while let Some(l) = pending.pop() {
            let v = l.var();
            refs[usize::from(v)] += 1;
            if refs[usize::from(v)] == 1 {
                pending.extend(ts.rel.dep(v).iter().map(|v| v.lit()));
            }
        }
        let ands = ts
            .rel
            .var_iter()
            .map(|v| {
                let c = &ts.rel[v];
                for polarity in [true, false] {
                    let out = v.lit().not_if(!polarity);
                    let mut inputs = Vec::new();
                    let mut main = None;
                    let mut valid = true;
                    for clause in c {
                        if clause.contains(&!out) && clause.len() == 2 {
                            inputs.push(*clause.iter().find(|l| **l != !out).unwrap());
                        } else if clause.contains(&out) && main.is_none() {
                            main = Some(clause);
                        } else {
                            valid = false;
                            break;
                        }
                    }
                    if valid
                        && !inputs.is_empty()
                        && main.is_some_and(|m| {
                            m.len() as usize == inputs.len() + 1
                                && inputs.iter().all(|l| m.contains(&!*l))
                        })
                    {
                        return Some((polarity, inputs));
                    }
                }
                None
            })
            .collect();
        let mut this = Self {
            ts,
            solver,
            origins: vec![],
            frames: vec![],
            ands,
            refs,
            clauses: 0,
        };
        let constant = this.allocate(None);
        assert_eq!(constant, Lit::FALSE);
        this.clause(&[!constant]);
        this
    }

    pub fn clause(&mut self, clause: &[Lit]) {
        self.clauses += 1;
        self.solver.add_clause(clause);
    }

    pub fn resources_ok(&self) -> bool {
        self.origins.len() <= super::MAX_UNROLL_VARS && self.clauses <= super::MAX_UNROLL_CLAUSES
    }

    fn allocate(&mut self, origin: Option<Var>) -> Lit {
        let v = Var::new(self.origins.len());
        if self.origins.len().is_multiple_of(4096) {
            self.solver.reserve(Var::new(self.origins.len() + 4095));
        }
        self.origins.push(origin);
        v.lit()
    }

    fn fanins(&self, v: Var) -> Vec<Lit> {
        let Some((_, inputs)) = &self.ands[usize::from(v)] else {
            return self.ts.rel.dep(v).iter().map(|v| v.lit()).collect();
        };
        let mut pending = inputs.clone();
        let mut result = Vec::new();
        while let Some(l) = pending.pop() {
            if self.refs[usize::from(l.var())] == 1
                && let Some((polarity, children)) = &self.ands[usize::from(l.var())]
                && *polarity == l.polarity()
            {
                pending.extend(children);
            } else {
                result.push(l);
            }
        }
        result
    }

    pub fn reference(&mut self, l: Lit, k: usize) -> Lit {
        while self.frames.len() <= k {
            let mut row = vec![None; usize::from(self.ts.max_var()) + 1];
            row[0] = Some(Lit::FALSE);
            self.frames.push(row);
        }
        let mut pending = vec![(l.var(), false)];
        while let Some((v, expanded)) = pending.pop() {
            if expanded {
                let z = self.frames[k][usize::from(v)].unwrap();
                if let Some((polarity, _)) = &self.ands[usize::from(v)] {
                    let inputs: Vec<_> = self
                        .fanins(v)
                        .iter()
                        .map(|a| {
                            self.frames[k][usize::from(a.var())]
                                .unwrap()
                                .not_if(!a.polarity())
                        })
                        .collect();
                    for c in LitVvec::cnf_and(z.not_if(!*polarity), &inputs) {
                        self.clause(&c);
                    }
                } else {
                    for c in &self.ts.rel[v] {
                        let mapped: Vec<_> = c
                            .iter()
                            .map(|a| {
                                self.frames[k][usize::from(a.var())]
                                    .unwrap()
                                    .not_if(!a.polarity())
                            })
                            .collect();
                        self.clause(&mapped);
                    }
                }
            } else if self.frames[k][usize::from(v)].is_none() {
                let z = self.allocate(Some(v));
                self.frames[k][usize::from(v)] = Some(z);
                if !self.ts.rel[v].is_empty() {
                    pending.push((v, true));
                    pending.extend(self.fanins(v).iter().map(|a| (a.var(), false)));
                }
            }
        }
        self.frames[k][usize::from(l.var())]
            .unwrap()
            .not_if(!l.polarity())
    }

    pub fn constraints(&mut self, k: usize) {
        for &c in &self.ts.constraint {
            let l = self.reference(c, k);
            self.clause(&[l]);
        }
    }

    pub fn transition(&mut self, k: usize) {
        for &q in &self.ts.latch {
            let a = self.reference(self.ts.next[&q], k);
            let b = self.reference(q.lit(), k + 1);
            self.clause(&[!a, b]);
            self.clause(&[a, !b]);
        }
    }

    pub fn initial(&mut self) {
        for (&q, &i) in self.ts.init.iter() {
            let a = self.reference(q.lit(), 0);
            let b = self.reference(i, 0);
            self.clause(&[!a, b]);
            self.clause(&[a, !b]);
        }
    }

    pub fn goal(&mut self, k: usize) -> LitVec {
        self.ts
            .bad
            .clone()
            .iter()
            .map(|b| self.reference(*b, k))
            .collect()
    }

    pub fn prefix(&mut self, depth: usize) -> bool {
        let mut goal = LitVec::new();
        for k in 0..=depth {
            goal.extend(self.goal(k));
            if !self.resources_ok() {
                return false;
            }
        }
        self.clause(&goal);
        self.constraints(depth);
        for k in (0..depth).rev() {
            self.transition(k);
            self.constraints(k);
            if !self.resources_ok() {
                return false;
            }
        }
        self.initial();
        self.resources_ok()
    }

    pub fn trace(&self, depth: usize) -> BlCex {
        let value = |v: Var, k: usize| {
            self.frames
                .get(k)
                .and_then(|f| f[usize::from(v)])
                .and_then(|l| self.solver.sat_value(l))
                .unwrap_or(false)
        };
        let mut trace = BlCex::default();
        for k in 0..=depth {
            trace.input.push(
                self.ts
                    .input
                    .iter()
                    .map(|v| v.lit().not_if(!value(*v, k)))
                    .collect(),
            );
            trace.state.push(
                self.ts
                    .latch
                    .iter()
                    .map(|v| v.lit().not_if(!value(*v, k)))
                    .collect(),
            );
            if let Some(bad) = self
                .ts
                .bad
                .iter()
                .position(|b| value(b.var(), k) == b.polarity())
            {
                trace.bad_id = bad;
                return trace;
            }
        }
        panic!("SAT query has no bad frame");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flattened_and_shared_logic_matches_its_truth_table() {
        let mut ts = Transys::new();
        let a = ts.new_var();
        let b = ts.new_var();
        let c = ts.new_var();
        for v in [a, b, c] {
            ts.add_input(v);
        }
        let inner = ts.rel.new_and([a.lit(), b.lit()]);
        let shared = ts.rel.new_and([b.lit(), c.lit()]);
        let branch = ts.rel.new_and([inner, shared]);
        let xor = ts.rel.new_xor(shared, a.lit());
        let root = ts.rel.new_or([branch, xor]);
        ts.bad.push(root);
        let mut e = Encoding::new(&ts, CaDiCaL::new());
        let output = e.reference(root, 0);
        assert!(!e.origins.contains(&Some(inner.var())));
        assert!(e.origins.contains(&Some(shared.var())));
        for bits in 0..8 {
            let values = [bits & 1 != 0, bits & 2 != 0, bits & 4 != 0];
            let expected =
                (values[0] && values[1] && values[2]) || ((values[1] && values[2]) ^ values[0]);
            let mut assumptions: Vec<_> = [a, b, c]
                .into_iter()
                .zip(values)
                .map(|(v, value)| e.reference(v.lit(), 0).not_if(!value))
                .collect();
            assumptions.push(output.not_if(!expected));
            assert!(e.solver.solve(&assumptions), "bits={bits}");
            *assumptions.last_mut().unwrap() = output.not_if(expected);
            assert!(!e.solver.solve(&assumptions), "bits={bits}");
        }
    }
}

#[cfg(test)]
mod resource_tests {
    use super::*;

    #[test]
    fn sparse_restore_ids_do_not_count_as_encoded_sat_variables() {
        let mut ts = Transys::new();
        let q = ts.new_var();
        ts.add_latch(q, Some(Lit::FALSE), q.lit());
        ts.bad.push(q.lit());
        ts.new_var_to(Var::new(100_000));
        let mut e = Encoding::new(&ts, CaDiCaL::new());
        assert!(e.prefix(32));
        assert!(e.origins.len() < 100);
        assert!(!e.solver.solve(&[]));
    }
}
