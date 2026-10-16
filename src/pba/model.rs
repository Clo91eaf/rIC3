//! JG's observed proof-node path completion and gate/state cut construction.
//! Evidence: 0x8b0c70, 0x8aa620, 0x8ac740, 0x8acb80 (JG 2021.03).
use crate::transys::{Transys, TransysIf};
use giputils::hash::{GHashMap, GHashSet};
use logicrs::{Lit, LitVec, Var};

pub(super) struct Abstraction {
    pub ts: Transys,
    /// Positive abstract node -> original node. Pulse helpers have no entry.
    pub projection: GHashMap<Var, Var>,
    pub selected: GHashSet<Var>,
    pub cut_gates: usize,
    pub cuts: usize,
}

/// Gate paths from proof seeds to roots; siblings remain cut. A variable
/// terminates this traversal, even when it denotes state with a successor.
pub(super) fn complete_selection(ts: &Transys, seed: &GHashSet<Var>) -> GHashSet<Var> {
    let mut selected = seed.clone();
    // Relational initializers are outside JG's {-1,0,+1} leaf initial values.
    // Keep their complete initial support so arbitrary BTOR2 init remains exact.
    let mut initial: Vec<_> = ts
        .latch
        .iter()
        .copied()
        .filter(|q| ts.init.get(q).is_some_and(|i| !i.var().is_constant()))
        .collect();
    let mut visited = GHashSet::new();
    while let Some(v) = initial.pop() {
        if !visited.insert(v) {
            continue;
        }
        selected.insert(v);
        initial.extend(ts.rel.dep(v));
        if let Some(i) = ts.init.get(&v) {
            initial.push(i.var());
        }
    }
    let mut roots: Vec<_> = ts
        .latch
        .iter()
        .filter(|q| selected.contains(q))
        .map(|q| ts.next[q].var())
        .collect();
    roots.extend(
        ts.bad
            .iter()
            .chain(ts.constraint.iter())
            .chain(ts.justice.iter())
            .map(|l| l.var()),
    );
    roots.extend(
        ts.latch
            .iter()
            .filter(|q| selected.contains(q))
            .filter_map(|q| ts.init.get(q))
            .map(|l| l.var()),
    );
    let mut reachable = GHashSet::new();
    while let Some(v) = roots.pop() {
        if reachable.insert(v) {
            roots.extend(ts.rel.dep(v));
        }
    }
    // DagCnf guarantees that every combinational dependency has a lower ID.
    for v in ts.rel.var_iter_woc() {
        if reachable.contains(&v) && ts.rel.dep(v).iter().any(|d| selected.contains(d)) {
            selected.insert(v);
        }
    }
    selected.insert(Var::CONST);
    selected
}

/// Sound three-valued evaluation of initial gate values. A clause whose other
/// literals are false forces its output; unknown leaves stay unknown.
fn initial_values(ts: &Transys) -> Vec<Option<bool>> {
    let mut values = vec![None; usize::from(ts.max_var()) + 1];
    values[0] = Some(false);
    for (&q, &i) in ts.init.iter() {
        values[usize::from(q)] = i.try_constant();
    }
    loop {
        for v in ts.rel.var_iter_woc() {
            if values[usize::from(v)].is_some() {
                continue;
            }
            for c in &ts.rel[v] {
                if c.iter()
                    .filter(|l| l.var() != v)
                    .all(|l| values[usize::from(l.var())].is_some_and(|b| b != l.polarity()))
                {
                    values[usize::from(v)] = c.iter().find(|l| l.var() == v).map(|l| l.polarity());
                    break;
                }
            }
        }
        let mut changed = false;
        for (&q, &i) in ts.init.iter() {
            if values[usize::from(q)].is_none()
                && let Some(b) = values[usize::from(i.var())]
            {
                values[usize::from(q)] = Some(b == i.polarity());
                changed = true;
            }
        }
        if !changed {
            return values;
        }
    }
}

struct Builder<'a> {
    source: &'a Transys,
    selected: GHashSet<Var>,
    result: Transys,
    forward: GHashMap<Var, Var>,
    projection: GHashMap<Var, Var>,
    cuts: Vec<(Var, Var)>,
}

impl Builder<'_> {
    fn rewrite(&mut self, root: Lit) -> Lit {
        let mut pending = vec![(root.var(), false)];
        while let Some((v, expanded)) = pending.pop() {
            if self.forward.contains_key(&v) {
                continue;
            }
            if !self.selected.contains(&v) {
                let cut = self.result.new_var();
                self.result.input.push(cut);
                self.cuts.push((cut, v));
                self.forward.insert(v, cut);
                self.projection.insert(cut, v);
            } else if !self.source.rel[v].is_empty() {
                if !expanded {
                    pending.push((v, true));
                    pending.extend(self.source.rel.dep(v).iter().map(|d| (*d, false)));
                    continue;
                }
                let mapped = self.result.new_var();
                let clauses: Vec<LitVec> = self.source.rel[v]
                    .iter()
                    .map(|c| {
                        c.iter()
                            .map(|l| l.map_var(|q| if q == v { mapped } else { self.forward[&q] }))
                            .collect()
                    })
                    .collect();
                self.result.rel.add_rel(mapped, &clauses);
                self.forward.insert(v, mapped);
                self.projection.insert(mapped, v);
            } else {
                // Retained primary inputs/state were installed before traversal.
                assert!(
                    v.is_constant() || self.forward.contains_key(&v),
                    "unclassified model leaf"
                );
            }
        }
        root.map_var(|v| self.forward[&v])
    }
}

pub(super) fn build(ts: &Transys, selected: GHashSet<Var>) -> Abstraction {
    let mut b = Builder {
        source: ts,
        selected,
        result: Transys::new(),
        forward: GHashMap::new(),
        projection: GHashMap::new(),
        cuts: Vec::new(),
    };
    b.result.new_var_to(ts.max_var());
    b.forward.insert(Var::CONST, Var::CONST);
    for &v in ts.input.iter().chain(ts.latch.iter()) {
        if b.selected.contains(&v) {
            b.forward.insert(v, v);
            if ts.is_latch(v) {
                b.result.latch.push(v);
            } else {
                b.result.input.push(v);
            }
        }
    }
    for &q in &ts.latch {
        if b.selected.contains(&q) {
            let next = b.rewrite(ts.next[&q]);
            b.result.next.insert(q, next);
            if let Some(&i) = ts.init.get(&q) {
                let init = b.rewrite(i);
                b.result.init.insert(q, init);
            }
        }
    }
    for &root in &ts.bad {
        let mapped = b.rewrite(root);
        b.result.bad.push(mapped);
    }
    for &root in &ts.constraint {
        let mapped = b.rewrite(root);
        b.result.constraint.push(mapped);
    }
    for &root in &ts.justice {
        let mapped = b.rewrite(root);
        b.result.justice.push(mapped);
    }
    let initial = initial_values(ts);
    let known: Vec<_> = b
        .cuts
        .iter()
        .filter_map(|&(cut, v)| initial[usize::from(v)].map(|value| (cut, value)))
        .collect();
    if !known.is_empty() {
        let pulse = b.result.add_init_var().lit();
        for (cut, value) in known {
            let guard = b.result.rel.new_imply(pulse, cut.lit().not_if(!value));
            b.result.constraint.push(guard);
        }
    }
    Abstraction {
        cut_gates: b
            .cuts
            .iter()
            .filter(|(_, v)| !ts.rel[*v].is_empty())
            .count(),
        cuts: b.cuts.len(),
        ts: b.result,
        projection: b.projection,
        selected: b.selected,
    }
}
