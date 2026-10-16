//! Use the same word-level simplification and Boolean lowering as BTOR input.
//! A fresh thread owns the temporary Term arena; only plain CNF and variable
//! mappings cross its boundary. Prior frontend terms cannot change numbering.
use super::model::Abstraction;
use crate::{
    transys::{Transys, TransysIf},
    wltransys::WlTransys,
};
use giputils::hash::GHashMap;
use log::{info, warn};
use logicrs::{
    Lit, Var,
    fol::{FolOp, Sort, Term},
};

// Word-level simplification and lowering recursively visit terms. Bound the
// expression we would build before creating any Terms, including the folds
// inside a single wide CNF definition. Keep deep models in their original CNF.
const MAX_EXPRESSION_DEPTH: usize = 1024;
const NORMALIZE_STACK_BYTES: usize = 16 * 1024 * 1024;

fn bounded_expression_depth(ts: &Transys) -> bool {
    let mut depth = vec![0usize; usize::from(ts.max_var()) + 1];
    for v in ts.rel.var_iter_woc() {
        if ts.rel[v].is_empty() {
            continue;
        }
        let mut output = 0;
        for clause in ts.rel[v].iter().filter(|c| c.contains(&v.lit())) {
            let mut product = 0;
            for lit in clause.iter().filter(|l| l.var() != v) {
                // Negation, then the left-associated conjunction fold.
                product = product.max(depth[usize::from(lit.var())] + 1) + 1;
                if product > MAX_EXPRESSION_DEPTH {
                    return false;
                }
            }
            output = output.max(product) + 1;
            if output > MAX_EXPRESSION_DEPTH {
                return false;
            }
        }
        // XOR/XNOR recognition can replace the positive-clause expression.
        let parity = ts
            .rel
            .dep(v)
            .iter()
            .map(|d| depth[usize::from(*d)] + 2)
            .max()
            .unwrap_or(0);
        depth[usize::from(v)] = output.max(parity);
        if depth[usize::from(v)] > MAX_EXPRESSION_DEPTH {
            return false;
        }
    }
    true
}

fn literal(map: &[Option<Term>], l: Lit) -> Term {
    map[usize::from(l.var())]
        .as_ref()
        .unwrap()
        .not_if(!l.polarity())
}

// Recognize n-ary AND/OR definitions, including complemented fanins. Large
// opaque relations must stay CNF: the positive-clause cofactor below is only
// a function when each fanin valuation allows exactly one output value.
fn conjunction(ts: &Transys, v: Var) -> Option<(bool, Vec<Lit>)> {
    for polarity in [true, false] {
        let out = v.lit().not_if(!polarity);
        let mut inputs = Vec::new();
        let mut main = None;
        let mut valid = true;
        for c in &ts.rel[v] {
            if c.len() == 2 && c.contains(&!out) {
                inputs.push(*c.iter().find(|l| **l != !out).unwrap());
            } else if c.contains(&out) && main.is_none() {
                main = Some(c);
            } else {
                valid = false;
                break;
            }
        }
        if valid
            && !inputs.is_empty()
            && main.is_some_and(|c| {
                c.len() as usize == inputs.len() + 1 && inputs.iter().all(|l| c.contains(&!*l))
            })
        {
            return Some((polarity, inputs));
        }
    }
    None
}

fn truth_table(ts: &Transys, v: Var) -> Option<u64> {
    let deps = ts.rel.dep(v);
    if deps.len() > 6
        || ts.rel[v]
            .iter()
            .any(|c| c.iter().filter(|l| l.var() == v).count() != 1)
    {
        return None;
    }
    let mut table = 0;
    for bits in 0..(1usize << deps.len()) {
        let mut unique = None;
        for out in [false, true] {
            let allowed = ts.rel[v].iter().all(|c| {
                c.iter().any(|l| {
                    let value = if l.var().is_constant() {
                        false
                    } else if l.var() == v {
                        out
                    } else {
                        bits & (1 << deps.iter().position(|d| *d == l.var()).unwrap()) != 0
                    };
                    value == l.polarity()
                })
            });
            if allowed {
                if unique.is_some() {
                    return None;
                }
                unique = Some(out);
            }
        }
        if unique? {
            table |= 1u64 << bits;
        }
    }
    Some(table)
}

fn rebuild(ts: &Transys, projection: &GHashMap<Var, Var>) -> Option<(Transys, GHashMap<Var, Var>)> {
    let mut map = vec![None; usize::from(ts.max_var()) + 1];
    map[0] = Some(Term::bool_const(false));
    let _one = Term::bool_const(true);
    let mut leaves = GHashMap::new();
    // Match a standalone BTOR export: state declarations, then inputs.
    for &v in ts.latch.iter().chain(ts.input.iter()) {
        let t = Term::new_var(Sort::bool());
        leaves.insert(t.clone(), v);
        map[usize::from(v)] = Some(t);
    }
    for v in ts.rel.var_iter_woc() {
        if ts.rel[v].is_empty() {
            continue;
        }
        let table = if conjunction(ts, v).is_some() {
            None
        } else {
            Some(truth_table(ts, v)?)
        };
        let deps = ts.rel.dep(v);
        let function = if deps.len() == 2 && table.is_some_and(|t| [6, 9].contains(&t)) {
            Term::new_op(
                if table == Some(6) {
                    FolOp::Xor
                } else {
                    FolOp::Xnor
                },
                deps.iter().map(|d| map[usize::from(*d)].as_ref().unwrap()),
            )
        } else {
            // Match the BTOR exporter exactly, including the left-associated
            // construction order of n-ary functions and positive OR outputs.
            Term::new_ors(ts.rel[v].iter().filter(|c| c.contains(&v.lit())).map(|c| {
                Term::new_ands(
                    c.iter()
                        .filter(|l| l.var() != v)
                        .map(|l| literal(&map, !*l)),
                )
            }))
        };
        map[usize::from(v)] = Some(function);
    }
    let mut wts = WlTransys {
        input: ts
            .input
            .iter()
            .map(|v| map[usize::from(*v)].as_ref().unwrap().clone())
            .collect(),
        ..Default::default()
    };
    for &q in &ts.latch {
        let init = ts.init.get(&q).map(|l| literal(&map, *l));
        let next = literal(&map, ts.next[&q]);
        wts.add_latch(map[usize::from(q)].as_ref().unwrap().clone(), init, next);
    }
    wts.bad = ts.bad.iter().map(|l| literal(&map, *l)).collect();
    let mut constraints: Vec<_> = ts.constraint.iter().copied().collect();
    if let Some(&pulse) = ts
        .latch
        .iter()
        .find(|q| ts.init.get(q) == Some(&Lit::TRUE) && ts.next[q] == Lit::FALSE)
    {
        constraints.sort_by_key(|l| !ts.rel.dep(l.var()).contains(&pulse));
    }
    wts.constraint = constraints.into_iter().map(|l| literal(&map, l)).collect();
    wts.justice = ts.justice.iter().map(|l| literal(&map, *l)).collect();
    wts.simplify(&mut vec![]);
    let (normalized, restore) = wts.bitblast_to_ts();
    let mut projected = GHashMap::new();
    projected.insert(Var::CONST, Var::CONST);
    for &v in normalized.input.iter().chain(normalized.latch.iter()) {
        let (term, bit) = restore.try_restore(v)?;
        if bit != 0 {
            return None;
        }
        let old = leaves.get(&term)?;
        if let Some(&source) = projection.get(old) {
            projected.insert(v, source);
        }
    }
    Some((normalized, projected))
}

pub(super) fn apply(abs: &mut Abstraction) -> bool {
    if !bounded_expression_depth(&abs.ts) {
        info!(
            "PBA frontend normalization skipped: expression depth exceeds {MAX_EXPRESSION_DEPTH}; retaining original CNF"
        );
        return false;
    }
    let result = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("pba-normalize".into())
            .stack_size(NORMALIZE_STACK_BYTES)
            .spawn_scoped(scope, || rebuild(&abs.ts, &abs.projection))
            .map(|worker| worker.join().unwrap())
    });
    let result = match result {
        Ok(result) => result,
        Err(error) => {
            warn!("PBA frontend normalization skipped: cannot start worker: {error}");
            return false;
        }
    };
    let Some((ts, projection)) = result else {
        info!("PBA frontend normalization skipped: opaque/nonfunctional CNF definition");
        return false;
    };
    info!("PBA frontend normalized model: {}", ts.statistic());
    abs.ts = ts;
    abs.projection = projection;
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{Frontend, btor::BtorFrontend};
    use logicrs::LitVvec;

    #[test]
    fn wide_gate_keeps_original_cnf_without_building_a_deep_term_fold() {
        let mut ts = Transys::new();
        let inputs: Vec<_> = (0..12_000)
            .map(|_| {
                let v = ts.new_var();
                ts.add_input(v);
                v.lit()
            })
            .collect();
        ts.bad.push(ts.rel.new_and(inputs));
        let before = serde_json::to_value(&ts).unwrap();
        let projection = ts
            .input
            .iter()
            .map(|v| (*v, *v))
            .chain([(Var::CONST, Var::CONST)])
            .collect();
        let mut abs = Abstraction {
            ts,
            projection,
            selected: Default::default(),
            cuts: 0,
            cut_gates: 0,
        };
        let projection = abs.projection.clone();
        assert!(!apply(&mut abs));
        assert_eq!(serde_json::to_value(&abs.ts).unwrap(), before);
        assert_eq!(abs.projection, projection);
    }

    #[test]
    fn leaves_have_explicit_projections_after_renumbering() {
        let mut ts = Transys::new();
        let input = ts.new_var();
        ts.add_input(input);
        let q = ts.new_var();
        ts.add_latch(q, Some(Lit::FALSE), input.lit());
        ts.constraint.push(!input.lit());
        ts.bad.push(q.lit());
        let mut abs = super::super::model::build(&ts, [Var::CONST, input, q].into_iter().collect());
        assert!(apply(&mut abs));
        assert!(
            abs.ts.input.is_empty(),
            "fixed input must be removed by word-level simplification"
        );
        assert_eq!(abs.projection[&Var::CONST], Var::CONST);
        assert_eq!(abs.projection[&abs.ts.latch[0]], q);
        assert_eq!(abs.ts.next[&abs.ts.latch[0]], Lit::FALSE);
    }

    #[test]
    fn nonfunctional_gate_is_preserved_without_normalization() {
        let mut ts = Transys::new();
        let a = ts.new_var();
        ts.add_input(a);
        let g = ts.new_var();
        ts.rel.add_rel(
            g,
            &LitVvec::from(vec![logicrs::LitVec::from([!a.lit(), g.lit()])]),
        );
        ts.bad.push(g.lit());
        let before = serde_json::to_value(&ts).unwrap();
        let mut abs = Abstraction {
            ts,
            projection: [(Var::CONST, Var::CONST), (a, a)].into_iter().collect(),
            selected: Default::default(),
            cuts: 0,
            cut_gates: 0,
        };
        assert!(!apply(&mut abs));
        assert_eq!(serde_json::to_value(&abs.ts).unwrap(), before);
    }

    #[test]
    #[ignore = "requires a paired PBA JSON model and its one-bit BTOR export"]
    fn matches_standalone_btor_frontend_exactly() {
        let path = std::env::var("RIC3_PBA_NORMALIZE_MODEL").unwrap();
        let btor = std::env::var("RIC3_PBA_NORMALIZE_BTOR").unwrap();
        let ts: Transys = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let projection = ts
            .input
            .iter()
            .chain(ts.latch.iter())
            .map(|v| (*v, *v))
            .chain([(Var::CONST, Var::CONST)])
            .collect();
        let mut abs = Abstraction {
            ts,
            projection,
            selected: Default::default(),
            cuts: 0,
            cut_gates: 0,
        };
        // Unrelated terms in the caller must not influence the fresh arena.
        let _noise: Vec<_> = (0..1000).map(|_| Term::new_var(Sort::bool())).collect();
        assert!(apply(&mut abs));
        let expected =
            std::thread::spawn(move || BtorFrontend::new(btor::Btor::from_file(btor)).ts().0)
                .join()
                .unwrap();
        assert_eq!(abs.ts.statistic(), expected.statistic());
        assert_eq!(
            serde_json::to_value(&abs.ts).unwrap(),
            serde_json::to_value(&expected).unwrap()
        );
    }
}
