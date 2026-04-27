use logicrs::Lit;

use super::clause::{CRef, Clause};
use super::gate::{Assign, LitAssign, Reason, TriVal};
use super::watch::{Watcher, Watches};

/// Propagation result.
pub enum PropResult {
    Ok,
    Conflict(Vec<Lit>),
}

/// Boolean Constraint Propagation (BCP).
/// Corresponds to X-SAT `CSat::propagate()` (propagate.cpp:3-151)
///
/// Processes all enqueued assignments on the trail. For each propagated literal,
/// checks all watches registered on its negation (~lit means "lit became false").
///
/// Three layers, checked in order:
///   1. Binary clauses  (size 2) — direct literal lookup, no CRef
///   2. Ternary clauses (size 3) — CRef lookup, swap-based watch update
///   3. General clauses (size 4+) — standard watched literal with blocker
///
/// Returns:
///   PropResult::Ok          — all propagations completed, no conflict
///   PropResult::Conflict(lits) — conflicting clause literals
pub fn propagate(
    trail: &mut Vec<Lit>,
    propagated: &mut usize,
    watches: &mut Watches,
    clauses: &mut [Clause],
    value: &mut LitAssign,
    assigns: &mut [Assign],
) -> PropResult {
    while *propagated < trail.len() {
        let lit = trail[*propagated];
        *propagated += 1;

        let level = assigns[*lit.var() as usize].level;

        // --- Layer 1: Binary clauses ---
        // X-SAT: propagate.cpp:14-23
        // Watches are registered at notlit(clause[0]) = ~a.
        // When lit (= ~a) appears on trail, we look up watches[lit] to find partner.
        for &target in watches.bin(lit) {
            match value.val(target) {
                TriVal::None => {
                    assign_lit(target, level, Reason::Direct(lit), value, assigns, trail);
                }
                TriVal::False => {
                    return PropResult::Conflict(vec![!lit, target]);
                }
                TriVal::True => {}
            }
        }

        // --- Layer 2: Ternary clauses ---
        // X-SAT: propagate.cpp:25-76
        let not_lit = !lit;
        let tri_entries: Vec<CRef> = watches.tri_mut(lit).drain(..).collect();
        let mut tri_keep = Vec::with_capacity(tri_entries.len());

        for cref in &tri_entries {
            let cls = &mut clauses[cref.idx()];
            debug_assert_eq!(cls.data.len(), 3);

            if cls.data[1] != not_lit {
                cls.data.swap(0, 1);
            }
            debug_assert_eq!(cls.data[1], not_lit);

            if value.val(cls.data[0]).is_true() {
                tri_keep.push(*cref);
                continue;
            }

            if !value.val(cls.data[2]).is_false() {
                cls.data.swap(1, 2);
                watches.tri_mut(!cls.data[1]).push(*cref);
                continue;
            }

            tri_keep.push(*cref);

            if value.val(cls.data[0]).is_none() {
                assign_lit(
                    cls.data[0],
                    level,
                    Reason::Clause(*cref),
                    value,
                    assigns,
                    trail,
                );
            } else {
                let conflict: Vec<Lit> = cls.data.clone();
                watches.tri_mut(not_lit).extend(tri_keep);
                return PropResult::Conflict(conflict);
            }
        }

        watches.tri_mut(lit).extend(tri_keep);

        // --- Layer 3: General clauses ---
        // X-SAT: propagate.cpp:78-147
        let gen_ws: Vec<_> = watches.general(lit).to_vec();
        let mut gen_keep = Vec::with_capacity(gen_ws.len());

        for w in &gen_ws {
            if value.val(w.blocker).is_true() {
                gen_keep.push(*w);
                continue;
            }

            let cls = &mut clauses[w.cref.idx()];

            if cls.data[1] != not_lit {
                cls.data.swap(0, 1);
            }
            debug_assert_eq!(cls.data[1], not_lit);

            let first = cls.data[0];

            if first != w.blocker && value.val(first).is_true() {
                gen_keep.push(Watcher {
                    cref: w.cref,
                    blocker: first,
                });
                continue;
            }

            let mut found = None;
            for r in 2..cls.data.len() {
                if !value.val(cls.data[r]).is_false() {
                    found = Some(r);
                    break;
                }
            }

            if let Some(r) = found {
                cls.data.swap(1, r);
                watches.general_mut(!cls.data[1]).push(Watcher {
                    cref: w.cref,
                    blocker: cls.data[0],
                });
            } else {
                gen_keep.push(Watcher {
                    cref: w.cref,
                    blocker: first,
                });
                if value.val(cls.data[0]).is_false() {
                    let conflict: Vec<Lit> = cls.data.clone();
                    for w2 in &gen_ws[gen_keep.len()..] {
                        gen_keep.push(*w2);
                    }
                    *watches.general_mut(lit) = gen_keep;
                    return PropResult::Conflict(conflict);
                } else {
                    assign_lit(
                        cls.data[0],
                        level,
                        Reason::Clause(w.cref),
                        value,
                        assigns,
                        trail,
                    );
                }
            }
        }

        *watches.general_mut(not_lit) = gen_keep;
    }

    PropResult::Ok
}

/// Assign a literal at the given level with the given reason.
/// Corresponds to X-SAT `CSat::assign()` (solver.cpp:87-116)
///
/// This is the central assignment function:
///   1. Set the literal to true (and its negation to false) in value[]
///   2. Record the level and reason in assigned[]
///   3. Push the literal onto the trail
fn assign_lit(
    lit: Lit,
    level: u32,
    reason: Reason,
    value: &mut LitAssign,
    assigns: &mut [Assign],
    trail: &mut Vec<Lit>,
) {
    debug_assert!(value.val(lit).is_none());

    value.assign(lit);
    let var = *lit.var() as usize;
    assigns[var].level = level;
    assigns[var].reason = reason;
    trail.push(lit);
}

#[cfg(test)]
mod tests {
    use super::*;
    use logicrs::Var;

    fn setup(num_vars: usize) -> (Watches, Vec<Clause>, LitAssign, Vec<Assign>) {
        let num_lits = (num_vars + 1) * 2;
        let watches = Watches::new(num_lits);
        let clauses = Vec::new();
        let mut value = LitAssign::new();
        let mut assigns = Vec::new();
        for v in 0..=num_vars {
            value.reserve_var(Var(v as u32));
            assigns.push(Assign::default());
        }
        (watches, clauses, value, assigns)
    }

    #[test]
    fn test_binary_propagation() {
        let (mut watches, _clauses, mut value, mut assigns) = setup(3);

        let a = Var(1).lit();
        let b = Var(2).lit();
        watches.add_bin(a, b);

        let mut trail = vec![!a];
        let mut propagated = 0;

        value.assign(!a);
        assigns[1].level = 0;

        let result = propagate(
            &mut trail,
            &mut propagated,
            &mut watches,
            &mut [],
            &mut value,
            &mut assigns,
        );

        assert!(matches!(result, PropResult::Ok));
        assert!(value.val(b).is_true());
    }

    #[test]
    fn test_binary_conflict() {
        let (mut watches, _clauses, mut value, mut assigns) = setup(3);

        let a = Var(1).lit();
        let b = Var(2).lit();
        watches.add_bin(a, b);

        value.assign(!a);
        value.assign(!b);
        assigns[1].level = 0;
        assigns[2].level = 0;

        let mut trail = vec![!a];
        let mut propagated = 0;

        let result = propagate(
            &mut trail,
            &mut propagated,
            &mut watches,
            &mut [],
            &mut value,
            &mut assigns,
        );

        match result {
            PropResult::Conflict(lits) => {
                assert_eq!(lits.len(), 2);
            }
            PropResult::Ok => panic!("expected conflict"),
        }
    }
}
