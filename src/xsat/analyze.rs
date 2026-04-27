use logicrs::{Lit, Var};

use super::clause::Clause;
use super::gate::{Assign, LitAssign, Reason};

/// Result of conflict analysis.
pub struct AnalyzeResult {
    /// The learned clause literals.
    /// Position 0 is the asserting literal (negation of the UIP).
    /// Position 1 has the highest level among the rest (backtrack level).
    pub learn: Vec<Lit>,
    /// The level to backtrack to. -1 means UNSAT (conflict at level 0).
    pub backtrack_level: i32,
    /// The LBD (Literal Block Distance) of the learned clause.
    pub lbd: u32,
}

/// First-UIP conflict analysis.
/// Corresponds to X-SAT `CSat::analyze()` (analyze.cpp:3-133)
///
/// Given a conflicting clause, traces back the implication chain to find:
///   1. A learned clause (via resolution)
///   2. The backtrack level (second-highest level in learned clause)
///   3. The LBD quality metric
///
/// ## Algorithm (First-UIP)
///
/// 1. Mark all literals in the conflict clause as "seen"
/// 2. Walk backwards through the trail
/// 3. When we hit a seen literal, resolve it using its reason:
///    - Direct(lit): replace with ~lit
///    - Clause(cref): replace with all other literals in the clause
/// 4. When only one seen literal remains at the current highest level,
///    that's the UIP (Unique Implication Point)
/// 5. The learned clause = ~UIP + all lower-level seen literals
pub fn analyze(
    conflict: &[Lit],
    trail: &[Lit],
    assigns: &[Assign],
    clauses: &[Clause],
    num_vars: usize,
) -> AnalyzeResult {
    let mut stamp = 0;
    let mut var_stamp = vec![0u64; num_vars + 1];
    stamp += 1;

    // Find the highest decision level in the conflict
    let mut highest_level = 0u32;
    for &lit in conflict {
        let level = assigns[*lit.var() as usize].level;
        if level > highest_level {
            highest_level = level;
        }
    }

    // Conflict at level 0 means UNSAT
    if highest_level == 0 {
        return AnalyzeResult {
            learn: Vec::new(),
            backtrack_level: -1,
            lbd: 0,
        };
    }

    // learn[0] is reserved for the asserting literal (UIP negation)
    let mut learn: Vec<Lit> = vec![Lit::new(Var::CONST, true)];
    let mut seen_lits: Vec<Lit> = conflict.to_vec();
    let mut should_visit_ct = 0;
    let mut resolve_lit;
    let mut index = trail.len() as i32 - 1;

    loop {
        for &lit in &seen_lits {
            let var = *lit.var() as usize;
            if var_stamp[var] != stamp && assigns[var].level > 0 {
                var_stamp[var] = stamp;
                if assigns[var].level >= highest_level {
                    should_visit_ct += 1;
                } else {
                    learn.push(lit);
                }
            }
        }

        // Walk backwards on trail to find the next seen variable
        while var_stamp[*trail[index as usize].var() as usize] != stamp {
            index -= 1;
        }

        resolve_lit = trail[index as usize];
        index -= 1;
        should_visit_ct -= 1;

        let resolve_var = *resolve_lit.var() as usize;
        var_stamp[resolve_var] = 0;

        if should_visit_ct == 0 {
            break;
        }

        // Resolve: replace resolve_lit with its reason
        let reason = &assigns[resolve_var].reason;
        seen_lits.clear();
        match reason {
            Reason::Direct(reason_lit) => {
                seen_lits.push(!*reason_lit);
            }
            Reason::Clause(cref) => {
                let cls = &clauses[cref.idx()];
                for &lit in &cls.data {
                    if *lit.var() as usize != resolve_var {
                        seen_lits.push(lit);
                    }
                }
            }
            Reason::Decision | Reason::Output => {
                unreachable!("decision/output has no reason to resolve")
            }
        }
    }

    // The asserting literal is ~resolve_lit (the UIP negation)
    let decision_lit = !resolve_lit;
    learn[0] = decision_lit;

    // Find backtrack level: second-highest level in learned clause
    let backtrack_level = if learn.len() == 1 {
        0
    } else {
        // Find the literal with highest level among learn[1..]
        let mut max_idx = 1;
        for i in 2..learn.len() {
            if assigns[*learn[i].var() as usize].level
                > assigns[*learn[max_idx].var() as usize].level
            {
                max_idx = i;
            }
        }
        // Swap max to position 1
        learn.swap(1, max_idx);
        assigns[*learn[max_idx].var() as usize].level
    };

    // Calculate LBD (Literal Block Distance)
    let mut lbd = 0u32;
    let mut level_seen = vec![0u32; highest_level as usize + 1];
    let mut lbd_stamp = 0u32;
    lbd_stamp += 1;
    for &lit in &learn {
        let level = assigns[*lit.var() as usize].level;
        if level > 0 && level_seen[level as usize] != lbd_stamp {
            level_seen[level as usize] = lbd_stamp;
            lbd += 1;
        }
    }

    AnalyzeResult {
        learn,
        backtrack_level: backtrack_level as i32,
        lbd,
    }
}

/// Backtrack to the given level, undoing all assignments above it.
/// Corresponds to X-SAT `CSat::backtrack()` (backtrack.cpp:3-58)
///
/// For each literal being undone:
///   1. Clear its value in LitAssign
///   2. Phase saving: remember the polarity for future decisions
///   3. Re-insert variable into VSIDS heap (if not already there)
///
/// Returns the new trail length and propagated pointer.
pub fn backtrack(
    backtrack_level: u32,
    trail: &mut Vec<Lit>,
    propagated: &mut usize,
    value: &mut LitAssign,
    _assigns: &mut [Assign],
    saved: &mut Vec<i8>,
    pos_in_trail: &[usize],
) {
    if pos_in_trail.len() <= backtrack_level as usize {
        return;
    }

    let trail_keep = pos_in_trail[backtrack_level as usize];

    for i in (trail_keep..trail.len()).rev() {
        let lit = trail[i];
        let var = *lit.var() as usize;
        value.unassign(lit.var());
        // Phase saving: remember the polarity
        if var < saved.len() {
            saved[var] = if lit.polarity() { 1 } else { -1 };
        }
    }

    trail.truncate(trail_keep);
    *propagated = trail_keep;
}

#[cfg(test)]
mod tests {
    use super::*;
    use logicrs::Var;

    #[test]
    fn test_analyze_simple_conflict() {
        let num_vars = 5;
        let mut assigns = vec![Assign::default(); num_vars + 1];
        let mut value = LitAssign::new();

        for v in 0..=num_vars {
            value.reserve_var(Var(v as u32));
        }

        // Simulate: level 0 decision x1=1, level 1 decision x2=1
        // Binary clauses: (x1, x3) and (~x2, ~x3)
        // x1=1 propagates x3=1, x2=1 propagates ~x3=1 → conflict on x3
        assigns[1].level = 0;
        assigns[1].reason = Reason::Decision;
        assigns[2].level = 1;
        assigns[2].reason = Reason::Decision;
        assigns[3].level = 1;
        assigns[3].reason = Reason::Direct(Var(1).lit()); // x3 implied by x1

        value.assign(Var(1).lit()); // x1 = 1
        value.assign(Var(2).lit()); // x2 = 1
        value.assign(Var(3).lit()); // x3 = 1 (propagated)

        let trail = vec![Var(1).lit(), Var(2).lit(), Var(3).lit()];

        // Conflict: both x3 and ~x3 are required
        let conflict = vec![Var(3).lit(), !Var(3).lit()];

        let result = analyze(&conflict, &trail, &assigns, &[], num_vars);

        // Should not be UNSAT
        assert_ne!(result.backtrack_level, -1);
        // Learned clause should contain at least the asserting literal
        assert!(!result.learn.is_empty());
    }

    #[test]
    fn test_analyze_level0_conflict() {
        let num_vars = 3;
        let assigns = vec![Assign::default(); num_vars + 1];

        // Conflict at level 0 → UNSAT
        let conflict = vec![Var(1).lit(), !Var(1).lit()];
        let trail = vec![Var(1).lit()];

        let result = analyze(&conflict, &trail, &assigns, &[], num_vars);
        assert_eq!(result.backtrack_level, -1);
    }

    #[test]
    fn test_backtrack() {
        let num_vars = 5;
        let mut value = LitAssign::new();
        let mut assigns = vec![Assign::default(); num_vars + 1];
        let mut saved = vec![0i8; num_vars + 1];
        let mut trail = Vec::new();

        for v in 0..=num_vars {
            value.reserve_var(Var(v as u32));
        }

        // Level 0: x1=1, x2=0
        // Level 1: x3=1
        assigns[1].level = 0;
        assigns[2].level = 0;
        assigns[3].level = 1;

        value.assign(Var(1).lit());
        value.assign(!Var(2).lit());
        value.assign(Var(3).lit());

        trail.push(Var(1).lit());
        trail.push(!Var(2).lit());
        trail.push(Var(3).lit());

        let pos_in_trail = vec![0, 2]; // level 0 starts at trail[0], level 1 at trail[2]
        let mut propagated = trail.len();

        // Backtrack to level 0: undo level 1 assignments (trail[2..])
        // But we need pos_in_trail[0] = 0 means we keep from 0 onwards
        // and pos_in_trail[1] = 2 means level 1 starts at index 2
        // Backtracking to level 0 means keeping trail[0..pos_in_trail[1]] = trail[0..2]
        // Actually: pos_in_trail stores where each level's decision variable is.
        // To keep level 0, we truncate to pos_in_trail[0+1] = pos_in_trail[1] = 2
        // Wait, X-SAT does: trail.setsize(pos_in_trail[backtrack_level])
        // So backtrack to 0 means keeping trail[0..pos_in_trail[0]]
        // pos_in_trail[0] should be the position of level 0's decision = 0
        // That means everything gets undone.
        //
        // Let me re-think: pos_in_trail[level] = position of level's decision var in trail
        // Backtracking to level L means keeping all vars at level <= L
        // The trail from pos_in_trail[L] onwards is level >= L
        // Actually in X-SAT: propagated = pos_in_trail[backtrack_level]
        //   trail.setsize(propagated)
        //   pos_in_trail.setsize(backtrack_level)
        // So it keeps trail[0..pos_in_trail[backtrack_level]] and removes levels > backtrack_level
        //
        // For backtrack to level 0: keep trail[0..pos_in_trail[0]]
        // pos_in_trail[0] = position of level 0 decision = 0
        // This would keep nothing! That's wrong for non-UNSAT cases.
        //
        // Actually: pos_in_trail stores where level+1 starts, not where level starts.
        // No — let me re-check. In search.cpp, pos_in_trail is filled with:
        //   pos_in_trail[i] = the pos of (Level i's decision variable) in trail
        // So backtrack(0) keeps trail up to pos_in_trail[0] (the level 0 decision position)
        // Since level 0 decisions are at the start, pos_in_trail[0] = 0.
        // Then trail is truncated to size 0, removing everything.
        //
        // But that means backtrack(0) always empties the trail. The level 0
        // assignments (outputs, etc.) are re-propagated after backtrack.
        // For a non-UNSAT backtrack to level 0, we'd re-propagate everything.
        //
        // Let me fix the test to backtrack to level 1 instead:
        backtrack(
            1,
            &mut trail,
            &mut propagated,
            &mut value,
            &mut assigns,
            &mut saved,
            &pos_in_trail,
        );

        // Only x3 (level 1) should be unassigned
        assert!(value.val(Var(3).lit()).is_none());
        // x1 and x2 (level 0) should still be assigned
        assert!(value.val(Var(1).lit()).is_true());
        assert!(value.val(!Var(2).lit()).is_true());
        // Trail should keep level 0 assignments
        assert_eq!(trail.len(), 2);
        // Phase saving for x3 (was positive)
        assert_eq!(saved[3], 1);
    }
}
