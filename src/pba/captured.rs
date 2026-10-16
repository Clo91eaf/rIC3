//! Replay JG's captured proof seeds; never feed captured selections into search.
use super::*;
use giputils::hash::GHashMap;
use serde_json::Value;

fn selection(table: &Value, refs: &GHashMap<u32, Var>) -> GHashSet<Var> {
    let mut result = GHashSet::new();
    for (kind, tag) in [("variables", 0), ("gates", 2)] {
        for (word, value) in table[kind]["values"].as_array().unwrap().iter().enumerate() {
            let value = value.as_u64().unwrap() as u32;
            for bit in 0..32 {
                if value & (1 << bit) != 0 {
                    let index = word * 32 + bit;
                    assert!(index >= 2);
                    let raw = (((index - 2) as u32) << 3) | tag;
                    result.insert(refs[&raw]);
                }
            }
        }
    }
    result
}

fn reference(refs: &GHashMap<u32, Var>, raw: u32) -> Lit {
    match raw {
        0xfffffff8 => Lit::TRUE,
        0xfffffffc => Lit::FALSE,
        _ => refs[&(raw & !4)].lit().not_if(raw & 4 != 0),
    }
}

#[test]
#[ignore = "requires the local JG 2021.03 p530 proof-selection capture"]
fn rebuild_all_nine_jg_selections_and_gate_cuts() {
    let path =
        std::env::var("RIC3_JG_CAPTURE").expect("set RIC3_JG_CAPTURE to model-snapshot.json");
    let snapshot: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let source = snapshot["proof_source_models"]
        .as_object()
        .unwrap()
        .values()
        .next()
        .unwrap();
    let variables = source["variables"].as_array().unwrap();
    let flop_count = source["flop_count"].as_u64().unwrap() as usize;
    let mut ts = Transys::new();
    let mut refs = GHashMap::new();
    for i in 0..variables.len() {
        refs.insert((i as u32) << 3, ts.new_var());
    }
    let mut gates: Vec<_> = source["gates"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(i, g)| (i.parse::<u32>().unwrap(), g))
        .collect();
    gates.sort_unstable_by_key(|(i, _)| *i);
    for (i, g) in gates {
        let a = reference(&refs, g["a"].as_u64().unwrap() as u32);
        let b = reference(&refs, g["b"].as_u64().unwrap() as u32);
        let v = ts.new_var();
        let clauses = if g["kind"] == "and" {
            LitVvec::cnf_and(v.lit(), &[a, b])
        } else {
            assert_eq!(g["kind"], "xnor");
            LitVvec::cnf_xnor(v.lit(), a, b)
        };
        ts.rel.add_rel(v, &clauses);
        refs.insert((i << 3) | 2, v);
    }
    for (i, variable) in variables.iter().enumerate() {
        let v = refs[&((i as u32) << 3)];
        if i < flop_count && variable["valid"] == true {
            let init = match variable["initial"].as_i64().unwrap() {
                1 => Some(Lit::TRUE),
                -1 => Some(Lit::FALSE),
                0 => None,
                _ => panic!(),
            };
            let next = reference(&refs, source["next"][i].as_u64().unwrap() as u32);
            ts.add_latch(v, init, next);
        } else {
            ts.add_input(v);
        }
    }
    for p in source["targets"].as_array().unwrap() {
        ts.bad.push(!reference(&refs, p.as_u64().unwrap() as u32));
    }
    for c in source["constraints"].as_array().unwrap() {
        assert_eq!(c["tag"], 0);
        ts.constraint
            .push(reference(&refs, c["signal"].as_u64().unwrap() as u32));
    }
    let events = snapshot["proof_selection_events"].as_array().unwrap();
    assert_eq!(events.len(), 27);
    let mut last = None;
    for (round, rows) in events.chunks(3).enumerate() {
        let seed = selection(&rows[1]["selected"], &refs);
        let mut expected = selection(&rows[2]["selected"], &refs);
        expected.insert(Var::CONST);
        let selected = model::complete_selection(&ts, &seed);
        assert_eq!(selected, expected, "JG selection closure round {round}");
        let abs = model::build(&ts, selected);
        let states = ts.latch.iter().filter(|q| abs.selected.contains(q)).count();
        println!(
            "JG round {round}: {states} states, {} cuts, {} gate cuts",
            abs.cuts, abs.cut_gates
        );
        last = Some(abs);
    }
    let last = last.unwrap();
    assert_eq!(last.ts.latch.len(), 311); // 310 original + first-cycle pulse
    assert_eq!(last.cuts, 795);
    assert_eq!(last.cut_gates, 352);
    assert_eq!(last.ts.input.len(), 815);
    assert_eq!(last.ts.constraint.len(), 688);
    assert_eq!(
        last.ts
            .rel
            .var_iter_woc()
            .filter(|v| !last.ts.rel[*v].is_empty())
            .count(),
        8280 + 566
    );
}
