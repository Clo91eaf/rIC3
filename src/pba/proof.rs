//! Original clauses reachable from CaDiCaL's empty-clause LRAT derivation.
//! JG 0x1417060/0x1428d90 visits this proof DAG and 0x991a30 marks
//! variables of original clauses. Deleted ancestors must remain available.
use cadical::tracer::Tracer;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::{Lit, LitVec, Var};

enum Node {
    Original(LitVec),
    Derived(Vec<usize>),
}

#[derive(Default)]
pub(super) struct Dependencies {
    nodes: GHashMap<usize, Node>,
    empty: Option<usize>,
}

impl Tracer for Dependencies {
    fn add_original_clause(&mut self, id: usize, _: bool, c: &[Lit], _: bool) {
        if c.is_empty() {
            self.empty = Some(id);
        }
        self.nodes
            .entry(id)
            .or_insert_with(|| Node::Original(c.iter().copied().collect()));
    }

    fn add_derived_clause(&mut self, id: usize, _: bool, c: &[Lit], parents: &[usize]) {
        if c.is_empty() {
            self.empty = Some(id);
        }
        self.nodes.insert(id, Node::Derived(parents.to_vec()));
    }
}

pub(super) struct Core {
    pub clauses: Vec<LitVec>,
    pub variables: GHashSet<Var>,
    pub proof_nodes: usize,
}

impl Dependencies {
    pub fn core(&self) -> Result<Core, &'static str> {
        let mut pending = vec![self.empty.ok_or("proof has no empty-clause derivation")?];
        let mut visited = GHashSet::new();
        let mut original = Vec::new();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            match self.nodes.get(&id).ok_or("missing LRAT antecedent")? {
                Node::Original(_) => original.push(id),
                Node::Derived(parents) => {
                    if parents.is_empty() {
                        return Err("derived proof clause has no antecedents");
                    }
                    pending.extend(parents);
                }
            }
        }
        original.sort_unstable();
        let mut clauses = Vec::new();
        let mut variables = GHashSet::new();
        for id in original {
            let Node::Original(c) = &self.nodes[&id] else {
                unreachable!()
            };
            variables.extend(c.iter().map(|l| l.var()));
            clauses.push(c.clone());
        }
        Ok(Core {
            clauses,
            variables,
            proof_nodes: visited.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cadical::CaDiCaL;
    use logicrs::satif::Satif;

    #[test]
    fn proof_core_excludes_unused_clauses_and_is_itself_unsat() {
        let dependencies = Box::pin(Dependencies::default());
        let mut solver = CaDiCaL::new();
        solver.connect_tracer(dependencies.as_ref());
        let a = solver.new_var().lit();
        let b = solver.new_var().lit();
        let noise = solver.new_var().lit();
        for c in [
            vec![a, b],
            vec![a, !b],
            vec![!a, b],
            vec![!a, !b],
            vec![noise],
        ] {
            solver.add_clause(&c);
        }
        assert!(!solver.solve(&[]));
        solver.disconnect_tracer(dependencies.as_ref());
        let core = dependencies.core().unwrap();
        assert!(core.variables.contains(&a.var()));
        assert!(core.variables.contains(&b.var()));
        assert!(!core.variables.contains(&noise.var()));
        let mut checker = CaDiCaL::new();
        for c in &core.clauses {
            checker.add_clause(c);
        }
        assert!(!checker.solve(&[]));
    }
}
