use logicrs::Var;
use serde::Deserialize;
use std::collections::HashMap;
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, Deserialize)]
struct VarHintRaw {
    name: String,
    #[serde(rename = "type")]
    hint_type: String,
    #[serde(default)]
    score: Option<f64>,
}

#[derive(Debug, Clone, Deserialize)]
struct StructHintRaw {
    version: u32,
    source: String,
    var_hints: HashMap<String, VarHintRaw>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignalType {
    Control,
    Datapath,
    Mixed,
}

#[derive(Debug, Clone)]
pub struct VarHint {
    pub name: String,
    pub signal_type: SignalType,
    pub score: Option<f64>,
}

#[derive(Debug, Clone)]
pub struct StructHint {
    pub source: String,
    hints: HashMap<u32, VarHint>,
}

impl StructHint {
    pub fn load(path: &Path) -> Option<Self> {
        let content = fs::read_to_string(path).ok()?;
        let raw: StructHintRaw = serde_json::from_str(&content).ok()?;
        let mut hints = HashMap::new();
        for (var_str, raw_hint) in raw.var_hints {
            let var_id: u32 = var_str.parse().ok()?;
            let signal_type = match raw_hint.hint_type.as_str() {
                "control" => SignalType::Control,
                "datapath" => SignalType::Datapath,
                _ => SignalType::Mixed,
            };
            hints.insert(
                var_id,
                VarHint {
                    name: raw_hint.name,
                    signal_type,
                    score: raw_hint.score,
                },
            );
        }
        Some(StructHint {
            source: raw.source,
            hints,
        })
    }

    pub fn get(&self, var: Var) -> Option<SignalType> {
        self.hints.get(&(*var)).map(|h| h.signal_type)
    }

    pub fn hints_ref(&self) -> &HashMap<u32, VarHint> {
        &self.hints
    }

    pub fn activity_weight(&self, var: Var, alpha: f64) -> f64 {
        let score = match self.hints.get(&(*var)) {
            Some(hint) => {
                if let Some(s) = hint.score {
                    s
                } else {
                    // Binary hint without score: control=1.0, datapath=0.2
                    match hint.signal_type {
                        SignalType::Control => 1.0,
                        _ => 0.2,
                    }
                }
            }
            None => 0.2,
        };
        // Uniform mapping: score [0,1] -> activity [1, alpha]
        1.0 + score * (alpha - 1.0)
    }

    pub fn bump_weight(&self, var: Var, alpha: f64) -> f64 {
        match self.hints.get(&(*var)) {
            Some(hint) => {
                if let Some(score) = hint.score {
                    // Persistent bump: score [0,1] -> bump multiplier [1, 1+alpha]
                    1.0 + score * alpha
                } else {
                    match hint.signal_type {
                        SignalType::Control => 1.0 + alpha,
                        _ => 1.0,
                    }
                }
            }
            None => 1.0,
        }
    }

    pub fn len(&self) -> usize {
        self.hints.len()
    }

    pub fn is_empty(&self) -> bool {
        self.hints.is_empty()
    }

    /// Remap hint variable IDs through a forward variable map.
    /// Used after preprocessing (COI, SCORR, rearrangement) to align
    /// original AIGER variable IDs with the solver's internal IDs.
    pub fn remap(&self, forward: impl Fn(Var) -> Option<Var>) -> Self {
        let mut new_hints = HashMap::new();
        let mut mapped = 0u32;
        let mut dropped = 0u32;
        for (&old_id, hint) in &self.hints {
            let old_var = Var::new(old_id as usize);
            if let Some(new_var) = forward(old_var) {
                new_hints.insert(*new_var, hint.clone());
                mapped += 1;
            } else {
                dropped += 1;
            }
        }
        log::info!(
            "StructHint remap: {} mapped, {} dropped (eliminated by preprocessing)",
            mapped, dropped
        );
        StructHint {
            source: self.source.clone(),
            hints: new_hints,
        }
    }
}
