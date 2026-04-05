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

    pub fn activity_weight(&self, var: Var, alpha: f64) -> f64 {
        match self.get(var) {
            Some(SignalType::Control) => alpha,
            _ => 1.0,
        }
    }

    pub fn len(&self) -> usize {
        self.hints.len()
    }

    pub fn is_empty(&self) -> bool {
        self.hints.is_empty()
    }
}
