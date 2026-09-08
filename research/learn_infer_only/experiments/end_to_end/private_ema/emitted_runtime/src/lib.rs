//! Generic Boolean schedule interpreter. No learner arithmetic lives here.
use serde::{Deserialize, Serialize};

pub const SCHEMA: &str = "private-address-ema-bool-schedule-v1";
pub const MAX_SCHEDULE_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_WIRES: usize = 100_000;
pub const MAX_GATES: usize = 100_000;

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Operation {
    Learn,
    Infer,
}

impl Operation {
    pub fn n_inputs(self) -> usize {
        match self {
            Self::Learn => 42,
            Self::Infer => 34,
        }
    }
    pub fn n_outputs(self) -> usize {
        match self {
            Self::Learn => 32,
            Self::Infer => 1,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::Learn => "learn",
            Self::Infer => "infer",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireIndex {
    w: usize,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Constant {
    c: bool,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(untagged)]
enum Reference {
    Wire(WireIndex),
    Constant(Constant),
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Operator {
    Xor,
    And,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Gate {
    op: Operator,
    a: Reference,
    b: Reference,
    out: usize,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct Descriptor {
    schema: String,
    operation: Operation,
    n_inputs: usize,
    n_wires: usize,
    gates: Vec<Gate>,
    outputs: Vec<Reference>,
}

/// Only parsing plus complete validation can construct this type.
#[derive(Debug)]
pub struct Schedule(Descriptor);

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Summary {
    pub schema: &'static str,
    pub operation: Operation,
    pub n_inputs: usize,
    pub n_wires: usize,
    pub n_gates: usize,
    pub n_outputs: usize,
    pub xor: usize,
    pub and: usize,
    pub unused_wire_slots: usize,
}

impl Schedule {
    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > MAX_SCHEDULE_BYTES {
            return Err("schedule exceeds byte limit".into());
        }
        let d: Descriptor =
            serde_json::from_slice(bytes).map_err(|e| format!("invalid schedule JSON: {e}"))?;
        if d.schema != SCHEMA {
            return Err("unsupported schedule schema".into());
        }
        if d.n_inputs != d.operation.n_inputs() {
            return Err("operation/input dimension mismatch".into());
        }
        if d.outputs.len() != d.operation.n_outputs() {
            return Err("operation/output dimension mismatch".into());
        }
        if d.n_wires < d.n_inputs || d.n_wires > MAX_WIRES {
            return Err("invalid wire bound".into());
        }
        if d.gates.len() > MAX_GATES {
            return Err("schedule exceeds gate limit".into());
        }
        let mut initialized = vec![false; d.n_wires];
        initialized[..d.n_inputs].fill(true);
        let mut previous_output = None;
        for (i, gate) in d.gates.iter().enumerate() {
            if gate.out < d.n_inputs || gate.out >= d.n_wires {
                return Err(format!("gate {i}: output outside allocated gate wires"));
            }
            if previous_output.is_some_and(|previous| gate.out <= previous) {
                return Err(format!("gate {i}: output indices must strictly increase"));
            }
            if initialized[gate.out] {
                return Err(format!("gate {i}: duplicate output write"));
            }
            validate_reference(gate.a, &initialized)
                .map_err(|e| format!("gate {i} operand a: {e}"))?;
            validate_reference(gate.b, &initialized)
                .map_err(|e| format!("gate {i} operand b: {e}"))?;
            initialized[gate.out] = true;
            previous_output = Some(gate.out);
        }
        for (i, reference) in d.outputs.iter().enumerate() {
            validate_reference(*reference, &initialized).map_err(|e| format!("output {i}: {e}"))?;
        }
        Ok(Self(d))
    }

    pub fn operation(&self) -> Operation {
        self.0.operation
    }

    pub fn summary(&self) -> Summary {
        Summary {
            schema: SCHEMA,
            operation: self.0.operation,
            n_inputs: self.0.n_inputs,
            n_wires: self.0.n_wires,
            n_gates: self.0.gates.len(),
            n_outputs: self.0.outputs.len(),
            xor: self
                .0
                .gates
                .iter()
                .filter(|g| matches!(g.op, Operator::Xor))
                .count(),
            and: self
                .0
                .gates
                .iter()
                .filter(|g| matches!(g.op, Operator::And))
                .count(),
            unused_wire_slots: self.0.n_wires - self.0.n_inputs - self.0.gates.len(),
        }
    }

    pub fn evaluate<B: Backend>(
        &self,
        inputs: Vec<B::Bit>,
        backend: &mut B,
    ) -> Result<Vec<B::Bit>, String> {
        if inputs.len() != self.0.n_inputs {
            return Err("runtime/input dimension mismatch".into());
        }
        let mut wires: Vec<Option<B::Bit>> = inputs.into_iter().map(Some).collect();
        wires.resize_with(self.0.n_wires, || None);
        // These two public values are internal. Artifact output policy is separate.
        let constants = [backend.constant(false), backend.constant(true)];
        for gate in &self.0.gates {
            let a = resolve(gate.a, &wires, &constants)?;
            let b = resolve(gate.b, &wires, &constants)?;
            let out = match gate.op {
                Operator::Xor => backend.xor(a, b),
                Operator::And => backend.and(a, b),
            };
            wires[gate.out] = Some(out);
        }
        self.0
            .outputs
            .iter()
            .map(|r| resolve(*r, &wires, &constants).cloned())
            .collect()
    }
}

fn validate_reference(reference: Reference, initialized: &[bool]) -> Result<(), String> {
    match reference {
        Reference::Constant(_) => Ok(()),
        Reference::Wire(WireIndex { w }) => match initialized.get(w) {
            Some(true) => Ok(()),
            Some(false) => Err(format!("wire {w} is uninitialized")),
            None => Err(format!("wire {w} is out of range")),
        },
    }
}

fn resolve<'a, T>(
    reference: Reference,
    wires: &'a [Option<T>],
    constants: &'a [T; 2],
) -> Result<&'a T, String> {
    match reference {
        Reference::Constant(Constant { c }) => Ok(&constants[usize::from(c)]),
        Reference::Wire(WireIndex { w }) => wires
            .get(w)
            .and_then(Option::as_ref)
            .ok_or_else(|| format!("validated wire {w} unavailable at runtime")),
    }
}

pub trait Backend {
    type Bit: Clone;
    fn constant(&mut self, value: bool) -> Self::Bit;
    fn xor(&mut self, a: &Self::Bit, b: &Self::Bit) -> Self::Bit;
    fn and(&mut self, a: &Self::Bit, b: &Self::Bit) -> Self::Bit;
}

pub struct PlainBoolean;
impl Backend for PlainBoolean {
    type Bit = bool;
    fn constant(&mut self, value: bool) -> bool {
        value
    }
    fn xor(&mut self, a: &bool, b: &bool) -> bool {
        *a ^ *b
    }
    fn and(&mut self, a: &bool, b: &bool) -> bool {
        *a & *b
    }
}

pub mod ciphertext;

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    fn base() -> Value {
        json!({"schema": SCHEMA, "operation": "infer", "nInputs": 34, "nWires": 40,
            "gates": [{"op":"xor","a":{"w":0},"b":{"c":true},"out":35},
                      {"op":"and","a":{"w":35},"b":{"w":1},"out":38}],
            "outputs":[{"w":38}]})
    }
    fn parse(v: &Value) -> Result<Schedule, String> {
        Schedule::parse(&serde_json::to_vec(v).unwrap())
    }

    #[test]
    fn gaps_unused_top_wire_and_gate_truth_table() {
        let schedule = parse(&base()).unwrap();
        assert_eq!(schedule.summary().unused_wire_slots, 4);
        for a in [false, true] {
            for b in [false, true] {
                let mut inputs = vec![false; 34];
                inputs[0] = a;
                inputs[1] = b;
                assert_eq!(
                    schedule.evaluate(inputs, &mut PlainBoolean).unwrap(),
                    vec![!a & b]
                );
            }
        }
    }

    #[test]
    fn all_references_must_be_initialized() {
        for (field, wire) in [("a", 34), ("a", 35), ("b", 38), ("a", 40)] {
            let mut v = base();
            v["gates"][0][field] = json!({"w":wire});
            assert!(parse(&v).is_err(), "{field}={wire}");
        }
        for wire in [34, 39, 40] {
            let mut v = base();
            v["outputs"][0] = json!({"w":wire});
            assert!(parse(&v).is_err());
        }
    }

    #[test]
    fn output_write_rules() {
        for out in [0, 33, 35, 34, 40] {
            let mut v = base();
            v["gates"][1]["out"] = json!(out);
            assert!(parse(&v).is_err());
        }
    }

    #[test]
    fn strict_schema_and_reference_types() {
        let mutations = [
            ("schema", json!("v2")),
            ("operation", json!("mux")),
            ("nInputs", json!(42)),
            ("nWires", json!(33)),
            ("nWires", json!(100001)),
            ("outputs", json!([])),
            ("unexpected", json!(true)),
        ];
        for (key, value) in mutations {
            let mut v = base();
            v[key] = value;
            assert!(parse(&v).is_err());
        }
        for reference in [
            json!({"w":0,"c":false}),
            json!({"w":-1}),
            json!({"w":1.0}),
            json!({"w":"1"}),
            json!({"c":0}),
            json!({"c":false,"x":0}),
            json!({}),
            json!(0),
            json!(true),
        ] {
            let mut v = base();
            v["gates"][0]["a"] = reference;
            assert!(parse(&v).is_err());
        }
        let mut v = base();
        v["gates"][0]["op"] = json!("mux");
        assert!(parse(&v).is_err());
        let mut v = base();
        v["gates"][0]["extra"] = json!(0);
        assert!(parse(&v).is_err());
    }

    #[test]
    fn duplicate_fields_and_trailing_json_rejected() {
        let original = serde_json::to_string(&base()).unwrap();
        for text in [
            original.replace("\"w\":0", "\"w\":0,\"w\":1"),
            original.replace("\"c\":true", "\"c\":true,\"c\":false"),
            original.replace("\"nInputs\":34", "\"nInputs\":34,\"nInputs\":34"),
            format!("{original} {{}}"),
        ] {
            assert!(Schedule::parse(text.as_bytes()).is_err(), "{text}");
        }
    }

    #[test]
    fn constant_outputs_valid_in_schedule_and_input_length_checked() {
        let mut v = base();
        v["outputs"][0] = json!({"c":true});
        let s = parse(&v).unwrap();
        assert_eq!(
            s.evaluate(vec![false; 34], &mut PlainBoolean).unwrap(),
            [true]
        );
        assert!(s.evaluate(vec![false; 33], &mut PlainBoolean).is_err());
        assert!(s.evaluate(vec![false; 35], &mut PlainBoolean).is_err());
    }
}
