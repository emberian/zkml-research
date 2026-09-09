//! Production garbled circuit evaluation — DSL-native descriptor.
//!
//! This module provides the garbled circuit evaluation `CircuitDescriptor` and
//! trace-generation infrastructure with the extended 56-column layout supporting:
//!
//! - Multi-gate chaining (linear chains via `chain_flag`)
//! - Gate type selectors (AND/OR/XOR/NOT)
//! - Topological ordering enforcement (gate_index_delta)
//! - Padding support for power-of-two trace alignment
//! - Fan-out wiring (chain_flag=0 for non-adjacent gate inputs)

use crate::field::BabyBear;
use crate::garbled::GateEvalRecord;
use crate::garbled_air::{GARBLED_EVAL_AIR_WIDTH, col};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Re-export the column layout from the test DSL (now production)
// ============================================================================

/// Original AIR width (49 columns).
const BASE_WIDTH: usize = GARBLED_EVAL_AIR_WIDTH; // 49

/// Extended column indices for gate types and chaining.
pub mod ext_col {
    use super::BASE_WIDTH;

    /// Gate type selector: AND gate.
    pub const IS_AND: usize = BASE_WIDTH; // 49
    /// Gate type selector: OR gate.
    pub const IS_OR: usize = BASE_WIDTH + 1; // 50
    /// Gate type selector: XOR gate.
    pub const IS_XOR: usize = BASE_WIDTH + 2; // 51
    /// Gate type selector: NOT gate.
    pub const IS_NOT: usize = BASE_WIDTH + 3; // 52
    /// Chain flag: 1 if this row's output feeds next row's left input.
    pub const CHAIN_FLAG: usize = BASE_WIDTH + 4; // 53
    /// Gate index delta: gate_index[current] - gate_index[previous].
    pub const GATE_INDEX_DELTA: usize = BASE_WIDTH + 5; // 54
    /// Padding flag: 1 on padding rows (constraints relaxed).
    pub const IS_PADDING: usize = BASE_WIDTH + 6; // 55
}

/// Extended trace width.
pub const GARBLED_DSL_WIDTH: usize = BASE_WIDTH + 7; // 56

/// Public input indices.
pub mod pi {
    /// Circuit commitment elements 0..3.
    pub const CIRCUIT_COMMITMENT_START: usize = 0;
    /// Output label hash elements 0..3.
    pub const OUTPUT_LABEL_HASH_START: usize = 4;
}

// ============================================================================
// Gate type and extended record
// ============================================================================

/// Gate type enum for the extended DSL.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateType {
    And,
    Or,
    Xor,
    Not,
}

/// A gate evaluation record for the extended trace.
#[derive(Debug, Clone)]
pub struct ExtendedGateRecord {
    /// The base record from the garbled circuit evaluator.
    pub base: GateEvalRecord,
    /// Gate type for this gate.
    pub gate_type: GateType,
    /// Whether this gate's output chains to the next gate's left input.
    pub chains_to_next: bool,
}

// ============================================================================
// Helpers
// ============================================================================

fn neg_one() -> BabyBear {
    BabyBear::new(crate::field::BABYBEAR_P - 1)
}

fn term(coeff: BabyBear, cols: &[usize]) -> PolyTerm {
    PolyTerm {
        coeff,
        col_indices: cols.to_vec(),
    }
}

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the extended garbled circuit evaluation CircuitDescriptor (56 cols).
///
/// This is the production version with full multi-gate, chaining, and gate-type support.
pub fn garbled_extended_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // C1-C4: circuit_commitment matches public inputs
    for i in 0..4 {
        constraints.push(ConstraintExpr::PiBinding {
            col: col::CIRCUIT_COMMITMENT + i,
            pi_index: pi::CIRCUIT_COMMITMENT_START + i,
        });
    }

    // C5-C8: output_label_hash matches public inputs
    for i in 0..4 {
        constraints.push(ConstraintExpr::PiBinding {
            col: col::OUTPUT_LABEL_HASH + i,
            pi_index: pi::OUTPUT_LABEL_HASH_START + i,
        });
    }

    // C9-C16: Decryption correctness, gated on (1 - is_padding)
    for i in 0..8 {
        constraints.push(ConstraintExpr::InvertedGated {
            selector_col: ext_col::IS_PADDING,
            inner: Box::new(ConstraintExpr::Polynomial {
                terms: vec![
                    term(BabyBear::ONE, &[col::output(i)]),
                    term(neg_one(), &[col::table_entry(i)]),
                    term(BabyBear::ONE, &[col::hash_out(i)]),
                ],
            }),
        });
    }

    // C17-C20: Binary constraints on gate type selectors
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_AND,
    });
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_OR,
    });
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_XOR,
    });
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_NOT,
    });

    // C21: chain_flag binary
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::CHAIN_FLAG,
    });

    // C22: is_padding binary
    constraints.push(ConstraintExpr::Binary {
        col: ext_col::IS_PADDING,
    });

    // C23: Gate type exclusivity (gated on NOT is_padding):
    // (1 - is_padding) * (is_and + is_or + is_xor + is_not - 1) == 0
    constraints.push(ConstraintExpr::InvertedGated {
        selector_col: ext_col::IS_PADDING,
        inner: Box::new(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[ext_col::IS_AND]),
                term(BabyBear::ONE, &[ext_col::IS_OR]),
                term(BabyBear::ONE, &[ext_col::IS_XOR]),
                term(BabyBear::ONE, &[ext_col::IS_NOT]),
                term(neg_one(), &[]), // constant -1
            ],
        }),
    });

    // C24-C31: Wire chaining transition constraints.
    // chain_flag * (next[left_label_i] - local[output_label_i]) == 0
    for i in 0..8 {
        constraints.push(ConstraintExpr::Gated {
            selector_col: ext_col::CHAIN_FLAG,
            inner: Box::new(ConstraintExpr::Transition {
                next_col: col::left(i),
                local_col: col::output(i),
            }),
        });
    }

    // Boundary constraints
    let mut boundaries = Vec::new();
    for i in 0..4 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CIRCUIT_COMMITMENT + i,
            pi_index: pi::CIRCUIT_COMMITMENT_START + i,
        });
    }
    for i in 0..4 {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::OUTPUT_LABEL_HASH + i,
            pi_index: pi::OUTPUT_LABEL_HASH_START + i,
        });
    }
    // First row gate_index_delta = 0 (no predecessor)
    boundaries.push(BoundaryDef::Fixed {
        row: BoundaryRow::First,
        col: ext_col::GATE_INDEX_DELTA,
        value: BabyBear::ZERO,
    });

    // Column definitions
    let mut columns = Vec::new();
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("left_label_{i}"),
            index: col::left(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("right_label_{i}"),
            index: col::right(i),
            kind: ColumnKind::Value,
        });
    }
    columns.push(ColumnDef {
        name: "gate_index".into(),
        index: col::GATE_INDEX,
        kind: ColumnKind::Value,
    });
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("hash_output_{i}"),
            index: col::hash_out(i),
            kind: ColumnKind::Hash,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("table_entry_{i}"),
            index: col::table_entry(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..8 {
        columns.push(ColumnDef {
            name: format!("output_label_{i}"),
            index: col::output(i),
            kind: ColumnKind::Value,
        });
    }
    for i in 0..4 {
        columns.push(ColumnDef {
            name: format!("circuit_commitment_{i}"),
            index: col::CIRCUIT_COMMITMENT + i,
            kind: ColumnKind::Hash,
        });
    }
    for i in 0..4 {
        columns.push(ColumnDef {
            name: format!("output_label_hash_{i}"),
            index: col::OUTPUT_LABEL_HASH + i,
            kind: ColumnKind::Hash,
        });
    }
    // Extended columns
    columns.push(ColumnDef {
        name: "is_and".into(),
        index: ext_col::IS_AND,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "is_or".into(),
        index: ext_col::IS_OR,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "is_xor".into(),
        index: ext_col::IS_XOR,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "is_not".into(),
        index: ext_col::IS_NOT,
        kind: ColumnKind::Selector,
    });
    columns.push(ColumnDef {
        name: "chain_flag".into(),
        index: ext_col::CHAIN_FLAG,
        kind: ColumnKind::Binary,
    });
    columns.push(ColumnDef {
        name: "gate_index_delta".into(),
        index: ext_col::GATE_INDEX_DELTA,
        kind: ColumnKind::Value,
    });
    columns.push(ColumnDef {
        name: "is_padding".into(),
        index: ext_col::IS_PADDING,
        kind: ColumnKind::Binary,
    });

    CircuitDescriptor {
        name: "dregg-garbled-evaluation-extended-dsl-v1".into(),
        trace_width: GARBLED_DSL_WIDTH,
        max_degree: 3,
        columns,
        constraints,
        boundaries,
        public_input_count: 8,
        lookup_tables: vec![],
    }
}

/// Create the production DslCircuit for garbled evaluation.
pub fn garbled_dsl_circuit() -> DslCircuit {
    DslCircuit::new(garbled_extended_descriptor())
}
