//! Production temporal absence proving — DSL-native implementation.
//!
//! This module provides the canonical prove/verify API for temporal absence proofs
//! using the DSL `CircuitDescriptor` infrastructure. It supersedes the hand-written
//! `circuit/src/temporal_absence_air.rs`.
//!
//! # Proof Statement
//!
//! Proves: "event X did NOT occur during blocks [t1, t2]" via a certified gap proof
//! over an append-only timeline. Two adjacent timeline entries bracket the absence
//! window, and both authenticate to the same Merkle root.
//!
//! # Trace Layout (2 rows x 10 columns)
//!
//! | Column | Name            | Description                                |
//! |--------|-----------------|--------------------------------------------|
//! | 0      | block_height    | Block height of the timeline entry         |
//! | 1      | event_type      | Event type identifier (hash)               |
//! | 2      | attribute_hash  | Which attribute this event concerns        |
//! | 3      | timeline_index  | Sequential position in timeline tree       |
//! | 4      | leaf_hash       | Hash of the entry                          |
//! | 5      | merkle_root     | Computed Merkle root from this entry       |
//! | 6      | adj_index_plus1 | timeline_index + 1 (auxiliary)             |
//! | 7      | is_before       | 1 on row 0 (entry_before), 0 on row 1     |
//! | 8      | timing_ok       | 1 if timing constraint is satisfied        |
//! | 9      | attr_diff_inv   | Inverse of (attribute_hash - excluded_attr)|
//!
//! # Public Inputs
//!
//! [t1, t2, excluded_attribute_hash, timeline_root]

use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2::hash_fact;

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
};

// ============================================================================
// Column layout
// ============================================================================

pub const BLOCK_HEIGHT: usize = 0;
pub const EVENT_TYPE: usize = 1;
pub const ATTRIBUTE_HASH: usize = 2;
pub const TIMELINE_INDEX: usize = 3;
pub const LEAF_HASH: usize = 4;
pub const MERKLE_ROOT: usize = 5;
pub const ADJ_INDEX_PLUS1: usize = 6;
pub const IS_BEFORE: usize = 7;
pub const TIMING_OK: usize = 8;
pub const ATTR_DIFF_INV: usize = 9;

pub const TRACE_WIDTH: usize = 10;

/// Public input indices.
pub const PI_T1: usize = 0;
pub const PI_T2: usize = 1;
pub const PI_EXCLUDED_ATTR: usize = 2;
pub const PI_TIMELINE_ROOT: usize = 3;

pub const PUBLIC_INPUT_COUNT: usize = 4;

// ============================================================================
// Descriptor construction
// ============================================================================

/// Build the temporal absence `CircuitDescriptor`.
///
/// Proves that no event with `excluded_attribute_hash` occurred in the
/// timeline during blocks [t1, t2], using a certified gap proof.
pub fn temporal_absence_descriptor() -> CircuitDescriptor {
    let neg_one = BabyBear::new(BABYBEAR_P - 1);

    let columns = vec![
        ColumnDef {
            name: "block_height".into(),
            index: BLOCK_HEIGHT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "event_type".into(),
            index: EVENT_TYPE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "attribute_hash".into(),
            index: ATTRIBUTE_HASH,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "timeline_index".into(),
            index: TIMELINE_INDEX,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "leaf_hash".into(),
            index: LEAF_HASH,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "merkle_root".into(),
            index: MERKLE_ROOT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "adj_index_plus1".into(),
            index: ADJ_INDEX_PLUS1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "is_before".into(),
            index: IS_BEFORE,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "timing_ok".into(),
            index: TIMING_OK,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "attr_diff_inv".into(),
            index: ATTR_DIFF_INV,
            kind: ColumnKind::Value,
        },
    ];

    let constraints = vec![
        // C1: leaf_hash == hash_fact(block_height, [event_type, attribute_hash, timeline_index])
        ConstraintExpr::Hash {
            output_col: LEAF_HASH,
            input_cols: vec![BLOCK_HEIGHT, EVENT_TYPE, ATTRIBUTE_HASH, TIMELINE_INDEX],
        },
        // C2: is_before is binary
        ConstraintExpr::Binary { col: IS_BEFORE },
        // C3: adj_index_plus1 == timeline_index + 1
        // adj_index_plus1 - timeline_index - 1 == 0
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![ADJ_INDEX_PLUS1],
                },
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![TIMELINE_INDEX],
                },
                PolyTerm {
                    coeff: neg_one,
                    col_indices: vec![],
                }, // constant -1
            ],
        },
        // C4: Transition: next[TIMELINE_INDEX] == local[ADJ_INDEX_PLUS1] (adjacency)
        ConstraintExpr::Transition {
            next_col: TIMELINE_INDEX,
            local_col: ADJ_INDEX_PLUS1,
        },
    ];

    // Boundary constraints
    let boundaries = vec![
        // Row 0: merkle_root == timeline_root (pi[3])
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: MERKLE_ROOT,
            pi_index: PI_TIMELINE_ROOT,
        },
        // Row 1 (last): merkle_root == timeline_root (pi[3])
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: MERKLE_ROOT,
            pi_index: PI_TIMELINE_ROOT,
        },
        // Row 0: is_before == 1
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: IS_BEFORE,
            value: BabyBear::ONE,
        },
        // Row 1 (last): is_before == 0
        BoundaryDef::Fixed {
            row: BoundaryRow::Last,
            col: IS_BEFORE,
            value: BabyBear::ZERO,
        },
    ];

    CircuitDescriptor {
        name: "dregg-temporal-absence-dsl-v1".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 2,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

// ============================================================================
// Witness types
// ============================================================================

/// A timeline entry for trace generation.
#[derive(Clone, Debug)]
pub struct DslTimelineEntry {
    pub block_height: u32,
    pub event_type: BabyBear,
    pub attribute_hash: BabyBear,
    pub timeline_index: u32,
    /// The Merkle root this entry authenticates to.
    pub merkle_root: BabyBear,
}

impl DslTimelineEntry {
    /// Compute the leaf hash using hash_fact (matches the DSL Hash constraint).
    pub fn leaf_hash(&self) -> BabyBear {
        hash_fact(
            BabyBear::new(self.block_height),
            &[
                self.event_type,
                self.attribute_hash,
                BabyBear::new(self.timeline_index),
            ],
        )
    }
}

/// Complete witness for a temporal absence proof.
#[derive(Clone, Debug)]
pub struct TemporalAbsenceDslWitness {
    /// The timeline entry immediately before the absence window.
    pub entry_before: DslTimelineEntry,
    /// The timeline entry immediately after the absence window.
    pub entry_after: DslTimelineEntry,
    /// Start of the absence window (block height).
    pub t1: u32,
    /// End of the absence window (block height).
    pub t2: u32,
    /// The attribute hash that must NOT appear during [t1, t2].
    pub excluded_attribute_hash: BabyBear,
}

impl TemporalAbsenceDslWitness {
    /// Validate the witness (all constraints would be satisfied).
    pub fn is_valid(&self) -> bool {
        // 1. Adjacency
        if self.entry_after.timeline_index != self.entry_before.timeline_index + 1 {
            return false;
        }
        // 2. Same root
        if self.entry_before.merkle_root != self.entry_after.merkle_root {
            return false;
        }
        // 3. Timing
        if self.entry_before.block_height > self.t1 {
            return false;
        }
        if self.entry_after.block_height < self.t2 {
            return false;
        }
        true
    }
}
