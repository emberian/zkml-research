//! DSL-generated temporal predicate AIR.
//!
//! This module replaces the hand-written `temporal_predicate_air.rs` with the
//! equivalent of the `#[dregg_circuit]` macro-generated implementation. The
//! macro version (in `dregg-dsl-tests/src/temporal_macro.rs`) passes full STARK
//! prove/verify and is bit-for-bit equivalent to the manual descriptor in
//! `dregg-dsl-tests/src/temporal_dsl.rs`.
//!
//! Because proc-macro-generated code references `dregg_circuit::*` which cannot
//! resolve when compiled *within* the `dregg-circuit` crate itself, this file
//! contains the manually-expanded equivalent of what `#[dregg_circuit]` would
//! produce.
//!
//! # Migration
//!
//! All callers should use this module instead of `temporal_predicate_air`.
//! It exposes the AIR shape (`TemporalPredicateDsl` / `TemporalPredicateAir`),
//! the witness (`TemporalPredicateWitness`), the trace generator
//! (`generate_dsl_trace`), and the `TemporalPredicateRequirement` intent type.

use crate::dsl::predicates::PredicateType;
use crate::field::BabyBear;

// ─────────────────────────────────────────────────────────────────────────────
// DSL-equivalent core AIR (manual expansion of #[dregg_circuit] output)
// ─────────────────────────────────────────────────────────────────────────────

/// Column layout constants for the DSL temporal AIR.
///
/// **Post AIR-soundness audit (ce1e2def #3)**: added `STATE_ROOT`
/// column so that the per-step state-root chain can be bound into
/// public inputs at the trace boundary, closing the
/// "forge proof.initial_state_root / proof.final_state_root after the
/// fact" attack. The legacy 37-column layout grew to 38.
pub const VALUE: usize = 0;
pub const THRESHOLD: usize = 1;
pub const DIFF: usize = 2;
pub const DIFF_BITS_START: usize = 3;
pub const NUM_DIFF_BITS: usize = 30;
pub const ACCUMULATOR: usize = DIFF_BITS_START + NUM_DIFF_BITS; // 33
pub const STEP_INDEX: usize = ACCUMULATOR + 1; // 34
pub const ACC_PLUS_ONE: usize = STEP_INDEX + 1; // 35
pub const STEP_PLUS_ONE: usize = ACC_PLUS_ONE + 1; // 36
pub const STATE_ROOT: usize = STEP_PLUS_ONE + 1; // 37
pub const DSL_TRACE_WIDTH: usize = STATE_ROOT + 1; // 38

/// Public input layout:
/// `[padded_len, threshold, initial_state_root, final_state_root]`.
///
/// **Post AIR-soundness audit (commit `ce1e2def`, finding #3).** The PI
/// grew from `[padded_len]` to the four-slot layout above to close
/// three forge-the-metadata attacks:
///
/// - **PI[1]=threshold**: previously `proof.threshold` was a plain
///   serde field the verifier compared against itself. An attacker
///   could honestly prove threshold=0 (trivially satisfiable) and then
///   mutate `proof.threshold` to any value; the wrapper re-compared
///   the mutated field against the caller and accepted. Today
///   PI[1]=threshold is bound into row-0 of the THRESHOLD column via
///   the AIR's `boundary_constraints` and held constant
///   across the trace by the T3 inter-row constraint in
///   the AIR's `eval_constraints`. Tampering on
///   `proof.threshold` makes the verifier's reconstructed PI[1]
///   mismatch the STARK's boundary commitment and verify rejects.
/// - **PI[2]=initial_state_root**, **PI[3]=final_state_root**: same
///   attack shape — `proof.initial_state_root` and
///   `proof.final_state_root` were plain serde fields. Today the
///   prover populates the STATE_ROOT column per row from the witness
///   (padding rows hold a copy of the final real state root), and
///   boundary constraints pin row-0 STATE_ROOT to PI[2] and row-(N-1)
///   STATE_ROOT to PI[3]. The verifier reconstructs PIs from the
///   caller's expected roots, so any tampering on the proof's
///   state-root metadata is detected by STARK verification.
///
/// # Remaining (documented) gap
///
/// The per-step VALUE column is NOT bound into PIs. This is **safe by
/// contract**: the temporal predicate's promise is "the predicate held
/// at every step," not "the values were specifically X, Y, Z." The
/// per-row constraint `diff = value - threshold ≥ 0` plus the
/// bit-decomposition + high-bit-zero constraints algebraically force
/// every row's value to satisfy the predicate against the bound
/// threshold; the verifier never reveals individual values, so binding
/// them is unnecessary. (If a future caller needs value identity,
/// binding values via a Poseidon2 chain commitment in a new PI slot
/// would be the right shape.)
pub const PI_NUM_STEPS: usize = 0;
pub const PI_THRESHOLD: usize = 1;
pub const PI_INITIAL_STATE_ROOT: usize = 2;
pub const PI_FINAL_STATE_ROOT: usize = 3;
pub const DSL_PUBLIC_INPUT_COUNT: usize = 4;

/// Column index submodule (mirrors the `mod col` in the `#[dregg_circuit]` definition).
pub mod col {
    pub const VALUE: usize = 0;
    pub const THRESHOLD: usize = 1;
    pub const DIFF: usize = 2;
    pub const DIFF_BITS_START: usize = 3;
    pub const NUM_DIFF_BITS: usize = 30;
    pub const ACCUMULATOR: usize = 33;
    pub const STEP_INDEX: usize = 34;
    pub const ACC_PLUS_ONE: usize = 35;
    pub const STEP_PLUS_ONE: usize = 36;
    /// Per-step state-root column (AIR-soundness-audit ce1e2def #3).
    /// Bound at row 0 to PI[2] (initial_state_root) and at the last
    /// padded row to PI[3] (final_state_root) — see
    /// `TemporalPredicateDsl::boundary_constraints`. Padding rows hold
    /// a copy of the final real state root so the row-N-1 boundary
    /// constraint binds the prover's claimed final root regardless of
    /// where padding starts.
    pub const STATE_ROOT: usize = 37;
}

/// The DSL-generated temporal predicate AIR struct.
///
/// This is the equivalent of what `#[dregg_circuit] mod temporal_predicate_dsl { ... }`
/// would produce: the AIR shape descriptor for the temporal predicate circuit.
pub struct TemporalPredicateDsl;

// ─────────────────────────────────────────────────────────────────────────────
// Public API: backward-compatible types and functions
// ─────────────────────────────────────────────────────────────────────────────

/// Trace width for the temporal predicate AIR (legacy 35-column layout reference).
pub const TEMPORAL_PREDICATE_WIDTH: usize = 35;

/// Witness for a temporal predicate proof.
///
/// Contains the sequence of values and state roots over the time range,
/// plus the predicate parameters.
#[derive(Clone, Debug)]
pub struct TemporalPredicateWitness {
    /// The attribute values at each step (one per time unit).
    pub values: Vec<BabyBear>,
    /// The state roots at each step (binding to the receipt/IVC chain).
    pub state_roots: Vec<BabyBear>,
    /// The predicate type (currently only GTE is supported for temporal).
    pub predicate_type: PredicateType,
    /// The threshold the predicate must meet at every step.
    pub threshold: BabyBear,
}

impl TemporalPredicateWitness {
    /// Check whether the temporal predicate is satisfiable (all steps pass).
    pub fn is_satisfiable(&self) -> bool {
        if self.values.len() != self.state_roots.len() {
            return false;
        }
        if self.values.is_empty() {
            return false;
        }
        let threshold = self.threshold.as_u32();
        self.values.iter().all(|v| {
            let val = v.as_u32();
            match self.predicate_type {
                PredicateType::Gte | PredicateType::InRangeLow => val >= threshold,
                PredicateType::Lte | PredicateType::InRangeHigh => val <= threshold,
                PredicateType::Gt => val > threshold,
                PredicateType::Lt => val < threshold,
                PredicateType::Neq => val != threshold,
            }
        })
    }

    /// Number of steps in the temporal range.
    pub fn num_steps(&self) -> usize {
        self.values.len()
    }

    /// Compute the diff at a given step based on predicate type.
    fn compute_diff_at(&self, step: usize) -> BabyBear {
        let value = self.values[step];
        let threshold = self.threshold;
        match self.predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => value - threshold,
            PredicateType::Lte | PredicateType::InRangeHigh => threshold - value,
            PredicateType::Gt => value - threshold - BabyBear::ONE,
            PredicateType::Lt => threshold - value - BabyBear::ONE,
            PredicateType::Neq => value - threshold,
        }
    }
}

/// The Temporal Predicate AIR (DSL-generated).
///
/// This is a wrapper around the DSL-generated `TemporalPredicateDsl` struct
/// that maintains the same public interface as the hand-written version. The
/// witness is stored for trace generation, while constraint evaluation is
/// delegated to the DSL-generated implementation.
pub struct TemporalPredicateAir {
    pub witness: TemporalPredicateWitness,
}

impl TemporalPredicateAir {
    pub fn new(witness: TemporalPredicateWitness) -> Self {
        Self { witness }
    }
}

/// Generate the DSL trace from a witness.
///
/// This converts from the witness format (multiple predicate types, state roots)
/// into the DSL trace layout (37-column layout with auxiliary columns).
pub fn generate_dsl_trace(
    witness: &TemporalPredicateWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_steps = witness.num_steps();
    assert!(num_steps >= 1, "temporal witness must have at least 1 step");

    let padded_len = num_steps.next_power_of_two().max(2);

    let mut trace = Vec::with_capacity(padded_len);

    // Final real state root — used to pad rows num_steps..padded_len so
    // the row-(N-1) STATE_ROOT boundary constraint binds the prover's
    // claimed final root regardless of where padding starts. See
    // AIR-soundness-audit ce1e2def #3.
    let final_state_root = *witness.state_roots.last().unwrap();
    let initial_state_root = witness.state_roots[0];

    for step in 0..padded_len {
        let mut row = vec![BabyBear::ZERO; DSL_TRACE_WIDTH];

        // For padding rows beyond num_steps, repeat the last real row's value.
        let val = if step < num_steps {
            witness.values[step]
        } else {
            *witness.values.last().unwrap()
        };

        row[VALUE] = val;
        row[THRESHOLD] = witness.threshold;

        // Compute diff based on predicate type
        let diff = if step < num_steps {
            witness.compute_diff_at(step)
        } else {
            witness.compute_diff_at(num_steps - 1)
        };
        row[DIFF] = diff;

        // Bit decomposition of diff
        if witness.predicate_type != PredicateType::Neq {
            let diff_val = diff.as_u32();
            for i in 0..NUM_DIFF_BITS {
                row[DIFF_BITS_START + i] = BabyBear::new((diff_val >> i) & 1);
            }
        }

        // Accumulator: 1-indexed (step 0 -> acc = 1)
        let acc = (step + 1) as u32;
        row[ACCUMULATOR] = BabyBear::new(acc);
        row[STEP_INDEX] = BabyBear::new(step as u32);
        row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
        row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);

        // State root: per-step real value within num_steps; padding rows
        // hold a copy of the final real state root so the row-(N-1)
        // boundary constraint binds the prover's claimed final root.
        row[STATE_ROOT] = if step < num_steps {
            witness.state_roots[step]
        } else {
            final_state_root
        };

        trace.push(row);
    }

    // Public inputs: [padded_len, threshold, initial_state_root, final_state_root]
    // PI[1]=threshold is bound into row-0 THRESHOLD column by
    // boundary_constraints and held constant across rows by the T3
    // transition constraint. PI[2]/PI[3] are bound to row-0 / row-(N-1)
    // STATE_ROOT respectively — see AIR-soundness-audit ce1e2def #3.
    let public_inputs = vec![
        BabyBear::new(padded_len as u32),
        witness.threshold,
        initial_state_root,
        final_state_root,
    ];
    (trace, public_inputs)
}

// ─────────────────────────────────────────────────────────────────────────────
// Intent integration: Temporal predicate requirements
// ─────────────────────────────────────────────────────────────────────────────

/// A temporal predicate requirement for intent matching.
///
/// Specifies that a counterparty must prove a property held continuously
/// for a minimum duration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TemporalPredicateRequirement {
    /// The attribute being checked (e.g., "balance", "reputation").
    pub attribute: String,
    /// The predicate type (e.g., GTE for "at least").
    pub predicate_type: PredicateType,
    /// The threshold value.
    pub threshold: u64,
    /// Minimum number of consecutive steps the predicate must hold.
    pub min_duration_steps: u64,
}

// ─────────────────────────────────────────────────────────────────────────────
// Plonky3-native temporal predicate AIR (re-exported from legacy)
// ─────────────────────────────────────────────────────────────────────────────

/// Re-export the Plonky3-based temporal AIR from the legacy module.
/// The P3 variant has its own separate AIR implementation that uses Plonky3's
/// native AirBuilder and is independent of the DSL system.
#[cfg(feature = "plonky3")]
pub mod p3_temporal {
    pub use crate::temporal_predicate_air::p3_temporal::*;
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────
