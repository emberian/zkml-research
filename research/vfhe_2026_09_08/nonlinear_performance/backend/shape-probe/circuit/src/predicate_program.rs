//! Programmable predicate compilation pipeline.
//!
//! Turns a predicate specification into the appropriate AIR proof(s).
//! This implements Stage 1 of the programmable predicates compilation pipeline
//! from `.docs-history-noclaude/programmable-predicates.md`:
//!
//! ```text
//! PredicateProgram
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Program Analyzer   │  Determine which built-ins are needed
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  AIR Selector       │  Map each built-in to its specialized AIR
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Witness Generator  │  Fill traces from private state
//! └─────────────────────┘
//!     │
//!     ▼
//! ┌─────────────────────┐
//! │  Proof Compositor   │  Compose sub-proofs into a single proof
//! └─────────────────────┘
//!     │
//!     ▼
//! PredicateProof (verifiable by anyone)
//! ```
//!
//! # Overview
//!
//! A `PredicateProgram` is a structured expression tree over leaf predicates
//! (range checks, membership, temporal continuity, relational comparisons,
//! committed thresholds) composed with boolean operators (AND, OR, NOT, Threshold).
//!
//! The compiler analyzes the program, maps each leaf to its specialized AIR,
//! and determines whether the program can be flattened into a single
//! `CompoundPredicateAir` or requires multi-AIR composition.
//!
//! # Compilation Strategy
//!
//! - **Single range leaf**: Dispatches directly to `PredicateAir`.
//! - **Multiple range leaves combined with AND/OR/Threshold**: Flattens into
//!   `CompoundPredicateAir` (up to 8 sub-predicates).
//! - **Temporal leaves**: Each becomes an independent `TemporalPredicateAir`.
//! - **Mixed AIR types or nested compositions**: Multi-AIR composition with
//!   a boolean formula over sub-proofs.

use std::collections::HashMap;

use crate::dsl::predicates::PredicateType;
use crate::dsl::predicates::RelationalOp as RelationType;
use crate::dsl::predicates::{BooleanFormula, MAX_COMPOUND_PREDICATES};
use crate::field::BabyBear;

// =============================================================================
// Program Representation
// =============================================================================

/// A predicate expression tree — the "program" that gets compiled to AIR proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PredicateExpr {
    // ─── Leaf predicates (dispatch to specific AIRs) ───
    /// Range comparison: `attribute <op> threshold`.
    /// Dispatches to `PredicateAir`.
    Range {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
    },

    /// Set membership: `attribute IN committed_set`.
    /// Dispatches to `MerklePoseidon2StarkAir`.
    Membership {
        attribute: String,
        set_commitment: BabyBear,
    },

    /// Temporal continuity: `attribute <op> threshold for min_blocks consecutive steps`.
    /// Dispatches to `TemporalPredicateAir`.
    Temporal {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
        min_blocks: u64,
    },

    /// Relational comparison between two parties' committed values.
    /// Dispatches to `RelationalPredicateAir`.
    Relational {
        my_attribute: String,
        their_commitment: BabyBear,
        relation: RelationType,
    },

    /// Private threshold comparison where the threshold is committed.
    /// Dispatches to `CommittedThresholdAir`.
    CommittedThreshold {
        attribute: String,
        threshold_commitment: BabyBear,
    },

    /// Arithmetic predicate: an expression over multiple inputs satisfies a comparison.
    /// Dispatches to `ArithmeticPredicateAir`.
    ///
    /// Example: `balance_a + balance_b >= 2000`
    Arithmetic {
        /// The attribute names that serve as inputs to the expression.
        inputs: Vec<String>,
        /// The arithmetic expression over the inputs (Var(0), Var(1), etc.).
        expression: crate::dsl::predicates::ArithExpr,
        /// The predicate to prove about the expression result.
        predicate: crate::dsl::predicates::ArithPredicate,
    },

    /// Non-membership: `attribute NOT IN property_set`.
    /// Dispatches to `AccumulatorNonMembershipAir` (generalized from non-revocation).
    ///
    /// This is the sound way to express `NOT(Membership { ... })` -- instead of
    /// trying to negate a proof (which is unsound), we use the polynomial-evaluation
    /// accumulator to directly prove non-membership.
    NonMembership {
        /// The attribute whose hash must NOT appear in the set.
        attribute: String,
        /// Identifier for the property set (domain-separated).
        set_id: BabyBear,
    },

    // ─── Negation extensions (no new AIR needed) ───
    /// Inequality: prove `attribute != value`.
    /// Compiles to `ArithmeticPredicateAir` with `ExprNeq`.
    Neq { attribute: String, value: u64 },

    /// Range exclusion: prove `value NOT IN [low, high]`.
    /// Strategy: compiles to `Or(Lt(low), Gt(high))` using existing range predicates.
    NotInRange {
        attribute: String,
        low: u64,
        high: u64,
    },

    /// Threshold below: prove that FEWER than `max_k` of the given predicates hold.
    /// Purely compositional: during proving, count how many sub-predicates succeed,
    /// reject (produce no proof) if count >= max_k. Verifier checks fewer than max_k proofs.
    ThresholdBelow {
        max_k: usize,
        predicates: Vec<PredicateExpr>,
    },

    // ─── Composition operators ───
    /// All sub-predicates must hold.
    And(Vec<PredicateExpr>),

    /// At least one sub-predicate must hold.
    Or(Vec<PredicateExpr>),

    /// The negation of a sub-predicate.
    Not(Box<PredicateExpr>),

    /// At least `k` of the given predicates must hold.
    Threshold {
        k: usize,
        predicates: Vec<PredicateExpr>,
    },
}

/// A predicate program: an expression tree with resource limits.
#[derive(Clone, Debug)]
pub struct PredicateProgram {
    /// The predicate expression to evaluate and prove.
    pub expr: PredicateExpr,
    /// Maximum nesting depth (for resource limiting).
    pub max_depth: usize,
}

impl PredicateProgram {
    /// Create a new predicate program with the given expression and depth limit.
    pub fn new(expr: PredicateExpr, max_depth: usize) -> Self {
        Self { expr, max_depth }
    }

    /// Create a predicate program with the default depth limit (8).
    pub fn with_default_depth(expr: PredicateExpr) -> Self {
        Self { expr, max_depth: 8 }
    }
}

// =============================================================================
// Compilation Output
// =============================================================================

/// The type of AIR that a leaf predicate compiles to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AirType {
    /// `PredicateAir` — single range/comparison check.
    Range,
    /// `CompoundPredicateAir` — boolean combination of range checks.
    Compound,
    /// `TemporalPredicateAir` — predicate held over N steps.
    Temporal,
    /// `RelationalPredicateAir` — two-party value comparison.
    Relational,
    /// `CommittedThresholdAir` — value >= committed threshold.
    CommittedThreshold,
    /// `MerklePoseidon2StarkAir` — set membership proof.
    Membership,
    /// `ArithmeticPredicateAir` — arithmetic expression over multiple inputs.
    Arithmetic,
    /// `AccumulatorNonMembershipAir` — accumulator-based non-membership proof.
    NonMembership,
}

/// Specification of what witness data is needed for a particular compiled sub-proof.
#[derive(Clone, Debug, PartialEq)]
pub enum WitnessSpec {
    /// Single range predicate: needs (attribute_name, predicate_type, threshold).
    Range {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
    },
    /// Temporal predicate: needs values at each step + state roots.
    Temporal {
        attribute: String,
        predicate_type: PredicateType,
        threshold: u64,
        min_blocks: u64,
    },
    /// Relational: needs my value + their commitment.
    Relational {
        my_attribute: String,
        their_commitment: BabyBear,
        relation: RelationType,
    },
    /// Committed threshold: needs my value + threshold + blinding.
    CommittedThreshold {
        attribute: String,
        threshold_commitment: BabyBear,
    },
    /// Membership: needs value + Merkle path.
    Membership {
        attribute: String,
        set_commitment: BabyBear,
    },
    /// Arithmetic: needs multiple attribute values + expression + predicate.
    Arithmetic {
        inputs: Vec<String>,
        expression: crate::dsl::predicates::ArithExpr,
        predicate: crate::dsl::predicates::ArithPredicate,
    },
    /// Non-membership: needs element hash + set parameters.
    NonMembership { attribute: String, set_id: BabyBear },
}

/// The compiled form of a predicate program — a plan for proof generation.
#[derive(Clone, Debug, PartialEq)]
pub enum CompiledPredicate {
    /// A single leaf that maps to one AIR instance.
    Single {
        air_type: AirType,
        witness_spec: WitnessSpec,
    },
    /// A compound predicate that uses `CompoundPredicateAir` to prove
    /// a boolean formula over multiple range sub-predicates in one proof.
    CompoundRange {
        /// The individual range sub-predicates (flattened from the expression tree).
        sub_predicates: Vec<WitnessSpec>,
        /// The boolean formula combining them.
        formula: BooleanFormula,
    },
    /// A multi-AIR composition: multiple independent sub-proofs combined
    /// by a boolean formula. This is used when the program mixes AIR types
    /// (e.g., range + temporal) that cannot be flattened into one AIR.
    Composite {
        sub_proofs: Vec<CompiledPredicate>,
        formula: CompositeFormula,
    },
}

/// Boolean formula for multi-AIR composition (over sub-proof results).
#[derive(Clone, Debug, PartialEq)]
pub enum CompositeFormula {
    /// All sub-proofs must verify.
    And,
    /// At least one sub-proof must verify.
    Or,
    /// At least `k` sub-proofs must verify.
    Threshold(usize),
    /// Fewer than `k` sub-proofs verify (the inverse of Threshold).
    ThresholdBelow(usize),
    /// Negate the single sub-proof's result.
    Not,
}

// =============================================================================
// Compilation Errors
// =============================================================================

/// Errors that can occur during predicate compilation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// The program exceeds the maximum allowed nesting depth.
    DepthExceeded { max: usize, actual: usize },
    /// The program has too many leaves for a compound AIR (> MAX_COMPOUND_PREDICATES).
    TooManyPredicates { max: usize, actual: usize },
    /// The program is empty (no predicates to prove).
    EmptyProgram,
    /// A NOT operator was applied to a non-single predicate (unsupported in current AIR).
    UnsupportedNot,
    /// Threshold `k` is zero or exceeds the number of predicates.
    InvalidThreshold { k: usize, n: usize },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DepthExceeded { max, actual } => {
                write!(f, "program depth {actual} exceeds maximum {max}")
            }
            Self::TooManyPredicates { max, actual } => {
                write!(f, "program has {actual} predicates, maximum is {max}")
            }
            Self::EmptyProgram => write!(f, "empty predicate program"),
            Self::UnsupportedNot => {
                write!(
                    f,
                    "NOT is not supported: requires MPC-in-the-head proof of non-satisfaction (not yet implemented). Use comparison flipping (GTE -> LT) instead."
                )
            }
            Self::InvalidThreshold { k, n } => {
                write!(f, "threshold k={k} is invalid for {n} predicates")
            }
        }
    }
}

// =============================================================================
// Compiler
// =============================================================================

/// Compile a predicate program into a proof plan.
///
/// The compiler:
/// 1. Validates depth/size limits.
/// 2. Flattens nested AND/OR into `CompoundPredicateAir` where possible
///    (when all leaves are range predicates and count <= MAX_COMPOUND_PREDICATES).
/// 3. Identifies which AIRs are needed.
/// 4. Returns a compilation plan (`CompiledPredicate`).
pub fn compile_predicate(program: &PredicateProgram) -> Result<CompiledPredicate, CompileError> {
    // Validate depth.
    let actual_depth = compute_depth(&program.expr);
    if actual_depth > program.max_depth {
        return Err(CompileError::DepthExceeded {
            max: program.max_depth,
            actual: actual_depth,
        });
    }

    compile_expr(&program.expr)
}

/// Compute the nesting depth of an expression.
fn compute_depth(expr: &PredicateExpr) -> usize {
    match expr {
        // Leaves have depth 1.
        PredicateExpr::Range { .. }
        | PredicateExpr::Membership { .. }
        | PredicateExpr::NonMembership { .. }
        | PredicateExpr::Temporal { .. }
        | PredicateExpr::Relational { .. }
        | PredicateExpr::CommittedThreshold { .. }
        | PredicateExpr::Arithmetic { .. }
        | PredicateExpr::Neq { .. }
        | PredicateExpr::NotInRange { .. } => 1,

        // Composition operators have depth = 1 + max(children).
        PredicateExpr::And(children) | PredicateExpr::Or(children) => {
            1 + children.iter().map(compute_depth).max().unwrap_or(0)
        }
        PredicateExpr::Not(inner) => 1 + compute_depth(inner),
        PredicateExpr::Threshold { predicates, .. }
        | PredicateExpr::ThresholdBelow {
            max_k: _,
            predicates,
        } => 1 + predicates.iter().map(compute_depth).max().unwrap_or(0),
    }
}

/// Compile a single expression node.
fn compile_expr(expr: &PredicateExpr) -> Result<CompiledPredicate, CompileError> {
    match expr {
        // ─── Leaf nodes ───
        PredicateExpr::Range {
            attribute,
            predicate_type,
            threshold,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Range,
            witness_spec: WitnessSpec::Range {
                attribute: attribute.clone(),
                predicate_type: *predicate_type,
                threshold: *threshold,
            },
        }),

        PredicateExpr::Membership {
            attribute,
            set_commitment,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Membership,
            witness_spec: WitnessSpec::Membership {
                attribute: attribute.clone(),
                set_commitment: *set_commitment,
            },
        }),

        PredicateExpr::Temporal {
            attribute,
            predicate_type,
            threshold,
            min_blocks,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Temporal,
            witness_spec: WitnessSpec::Temporal {
                attribute: attribute.clone(),
                predicate_type: *predicate_type,
                threshold: *threshold,
                min_blocks: *min_blocks,
            },
        }),

        PredicateExpr::Relational {
            my_attribute,
            their_commitment,
            relation,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Relational,
            witness_spec: WitnessSpec::Relational {
                my_attribute: my_attribute.clone(),
                their_commitment: *their_commitment,
                relation: *relation,
            },
        }),

        PredicateExpr::CommittedThreshold {
            attribute,
            threshold_commitment,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::CommittedThreshold,
            witness_spec: WitnessSpec::CommittedThreshold {
                attribute: attribute.clone(),
                threshold_commitment: *threshold_commitment,
            },
        }),

        PredicateExpr::Arithmetic {
            inputs,
            expression,
            predicate,
        } => Ok(CompiledPredicate::Single {
            air_type: AirType::Arithmetic,
            witness_spec: WitnessSpec::Arithmetic {
                inputs: inputs.clone(),
                expression: expression.clone(),
                predicate: predicate.clone(),
            },
        }),

        PredicateExpr::NonMembership { attribute, set_id } => Ok(CompiledPredicate::Single {
            air_type: AirType::NonMembership,
            witness_spec: WitnessSpec::NonMembership {
                attribute: attribute.clone(),
                set_id: *set_id,
            },
        }),

        // ─── Negation extensions ───
        PredicateExpr::Neq { attribute, value } => {
            // Compile as ArithmeticPredicateAir with ExprNeq.
            use crate::dsl::predicates::{ArithExpr, ArithPredicate};
            Ok(CompiledPredicate::Single {
                air_type: AirType::Arithmetic,
                witness_spec: WitnessSpec::Arithmetic {
                    inputs: vec![attribute.clone()],
                    expression: ArithExpr::Var(0),
                    predicate: ArithPredicate::ExprNeq(ArithExpr::Var(0), *value as u32),
                },
            })
        }

        PredicateExpr::NotInRange {
            attribute,
            low,
            high,
        } => {
            // Compile to Or(Lt(low), Gt(high)) — value < low OR value > high.
            // This means value is outside [low, high].
            let lt_low = PredicateExpr::Range {
                attribute: attribute.clone(),
                predicate_type: PredicateType::Lt,
                threshold: *low,
            };
            let gt_high = PredicateExpr::Range {
                attribute: attribute.clone(),
                predicate_type: PredicateType::Gt,
                threshold: *high,
            };
            compile_expr(&PredicateExpr::Or(vec![lt_low, gt_high]))
        }

        PredicateExpr::ThresholdBelow { max_k, predicates } => {
            if predicates.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            if *max_k == 0 || *max_k > predicates.len() {
                return Err(CompileError::InvalidThreshold {
                    k: *max_k,
                    n: predicates.len(),
                });
            }
            // ThresholdBelow { max_k, predicates } means "fewer than max_k hold".
            // Equivalently: at most (max_k - 1) hold.
            // We compile this as a Composite with a ThresholdBelow formula.
            let sub_proofs: Vec<CompiledPredicate> = predicates
                .iter()
                .map(compile_expr)
                .collect::<Result<Vec<_>, _>>()?;

            Ok(CompiledPredicate::Composite {
                sub_proofs,
                formula: CompositeFormula::ThresholdBelow(*max_k),
            })
        }

        // ─── AND composition ───
        PredicateExpr::And(children) => {
            if children.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            compile_boolean_composition(children, CompositeFormulaKind::And)
        }

        // ─── OR composition ───
        PredicateExpr::Or(children) => {
            if children.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            compile_boolean_composition(children, CompositeFormulaKind::Or)
        }

        // ─── NOT ───
        PredicateExpr::Not(inner) => {
            // Special case: NOT(Membership { ... }) compiles to NonMembership.
            //
            // This is the ONE case where NOT can be soundly implemented: we use the
            // polynomial-evaluation accumulator to directly prove non-membership,
            // rather than trying to negate an existential proof.
            if let PredicateExpr::Membership {
                attribute,
                set_commitment,
            } = inner.as_ref()
            {
                return Ok(CompiledPredicate::Single {
                    air_type: AirType::NonMembership,
                    witness_spec: WitnessSpec::NonMembership {
                        attribute: attribute.clone(),
                        set_id: *set_commitment,
                    },
                });
            }

            // SOUNDNESS FIX: General NOT cannot be soundly implemented in the current
            // proof system.
            //
            // The previous implementation accepted NOT(P) when the prover "failed to
            // generate a proof for P." This is UNSOUND: a malicious prover can claim
            // NOT(P) for ANY P by simply omitting the inner proof (producing empty
            // sub_proofs). The verifier would then accept based on the absence of proof.
            //
            // Correct NOT requires either:
            // 1. MPC-in-the-head proof of non-satisfaction
            // 2. A proper algebraic NOT gate (requires proving the complement)
            // 3. Flipping the comparison (GTE -> LT) at the expression level before
            //    compilation (caller's responsibility)
            //
            // Only NOT(Membership(...)) is supported (compiles to NonMembership above).
            // All other NOT forms are rejected at compile time.
            Err(CompileError::UnsupportedNot)
        }

        // ─── Threshold ───
        PredicateExpr::Threshold { k, predicates } => {
            if predicates.is_empty() {
                return Err(CompileError::EmptyProgram);
            }
            if *k == 0 || *k > predicates.len() {
                return Err(CompileError::InvalidThreshold {
                    k: *k,
                    n: predicates.len(),
                });
            }
            compile_boolean_composition(predicates, CompositeFormulaKind::Threshold(*k))
        }
    }
}

/// Internal enum for tracking which boolean composition to build.
#[derive(Clone, Debug)]
enum CompositeFormulaKind {
    And,
    Or,
    Threshold(usize),
}

/// Compile a boolean composition (AND, OR, Threshold) of child expressions.
///
/// If ALL children are range predicates and the total count fits in a single
/// `CompoundPredicateAir`, this flattens into a `CompoundRange` compilation.
/// Otherwise, it produces a `Composite` with independently compiled sub-proofs.
fn compile_boolean_composition(
    children: &[PredicateExpr],
    kind: CompositeFormulaKind,
) -> Result<CompiledPredicate, CompileError> {
    // Check if all children are range-type leaves (can flatten into CompoundPredicateAir).
    let all_range = children
        .iter()
        .all(|c| matches!(c, PredicateExpr::Range { .. }));

    if all_range && children.len() <= MAX_COMPOUND_PREDICATES {
        // Flatten into a single CompoundPredicateAir.
        let sub_predicates: Vec<WitnessSpec> = children
            .iter()
            .map(|c| match c {
                PredicateExpr::Range {
                    attribute,
                    predicate_type,
                    threshold,
                } => WitnessSpec::Range {
                    attribute: attribute.clone(),
                    predicate_type: *predicate_type,
                    threshold: *threshold,
                },
                _ => unreachable!("checked all_range above"),
            })
            .collect();

        let indices: Vec<usize> = (0..sub_predicates.len()).collect();
        let formula = match kind {
            CompositeFormulaKind::And => BooleanFormula::And(indices),
            CompositeFormulaKind::Or => BooleanFormula::Or(indices),
            CompositeFormulaKind::Threshold(k) => BooleanFormula::Threshold(k, indices),
        };

        Ok(CompiledPredicate::CompoundRange {
            sub_predicates,
            formula,
        })
    } else {
        // Mixed AIR types or too many predicates: compile each child independently.
        let sub_proofs: Vec<CompiledPredicate> = children
            .iter()
            .map(compile_expr)
            .collect::<Result<Vec<_>, _>>()?;

        let formula = match kind {
            CompositeFormulaKind::And => CompositeFormula::And,
            CompositeFormulaKind::Or => CompositeFormula::Or,
            CompositeFormulaKind::Threshold(k) => CompositeFormula::Threshold(k),
        };

        Ok(CompiledPredicate::Composite {
            sub_proofs,
            formula,
        })
    }
}

// =============================================================================
// Proof Execution
// =============================================================================

/// Errors that can occur during proof generation.
#[derive(Clone, Debug)]
pub enum ProveError {
    /// A required attribute value is missing from the private state.
    MissingAttribute(String),
    /// The predicate is not satisfiable with the given private state.
    NotSatisfiable(String),
    /// Proof generation failed (AIR constraint violation or internal error).
    ProofGenerationFailed(String),
    /// Temporal proof requires historical values not provided.
    MissingTemporalData { attribute: String, needed: u64 },
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingAttribute(name) => write!(f, "missing attribute: {name}"),
            Self::NotSatisfiable(msg) => write!(f, "not satisfiable: {msg}"),
            Self::ProofGenerationFailed(msg) => write!(f, "proof generation failed: {msg}"),
            Self::MissingTemporalData { attribute, needed } => {
                write!(
                    f,
                    "temporal proof for '{attribute}' needs {needed} historical values"
                )
            }
        }
    }
}

/// The structure of a program proof (mirrors the compiled predicate shape).
#[derive(Clone, Debug)]
pub enum ProofStructure {
    /// Single proof — just verify the sub-proof directly.
    Single,
    /// Compound range — one CompoundPredicateAir proof covers everything.
    CompoundRange,
    /// Composite — multiple sub-proofs composed with a formula.
    Composite(CompositeFormula),
}

/// Extended private state for proof generation.
///
/// Maps attribute names to their private values. For temporal predicates,
/// historical values and state roots are also provided. For relational and
/// committed-threshold predicates, counterparty values received via sealed
/// channels are included.
#[derive(Clone, Debug, Default)]
pub struct PrivateState {
    /// Current attribute values: attribute_name -> value.
    pub values: HashMap<String, u64>,
    /// Historical values for temporal predicates: attribute_name -> (values, state_roots).
    pub temporal_history: HashMap<String, (Vec<u64>, Vec<BabyBear>)>,
    /// Fact hashes for each attribute (for computing fact commitments).
    pub fact_hashes: HashMap<String, BabyBear>,
    /// Counterparty values for relational predicates, keyed by their commitment.
    /// Each entry: (their_value, their_blinding) received via OT or sealed channel.
    /// The prover also needs their own blinding for the commitment.
    pub relational_context: HashMap<String, RelationalContext>,
    /// Committed thresholds received from verifiers, keyed by the threshold commitment.
    /// Each entry: (threshold, blinding) as provided by the verifier via secure channel.
    pub committed_thresholds: HashMap<String, CommittedThresholdContext>,
    /// Non-membership contexts keyed by attribute name.
    /// Each entry provides the set elements needed to generate the accumulator witness.
    pub non_membership_context: HashMap<String, NonMembershipContext>,
}

/// Context needed to prove a relational predicate.
///
/// The prover (comparison service) must know both values and their blinding factors.
#[derive(Clone, Debug)]
pub struct RelationalContext {
    /// The prover's own blinding factor for their commitment.
    pub my_blinding: BabyBear,
    /// The counterparty's value (received via sealed channel).
    pub their_value: u64,
    /// The counterparty's blinding factor (received via sealed channel).
    pub their_blinding: BabyBear,
}

/// Context needed to prove a committed-threshold predicate.
///
/// The verifier sends the threshold and blinding to the prover via a secure channel.
#[derive(Clone, Debug)]
pub struct CommittedThresholdContext {
    /// The verifier's secret threshold.
    pub threshold: u64,
    /// The verifier's blinding randomness.
    pub blinding: BabyBear,
}

/// Context needed to prove a non-membership predicate.
///
/// The prover needs the set elements to generate the accumulator witness.
/// In production, this would come from a federation's published exclusion set.
#[derive(Clone, Debug)]
pub struct NonMembershipContext {
    /// Human-readable set name (e.g., "suspended_users", "blacklist").
    pub set_name: String,
    /// The elements in the exclusion set.
    pub set_elements: Vec<BabyBear>,
}

// =============================================================================
// Verification
// =============================================================================

// =============================================================================
// Helpers
// =============================================================================

// =============================================================================
// Tests
// =============================================================================
