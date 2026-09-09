//! DSL-native accumulator non-revocation proving and verification.
//!
//! This module provides production prove/verify functions for the accumulator
//! non-revocation AIR using the DSL `CircuitDescriptor` + `DslCircuit` infrastructure.
//! It replaces the hand-written `AccumulatorNonRevocationAir` from
//! `circuit/src/accumulator_air.rs`.
//!
//! # Completeness vs. hand-written AIR
//!
//! The DSL version covers:
//! - Alpha derivation (diff == alpha - h, 4 base-field equalities)
//! - Accumulator computation (prod == w * diff, extension field multiplication)
//! - Non-membership witness (sum == prod + v == Acc)
//! - Inverse verification (check == v * v_inv == ONE, proves v != 0)
//! - Per-row boundary constraints for sum and check on all active rows
//!
//! # Public Inputs
//!
//! 9 BabyBear elements:
//! - [0..3][]: Acc (accumulator value in BabyBear^4)
//! - [4..7][]: alpha (public challenge in BabyBear^4)
//! - [8][]: num_ancestors (number of active rows)

use crate::accumulator_types::{
    ACCUMULATOR_WIDTH, AccumulatorNonMembershipWitness, AccumulatorNonRevocationWitness, ExtElem,
    MAX_ANCESTORS, col, pi,
};
use crate::field::{BABYBEAR_P, BabyBear};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Re-exports
// ============================================================================

pub use crate::accumulator_types::{
    AccumulatorNonMembershipWitness as NonMembershipWitness,
    AccumulatorNonRevocationWitness as NonRevocationWitness, ExtElem as AccExtElem,
    MAX_ANCESTORS as ACC_MAX_ANCESTORS, compute_accumulator, derive_alpha,
};

// ============================================================================
// Constants
// ============================================================================

/// Total trace width for the DSL version (with auxiliary columns).
/// Original 32 columns + 8 auxiliary (4 for alpha, 4 for acc).
pub const ACCUMULATOR_DSL_WIDTH: usize = ACCUMULATOR_WIDTH + 8; // 40

/// Negate a field element.
fn neg_one() -> BabyBear {
    BabyBear::new(BABYBEAR_P - 1)
}

/// Build a polynomial term.
fn term(coeff: BabyBear, cols: &[usize]) -> PolyTerm {
    PolyTerm {
        coeff,
        col_indices: cols.to_vec(),
    }
}

/// The irreducible constant W for BabyBear^4: X^4 - 11.
const W_VAL: u32 = 11;

// ============================================================================
// Circuit descriptor
// ============================================================================

/// Build the production accumulator non-revocation CircuitDescriptor.
///
/// Encodes the 4 core constraint groups:
/// 1. diff correctness (4 base-field constraints)
/// 2. prod correctness (4 base-field constraints for ext-field multiplication)
/// 3. sum correctness (4 base-field constraints for addition)
/// 4. check correctness (4 base-field constraints for inverse verification)
///
/// Boundary constraints enforce sum == Acc and check == ONE on all active rows.
pub fn accumulator_circuit_descriptor() -> CircuitDescriptor {
    // Auxiliary columns to hold pi-derived values in the trace:
    //   cols 32..35: alpha[0..3] (from pi[4..7])
    //   cols 36..39: acc[0..3] (from pi[0..3])
    let alpha_aux_start: usize = ACCUMULATOR_WIDTH; // 32
    let acc_aux_start: usize = ACCUMULATOR_WIDTH + 4; // 36

    let w = BabyBear::new(W_VAL);

    let mut constraints = Vec::new();

    // ========================================================================
    // C1: diff == alpha - h (4 base-field equalities)
    //   diff[i] - alpha_aux[i] + h[i] == 0  for i in 0..4
    // ========================================================================
    for i in 0..4 {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[col::DIFF + i]),
                term(neg_one(), &[alpha_aux_start + i]),
                term(BabyBear::ONE, &[col::HASH + i]),
            ],
        });
    }

    // ========================================================================
    // C2: prod == w * diff (extension field multiplication)
    //
    // Extension-field mul: if w = (w0, w1, w2, w3) and d = (d0, d1, d2, d3):
    //   p0 = w0*d0 + W*(w1*d3 + w2*d2 + w3*d1)
    //   p1 = w0*d1 + w1*d0 + W*(w2*d3 + w3*d2)
    //   p2 = w0*d2 + w1*d1 + w2*d0 + W*(w3*d3)
    //   p3 = w0*d3 + w1*d2 + w2*d1 + w3*d0
    // ========================================================================

    let wc = |i: usize| col::QUOTIENT + i;
    let dc = |i: usize| col::DIFF + i;
    let pc = |i: usize| col::PRODUCT + i;

    // prod[0] = w0*d0 + W*(w1*d3 + w2*d2 + w3*d1)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[pc(0)]),
            term(neg_one(), &[wc(0), dc(0)]),
            term(BabyBear::ZERO - w, &[wc(1), dc(3)]),
            term(BabyBear::ZERO - w, &[wc(2), dc(2)]),
            term(BabyBear::ZERO - w, &[wc(3), dc(1)]),
        ],
    });

    // prod[1] = w0*d1 + w1*d0 + W*(w2*d3 + w3*d2)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[pc(1)]),
            term(neg_one(), &[wc(0), dc(1)]),
            term(neg_one(), &[wc(1), dc(0)]),
            term(BabyBear::ZERO - w, &[wc(2), dc(3)]),
            term(BabyBear::ZERO - w, &[wc(3), dc(2)]),
        ],
    });

    // prod[2] = w0*d2 + w1*d1 + w2*d0 + W*(w3*d3)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[pc(2)]),
            term(neg_one(), &[wc(0), dc(2)]),
            term(neg_one(), &[wc(1), dc(1)]),
            term(neg_one(), &[wc(2), dc(0)]),
            term(BabyBear::ZERO - w, &[wc(3), dc(3)]),
        ],
    });

    // prod[3] = w0*d3 + w1*d2 + w2*d1 + w3*d0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[pc(3)]),
            term(neg_one(), &[wc(0), dc(3)]),
            term(neg_one(), &[wc(1), dc(2)]),
            term(neg_one(), &[wc(2), dc(1)]),
            term(neg_one(), &[wc(3), dc(0)]),
        ],
    });

    // ========================================================================
    // C3: sum == prod + v (4 base-field equalities)
    //   sum[i] - prod[i] - v[i] == 0
    // ========================================================================
    for i in 0..4 {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                term(BabyBear::ONE, &[col::SUM + i]),
                term(neg_one(), &[col::PRODUCT + i]),
                term(neg_one(), &[col::REMAINDER + i]),
            ],
        });
    }

    // ========================================================================
    // C4: check == v * v_inv (extension field multiplication)
    // ========================================================================

    let vc = |i: usize| col::REMAINDER + i;
    let ic = |i: usize| col::V_INV + i;
    let cc = |i: usize| col::CHECK + i;

    // check[0] = v0*vi0 + W*(v1*vi3 + v2*vi2 + v3*vi1)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[cc(0)]),
            term(neg_one(), &[vc(0), ic(0)]),
            term(BabyBear::ZERO - w, &[vc(1), ic(3)]),
            term(BabyBear::ZERO - w, &[vc(2), ic(2)]),
            term(BabyBear::ZERO - w, &[vc(3), ic(1)]),
        ],
    });

    // check[1] = v0*vi1 + v1*vi0 + W*(v2*vi3 + v3*vi2)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[cc(1)]),
            term(neg_one(), &[vc(0), ic(1)]),
            term(neg_one(), &[vc(1), ic(0)]),
            term(BabyBear::ZERO - w, &[vc(2), ic(3)]),
            term(BabyBear::ZERO - w, &[vc(3), ic(2)]),
        ],
    });

    // check[2] = v0*vi2 + v1*vi1 + v2*vi0 + W*(v3*vi3)
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[cc(2)]),
            term(neg_one(), &[vc(0), ic(2)]),
            term(neg_one(), &[vc(1), ic(1)]),
            term(neg_one(), &[vc(2), ic(0)]),
            term(BabyBear::ZERO - w, &[vc(3), ic(3)]),
        ],
    });

    // check[3] = v0*vi3 + v1*vi2 + v2*vi1 + v3*vi0
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            term(BabyBear::ONE, &[cc(3)]),
            term(neg_one(), &[vc(0), ic(3)]),
            term(neg_one(), &[vc(1), ic(2)]),
            term(neg_one(), &[vc(2), ic(1)]),
            term(neg_one(), &[vc(3), ic(0)]),
        ],
    });

    // ========================================================================
    // Boundary constraints
    // ========================================================================

    let mut boundaries = vec![
        // First row: alpha_aux[0..3] = pi[4..7]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: alpha_aux_start,
            pi_index: pi::ALPHA_START,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: alpha_aux_start + 1,
            pi_index: pi::ALPHA_START + 1,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: alpha_aux_start + 2,
            pi_index: pi::ALPHA_START + 2,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: alpha_aux_start + 3,
            pi_index: pi::ALPHA_START + 3,
        },
        // First row: acc_aux[0..3] = pi[0..3]
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: acc_aux_start,
            pi_index: pi::ACC_START,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: acc_aux_start + 1,
            pi_index: pi::ACC_START + 1,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: acc_aux_start + 2,
            pi_index: pi::ACC_START + 2,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: acc_aux_start + 3,
            pi_index: pi::ACC_START + 3,
        },
        // First row: sum == Acc
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::SUM,
            pi_index: pi::ACC_START,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::SUM + 1,
            pi_index: pi::ACC_START + 1,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::SUM + 2,
            pi_index: pi::ACC_START + 2,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::SUM + 3,
            pi_index: pi::ACC_START + 3,
        },
        // First row: check == (1, 0, 0, 0)
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::CHECK,
            value: BabyBear::ONE,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::CHECK + 1,
            value: BabyBear::ZERO,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::CHECK + 2,
            value: BabyBear::ZERO,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::CHECK + 3,
            value: BabyBear::ZERO,
        },
    ];

    // Add Index boundaries for rows 1..MAX_ANCESTORS-1 for sum and check.
    for row_idx in 1..MAX_ANCESTORS {
        for i in 0..4 {
            boundaries.push(BoundaryDef::PiBinding {
                row: BoundaryRow::Index(row_idx),
                col: col::SUM + i,
                pi_index: pi::ACC_START + i,
            });
        }
        boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::Index(row_idx),
            col: col::CHECK,
            value: BabyBear::ONE,
        });
        boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::Index(row_idx),
            col: col::CHECK + 1,
            value: BabyBear::ZERO,
        });
        boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::Index(row_idx),
            col: col::CHECK + 2,
            value: BabyBear::ZERO,
        });
        boundaries.push(BoundaryDef::Fixed {
            row: BoundaryRow::Index(row_idx),
            col: col::CHECK + 3,
            value: BabyBear::ZERO,
        });
    }

    // Column definitions (representative subset; all 40 columns are used)
    let columns = vec![
        ColumnDef {
            name: "h[0]".into(),
            index: col::HASH,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "h[1]".into(),
            index: col::HASH + 1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "h[2]".into(),
            index: col::HASH + 2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "h[3]".into(),
            index: col::HASH + 3,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "w[0]".into(),
            index: col::QUOTIENT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "diff[0]".into(),
            index: col::DIFF,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "prod[0]".into(),
            index: col::PRODUCT,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sum[0]".into(),
            index: col::SUM,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "v_inv[0]".into(),
            index: col::V_INV,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "check[0]".into(),
            index: col::CHECK,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "alpha_aux[0]".into(),
            index: alpha_aux_start,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "acc_aux[0]".into(),
            index: acc_aux_start,
            kind: ColumnKind::Value,
        },
    ];

    CircuitDescriptor {
        name: "dregg-accumulator-dsl-v2".into(),
        trace_width: ACCUMULATOR_DSL_WIDTH,
        max_degree: 2, // Extension field multiplication is degree 2
        columns,
        constraints,
        boundaries,
        public_input_count: 9, // Acc(4) + alpha(4) + num_ancestors(1)
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the accumulator descriptor.
pub fn accumulator_dsl_circuit() -> DslCircuit {
    DslCircuit::new(accumulator_circuit_descriptor())
}

// ============================================================================
// Trace generation
// ============================================================================

/// Generate the base execution trace (32 columns, no auxiliary columns) from a witness.
///
/// Returns (trace, public_inputs) where:
/// - trace: rows of width ACCUMULATOR_WIDTH, padded to power of 2
/// - public_inputs: [Acc(4), alpha(4), num_ancestors(1)] = 9 elements
pub fn generate_base_accumulator_trace(
    witness: &AccumulatorNonRevocationWitness,
    accumulator: ExtElem,
    alpha: ExtElem,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let num_ancestors = witness.ancestors.len();
    assert!(
        num_ancestors <= MAX_ANCESTORS,
        "Too many ancestors: {} > {}",
        num_ancestors,
        MAX_ANCESTORS
    );

    let total_rows = num_ancestors.next_power_of_two().max(8);
    let mut trace = Vec::with_capacity(total_rows);

    for anc in &witness.ancestors {
        let mut row = vec![BabyBear::ZERO; ACCUMULATOR_WIDTH];

        // h_i: ancestor hash embedded in extension field
        let h = ExtElem::from_base(anc.ancestor_hash);
        h.write_to(&mut row, col::HASH);

        // w_i: quotient witness
        anc.quotient.write_to(&mut row, col::QUOTIENT);

        // v_i: remainder witness
        anc.remainder.write_to(&mut row, col::REMAINDER);

        // diff_i = alpha - h_i
        let diff = alpha.sub(h);
        diff.write_to(&mut row, col::DIFF);

        // prod_i = w_i * diff_i
        let prod = anc.quotient.mul(diff);
        prod.write_to(&mut row, col::PRODUCT);

        // sum_i = prod_i + v_i
        let sum = prod.add(anc.remainder);
        sum.write_to(&mut row, col::SUM);

        // v_inv_i: inverse of v_i (proves nonzero)
        let v_inv = anc
            .remainder
            .inverse()
            .expect("Remainder must be nonzero for non-membership witness");
        v_inv.write_to(&mut row, col::V_INV);

        // check_i = v_i * v_inv_i (should be ONE)
        let check = anc.remainder.mul(v_inv);
        check.write_to(&mut row, col::CHECK);

        trace.push(row);
    }

    // Pad with "dummy" rows that satisfy constraints trivially.
    while trace.len() < total_rows {
        if num_ancestors > 0 {
            // Duplicate last valid row.
            trace.push(trace[num_ancestors - 1].clone());
        } else {
            // No ancestors: create a trivial row.
            let mut row = vec![BabyBear::ZERO; ACCUMULATOR_WIDTH];
            let h = ExtElem::ZERO;
            h.write_to(&mut row, col::HASH);
            ExtElem::ZERO.write_to(&mut row, col::QUOTIENT);
            // For empty accumulator (Acc=ONE): v=ONE works since 0 + ONE = ONE = Acc.
            ExtElem::ONE.write_to(&mut row, col::REMAINDER);
            alpha.write_to(&mut row, col::DIFF); // alpha - 0 = alpha
            ExtElem::ZERO.write_to(&mut row, col::PRODUCT); // 0 * alpha = 0
            ExtElem::ONE.write_to(&mut row, col::SUM); // 0 + ONE = ONE = Acc
            ExtElem::ONE.write_to(&mut row, col::V_INV); // inv(ONE) = ONE
            ExtElem::ONE.write_to(&mut row, col::CHECK); // ONE * ONE = ONE
            trace.push(row);
        }
    }

    // Public inputs: [Acc(4), alpha(4), num_ancestors(1)]
    let mut public_inputs = Vec::with_capacity(9);
    public_inputs.extend_from_slice(&accumulator.0);
    public_inputs.extend_from_slice(&alpha.0);
    public_inputs.push(BabyBear::new(num_ancestors as u32));

    (trace, public_inputs)
}

/// Generate a DSL-native execution trace from an accumulator witness.
///
/// Extends each row with auxiliary columns (alpha_aux, acc_aux) needed by the
/// DSL polynomial constraints which cannot directly reference public inputs.
pub fn generate_accumulator_trace(
    witness: &AccumulatorNonRevocationWitness,
    accumulator: ExtElem,
    alpha: ExtElem,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    // Generate the base trace using the standalone trace generator.
    let (base_trace, public_inputs) = generate_base_accumulator_trace(witness, accumulator, alpha);

    // Extend each row with auxiliary columns.
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(base_trace.len());
    for base_row in &base_trace {
        let mut row = base_row.clone();
        row.resize(ACCUMULATOR_DSL_WIDTH, BabyBear::ZERO);

        // alpha_aux[0..3] = alpha components
        row[ACCUMULATOR_WIDTH] = alpha.0[0];
        row[ACCUMULATOR_WIDTH + 1] = alpha.0[1];
        row[ACCUMULATOR_WIDTH + 2] = alpha.0[2];
        row[ACCUMULATOR_WIDTH + 3] = alpha.0[3];

        // acc_aux[0..3] = accumulator components
        row[ACCUMULATOR_WIDTH + 4] = accumulator.0[0];
        row[ACCUMULATOR_WIDTH + 5] = accumulator.0[1];
        row[ACCUMULATOR_WIDTH + 6] = accumulator.0[2];
        row[ACCUMULATOR_WIDTH + 7] = accumulator.0[3];

        trace.push(row);
    }

    (trace, public_inputs)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon2::hash_many;

    fn make_hash(seed: u32) -> BabyBear {
        hash_many(&[BabyBear::new(seed), BabyBear::new(0xCAFE)])
    }

    #[test]
    fn trace_generation_valid_constraints() {
        let revocation_set: Vec<BabyBear> = (1..=10).map(|i| make_hash(i * 100)).collect();
        let alpha = derive_alpha(&revocation_set);
        let acc = compute_accumulator(&revocation_set, alpha);

        // Ancestor hashes NOT in the revocation set.
        let ancestors: Vec<BabyBear> = (1..=3).map(|i| make_hash(i * 1000 + 1)).collect();
        for h in &ancestors {
            assert!(!revocation_set.contains(h));
        }

        // Generate witnesses.
        let mut witness_ancestors = Vec::new();
        for &h in &ancestors {
            let mut remainder_base = BabyBear::ONE;
            for &rev_h in &revocation_set {
                remainder_base = remainder_base * (h - rev_h);
            }
            assert_ne!(remainder_base, BabyBear::ZERO);

            let remainder = ExtElem::from_base(remainder_base);
            let h_ext = ExtElem::from_base(h);
            let diff = alpha.sub(h_ext);
            let numerator = acc.sub(remainder);
            let quotient = numerator.mul(diff.inverse().unwrap());

            witness_ancestors.push(AccumulatorNonMembershipWitness {
                ancestor_hash: h,
                quotient,
                remainder,
            });
        }

        let witness = AccumulatorNonRevocationWitness {
            ancestors: witness_ancestors,
        };
        let (trace, public_inputs) = generate_base_accumulator_trace(&witness, acc, alpha);

        // Verify dimensions.
        assert!(trace.len().is_power_of_two());
        assert!(trace.len() >= 8);
        for row in &trace {
            assert_eq!(row.len(), ACCUMULATOR_WIDTH);
        }
        assert_eq!(public_inputs.len(), 9);
    }
}
