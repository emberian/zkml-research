//! Quantified FOR-ALL NOT proofs: "for all X in S, P(X) does not hold".
//!
//! Column layouts, widths, and the set-commitment / alpha-challenge helpers for
//! the quantified-absence circuits. Two AIR shapes are described by the column
//! modules here:
//!
//! - **Per-chunk absence** ([`chunk_col`], [`CHUNK_ABSENCE_WIDTH`]): each row
//!   proves one element does NOT satisfy the predicate; chunks chain via a
//!   running hash accumulator.
//! - **Quotient accumulator** ([`qacc_col`], [`QUOTIENT_ACC_WIDTH`]): proves
//!   `Acc_satisfying == ONE` (the set of elements satisfying P is empty) via a
//!   polynomial-quotient witness in the BabyBear^4 extension field.

use crate::accumulator_types::ExtElem;
use crate::field::BabyBear;
use crate::poseidon2::hash_many;

// ═══════════════════════════════════════════════════════════════════════════════
// Approach A: IVC-chained per-chunk absence STARKs
// ═══════════════════════════════════════════════════════════════════════════════

/// Default chunk size for the IVC approach.
pub const DEFAULT_ABSENCE_CHUNK_SIZE: usize = 16;

/// Width of the per-chunk absence AIR trace.
///
/// Columns: [element, predicate_result, element_hash, chunk_acc_hash]
///
/// Each row proves that one element does NOT satisfy the predicate.
pub const CHUNK_ABSENCE_WIDTH: usize = 4;

/// Column indices for the chunk absence AIR.
pub mod chunk_col {
    /// The element being tested.
    pub const ELEMENT: usize = 0;
    /// The predicate evaluation result (must be 0 for absence).
    pub const PREDICATE_RESULT: usize = 1;
    /// Hash of the element (for set commitment binding).
    pub const ELEMENT_HASH: usize = 2;
    /// Running accumulator hash over processed elements.
    pub const CHUNK_ACC: usize = 3;
}

/// A predicate function over field elements.
/// Returns a nonzero value if the predicate holds, zero if it does not.
pub type PredicateFn = fn(BabyBear) -> BabyBear;

// ═══════════════════════════════════════════════════════════════════════════════
// Approach B: Certified complement accumulator (polynomial quotient)
// ═══════════════════════════════════════════════════════════════════════════════

/// Width of the quotient accumulator AIR.
///
/// Columns: element(4) + quotient(4) + remainder(4) + diff(4) + product(4) + sum(4) = 24
/// (Operating in BabyBear^4 extension field for 124-bit security.)
pub const QUOTIENT_ACC_WIDTH: usize = 24;

/// Column groups for the quotient accumulator AIR.
pub mod qacc_col {
    /// Element hash embedded in BabyBear^4: cols 0..3.
    pub const ELEMENT: usize = 0;
    /// Quotient witness w: cols 4..7.
    pub const QUOTIENT: usize = 4;
    /// Remainder witness v: cols 8..11. Must equal Acc_complement evaluated at element.
    pub const REMAINDER: usize = 8;
    /// Difference (alpha - element): cols 12..15.
    pub const DIFF: usize = 12;
    /// Product w * diff: cols 16..19.
    pub const PRODUCT: usize = 16;
    /// Sum prod + v (should equal Acc_complement): cols 20..23.
    pub const SUM: usize = 20;
}

/// Helper trait extension for ExtElem to read from a slice.
impl ExtElem {
    /// Read from a slice of BabyBear values.
    pub fn read_from_slice(slice: &[BabyBear]) -> Self {
        Self([slice[0], slice[1], slice[2], slice[3]])
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════════════════════

/// Compute a commitment to a set of elements.
pub fn compute_set_commitment(elements: &[BabyBear]) -> BabyBear {
    if elements.is_empty() {
        return BabyBear::ZERO;
    }
    let mut acc = BabyBear::new(0x53455400); // "SET\0" domain
    for &elem in elements {
        acc = hash_many(&[acc, elem]);
    }
    acc
}

/// Derive the alpha challenge for the absence proof.
/// Binds to the element set and predicate identity.
pub fn derive_alpha_for_absence(element_hashes: &[BabyBear], predicate_id: BabyBear) -> ExtElem {
    // Domain separator incorporating predicate_id
    let domain = hash_many(&[
        BabyBear::new(0x41425300), // "ABS\0"
        predicate_id,
        BabyBear::new(element_hashes.len() as u32),
    ]);

    let binding = if element_hashes.is_empty() {
        domain
    } else {
        let sample_count = element_hashes.len().min(16);
        let mut elems = vec![domain];
        for &h in &element_hashes[..sample_count] {
            elems.push(h);
        }
        hash_many(&elems)
    };

    let h0 = binding;
    let h1 = hash_many(&[h0, BabyBear::new(1)]);
    let h2 = hash_many(&[h0, BabyBear::new(2)]);
    let h3 = hash_many(&[h0, BabyBear::new(3)]);

    ExtElem([h0, h1, h2, h3])
}

/// Helper: write ExtElem to a trace row at offset.
impl ExtElem {
    pub fn write_to_row(&self, row: &mut [BabyBear], offset: usize) {
        row[offset] = self.0[0];
        row[offset + 1] = self.0[1];
        row[offset + 2] = self.0[2];
        row[offset + 3] = self.0[3];
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_commitment_deterministic() {
        let elements: Vec<BabyBear> = (1..=10).map(BabyBear::new).collect();
        let c1 = compute_set_commitment(&elements);
        let c2 = compute_set_commitment(&elements);
        assert_eq!(c1, c2);
        assert_ne!(c1, BabyBear::ZERO);
    }

    #[test]
    fn test_set_commitment_order_sensitive() {
        let elements_a: Vec<BabyBear> = vec![BabyBear::new(1), BabyBear::new(2)];
        let elements_b: Vec<BabyBear> = vec![BabyBear::new(2), BabyBear::new(1)];
        let c_a = compute_set_commitment(&elements_a);
        let c_b = compute_set_commitment(&elements_b);
        assert_ne!(
            c_a, c_b,
            "Different orderings should produce different commitments"
        );
    }

    #[test]
    fn test_derive_alpha_deterministic() {
        let hashes: Vec<BabyBear> = (1..=5).map(BabyBear::new).collect();
        let pred_id = BabyBear::new(99);
        let a1 = derive_alpha_for_absence(&hashes, pred_id);
        let a2 = derive_alpha_for_absence(&hashes, pred_id);
        assert_eq!(a1, a2);
    }

    #[test]
    fn test_derive_alpha_different_predicates() {
        let hashes: Vec<BabyBear> = (1..=5).map(BabyBear::new).collect();
        let a1 = derive_alpha_for_absence(&hashes, BabyBear::new(1));
        let a2 = derive_alpha_for_absence(&hashes, BabyBear::new(2));
        assert_ne!(
            a1, a2,
            "Different predicates should produce different alphas"
        );
    }
}
