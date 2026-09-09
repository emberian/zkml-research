//! In-circuit Poseidon2 Merkle membership proofs for body facts.
//!
//! This module closes the soundness gap in the multi-step derivation AIR:
//! constraint 19 checks that `body_root == state_root` (public input), but the
//! body HASH itself is prover-supplied. A malicious prover could place arbitrary
//! hash values in the body_hash columns without proving those hashes correspond
//! to actual leaves in the committed Merkle tree.
//!
//! **The fix (Approach 3 -- proof composition):**
//!
//! For each body fact used in the derivation, the prover must also produce a
//! separate Merkle membership STARK proving that the fact's hash is a leaf in
//! the Poseidon2 Merkle tree committed at `state_root`. The verifier checks:
//!
//! 1. The derivation STARK is valid (rules applied correctly, conclusion is ALLOW)
//! 2. For each body fact: a Merkle membership STARK proves the fact is in the tree
//! 3. The leaf hashes in the membership proofs match the body_hash values used
//!    in the derivation trace
//! 4. All membership proofs share the same `state_root` as the derivation proof
//!
//! This is IVC/composition: two proof types sharing the public `state_root`.
//! No trace widening needed -- just additional proof obligations.

use crate::dsl::descriptors::merkle_poseidon2_circuit;
use crate::field::BabyBear;
use crate::multi_step_witness::MultiStepWitness;
use serde::{Deserialize, Serialize};

/// A Merkle proof for a single body fact: siblings + positions (leaf-to-root).
///
/// This is the raw data needed to produce a membership STARK. It mirrors
/// `Poseidon2MerkleProof` from the commit crate but is self-contained here
/// so the circuit crate has no dependency on the commit crate.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BodyFactMerkleProof {
    /// The hash of the body fact (leaf in the Merkle tree).
    pub fact_hash: BabyBear,
    /// 3 sibling hashes at each level (leaf-to-root order).
    pub siblings: Vec<[BabyBear; 3]>,
    /// Position (0..3) at each level (leaf-to-root order).
    pub positions: Vec<u8>,
}

/// Convenience: extract all distinct body fact hashes from a MultiStepWitness.
///
/// This is used by the verifier to know which body facts need membership proofs.
pub fn collect_body_fact_hashes(witness: &MultiStepWitness) -> Vec<BabyBear> {
    let mut hashes = Vec::new();
    for step in &witness.steps {
        for &hash in &step.body_fact_hashes {
            if !hashes.contains(&hash) {
                hashes.push(hash);
            }
        }
    }
    hashes
}

// ============================================================================
// Tests
// ============================================================================
