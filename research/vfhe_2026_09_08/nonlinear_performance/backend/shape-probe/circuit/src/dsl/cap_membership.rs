//! Capability-membership DSL circuit (cap Phase D): a STARK that a leaf digest
//! is a member of the canonical **openable** capability tree
//! ([`crate::cap_root::CanonicalCapTree`] — the sorted binary Poseidon2 Merkle
//! tree whose root is the cell's `capability_root` since cap Phase A).
//!
//! ## Native 8-felt (Phase H-CAP-8)
//!
//! The canonical cap tree is native 8-felt: leaves are [`crate::cap_root::CapLeaf::digest`]
//! (an 8-lane rate-8 absorb), and internal nodes are [`crate::cap_root::cap_node8`] (the
//! arity-16 `node8` compression `perm(L8 ‖ R8)[0..8]`). This standalone leg is FAITHFUL to
//! that width: it folds 8-felt `cur8/left8/right8/parent8` per level via the multi-output
//! [`crate::dsl::circuit::ConstraintExpr::MerkleHash8`] gadget (the DSL-AIR twin of
//! `cap_node8`, binding all 8 genuine Poseidon2 output lanes), and pins a 16-felt public
//! input `[leaf_digest(8) ‖ cap_root(8)]`. There is NO lane-0 projection anywhere — the
//! per-node and per-boundary collision floor is the full 8-felt width (~124-bit), matching
//! the deployed FRI/STARK soundness.
//!
//! ## Why this exists (the AUTHORITY payoff leg)
//!
//! Phase B proves capability membership IN-ROW for the Attenuate/Grant EffectVm selectors
//! (the non-amplification gates). Every OTHER verb's capability-gated turn needs a STANDALONE
//! membership leg the composed full-turn proof can carry: "the consumed capability's 7-field
//! leaf is a member of the holder's pre-state `capability_root`". The Phase-C executor witness
//! ([`dregg_turn::TurnReceipt::consumed_capabilities`]) supplies the leaf preimage + sorted-Merkle
//! path (8-felt sibling digests); this circuit proves the path, and
//! `dregg_sdk::verify_full_turn_bound` pins its public inputs:
//!
//!   * `pi[LEAF_DIGEST..][0..8]` — the 8-felt Poseidon2 digest of the consumed cap's 7-field
//!     leaf preimage (the verifier recomputes it from the receipt's witnessed fields, so a
//!     leaf-field tamper mismatches);
//!   * `pi[CAP_ROOT..][0..8]` — the 8-felt Merkle root the path reaches (the verifier pins it
//!     to the holder's CANONICAL pre-state `capability_root`, so a path into a prover-chosen
//!     tree mismatches).
//!
//! ## The statement (depth = [`CAP_TREE_DEPTH`], 8-felt `cap_node8` nodes)
//!
//! The trace is exactly `CAP_TREE_DEPTH` rows (16 — a power of two, no padding), one per tree
//! level, bottom-up:
//!
//! ```text
//! row r:  cur8_r  ∈ {left8_r, right8_r}   (selected lane-wise by dir_r ∈ {0,1})
//!         parent8_r = cap_node8(left8_r, right8_r)   (in-circuit arity-16 node8, 8 lanes)
//!         cur8_{r+1} = parent8_r                     (chain continuity, per lane)
//! row 0:  cur8_0 = pi[LEAF_DIGEST..][0..8]
//! last:   parent8 = pi[CAP_ROOT..][0..8]
//! ```

use crate::cap_root::{CAP_DIGEST_W, CAP_TREE_DEPTH, cap_node8};
use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use crate::field::BabyBear;

/// Trace width: `[cur8, left8, right8, parent8, dir]` = 4·8 + 1.
pub const TRACE_WIDTH: usize = 4 * CAP_DIGEST_W + 1;

/// Column base indices (each 8-felt block spans `base..base+8`).
pub mod col {
    use super::CAP_DIGEST_W;
    /// The child node being authenticated at this level (= previous parent;
    /// row 0 carries the 8-felt leaf digest). Lanes `CUR..CUR+8`.
    pub const CUR: usize = 0;
    /// Left child of this level's node hash. Lanes `LEFT..LEFT+8`.
    pub const LEFT: usize = CUR + CAP_DIGEST_W;
    /// Right child of this level's node hash. Lanes `RIGHT..RIGHT+8`.
    pub const RIGHT: usize = LEFT + CAP_DIGEST_W;
    /// `cap_node8(left8, right8)` — the parent node. Lanes `PARENT..PARENT+8`.
    pub const PARENT: usize = RIGHT + CAP_DIGEST_W;
    /// Direction bit: 0 ⇒ `cur` is the LEFT child (sibling right), 1 ⇒ RIGHT.
    pub const DIR: usize = PARENT + CAP_DIGEST_W;
}

/// Public input base indices (each spans `base..base+8`).
pub mod pi {
    use super::CAP_DIGEST_W;
    /// The 8-felt leaf digest being proven a member (row-0 `cur8` boundary). The
    /// composing verifier recomputes this from the consumed-cap witness's 7-field
    /// leaf preimage, so the leaf FIELDS are bound. Lanes `0..8`.
    pub const LEAF_DIGEST: usize = 0;
    /// The 8-felt Merkle root the path reaches (last-row `parent8` boundary). The
    /// composing verifier pins this to the holder's canonical pre-state
    /// `capability_root`. Lanes `8..16`.
    pub const CAP_ROOT: usize = LEAF_DIGEST + CAP_DIGEST_W;
}

/// Public input count: `[leaf_digest(8), cap_root(8)]`.
pub const PUBLIC_INPUT_COUNT: usize = 2 * CAP_DIGEST_W;

/// Build the capability-membership CircuitDescriptor (native 8-felt).
pub fn cap_membership_circuit_descriptor() -> CircuitDescriptor {
    let mut constraints: Vec<ConstraintExpr> = Vec::new();

    // C1: the direction bit is binary.
    constraints.push(ConstraintExpr::Binary { col: col::DIR });

    // C2 (per lane i): `cur8[i]` occupies the child slot `dir` selects:
    //     (1 - dir)·(left[i] - cur[i]) + dir·(right[i] - cur[i]) == 0
    //   ⇔ left[i] - cur[i] - dir·left[i] + dir·right[i] == 0
    // (dir = 0 ⇒ left[i] == cur[i]; dir = 1 ⇒ right[i] == cur[i]). The OTHER slot is the
    // prover-supplied sibling — unconstrained by design (any sibling defines SOME path;
    // only a path whose top equals the pinned canonical root verifies). Enforced on all
    // 8 lanes so the SELECTED 8-felt child equals `cur8` in full width.
    for i in 0..CAP_DIGEST_W {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::LEFT + i],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::CUR + i],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::DIR, col::LEFT + i],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::DIR, col::RIGHT + i],
                },
            ],
        });
    }

    // C3: parent8 = cap_node8(left8, right8) — REAL in-circuit arity-16 Poseidon2 node8
    // compression (one permutation aux block per row), ALL 8 output lanes bound. The EXACT
    // node hash `CanonicalCapTree` builds with since Phase H-CAP-8.
    let out_cols: [usize; CAP_DIGEST_W] = core::array::from_fn(|i| col::PARENT + i);
    let left_cols: [usize; CAP_DIGEST_W] = core::array::from_fn(|i| col::LEFT + i);
    let right_cols: [usize; CAP_DIGEST_W] = core::array::from_fn(|i| col::RIGHT + i);
    constraints.push(ConstraintExpr::MerkleHash8 {
        output_cols: out_cols,
        left_cols,
        right_cols,
    });

    // C4 (per lane i): chain continuity — the next level authenticates THIS level's parent.
    // (Transition constraints are when_transition-gated on the p3 path, so the last row has
    // no wrap-around obligation.)
    for i in 0..CAP_DIGEST_W {
        constraints.push(ConstraintExpr::Transition {
            next_col: col::CUR + i,
            local_col: col::PARENT + i,
        });
    }

    // Boundaries: the 8-felt leaf digest enters at the bottom, the 8-felt root exits at the top.
    let mut boundaries: Vec<BoundaryDef> = Vec::new();
    for i in 0..CAP_DIGEST_W {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::CUR + i,
            pi_index: pi::LEAF_DIGEST + i,
        });
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT + i,
            pi_index: pi::CAP_ROOT + i,
        });
    }

    let mut columns: Vec<ColumnDef> = Vec::new();
    for i in 0..CAP_DIGEST_W {
        columns.push(ColumnDef {
            name: format!("cur{i}"),
            index: col::CUR + i,
            kind: ColumnKind::Value,
        });
    }
    for i in 0..CAP_DIGEST_W {
        columns.push(ColumnDef {
            name: format!("left{i}"),
            index: col::LEFT + i,
            kind: ColumnKind::Value,
        });
    }
    for i in 0..CAP_DIGEST_W {
        columns.push(ColumnDef {
            name: format!("right{i}"),
            index: col::RIGHT + i,
            kind: ColumnKind::Value,
        });
    }
    for i in 0..CAP_DIGEST_W {
        columns.push(ColumnDef {
            name: format!("parent{i}"),
            index: col::PARENT + i,
            kind: ColumnKind::Hash,
        });
    }
    columns.push(ColumnDef {
        name: "dir".into(),
        index: col::DIR,
        kind: ColumnKind::Binary,
    });

    CircuitDescriptor {
        name: "dregg-cap-membership-dsl-v2-node8".into(),
        trace_width: TRACE_WIDTH,
        max_degree: 7, // Poseidon2 S-box
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT, // [leaf_digest(8), cap_root(8)]
        lookup_tables: vec![],
    }
}

/// Create a DslCircuit from the cap-membership descriptor.
pub fn cap_membership_dsl_circuit() -> DslCircuit {
    DslCircuit::new(cap_membership_circuit_descriptor())
}

/// Generate the cap-membership trace from an 8-felt leaf digest + sorted-Merkle path
/// (the [`crate::cap_root::CanonicalCapTree::prove_membership`] / `ConsumedCapWitness`
/// shape: bottom-up 8-felt siblings + direction bits, 0 = current node is the LEFT child).
///
/// Returns `(trace, public_inputs)` where `public_inputs = [leaf_digest(8) ‖ root(8)]`
/// and `root` is the path's recomputed top. Errs on a malformed witness (wrong path length
/// or a non-binary direction bit).
pub fn generate_cap_membership_trace(
    leaf_digest: [BabyBear; CAP_DIGEST_W],
    siblings: &[[BabyBear; CAP_DIGEST_W]],
    directions: &[u8],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if siblings.len() != CAP_TREE_DEPTH || directions.len() != CAP_TREE_DEPTH {
        return Err(format!(
            "cap-membership witness must have exactly {CAP_TREE_DEPTH} levels \
             (got {} siblings / {} directions)",
            siblings.len(),
            directions.len()
        ));
    }
    let mut trace = Vec::with_capacity(CAP_TREE_DEPTH);
    let mut cur = leaf_digest;
    for level in 0..CAP_TREE_DEPTH {
        let sib = siblings[level];
        let (left, right) = match directions[level] {
            0 => (cur, sib),
            1 => (sib, cur),
            d => return Err(format!("direction bit {d} at level {level} is not binary")),
        };
        let parent = cap_node8(left, right);
        let mut row = Vec::with_capacity(TRACE_WIDTH);
        row.extend_from_slice(&cur);
        row.extend_from_slice(&left);
        row.extend_from_slice(&right);
        row.extend_from_slice(&parent);
        row.push(BabyBear::new(directions[level] as u32));
        debug_assert_eq!(row.len(), TRACE_WIDTH);
        trace.push(row);
        cur = parent;
    }
    let mut pis = Vec::with_capacity(PUBLIC_INPUT_COUNT);
    pis.extend_from_slice(&leaf_digest);
    pis.extend_from_slice(&cur);
    Ok((trace, pis))
}

/// Prove capability membership through the AUDITED Plonky3 prover (`p3-batch-stark`).
/// Public inputs of the returned proof: `[leaf_digest(8) ‖ root(8)]` where `root` is the
/// path's recomputed top — the COMPOSING verifier is responsible for pinning that root to
/// the canonical pre-state `capability_root` (the non-vacuity tooth).
pub fn prove_cap_membership_p3(
    leaf_digest: [BabyBear; CAP_DIGEST_W],
    siblings: &[[BabyBear; CAP_DIGEST_W]],
    directions: &[u8],
) -> Result<(crate::dsl::dsl_p3_air::DslP3Proof, Vec<BabyBear>), String> {
    let (trace, public_inputs) = generate_cap_membership_trace(leaf_digest, siblings, directions)?;
    let circuit = cap_membership_dsl_circuit();
    let proof = crate::dsl::dsl_p3_air::prove_dsl_p3(&circuit, &trace, &public_inputs)
        .map_err(|e| format!("cap-membership p3 proof failed: {e}"))?;
    Ok((proof, public_inputs))
}

/// Verify a cap-membership proof on the AUDITED Plonky3 verifier. The caller supplies the
/// 8-felt `leaf_digest` AND 8-felt `root` it expects this proof to attest; both are bound
/// in-circuit (row-0 / last-row 8-lane boundaries), so a proof for a different leaf or
/// against a different tree is rejected.
pub fn verify_cap_membership_p3(
    proof: &crate::dsl::dsl_p3_air::DslP3Proof,
    leaf_digest: [BabyBear; CAP_DIGEST_W],
    root: [BabyBear; CAP_DIGEST_W],
) -> Result<(), String> {
    let circuit = cap_membership_dsl_circuit();
    let mut public_inputs = Vec::with_capacity(PUBLIC_INPUT_COUNT);
    public_inputs.extend_from_slice(&leaf_digest);
    public_inputs.extend_from_slice(&root);
    crate::dsl::dsl_p3_air::verify_dsl_p3(&circuit, proof, &public_inputs)
        .map_err(|e| format!("cap-membership p3 verification failed: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap_root::{
        CapLeaf, cap_node8, encode_breadstuff, encode_expiry, fold_bytes32, slot_hash,
        split_effect_mask,
    };

    fn leaf(slot: u32, target_byte: u8, tier: u32, mask: u32) -> CapLeaf {
        let mut tgt = [0u8; 32];
        tgt[0] = target_byte;
        let (mask_lo, mask_hi) = split_effect_mask(mask);
        CapLeaf {
            slot_hash: slot_hash(slot),
            target: fold_bytes32(&tgt),
            auth_tag: BabyBear::new(tier),
            mask_lo,
            mask_hi,
            expiry: encode_expiry(None),
            breadstuff: encode_breadstuff(None),
        }
    }

    /// Build an honest 8-felt membership witness self-consistent with the DSL AIR's own
    /// `cap_node8` fold. The leaf digest is a genuine `CapLeaf`'s FULL 8-felt digest; the
    /// siblings are deterministic 8-felt digests; the returned root is the `cap_node8`-folded
    /// path top.
    fn real_tree_witness() -> (
        [BabyBear; CAP_DIGEST_W],
        CapLeaf,
        Vec<[BabyBear; CAP_DIGEST_W]>,
        Vec<u8>,
    ) {
        let target = leaf(1, 9, 1, 0x0000_00FF);
        let leaf_digest = target.digest();
        let mut siblings = Vec::with_capacity(CAP_TREE_DEPTH);
        let mut directions = Vec::with_capacity(CAP_TREE_DEPTH);
        let mut cur = leaf_digest;
        for level in 0..CAP_TREE_DEPTH {
            let sib: [BabyBear; CAP_DIGEST_W] =
                core::array::from_fn(|i| BabyBear::new(0x1357 + (level * CAP_DIGEST_W + i) as u32));
            let dir = (level % 2) as u8;
            cur = if dir == 0 {
                cap_node8(cur, sib)
            } else {
                cap_node8(sib, cur)
            };
            siblings.push(sib);
            directions.push(dir);
        }
        (cur, target, siblings, directions)
    }

    /// CONTROL: an honest 8-felt membership witness proves + verifies through the audited p3
    /// verifier at 16 PIs, and the published root equals the `cap_node8`-folded path top.
    #[test]
    fn honest_cap_membership_round_trips_through_p3() {
        let (root, target, siblings, directions) = real_tree_witness();
        let leaf_digest = target.digest();
        let (proof, pis) = prove_cap_membership_p3(leaf_digest, &siblings, &directions)
            .expect("honest cap membership must prove+verify through audited p3");
        assert_eq!(
            pis.len(),
            PUBLIC_INPUT_COUNT,
            "16 PIs: leaf_digest(8) ‖ cap_root(8)"
        );
        assert_eq!(&pis[pi::LEAF_DIGEST..pi::LEAF_DIGEST + 8], &leaf_digest[..]);
        assert_eq!(
            &pis[pi::CAP_ROOT..pi::CAP_ROOT + 8],
            &root[..],
            "published 8-felt root IS the folded root"
        );
        verify_cap_membership_p3(&proof, leaf_digest, root)
            .expect("audited p3 verify accepts the honest membership");
    }

    /// ANTI-FORGERY (root): an honest proof verified against a DIFFERENT root is REJECTED —
    /// the last-row 8-lane boundary pins the genuine path top.
    #[test]
    fn forged_root_is_rejected() {
        let (root, target, siblings, directions) = real_tree_witness();
        let leaf_digest = target.digest();
        let (proof, _) =
            prove_cap_membership_p3(leaf_digest, &siblings, &directions).expect("honest");
        let mut forged_root = root;
        forged_root[0] = forged_root[0] + BabyBear::new(1);
        assert!(
            verify_cap_membership_p3(&proof, leaf_digest, forged_root).is_err(),
            "SOUNDNESS: a forged cap_root MUST be rejected by the audited p3 verifier"
        );
    }

    /// ANTI-FORGERY (leaf): an honest proof verified for a DIFFERENT leaf digest is REJECTED —
    /// the row-0 8-lane boundary pins the genuine leaf.
    #[test]
    fn forged_leaf_is_rejected() {
        let (root, target, siblings, directions) = real_tree_witness();
        let leaf_digest = target.digest();
        let (proof, _) =
            prove_cap_membership_p3(leaf_digest, &siblings, &directions).expect("honest");
        // An "inflated mask" tamper: same leaf but EFFECT_ALL rights.
        let mut inflated = target;
        let (lo, hi) = split_effect_mask(0xFFFF_FFFF);
        inflated.mask_lo = lo;
        inflated.mask_hi = hi;
        assert_ne!(inflated.digest(), leaf_digest);
        assert!(
            verify_cap_membership_p3(&proof, inflated.digest(), root).is_err(),
            "SOUNDNESS: an inflated-mask leaf digest MUST be rejected"
        );
    }

    /// ANTI-FORGERY (witness): a tampered sibling produces a path whose top is NOT the
    /// canonical root, so the proof cannot verify against it.
    #[test]
    fn tampered_path_does_not_reach_canonical_root() {
        let (root, target, mut siblings, directions) = real_tree_witness();
        let leaf_digest = target.digest();
        siblings[3][0] = siblings[3][0] + BabyBear::new(1);
        let (proof, pis) = prove_cap_membership_p3(leaf_digest, &siblings, &directions)
            .expect("the tampered path still proves membership in SOME tree");
        assert_ne!(
            &pis[pi::CAP_ROOT..pi::CAP_ROOT + 8],
            &root[..],
            "tampered path tops a different root"
        );
        assert!(
            verify_cap_membership_p3(&proof, leaf_digest, root).is_err(),
            "SOUNDNESS: a path that does not reach the canonical root MUST be rejected"
        );
    }

    /// THE 8-FELT FORGE TOOTH: a forged cap tree whose leaf differs but shares the SAME lane-0
    /// projection (`leaf_digest[0]`) is REJECTED by the 8-felt gadget. Under the OLD 1-felt
    /// `cap_node` leg (which bound only lane 0), this forgery would have verified; the native
    /// 8-felt node8 gadget binds ALL 8 lanes, so a lane-0-only collision no longer passes.
    #[test]
    fn lane0_collision_forgery_is_rejected() {
        let (root, target, siblings, directions) = real_tree_witness();
        let genuine = target.digest();
        // Craft a distinct 8-felt "leaf" that agrees with the genuine leaf on lane 0 but
        // differs in a higher lane — the exact class of forgery a 1-felt (lane-0) leg would
        // have accepted.
        let mut forged_leaf = genuine;
        forged_leaf[1] = forged_leaf[1] + BabyBear::new(1);
        assert_eq!(forged_leaf[0], genuine[0], "shares the lane-0 projection");
        assert_ne!(forged_leaf, genuine, "distinct as an 8-felt digest");
        // Prove membership of the GENUINE leaf, then attempt to verify the proof as attesting
        // the FORGED (lane-0-equal) leaf: the row-0 8-lane boundary rejects it.
        let (proof, _) = prove_cap_membership_p3(genuine, &siblings, &directions).expect("honest");
        assert!(
            verify_cap_membership_p3(&proof, forged_leaf, root).is_err(),
            "8-FELT TOOTH: a lane-0-equal but full-width-distinct leaf MUST be rejected"
        );
    }

    /// A leaf NOT in the tree (no fabricated position) has no honest witness; the trace
    /// generator rejects malformed paths outright.
    #[test]
    fn malformed_witness_is_refused() {
        let (_, target, siblings, mut directions) = real_tree_witness();
        let leaf_digest = target.digest();
        // Wrong length.
        assert!(
            generate_cap_membership_trace(leaf_digest, &siblings[..4], &directions[..4]).is_err()
        );
        // Non-binary direction bit.
        directions[0] = 2;
        assert!(generate_cap_membership_trace(leaf_digest, &siblings, &directions).is_err());
    }
}
