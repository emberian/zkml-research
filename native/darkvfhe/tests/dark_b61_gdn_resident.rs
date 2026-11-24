#![deny(warnings)]
//! Wave 11 Lane 5 Integration, Adversarial Falsifier, & Full `N = 8192` `Qwen3.5-0.8B` (`16 × 128 × 128`)
//! Benchmark Suite for `DarkB61GdnResident` (`dark_gdn_continual.rs`).

use darkvfhe::dark_gdn_continual::{
    cleartext_multihead_seq, verify_continual_whir_state_bytes, ContinualActionTag,
    ContinualCustodyQuorum, ContinualGdnError, DarkB61GdnResident, GdnChunkPlain, GdnHeadStepPlain,
    QWEN35_GDN_DK, QWEN35_GDN_DV, QWEN35_GDN_HEADS, QWEN35_STATE_CTS,
};
use darkvfhe::rns_hoist::HoistedEngine;
use darkvfhe::succinct_pcs::{Ext3Field, PcsRng};
use darkvfhe::whir_pcs::{GMask61, GMaskSpec61};
use darkvfhe::HoistedParams;
use std::sync::Arc;
use std::time::Instant;

fn make_deterministic_initial_state(
    num_heads: usize,
    d_v: usize,
    d_k: usize,
    t: u64,
) -> Vec<Vec<Vec<u64>>> {
    (0..num_heads)
        .map(|h| {
            (0..d_v)
                .map(|r| {
                    (0..d_k)
                        .map(|c| {
                            let v = (h as u64 + 1)
                                .wrapping_mul(1_000_003)
                                .wrapping_add((r as u64 + 3).wrapping_mul(65_537))
                                .wrapping_add((c as u64 + 7).wrapping_mul(257));
                            v % t
                        })
                        .collect()
                })
                .collect()
        })
        .collect()
}

struct ChunkSpec {
    num_heads: usize,
    tau: usize,
    d_v: usize,
    d_k: usize,
    col_range: std::ops::Range<usize>,
    unit_gamma: bool,
    seed: u64,
    t: u64,
}

fn make_chunk_supported_cols(spec: ChunkSpec) -> GdnChunkPlain {
    let ChunkSpec {
        num_heads,
        tau,
        d_v,
        d_k,
        col_range,
        unit_gamma,
        seed,
        t,
    } = spec;
    let heads = (0..num_heads)
        .map(|h| {
            (0..tau)
                .map(|m| {
                    let gamma = if unit_gamma {
                        1u64
                    } else {
                        ((seed
                            .wrapping_mul(31)
                            .wrapping_add((h * 17 + m * 13 + 5) as u64))
                            % (t - 3))
                            + 2
                    };
                    let beta = ((seed
                        .wrapping_mul(97)
                        .wrapping_add((h * 29 + m * 7 + 3) as u64))
                        % (t - 3))
                        + 2;
                    let mut k = vec![0u64; d_k];
                    for c in col_range.clone() {
                        k[c] = ((seed
                            .wrapping_mul(131)
                            .wrapping_add((h * 41 + m * 19 + c * 11 + 1) as u64))
                            % (t - 2))
                            + 1;
                    }
                    let v: Vec<u64> = (0..d_v)
                        .map(|r| {
                            (seed
                                .wrapping_mul(251)
                                .wrapping_add((h * 53 + m * 23 + r * 7 + 9) as u64))
                                % t
                        })
                        .collect();
                    GdnHeadStepPlain { gamma, beta, k, v }
                })
                .collect()
        })
        .collect();
    GdnChunkPlain { tau, heads }
}

fn tomb_chunk(chunk: &GdnChunkPlain) -> GdnChunkPlain {
    GdnChunkPlain {
        tau: chunk.tau,
        heads: chunk
            .heads
            .iter()
            .map(|h_steps| {
                h_steps
                    .iter()
                    .map(|st| GdnHeadStepPlain {
                        gamma: st.gamma,
                        beta: 0,
                        k: st.k.clone(),
                        v: st.v.clone(),
                    })
                    .collect()
            })
            .collect(),
    }
}

fn max_state_diff(a: &[Vec<Vec<u64>>], b: &[Vec<Vec<u64>>]) -> u64 {
    assert_eq!(a.len(), b.len());
    let mut max_d = 0u64;
    for h in 0..a.len() {
        assert_eq!(a[h].len(), b[h].len());
        for r in 0..a[h].len() {
            assert_eq!(a[h][r].len(), b[h][r].len());
            for c in 0..a[h][r].len() {
                let d = a[h][r][c].abs_diff(b[h][r][c]);
                if d > max_d {
                    max_d = d;
                }
            }
        }
    }
    max_d
}

#[test]
fn test_threshold_custody_epoch_gate_and_shadow_branch_refusal() {
    let params = Arc::new(HoistedParams::for_ring(64));
    let engine = Arc::new(HoistedEngine::new(params.clone()));
    let policy_digest = [0x5Au8; 32];
    let max_budget = 6u64;

    let mut quorum =
        ContinualCustodyQuorum::setup(params.clone(), engine, policy_digest, max_budget)
            .expect("quorum setup");
    let s0 = make_deterministic_initial_state(2, 8, 8, params.t);
    let (mut resident, _gen_bundle, gen_bytes) =
        DarkB61GdnResident::initialize(&mut quorum, &s0).expect("resident init");
    verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &gen_bytes,
    )
    .expect("genesis WHIR state proof valid");

    let genesis_snapshot_commitment = resident.commitment();

    // 1. Reject epoch == 0:
    let bad_zero = quorum
        .sign_epoch_authorization(
            0,
            ContinualActionTag::AdaptChunk {
                chunk_id: 0,
                tau: 1,
            },
            policy_digest,
            genesis_snapshot_commitment,
            [0x11; 32],
            &[0, 1],
        )
        .expect("sign zero epoch");
    assert_eq!(
        quorum.verify_and_latch_all(&bad_zero),
        Err(ContinualGdnError::ZeroEpochRejected)
    );

    // 2. Reject `< 2`-party unilateral single-custodian authorization (`NoSingleViewer >= 2`):
    let bad_single = quorum
        .sign_epoch_authorization(
            1,
            ContinualActionTag::AdaptChunk {
                chunk_id: 0,
                tau: 1,
            },
            policy_digest,
            genesis_snapshot_commitment,
            [0x11; 32],
            &[0],
        )
        .expect("sign 1-party");
    assert_eq!(
        quorum.verify_and_latch_all(&bad_single),
        Err(ContinualGdnError::InsufficientQuorumSignatures { have: 1, need: 2 })
    );

    // 3. Reject unsorted/duplicate signer sets:
    let bad_unsorted = quorum
        .sign_epoch_authorization(
            1,
            ContinualActionTag::AdaptChunk {
                chunk_id: 0,
                tau: 1,
            },
            policy_digest,
            genesis_snapshot_commitment,
            [0x11; 32],
            &[2, 0],
        )
        .expect("sign unsorted");
    assert_eq!(
        quorum.verify_and_latch_all(&bad_unsorted),
        Err(ContinualGdnError::NonCanonicalSigners)
    );

    // 4. Reject policy digest mismatch:
    let bad_policy = quorum
        .sign_epoch_authorization(
            1,
            ContinualActionTag::AdaptChunk {
                chunk_id: 0,
                tau: 1,
            },
            [0xEE; 32],
            genesis_snapshot_commitment,
            [0x11; 32],
            &[0, 1],
        )
        .expect("sign wrong policy");
    assert_eq!(
        quorum.verify_and_latch_all(&bad_policy),
        Err(ContinualGdnError::PolicyDigestMismatch)
    );

    let mut altered = quorum
        .sign_epoch_authorization(
            1,
            ContinualActionTag::AuditOpen,
            policy_digest,
            genesis_snapshot_commitment,
            [8; 32],
            &[0, 1],
        )
        .unwrap();
    altered.compute_cert_digest[0] ^= 1;
    assert!(matches!(
        quorum.verify_and_latch_all(&altered),
        Err(ContinualGdnError::HybridSignatureRejected(_))
    ));
    assert_eq!(quorum.high_water_epochs(), [0; 3]);

    // 5. Execute two genuine multi-step WY continual chunks (`tau = 2`, then `tau = 2` with refresh):
    let chunk0 = make_chunk_supported_cols(ChunkSpec {
        num_heads: 2,
        tau: 2,
        d_v: 8,
        d_k: 8,
        col_range: 0..8,
        unit_gamma: false,
        seed: 101,
        t: params.t,
    });
    let chunk1 = make_chunk_supported_cols(ChunkSpec {
        num_heads: 2,
        tau: 2,
        d_v: 8,
        d_k: 8,
        col_range: 0..8,
        unit_gamma: false,
        seed: 202,
        t: params.t,
    });
    let spdz0 = resident.share_chunk_to_custodians(&mut quorum, &chunk0);
    let (_, b0, m0) = resident
        .adapt_wy_chunk_spdz(&mut quorum, spdz0, &[0, 1], true)
        .expect("chunk0 adapt");
    assert!(m0.hoisted_whir_sample_bytes > 0);
    verify_continual_whir_state_bytes(&params, resident.handles(), resident.ciphertexts(), &b0)
        .expect("chunk0 WHIR verify");

    // 6. Attempt a shadow-branch fork from snapshotted genesis state (`genesis_snapshot_commitment`)
    //    at a fresh unused epoch (`quorum.next_epoch()`): MUST be rejected!
    let fresh_epoch = quorum.next_epoch();
    let shadow_attempt = quorum
        .sign_epoch_authorization(
            fresh_epoch,
            ContinualActionTag::AdaptChunk {
                chunk_id: 99,
                tau: 1,
            },
            policy_digest,
            genesis_snapshot_commitment,
            [0x22; 32],
            &[0, 2],
        )
        .expect("sign shadow fork");
    assert_eq!(
        quorum.verify_and_latch_all(&shadow_attempt),
        Err(ContinualGdnError::SnapshotShadowBranchRejected),
        "custodian latches must reject snapshotted ct_S shadow-branch fork"
    );
    // Verify atomic rollback: `high_water_epoch` must NOT have advanced on rejection!
    assert_eq!(quorum.high_water_epochs()[0], fresh_epoch - 1);

    // 7. Reject stale/replay epoch (`epoch == high_water_epoch`):
    let stale_attempt = quorum
        .sign_epoch_authorization(
            fresh_epoch - 1,
            ContinualActionTag::AdaptChunk {
                chunk_id: 1,
                tau: 2,
            },
            policy_digest,
            resident.commitment(),
            [0x33; 32],
            &[1, 2],
        )
        .expect("sign stale");
    assert_eq!(
        quorum.verify_and_latch_all(&stale_attempt),
        Err(ContinualGdnError::StaleOrReplayEpochRejected {
            got: fresh_epoch - 1,
            high_water: fresh_epoch - 1,
        })
    );

    // 8. Reject policy budget overflow (`epoch > max_budget`):
    let over_budget = quorum
        .sign_epoch_authorization(
            max_budget + 1,
            ContinualActionTag::AdaptChunk {
                chunk_id: 1,
                tau: 2,
            },
            policy_digest,
            resident.commitment(),
            [0x44; 32],
            &[0, 1],
        )
        .expect("sign over budget");
    assert_eq!(
        quorum.verify_and_latch_all(&over_budget),
        Err(ContinualGdnError::PolicyBudgetExceeded {
            got: max_budget + 1,
            budget: max_budget,
        })
    );

    // 9. Run chunk1 (`tau = 2`, exercises automatic depth-1 -> depth-0 refresh + WY update) and verify exact state:
    let spdz1 = resident.share_chunk_to_custodians(&mut quorum, &chunk1);
    let (_, b1, _) = resident
        .adapt_wy_chunk_spdz(&mut quorum, spdz1, &[1, 2], false)
        .expect("chunk1 adapt");
    verify_continual_whir_state_bytes(&params, resident.handles(), resident.ciphertexts(), &b1)
        .expect("chunk1 WHIR verify");

    let got_state = resident
        .open_verified_state_for_audit(&mut quorum, &[0, 2])
        .expect("audit open");
    let want_state = cleartext_multihead_seq(&params.fp_t, &s0, &[chunk0, chunk1]);
    assert_eq!(
        max_state_diff(&got_state, &want_state),
        0,
        "2-chunk stateful WY adaptation must match cleartext sequential GDN recurrence bit-for-bit"
    );
}

#[test]
fn test_w0_subspace_unlearning_orthogonal_tooth_and_wy_replay_exact() {
    let params = Arc::new(HoistedParams::for_ring(64));
    let engine = Arc::new(HoistedEngine::new(params.clone()));
    let policy_digest = [0xA5u8; 32];

    // Part A: Orthogonal-key fast subtract (`K_1^T K_0 == 0`) with BOTH general `gamma != 1` (`tombEpisode`)
    //         and unit `gamma == 1` (literal omission `eraseIdx`):
    for unit_gamma_ep0 in [false, true] {
        let mut quorum =
            ContinualCustodyQuorum::setup(params.clone(), engine.clone(), policy_digest, 32)
                .expect("quorum");
        let s0 = make_deterministic_initial_state(2, 8, 8, params.t);
        let (mut resident, _, _) = DarkB61GdnResident::initialize(&mut quorum, &s0).expect("init");

        // Episode 0 uses columns `0..4`; Episode 1 uses disjoint columns `4..8` => `<k_0, k_1> == 0`!
        let ep0 = make_chunk_supported_cols(ChunkSpec {
            num_heads: 2,
            tau: 2,
            d_v: 8,
            d_k: 8,
            col_range: 0..4,
            unit_gamma: unit_gamma_ep0,
            seed: 303,
            t: params.t,
        });
        let ep1 = make_chunk_supported_cols(ChunkSpec {
            num_heads: 2,
            tau: 2,
            d_v: 8,
            d_k: 8,
            col_range: 4..8,
            unit_gamma: false,
            seed: 404,
            t: params.t,
        });

        let spdz0 = resident.share_chunk_to_custodians(&mut quorum, &ep0);
        resident
            .adapt_wy_chunk_spdz(&mut quorum, spdz0, &[0, 1], false)
            .expect("ep0");
        let spdz1 = resident.share_chunk_to_custodians(&mut quorum, &ep1);
        resident
            .adapt_wy_chunk_spdz(&mut quorum, spdz1, &[0, 2], false)
            .expect("ep1");

        let (_, unlearn_bytes, u_metrics) = resident
            .unlearn_w0_orthogonal_fast(&mut quorum, 0, &[1, 2])
            .expect("orthogonal W0 unlearn");
        assert_eq!(u_metrics.mode, "orthogonal_fast_subtract");
        verify_continual_whir_state_bytes(
            &params,
            resident.handles(),
            resident.ciphertexts(),
            &unlearn_bytes,
        )
        .expect("orthogonal unlearn WHIR verify");

        // Reject double unlearning:
        assert_eq!(
            resident
                .unlearn_w0_orthogonal_fast(&mut quorum, 0, &[0, 1])
                .unwrap_err(),
            ContinualGdnError::EpisodeAlreadyUnlearned(0)
        );

        let got = resident
            .open_verified_state_for_audit(&mut quorum, &[0, 1])
            .expect("open");
        let want_tomb =
            cleartext_multihead_seq(&params.fp_t, &s0, &[tomb_chunk(&ep0), ep1.clone()]);
        assert_eq!(max_state_diff(&got, &want_tomb), 0);
        if unit_gamma_ep0 {
            let want_omitted = cleartext_multihead_seq(&params.fp_t, &s0, &[ep1]);
            assert_eq!(max_state_diff(&got, &want_omitted), 0);
        }
    }

    // Part B: Overlapping keys (`K_1^T K_0 != 0`) -> `#tooth` refusal on `unlearn_w0_orthogonal_fast`
    //         followed by bit-exact `unlearn_w0_wy_chunk_replay` (`S_unlearned == S_retrained_without_0`)!
    let mut quorum =
        ContinualCustodyQuorum::setup(params.clone(), engine, policy_digest, 32).expect("quorum");
    let s0 = make_deterministic_initial_state(2, 8, 8, params.t);
    let (mut resident, _, _) = DarkB61GdnResident::initialize(&mut quorum, &s0).expect("init");

    let ep0_ov = make_chunk_supported_cols(ChunkSpec {
        num_heads: 2,
        tau: 2,
        d_v: 8,
        d_k: 8,
        col_range: 0..8,
        unit_gamma: false,
        seed: 505,
        t: params.t,
    });
    let ep1_ov = make_chunk_supported_cols(ChunkSpec {
        num_heads: 2,
        tau: 2,
        d_v: 8,
        d_k: 8,
        col_range: 0..8,
        unit_gamma: false,
        seed: 606,
        t: params.t,
    });
    let ep2_ov = make_chunk_supported_cols(ChunkSpec {
        num_heads: 2,
        tau: 1,
        d_v: 8,
        d_k: 8,
        col_range: 0..8,
        unit_gamma: false,
        seed: 707,
        t: params.t,
    });

    for ep in [&ep0_ov, &ep1_ov, &ep2_ov] {
        let sh = resident.share_chunk_to_custodians(&mut quorum, ep);
        resident
            .adapt_wy_chunk_spdz(&mut quorum, sh, &[0, 1], false)
            .expect("adapt");
    }

    // `#tooth`: orthogonal fast subtract MUST refuse overlapping post-episode keys!
    let err = resident
        .unlearn_w0_orthogonal_fast(&mut quorum, 0, &[0, 2])
        .expect_err("overlapping keys must trigger CrossTermNonOrthogonal");
    assert_eq!(
        err,
        ContinualGdnError::CrossTermNonOrthogonal {
            episode_id: 0,
            post_chunk_id: 1,
        }
    );

    // Compressed WY chunk-operator replay succeeds and equals `S_retrained_without_0` bit-for-bit!
    let (_, wy_bytes, wy_metrics) = resident
        .unlearn_w0_wy_chunk_replay(&mut quorum, 0, &[0, 2])
        .expect("WY chunk replay unlearn");
    assert_eq!(wy_metrics.mode, "wy_chunk_operator_replay");
    verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &wy_bytes,
    )
    .expect("WY replay WHIR verify");

    let got_wy = resident
        .open_verified_state_for_audit(&mut quorum, &[1, 2])
        .expect("open WY replay state");
    let want_retrained = cleartext_multihead_seq(&params.fp_t, &s0, &[ep1_ov, ep2_ov]);
    assert_eq!(
        max_state_diff(&got_wy, &want_retrained),
        0,
        "compressed WY chunk-operator replay must equal S_retrained_without_0 bit-for-bit"
    );
}

// Expand the implemented mask map in the three base-field coordinates of Ext3.
fn verify_zero_tvd_full_rank_f_p(ef: &Ext3Field, spec: &GMaskSpec61) -> usize {
    let fp = ef.fp;
    let mut rng = PcsRng::from_seed([41; 32]);
    let challenges: Vec<_> = (0..spec.num_rounds)
        .map(|i| {
            let mut r = [0; 3];
            rng.fill_fp_row(&fp, i as u64, &mut r);
            r
        })
        .collect();
    let mut mask = GMask61::sample(*ef, vec![spec.clone()], &mut rng);
    let cols = mask.num_fp_cells();
    let rows = 3 * (1 + spec.deg * spec.num_rounds);
    let mut matrix = vec![vec![0; cols]; rows];
    for col in 0..cols {
        mask.coeffs.fill([0; 3]);
        mask.coeffs[col / 3][col % 3] = 1;
        let mut observed = mask.hypercube_sum(&spec.name).to_vec();
        for i in 0..spec.num_rounds {
            let poly = mask.round_poly(&spec.name, i, &challenges[..i]);
            observed.extend(poly[0]);
            observed.extend(poly[2..].iter().flatten());
        }
        for (row, value) in matrix.iter_mut().zip(observed) {
            row[col] = value;
        }
    }
    let mut rank = 0;
    for col in 0..cols {
        let Some(pivot) = (rank..rows).find(|&r| matrix[r][col] != 0) else {
            continue;
        };
        matrix.swap(rank, pivot);
        let inverse = fp.inv(matrix[rank][col]);
        let (above, below) = matrix.split_at_mut(rank + 1);
        for row in below {
            let factor = fp.mul(row[col], inverse);
            for c in col..cols {
                row[c] = fp.sub(row[c], fp.mul(factor, above[rank][c]));
            }
        }
        rank += 1;
    }
    rank
}

#[test]
fn test_whir_gmask61_tvd_zero_and_proof_tamper_soundness() {
    let params = Arc::new(HoistedParams::for_ring(64));
    let engine = Arc::new(HoistedEngine::new(params.clone()));
    let ef = Ext3Field::new(params.fp[0]);

    // 1. Verify full `F_p`-rank (`TVD == 0`) of `GMask61` blinders for `state_hvzk_sc` (`d = 2`):
    let spec_small = GMaskSpec61::new("state_hvzk_sc", 6, 2);
    let rank_small = verify_zero_tvd_full_rank_f_p(&ef, &spec_small);
    assert_eq!(rank_small, 3 * (2 * 6 + 1));

    let spec_n8192 = GMaskSpec61::new("state_hvzk_sc", 13, 2);
    let rank_n8192 = verify_zero_tvd_full_rank_f_p(&ef, &spec_n8192);
    assert_eq!(rank_n8192, 3 * (2 * 13 + 1));

    // 2. Verify tamper rejection across every section of serialized `ContinualWhirStateBundle`:
    let mut quorum =
        ContinualCustodyQuorum::setup(params.clone(), engine, [0x3Cu8; 32], 16).expect("quorum");
    let s0 = make_deterministic_initial_state(2, 8, 8, params.t);
    let (resident, bundle, valid_bytes) =
        DarkB61GdnResident::initialize(&mut quorum, &s0).expect("init");

    verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &valid_bytes,
    )
    .expect("valid bytes must verify");

    let mut malformed = bundle.clone();
    malformed.mr = 255;
    assert!(verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &malformed.to_bytes(params.fp[0].p)
    )
    .is_err());

    // 2a. Bad magic:
    let mut bad_magic = valid_bytes.clone();
    bad_magic[0] ^= 0xFF;
    assert!(verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &bad_magic
    )
    .is_err());

    // 2b. Swapped public ciphertext vs handle:
    let mut swapped_cts = resident.ciphertexts().to_vec();
    swapped_cts.swap(0, 1);
    assert!(verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        &swapped_cts,
        &valid_bytes
    )
    .is_err());

    // 2c. Tampered `p0_poly_evals`:
    let mut bad_eval = bundle.clone();
    bad_eval.p0_poly_evals[0] = (bad_eval.p0_poly_evals[0] + 1) % params.fp[0].p;
    let bad_eval_bytes = bad_eval.to_bytes(params.fp[0].p);
    assert!(verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &bad_eval_bytes
    )
    .is_err());

    // 2d. Tampered `GMask61` round polynomial:
    let mut bad_gm = bundle.clone();
    bad_gm.gmask_rounds[0][1][0] = (bad_gm.gmask_rounds[0][1][0] + 1) % params.fp[0].p;
    let bad_gm_bytes = bad_gm.to_bytes(params.fp[0].p);
    assert!(verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &bad_gm_bytes
    )
    .is_err());

    // 2e. Tampered `LogUpGkrProof` root:
    let mut bad_lu = bundle.clone();
    bad_lu.logup_proof.table_tree.roots[0][0] =
        (bad_lu.logup_proof.table_tree.roots[0][0] + 1) % params.fp[0].p;
    let bad_lu_bytes = bad_lu.to_bytes(params.fp[0].p);
    assert!(verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &bad_lu_bytes
    )
    .is_err());

    // 2f. Tampered `WhirOpeningBundle61` fiber bytes:
    let mut bad_tail = valid_bytes.clone();
    let tail_idx = bad_tail.len() - 17;
    bad_tail[tail_idx] ^= 0x01;
    assert!(verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &bad_tail
    )
    .is_err());

    // 2g. Trailing garbage byte:
    let mut trailing = valid_bytes.clone();
    trailing.push(0x00);
    assert!(verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &trailing
    )
    .is_err());
}

#[test]
fn corrupted_input_mac_refuses_adaptation() {
    let params = Arc::new(HoistedParams::for_ring(64));
    let engine = Arc::new(HoistedEngine::new(params.clone()));
    let mut quorum = ContinualCustodyQuorum::setup(params.clone(), engine, [9; 32], 6).unwrap();
    let s0 = make_deterministic_initial_state(1, 8, 8, params.t);
    let (mut resident, _, _) = DarkB61GdnResident::initialize(&mut quorum, &s0).unwrap();
    let chunk = make_chunk_supported_cols(ChunkSpec {
        num_heads: 1,
        tau: 1,
        d_v: 8,
        d_k: 8,
        col_range: 0..8,
        unit_gamma: false,
        seed: 8,
        t: params.t,
    });
    let mut shares = resident.share_chunk_to_custodians(&mut quorum, &chunk);
    let mac = &mut shares[0][0].k[0].parties[1].mac;
    *mac = params.fp_t.add(*mac, 1);
    let head = resident.commitment();
    assert!(matches!(
        resident.adapt_wy_chunk_spdz(&mut quorum, shares, &[0, 1], false),
        Err(ContinualGdnError::InvalidSpdzMac(_))
    ));
    assert_eq!(resident.commitment(), head);
}

#[test]
fn bench_full_qwen35_b61_n8192_dark_gdn_resident() {
    let t_setup0 = Instant::now();
    let params = Arc::new(HoistedParams::n8192());
    let engine = Arc::new(HoistedEngine::new(params.clone()));
    let policy_digest = [0x99u8; 32];
    let mut quorum = ContinualCustodyQuorum::setup(params.clone(), engine, policy_digest, 64)
        .expect("3-custodian N=8192 quorum setup");
    let setup_ms = t_setup0.elapsed().as_secs_f64() * 1e3;
    eprintln!("setup complete in {setup_ms:.2} ms");

    let s0 =
        make_deterministic_initial_state(QWEN35_GDN_HEADS, QWEN35_GDN_DV, QWEN35_GDN_DK, params.t);
    let t_init0 = Instant::now();
    let (mut resident, _gen_bundle, gen_bytes) =
        DarkB61GdnResident::initialize(&mut quorum, &s0).expect("N=8192 Qwen3.5 resident init");
    let init_ms = t_init0.elapsed().as_secs_f64() * 1e3;
    eprintln!("init complete in {init_ms:.2} ms");
    assert_eq!(resident.ciphertexts().len(), QWEN35_STATE_CTS);
    assert_eq!(resident.slice_geometry(), (64, 2));

    // Episode 0 (`tau = 2` stateful multi-step WY chunk across all 16 heads = 262,144 fast weights):
    let ep0 = make_chunk_supported_cols(ChunkSpec {
        num_heads: QWEN35_GDN_HEADS,
        tau: 2,
        d_v: QWEN35_GDN_DV,
        d_k: QWEN35_GDN_DK,
        col_range: 0..64,
        unit_gamma: false,
        seed: 1001,
        t: params.t,
    });
    let spdz0 = resident.share_chunk_to_custodians(&mut quorum, &ep0);
    let t_ep0 = Instant::now();
    let (_, ep0_bytes, ep0_metrics) = resident
        .adapt_wy_chunk_spdz(&mut quorum, spdz0, &[0, 1], true)
        .expect("N=8192 ep0 tau=2 WY adapt");
    let ep0_total_ms = t_ep0.elapsed().as_secs_f64() * 1e3;
    eprintln!("ep0_total complete in {ep0_total_ms:.2} ms");
    assert!(ep0_metrics.soundness_whir_bits >= 128.0);
    assert!(ep0_metrics.soundness_logup_bits >= 122.0);
    verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &ep0_bytes,
    )
    .expect("ep0 standalone WHIR verify");

    // Episode 1 (`tau = 1` orthogonal-key continual write on cols `64..128`, exercising refresh + adapt):
    let ep1 = make_chunk_supported_cols(ChunkSpec {
        num_heads: QWEN35_GDN_HEADS,
        tau: 1,
        d_v: QWEN35_GDN_DV,
        d_k: QWEN35_GDN_DK,
        col_range: 64..128,
        unit_gamma: false,
        seed: 2002,
        t: params.t,
    });
    let spdz1 = resident.share_chunk_to_custodians(&mut quorum, &ep1);
    let t_ep1 = Instant::now();
    let (_, ep1_bytes, ep1_metrics) = resident
        .adapt_wy_chunk_spdz(&mut quorum, spdz1, &[0, 2], false)
        .expect("N=8192 ep1 tau=1 adapt");
    let ep1_total_ms = t_ep1.elapsed().as_secs_f64() * 1e3;
    eprintln!("ep1_total complete in {ep1_total_ms:.2} ms");
    verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &ep1_bytes,
    )
    .expect("ep1 standalone WHIR verify");

    // Audit exactness after 2 continual episodes across all 262,144 weights:
    let state_after_ep1 = resident
        .open_verified_state_for_audit(&mut quorum, &[1, 2])
        .expect("audit open after ep1");
    let want_after_ep1 = cleartext_multihead_seq(&params.fp_t, &s0, &[ep0.clone(), ep1.clone()]);
    assert_eq!(
        max_state_diff(&state_after_ep1, &want_after_ep1),
        0,
        "N=8192 262,144-weight resident must match cleartext sequential GDN recurrence with max |diff| = 0"
    );

    // W0 Mode A: Orthogonal-key fast decayed sketch subtraction of Episode 0 (`<k_1, k_0> == 0`):
    let t_u0 = Instant::now();
    let (_, u0_bytes, u0_metrics) = resident
        .unlearn_w0_orthogonal_fast(&mut quorum, 0, &[0, 1])
        .expect("N=8192 orthogonal W0 unlearn");
    let u0_total_ms = t_u0.elapsed().as_secs_f64() * 1e3;
    eprintln!("u0_total complete in {u0_total_ms:.2} ms");
    verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &u0_bytes,
    )
    .expect("u0 standalone WHIR verify");

    let state_after_u0 = resident
        .open_verified_state_for_audit(&mut quorum, &[0, 2])
        .expect("audit open after u0");
    let want_after_u0 =
        cleartext_multihead_seq(&params.fp_t, &s0, &[tomb_chunk(&ep0), ep1.clone()]);
    assert_eq!(
        max_state_diff(&state_after_u0, &want_after_u0),
        0,
        "N=8192 orthogonal W0 unlearning must match S_retrained_without_0 (tombEpisode) with max |diff| = 0"
    );

    // Append Episode 2 (`tau = 1`, overlapping keys `64..128` with Episode 1 -> `K_2^T K_1 != 0`!):
    let ep2 = make_chunk_supported_cols(ChunkSpec {
        num_heads: QWEN35_GDN_HEADS,
        tau: 1,
        d_v: QWEN35_GDN_DV,
        d_k: QWEN35_GDN_DK,
        col_range: 64..128,
        unit_gamma: false,
        seed: 3003,
        t: params.t,
    });
    let spdz2 = resident.share_chunk_to_custodians(&mut quorum, &ep2);
    resident
        .adapt_wy_chunk_spdz(&mut quorum, spdz2, &[1, 2], false)
        .expect("N=8192 ep2 overlapping adapt");

    // Verify `#tooth` refusal on Episode 1 (`K_2^T K_1 != 0`), then execute W0 Mode B WY chunk replay!
    assert_eq!(
        resident
            .unlearn_w0_orthogonal_fast(&mut quorum, 1, &[0, 1])
            .unwrap_err(),
        ContinualGdnError::CrossTermNonOrthogonal {
            episode_id: 1,
            post_chunk_id: 2,
        }
    );

    let t_u1 = Instant::now();
    let (_, u1_bytes, u1_metrics) = resident
        .unlearn_w0_wy_chunk_replay(&mut quorum, 1, &[0, 1])
        .expect("N=8192 WY chunk replay unlearn");
    let u1_total_ms = t_u1.elapsed().as_secs_f64() * 1e3;
    eprintln!("u1_total complete in {u1_total_ms:.2} ms");
    verify_continual_whir_state_bytes(
        &params,
        resident.handles(),
        resident.ciphertexts(),
        &u1_bytes,
    )
    .expect("u1 standalone WHIR verify");

    let state_after_u1 = resident
        .open_verified_state_for_audit(&mut quorum, &[0, 2])
        .expect("audit open after u1");
    // The earlier orthogonal deletion retains only the decay of episode 0.
    let want_after_u1 = cleartext_multihead_seq(&params.fp_t, &s0, &[tomb_chunk(&ep0), ep2]);
    assert_eq!(
        max_state_diff(&state_after_u1, &want_after_u1),
        0,
        "N=8192 WY chunk replay from ep1 checkpoint must equal cleartext [tomb(ep0), ep2] with max |diff| = 0"
    );

    println!("\n==================== WAVE 11 B61 DARK-GDN CONTINUAL RESIDENT BENCHMARK ====================");
    println!(
        "Geometry: Qwen3.5-0.8B 16x128x128 = 262,144 fast weights in {} B61 N={} ciphertexts (t = {})",
        QWEN35_STATE_CTS, params.n, params.t
    );
    println!(
        "Setup 3-Custodian Hybrid-PQ + SPDZ + RLK: {:.2} ms | Genesis 32-Ct Encrypt+WHIR: {:.2} ms ({} B)",
        setup_ms,
        init_ms,
        gen_bytes.len()
    );
    println!(
        "Adapt Ep0 (tau=2 WY, fresh): total={:.2} ms [read_prove={:.2} ms, spdz+cross={:.2} ms, adapt_prove={:.2} ms, cert_vfy={:.2} ms, whir_prove={:.2} ms, whir_vfy={:.2} ms] | state_whir={} B | hoisted_whir_head0={} B | soundness=({:.2}b WHIR, {:.2}b LogUp) | peak_rss={:.1} MiB",
        ep0_total_ms,
        ep0_metrics.read_prove_ms,
        ep0_metrics.spdz_wy_cross_ms,
        ep0_metrics.adapt_prove_ms,
        ep0_metrics.cert_verify_ms,
        ep0_metrics.whir_prove_ms,
        ep0_metrics.whir_verify_ms,
        ep0_metrics.whir_proof_bytes,
        ep0_metrics.hoisted_whir_sample_bytes,
        ep0_metrics.soundness_whir_bits,
        ep0_metrics.soundness_logup_bits,
        ep0_metrics.peak_rss_mib
    );
    println!(
        "Adapt Ep1 (tau=1 + depth-1 refresh): total={:.2} ms [read_prove={:.2} ms, spdz+cross={:.2} ms, adapt_prove={:.2} ms, cert_vfy={:.2} ms, whir_prove={:.2} ms, whir_vfy={:.2} ms] | state_whir={} B | peak_rss={:.1} MiB",
        ep1_total_ms,
        ep1_metrics.read_prove_ms,
        ep1_metrics.spdz_wy_cross_ms,
        ep1_metrics.adapt_prove_ms,
        ep1_metrics.cert_verify_ms,
        ep1_metrics.whir_prove_ms,
        ep1_metrics.whir_verify_ms,
        ep1_metrics.whir_proof_bytes,
        ep1_metrics.peak_rss_mib
    );
    println!(
        "W0 Unlearn Mode A (Orthogonal Fast Subtract, 262,144 weights): total={:.2} ms [exec+prove={:.2} ms, cert_vfy={:.2} ms, whir_prove={:.2} ms, whir_vfy={:.2} ms] | proof={} B | peak_rss={:.1} MiB",
        u0_total_ms,
        u0_metrics.unlearn_exec_and_prove_ms,
        u0_metrics.cert_verify_ms,
        u0_metrics.whir_prove_ms,
        u0_metrics.whir_verify_ms,
        u0_metrics.whir_proof_bytes,
        u0_metrics.peak_rss_mib
    );
    println!(
        "W0 Unlearn Mode B (Compressed WY Operator Replay, 262,144 weights): total={:.2} ms [exec+prove={:.2} ms, cert_vfy={:.2} ms, whir_prove={:.2} ms, whir_vfy={:.2} ms] | proof={} B | peak_rss={:.1} MiB",
        u1_total_ms,
        u1_metrics.unlearn_exec_and_prove_ms,
        u1_metrics.cert_verify_ms,
        u1_metrics.whir_prove_ms,
        u1_metrics.whir_verify_ms,
        u1_metrics.whir_proof_bytes,
        u1_metrics.peak_rss_mib
    );
    println!(
        "Literature Baseline (Lasagne, eprint 2026/857, 16-level 2^20 BFV VCoED): Table 3 SizeOpt=6.11-12.47 min, 30.00 MB; abstract SIMD=4-5 min"
    );
    println!("===========================================================================================\n");
}
