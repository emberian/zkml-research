//! Comprehensive Integration, Zero-Leakage, & 6-Attack Adversarial Falsifier Suite
//! (`tests/homomorphic_gdn_and_block.rs`):
//! 1. Verifies closed-form BFV noise-budget derivation (`derive_homomorphic_state_noise_budget`)
//!    and empirical `phase_noise_bits` across multi-turn homomorphic state accumulation (proving
//!    `t_61 ~ 2^61` overflows at `L = 2` while `BLUM_PRIME_T32 = 4,355,803,843` achieves `max |diff| = 0`
//!    across `R_refresh = 3` consecutive turns!).
//! 2. Verifies bit-exact equivalence (`max |diff| = 0` mod `t`) of BOTH `HomomorphicUpdateStrategy::TwoMulRelinearizeSum`
//!    (`BFV_Mul_Relin(Enc(alpha_t), Enc(S_{t-1})) + BFV_Mul_Relin(Enc(k_t), Enc(beta_t u_t^T))`)
//!    AND `HomomorphicUpdateStrategy::FusedHoistedK2` across 6 consecutive turns (including `alpha_t = 0`
//!    state reset and periodic `R_refresh = 3` noise-reset crossing!).
//! 3. Verifies bit-exact equivalence (`max |diff| = 0` mod `t`) of the full 3-Custodian Encrypted `Qwen3.8`
//!    Hybrid Block (`EncryptedQwenHybridBlock`, tested at both `E = 8` and `E = 16` experts, `Top-2`)
//!    against `cleartext_qwen_hybrid_block_step` across 4 consecutive stateful turns, AND verifies
//!    **zero expert-routing leakage** to the untrusted host across disjoint active expert pairs!
//! 4. **All 6 Required Adversarial Attacks & Falsifiers**:
//!    - Attack 1: Forged relinearized state `Ct` / unverified `Ct3` handle -> REFUSED (`C8` & `Relin`)
//!    - Attack 2: Unverified router / state ciphertext `E2S` decryption-oracle attempt -> REFUSED (`C8 ABORT` before share release)
//!    - Attack 3: `HoistedSuccinctBundle` PCS / Merkle / Hole-B quotient shift on homomorphic state update -> REFUSED
//!    - Attack 4: Forged `R_PD` partial decryption share (`offset_partial` & `unrelated_boundary_shares`) -> REFUSED
//!    - Attack 5: Malicious SPDZ `RMSNorm` `r_inv` quadratic witness forgery & custodian MAC tampering -> REFUSED
//!    - Attack 6: Malicious Private-Router Top-2 MoE selector forgery (`C1` non-boolean, `C2` sum != 1, duplicate expert, MAC tamper) -> REFUSED

use darkstep::arith::addmod;
use darkvfhe::cert::{
    commit_persistent_grid_pcs, ct2_handle, ct3_handle, prove_hoisted_succinct_bundle,
    verify_hoisted_succinct_bundle, HoistedSuccinctBundle,
};
use darkvfhe::dark_block::{
    cleartext_qwen_hybrid_block_step, cleartext_router_top2_mod_t,
    derive_homomorphic_state_noise_budget, diagnostic_ct2_phase_noise_bits, params_n8192_homo,
    params_ring_homo, setup_threshold_cluster_with_rlk, spdz_private_router_top2,
    verify_and_ingest_pinned_persistent_bundle, verify_and_ingest_relinearized_ct,
    verify_spdz_rmsnorm_witness, verify_spdz_top2_selector_constraints, EncryptedQwenHybridBlock,
    HomomorphicDarkGdnResident, HomomorphicGdnState, HomomorphicUpdateStrategy, QwenHybridWeights,
    BLUM_PRIME_T32,
};
use darkvfhe::dark_gdn::{
    cleartext_gdn_step_mod_t, verify_pd_succinct_proof, ThreeCustodianCluster,
};
use darkvfhe::digits::LiftMode;
use darkvfhe::logup_gkr::LogUpConfig;
use darkvfhe::rns_hoist::{Ct3, HoistedEngine};
use darkvfhe::succinct_pcs::PcsRng;
use darkvfhe::HoistedParams;
use std::sync::Arc;

#[test]
fn test_noise_budget_derivation_t61_vs_blum_t32_at_n8192() {
    let p_t61 = HoistedParams::n8192();
    let e_t61 = (1u128 << 111) - 1;
    let sum_t61 = derive_homomorphic_state_noise_budget(&p_t61, e_t61, 2, 4);
    assert_eq!(
        sum_t61.r_refresh_correctness, 1,
        "At log2(Q)=183, log2(t)=61, unrefreshed ct*ct depth is strictly L=1 (R_refresh=1)"
    );
    assert!(!sum_t61.per_turn[1].bit_exact_decryption_safe);

    let p_t32 = params_n8192_homo();
    assert_eq!(p_t32.t, BLUM_PRIME_T32);
    let sum_t32 = derive_homomorphic_state_noise_budget(&p_t32, e_t61, 2, 4);
    assert_eq!(
        sum_t32.r_refresh_correctness, 3,
        "At log2(Q)=183, Blum t=4355803843, R_refresh=3 (2 pure homomorphic state updates per noise-reset crossing!)"
    );
    assert!(sum_t32.per_turn[0].tvd_40b_drowning_holds);
    assert!(sum_t32.per_turn[0].bit_exact_decryption_safe);
    assert!(sum_t32.per_turn[1].bit_exact_decryption_safe);
    assert!(sum_t32.per_turn[2].bit_exact_decryption_safe);
    assert!(!sum_t32.per_turn[3].bit_exact_decryption_safe);
}

#[test]
fn test_homomorphic_gdn_both_strategies_6_turns_bit_exact() {
    for strategy in [
        HomomorphicUpdateStrategy::TwoMulRelinearizeSum,
        HomomorphicUpdateStrategy::FusedHoistedK2,
    ] {
        let params = Arc::new(params_ring_homo(64));
        let engine = Arc::new(HoistedEngine::new(params.clone()));
        let seed = [0x4Au8; 32];
        let (mut cluster, rlk) =
            setup_threshold_cluster_with_rlk(params.clone(), engine.clone(), seed).unwrap();

        let vocab_size = 16usize;
        let d_k = 8usize;
        let d_v = 8usize;
        let fp_t = &params.fp_t;
        let t_mod = params.t;

        let embed_table: Vec<Vec<u64>> = (0..vocab_size)
            .map(|tok| (0..d_k).map(|i| ((tok * 13 + i * 5 + 3) as u64) % t_mod).collect())
            .collect();
        let mut state_ref: Vec<Vec<u64>> = (0..d_k)
            .map(|i| (0..d_v).map(|j| ((i * 7 + j * 3 + 1) as u64) % 29).collect())
            .collect();
        let w_q: Vec<Vec<u64>> = (0..d_k)
            .map(|r| (0..d_k).map(|c| ((r * 3 + c + 1) as u64) % 11).collect())
            .collect();
        let w_k: Vec<Vec<u64>> = (0..d_k)
            .map(|r| (0..d_k).map(|c| ((r + c * 5 + 2) as u64) % 11).collect())
            .collect();
        let w_v: Vec<Vec<u64>> = (0..d_v)
            .map(|r| (0..d_k).map(|c| ((r * 2 + c * 3 + 4) as u64) % 11).collect())
            .collect();

        let mut resident = HomomorphicDarkGdnResident::initialize(
            &mut cluster,
            &embed_table,
            &state_ref,
            w_q.clone(),
            w_k.clone(),
            w_v.clone(),
            LiftMode::ExactGarner15,
            LogUpConfig::MonolithicC4,
            3, // R_refresh = 3: Turns 0,1 homomorphic -> Turn 2 reset -> Turns 3,4 homomorphic -> Turn 5 reset!
            strategy,
        )
        .unwrap();

        // 6 consecutive turns including alpha_t = 0 reset on Turn 3!
        let turns = [
            (2usize, 3u64, 2u64),
            (11usize, 5u64, 4u64),
            (7usize, 2u64, 6u64),
            (15usize, 0u64, 5u64),
            (0usize, 7u64, 3u64),
            (9usize, 4u64, 8u64),
        ];

        for (turn_idx, &(tok, alpha, beta)) in turns.iter().enumerate() {
            let (y_got, metrics) = resident
                .step_turn(&mut cluster, &rlk, turn_idx, tok, alpha, beta)
                .unwrap();

            let x = &embed_table[tok];
            let q: Vec<u64> = w_q.iter().map(|r| fp_t.dot(r, x)).collect();
            let k: Vec<u64> = w_k.iter().map(|r| fp_t.dot(r, x)).collect();
            let v: Vec<u64> = w_v.iter().map(|r| fp_t.dot(r, x)).collect();
            let (y_want, s_next) =
                cleartext_gdn_step_mod_t(fp_t, &state_ref, &q, &k, &v, alpha, beta);
            assert_eq!(
                y_got, y_want,
                "Strategy {:?} turn {} output mismatch vs cleartext!",
                strategy, turn_idx
            );
            state_ref = s_next;

            // Verify cadence behavior & empirical state noise stays well below ceiling:
            let want_refreshed = (turn_idx + 1) % 3 == 0;
            assert_eq!(metrics.state_update_detail.refreshed_via_crossing, want_refreshed);
            if !want_refreshed {
                assert_eq!(metrics.state_update_detail.shipped_s2e_cts, 1 + resident.gdn_state.r_gdn);
            }
            let mut s0_flat = vec![0u64; params.n];
            for r_in in 0..resident.gdn_state.dr {
                for c_in in 0..resident.gdn_state.dc {
                    s0_flat[r_in * resident.gdn_state.dc + c_in] = state_ref[c_in][r_in];
                }
            }
            let state_noise_b = diagnostic_ct2_phase_noise_bits(
                &params,
                &engine,
                seed,
                &resident.gdn_state.enc_state_t_grid[0][0],
                &s0_flat,
            );
            assert!(
                state_noise_b < 140.0,
                "empirical state phase noise {state_noise_b:.2}b exceeded safe bound"
            );
        }
    }
}

#[test]
fn test_full_encrypted_qwen38_hybrid_block_e8_and_e16_zero_routing_leakage() {
    for &num_experts in &[8usize, 16usize] {
        let params = Arc::new(params_ring_homo(64));
        let engine = Arc::new(HoistedEngine::new(params.clone()));
        let (mut cluster, rlk) =
            setup_threshold_cluster_with_rlk(params.clone(), engine, [0x61u8 + num_experts as u8; 32])
                .unwrap();

        let weights = QwenHybridWeights::sample_deterministic(
            &params.fp_t,
            12,          // vocab_size
            8,           // d_model
            8,           // d_k
            8,           // d_v
            num_experts, // E in {8, 16}
            4,           // d_ff
            20261121 + num_experts as u64,
        );
        let mut state_ref: Vec<Vec<u64>> = (0..8)
            .map(|i| (0..8).map(|j| ((i * 3 + j * 2 + 1) as u64) % 17).collect())
            .collect();

        let mut block = EncryptedQwenHybridBlock::initialize(
            &mut cluster,
            &weights,
            &state_ref,
            LiftMode::ExactGarner15,
            LogUpConfig::MonolithicC4,
            3,
            HomomorphicUpdateStrategy::FusedHoistedK2,
        )
        .unwrap();

        let mut seen_expert_pairs = Vec::new();
        let mut host_views = Vec::new();

        for (turn_idx, &tok_id) in [1usize, 5, 9, 11].iter().enumerate() {
            let (h_got, metrics) = block
                .step_turn(&mut cluster, &rlk, turn_idx, tok_id)
                .expect("encrypted Qwen3.8 hybrid block turn must succeed");

            let (h_want, s_next, top2_exps) =
                cleartext_qwen_hybrid_block_step(&params.fp_t, &weights, &state_ref, tok_id);
            assert_eq!(
                h_got, h_want,
                "E={num_experts} Turn {turn_idx} (tok={tok_id}) hybrid block output mismatch vs cleartext!"
            );
            state_ref = s_next;
            seen_expert_pairs.push(top2_exps);
            host_views.push(metrics.host_moe_view);
        }

        // Verify multiple distinct Top-2 expert pairs fired in cleartext while the host's observable
        // ciphertext shapes, residue counts, and non-zero RLWE mask distributions remain 100% invariant!
        assert!(
            seen_expert_pairs.windows(2).any(|w| w[0] != w[1]),
            "test turns must exercise distinct Top-2 expert selections ({seen_expert_pairs:?})"
        );
        for (idx, view) in host_views.iter().enumerate() {
            assert_eq!(view.enc_kronecker_gate_up_inputs[0].len(), host_views[0].enc_kronecker_gate_up_inputs[0].len());
            assert_eq!(view.enc_kronecker_down_input.len(), host_views[0].enc_kronecker_down_input.len());
            // Every 1-hot selector ciphertext must be freshly RLWE-encrypted (`c0, c1` full-entropy non-zero, unique handles):
            for r in 0..2 {
                let ct_sel = &view.enc_one_hot_selectors[r];
                assert!(ct_sel.c0.iter().filter(|&&v| v != 0).count() == ct_sel.c0.len());
                assert!(ct_sel.c1.iter().filter(|&&v| v != 0).count() == ct_sel.c1.len());
                if idx > 0 {
                    assert_ne!(
                        view.h_one_hot_selectors[r],
                        host_views[0].h_one_hot_selectors[r],
                        "selector ciphertexts must use fresh crossing masks every turn (zero replay leakage!)"
                    );
                }
            }
        }
    }
}

#[test]
fn test_all_six_homomorphic_and_hybrid_block_adversarial_attacks() {
    let params = Arc::new(params_ring_homo(64));
    let engine = Arc::new(HoistedEngine::new(params.clone()));
    let (mut cluster, rlk) =
        setup_threshold_cluster_with_rlk(params.clone(), engine.clone(), [0x88u8; 32]).unwrap();
    let n = params.n;
    let fp0 = params.fp[0];
    let mut rng = PcsRng::from_seed([0x55u8; 32]);

    let a_grid = vec![vec![
        cluster.pub_key.encrypt_pk(&(0..n).map(|j| (j as u64) % 9).collect::<Vec<_>>(), &mut rng),
        cluster.pub_key.encrypt_pk(&(0..n).map(|j| ((j + 4) as u64) % 9).collect::<Vec<_>>(), &mut rng),
    ]];
    let b_vec = vec![
        cluster.pub_key.encrypt_pk(&{
            let mut v = vec![0u64; n];
            v[0] = 3; // alpha_t
            v
        }, &mut rng),
        cluster.pub_key.encrypt_pk(&(0..n).map(|j| if j % 8 == 0 { 5 } else { 0 }).collect::<Vec<_>>(), &mut rng),
    ];
    let ha: Vec<Vec<[u8; 32]>> = a_grid.iter().map(|r| r.iter().map(ct2_handle).collect()).collect();
    let hb: Vec<[u8; 32]> = b_vec.iter().map(ct2_handle).collect();

    for cust in &mut cluster.custodians {
        for r in &ha {
            for &h in r {
                cust.register_verified_input_handle(h);
            }
        }
        for &h in &hb {
            cust.register_verified_input_handle(h);
        }
    }

    let (honest_ct3s, honest_bun, _, _) = prove_hoisted_succinct_bundle(
        &engine,
        &a_grid,
        &b_vec,
        None,
        LiftMode::ExactGarner15,
        LogUpConfig::MonolithicC4,
    )
    .unwrap();
    let honest_bytes = honest_bun.to_bytes();
    let hout_ct3: Vec<[u8; 32]> = honest_ct3s.iter().map(ct3_handle).collect();
    let honest_relin = engine.relinearize_ct3(&honest_ct3s[0], &rlk);

    // =========================================================================
    // ATTACK 1: Forged Relinearized State `Ct` & Unverified `Ct3` Relin Attempt
    // =========================================================================
    {
        // 1a. Before `hout_ct3[0]` is verified via `HoistedSuccinctBundle`, relinearization ingest MUST abort (`C8`)!
        let err_unver = verify_and_ingest_relinearized_ct(
            &mut cluster.custodians[0],
            &engine,
            &rlk,
            &hout_ct3[0],
            &honest_ct3s[0],
            &honest_relin,
        )
        .expect_err("unverified Ct3 handle must trigger C8 abort on relinearization");
        assert!(err_unver.contains("C8 ABORT"), "{err_unver}");

        // 1b. After ingesting `honest_bytes` on Custodian 0, mutate 1 limb word of `honest_relin`:
        cluster.custodians[0]
            .verify_and_ingest_succinct_bundle(
                &ha,
                &hb,
                &hout_ct3,
                Some(&a_grid),
                &b_vec,
                &honest_ct3s,
                &honest_bytes,
            )
            .unwrap();
        let mut forged_relin = honest_relin.clone();
        forged_relin.c0[0] = addmod(forged_relin.c0[0], 1, params.qp[0]);
        let err_relin = verify_and_ingest_relinearized_ct(
            &mut cluster.custodians[0],
            &engine,
            &rlk,
            &hout_ct3[0],
            &honest_ct3s[0],
            &forged_relin,
        )
        .expect_err("forged relinearized state ciphertext must be refused");
        assert!(err_relin.contains("Relinearization verification FAILED"), "{err_relin}");
    }

    // =========================================================================
    // ATTACK 2: Unverified Router / State `E2S` Decryption-Oracle Attempt (`C8` Gate)
    // =========================================================================
    {
        // Custodians 1 & 2 have NOT ingested `honest_bytes` yet -> `e2s_ct3` MUST abort before share release!
        let err_c8 = cluster
            .e2s_ct3(&hout_ct3[0], &honest_ct3s[0], &[0, 1], "oracle_probe")
            .expect_err("C8 gate must refuse E2S when any custodian lacks verified handle");
        assert!(err_c8.contains("C8 ABORT"), "{err_c8}");
    }

    // =========================================================================
    // ATTACK 3: `HoistedSuccinctBundle` PCS / Merkle / Hole-B Quotient Forgery on State Update
    // =========================================================================
    {
        let mut hole_b_ct3 = honest_ct3s.clone();
        for k in 0..3 {
            hole_b_ct3[0].c0[k * n] = addmod(hole_b_ct3[0].c0[k * n], 1, params.qp[k]);
        }
        let h_holeb = vec![ct3_handle(&hole_b_ct3[0])];
        assert!(
            verify_hoisted_succinct_bundle(
                &params,
                &ha,
                &hb,
                &h_holeb,
                Some(&a_grid),
                &b_vec,
                &hole_b_ct3,
                &honest_bun,
            )
            .is_err(),
            "Hole B quotient shift on homomorphic state update must be refused"
        );

        let mut bad_pcs = honest_bun.clone();
        bad_pcs.pcs_opening.opened_cols[0][0] = fp0.add(bad_pcs.pcs_opening.opened_cols[0][0], 1);
        let dec_bad = HoistedSuccinctBundle::from_bytes(&bad_pcs.to_bytes(), &params).unwrap();
        assert!(
            verify_hoisted_succinct_bundle(
                &params,
                &ha,
                &hb,
                &hout_ct3,
                Some(&a_grid),
                &b_vec,
                &honest_ct3s,
                &dec_bad,
            )
            .is_err(),
            "mutated PCS column in state update bundle must be refused"
        );
    }

    // =========================================================================
    // ATTACK 4: Forged `R_PD` Partial Decryption Share & Cross-Ciphertext Replay
    // =========================================================================
    {
        for i in 1..3 {
            cluster.custodians[i]
                .verify_and_ingest_succinct_bundle(
                    &ha,
                    &hb,
                    &hout_ct3,
                    Some(&a_grid),
                    &b_vec,
                    &honest_ct3s,
                    &honest_bytes,
                )
                .unwrap();
        }
        let zero_mask = cluster.pub_key.encrypt_pk(&vec![0u64; n], &mut rng);
        let mut pd0 = cluster.custodians[0]
            .partial_decrypt_ct3_checked(&engine, &hout_ct3[0], &honest_ct3s[0], &zero_mask, "pd_atk")
            .unwrap();

        // Cross-ciphertext replay (`unrelated_boundary_shares`):
        let other_ct3 = Ct3 {
            c0: honest_ct3s[0].c0.clone(),
            c1: b_vec[1].c1.clone(),
            c2: honest_ct3s[0].c2.clone(),
        };
        assert!(
            verify_pd_succinct_proof(
                &params,
                0,
                &cluster.custodians[0].key_pcs_root,
                &cluster.custodians[0].key_pcs_shape,
                cluster.custodians[0].smudge_bound,
                cluster.custodians[0].smudge_top_bits,
                &other_ct3,
                "pd_atk",
                &pd0,
            )
            .is_err(),
            "R_PD replay onto different ciphertext must fail"
        );

        // Tamper `partial_rns[0] += 1`:
        pd0.partial_rns[0] = addmod(pd0.partial_rns[0], 1, params.qp[0]);
        assert!(
            verify_pd_succinct_proof(
                &params,
                0,
                &cluster.custodians[0].key_pcs_root,
                &cluster.custodians[0].key_pcs_shape,
                cluster.custodians[0].smudge_bound,
                cluster.custodians[0].smudge_top_bits,
                &honest_ct3s[0],
                "pd_atk",
                &pd0,
            )
            .is_err(),
            "R_PD tampered partial residue must fail"
        );
    }

    // =========================================================================
    // ATTACK 5: Malicious SPDZ `RMSNorm` `r_inv` Quadratic Witness Forgery & MAC Tampering
    // =========================================================================
    {
        let s_ms = cluster.share_authenticated(4); // 4 is QR: chi = 1, r_inv = 2^{-1} mod t
        let chi_good = cluster.share_authenticated(1);
        let r_inv_bad = cluster.share_authenticated(7); // 4 * 49 != 1 mod t!
        let err_quad =
            verify_spdz_rmsnorm_witness(&mut cluster, s_ms, chi_good, r_inv_bad, "atk5_quad")
                .expect_err("forged r_inv must fail quadratic RMSNorm check");
        assert!(err_quad.contains("RMSNorm quadratic r_inv check FAILED"), "{err_quad}");

        // Also test corrupted custodian SPDZ MAC on valid `r_inv = 2^{-1} mod t`:
        let mut r_inv_corrupt = cluster.share_authenticated(params.fp_t.inv(2));
        ThreeCustodianCluster::corrupt_mac_for_test(&mut r_inv_corrupt, 2, 1, params.t);
        let err_mac =
            verify_spdz_rmsnorm_witness(&mut cluster, s_ms, chi_good, r_inv_corrupt, "atk5_mac")
                .expect_err("corrupted SPDZ MAC in RMSNorm must fail mac_check");
        assert!(err_mac.contains("SPDZ MAC check FAILED"), "{err_mac}");
    }

    // =========================================================================
    // ATTACK 6: Malicious Private-Router Top-2 Selector Forgery (`C1`, `C2`, Duplicate Expert)
    // =========================================================================
    {
        // 6a. Non-boolean cheat `[2, t - 1, 0, ...]` (sums to 1, but violates `C1` booleanity!):
        let mut bad_bool0 = vec![cluster.share_authenticated(0); 8];
        bad_bool0[0] = cluster.share_authenticated(2);
        bad_bool0[1] = cluster.share_authenticated(params.t - 1);
        let mut valid_sel1 = vec![cluster.share_authenticated(0); 8];
        valid_sel1[3] = cluster.share_authenticated(1);
        let err_c1 =
            verify_spdz_top2_selector_constraints(&mut cluster, &bad_bool0, &valid_sel1, "atk6_c1")
                .expect_err("non-boolean Top-2 selector summing to 1 must fail C1");
        assert!(err_c1.contains("C1 booleanity"), "{err_c1}");

        // 6b. Duplicate-expert cheat (`sel0 == sel1`, selecting same expert twice!):
        let err_dup =
            verify_spdz_top2_selector_constraints(&mut cluster, &valid_sel1, &valid_sel1, "atk6_dup")
                .expect_err("duplicate Top-2 expert selection must fail disjointness");
        assert!(err_dup.contains("disjointness"), "{err_dup}");

        // 6c. Zero-expert capacity-drop cheat (`sum == 0`, skipping expert compute!):
        let zero_sel = vec![cluster.share_authenticated(0); 8];
        let err_c2 =
            verify_spdz_top2_selector_constraints(&mut cluster, &zero_sel, &valid_sel1, "atk6_c2")
                .expect_err("all-zero capacity-drop selector must fail C2 sum-to-1");
        assert!(err_c2.contains("C2 one-hot sum-to-1"), "{err_c2}");
    }

    // =========================================================================
    // ATTACK 7: Cross-Layer Persistent-Matrix Substitution (`W_gdn_out` <-> `W_router`)
    // =========================================================================
    {
        let grid_w1 = a_grid.clone();
        let grid_w2 = vec![vec![
            cluster.pub_key.encrypt_pk(&(0..n).map(|j| ((j * 3 + 1) as u64) % 9).collect::<Vec<_>>(), &mut rng),
            cluster.pub_key.encrypt_pk(&(0..n).map(|j| ((j * 5 + 2) as u64) % 9).collect::<Vec<_>>(), &mut rng),
        ]];
        let ha_w1: Vec<Vec<[u8; 32]>> = grid_w1.iter().map(|r| r.iter().map(ct2_handle).collect()).collect();
        let ha_w2: Vec<Vec<[u8; 32]>> = grid_w2.iter().map(|r| r.iter().map(ct2_handle).collect()).collect();
        let (pre_w1, pcs_w1) =
            commit_persistent_grid_pcs(&engine, &grid_w1, LiftMode::ExactGarner15).unwrap();
        let (_, pcs_w2) =
            commit_persistent_grid_pcs(&engine, &grid_w2, LiftMode::ExactGarner15).unwrap();
        for cust in &mut cluster.custodians {
            cust.ingest_verified_persistent_grid(
                LiftMode::ExactGarner15,
                &ha_w1,
                &pcs_w1.offline_range_proof,
            )
            .unwrap();
            cust.ingest_verified_persistent_grid(
                LiftMode::ExactGarner15,
                &ha_w2,
                &pcs_w2.offline_range_proof,
            )
            .unwrap();
        }
        // Host proves `W_1 * b_vec` (with valid verified `pcs_w1`), then attempts to pass it off as `W_2 * b_vec`!
        let (swapped_out, swapped_bun, _, _) = prove_hoisted_succinct_bundle(
            &engine,
            &grid_w1,
            &b_vec,
            Some((&pre_w1, &pcs_w1)),
            LiftMode::ExactGarner15,
            LogUpConfig::MonolithicC4,
        )
        .unwrap();
        let h_swapped: Vec<[u8; 32]> = swapped_out.iter().map(ct3_handle).collect();
        let err_swap = verify_and_ingest_pinned_persistent_bundle(
            &mut cluster.custodians[0],
            &pcs_w2.offline_range_proof.root,
            &ha_w2,
            &hb,
            &h_swapped,
            &grid_w2,
            &b_vec,
            &swapped_out,
            &swapped_bun.to_bytes(),
        )
        .expect_err("cross-layer persistent matrix substitution must be refused");
        assert!(err_swap.contains("C8 ABORT"), "{err_swap}");
    }

    // =========================================================================
    // AUDIT REGRESSIONS (#112): OS CSPRNG Non-Determinism, Cadence Guard,
    // `denom == 0` Partition-of-Unity (`g0 + g1 == 1`), & Atomic `StagedStateUpdate`
    // =========================================================================
    {
        let s0 = vec![vec![3u64; 8]; 8];
        // (a) Unsafe cadence (> R_refresh_correctness) rejected; R_refresh=1 marks strict 40b TVD:
        assert!(HomomorphicGdnState::initialize(
            &mut cluster,
            &s0,
            LiftMode::ExactGarner15,
            LogUpConfig::MonolithicC4,
            99,
            HomomorphicUpdateStrategy::FusedHoistedK2,
        )
        .is_err());
        let st_a = HomomorphicGdnState::initialize(
            &mut cluster,
            &s0,
            LiftMode::ExactGarner15,
            LogUpConfig::MonolithicC4,
            1,
            HomomorphicUpdateStrategy::FusedHoistedK2,
        )
        .unwrap();
        assert!(st_a.tvd_40b_strict_mode);
        // (b) OS CSPRNG produces fresh independent ciphertexts on identical genesis plaintext:
        let st_b = HomomorphicGdnState::initialize(
            &mut cluster,
            &s0,
            LiftMode::ExactGarner15,
            LogUpConfig::MonolithicC4,
            3,
            HomomorphicUpdateStrategy::FusedHoistedK2,
        )
        .unwrap();
        assert!(!st_b.tvd_40b_strict_mode);
        assert_ne!(st_a.h_state_t_grid, st_b.h_state_t_grid);

        // (c) Construct an exact `denom == 0 (mod t)` Top-2 logit vector (`(1 + l0^2) + (1 + l1^2) == 0 mod t`)
        //     and verify BOTH cleartext and 3-party SPDZ router satisfy `g0 + g1 == 1 (mod t)`!
        let fp_t = &params.fp_t;
        let t = params.t;
        let (l0_z, l1_z) = (1u64..1000)
            .find_map(|cand| {
                let rhs = fp_t.sub(t - 2, fp_t.mul(cand, cand));
                if fp_t.pow(rhs, (t - 1) / 2) == 1 {
                    let root = fp_t.pow(rhs, (t + 1) / 4);
                    Some((cand, root))
                } else {
                    None
                }
            })
            .expect("sum-of-two-squares solution for t - 2 must exist in F_t");
        // Ensure `l0_z, l1_z` are the Top-2 largest integers `< t` by using `t - l0_z, t - l1_z`!
        let top0 = (t - l0_z) % t;
        let top1 = (t - l1_z) % t;
        assert_eq!(
            fp_t.add(fp_t.add(1, fp_t.mul(top0, top0)), fp_t.add(1, fp_t.mul(top1, top1))),
            0
        );
        let z_logits = vec![0, top0, 1, top1];
        let (exps_want, gates_want) = cleartext_router_top2_mod_t(fp_t, &z_logits);
        assert_eq!(fp_t.add(gates_want[0], gates_want[1]), 1);
        let z_logits_sh = cluster.share_vec(&z_logits);
        let ([sel0_got, sel1_got], [g0_sh, g1_sh]) =
            spdz_private_router_top2(&mut cluster, &z_logits_sh, None, "zero_denom_reg").unwrap();
        let g_open = cluster.open_verified_output(&[g0_sh, g1_sh], "zero_denom_g").unwrap();
        assert_eq!(g_open, gates_want.to_vec());
        assert_eq!(fp_t.add(g_open[0], g_open[1]), 1);
        let s0_open = cluster.open_verified_output(&sel0_got, "zero_denom_s0").unwrap();
        let s1_open = cluster.open_verified_output(&sel1_got, "zero_denom_s1").unwrap();
        assert_eq!(s0_open[exps_want[0]], 1);
        assert_eq!(s1_open[exps_want[1]], 1);

        // (d) Atomic `prepare_state_update` leaves `st_b` untouched until `commit_staged_update`:
        let h_before = st_b.h_state_t_grid.clone();
        let turns_before = st_b.turns_since_refresh;
        let alpha_sh = cluster.share_authenticated(2);
        let u_sh = vec![cluster.share_authenticated(1); 8];
        let k_sh = vec![cluster.share_authenticated(1); 8];
        let k_slots: Vec<(usize, _)> = k_sh.iter().copied().enumerate().collect();
        let (k_ct, hk) = cluster.s2e_encrypt_slots(&k_slots, "reg_kfwd").unwrap();
        let _staged = st_b
            .prepare_state_update(&mut cluster, &rlk, 99, alpha_sh, &u_sh, &k_sh, &[k_ct], &[hk])
            .unwrap();
        assert_eq!(st_b.h_state_t_grid, h_before);
        assert_eq!(st_b.turns_since_refresh, turns_before);
    }
}
