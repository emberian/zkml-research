//! End-to-End Integration & Planted Adversarial Soundness Suite (`5` Required Attacks + `4`
//! `Claude Fable` / `Codex gpt-6.2-astra` Cross-Audit Exploits: Decoy `U ⊥ K` Registration,
//! Zeroed `L = 0` WY Bypass, Single-Entry `S_unlearned = 122880` `mod P` Wraparound, & MMR Leaf-Index Swap)
//! over Real Pretrained `Qwen/Qwen3.5-0.8B-Base` (`H_v = 16, d_k = d_v = 128`, `248,320` vocab)
//! and `Qwen3.8` (`H_v = 48 -> 64` head width).

use qwen35audit::continual_memory::{
    apply_continual_wy_episode, apply_rank_r_subspace_unlearning, build_gram_schmidt_subspace_basis,
    canonical_three_episodes, evaluate_episode_recall, prove_continual_wy_update_zk,
    prove_zk_unlearning_certificate, readout_snr_db_vs_counterfactual,
    verify_continual_wy_update_zk, verify_zk_unlearning_certificate, ContinualEpisodeMmr,
    FastWeightMemoryState, GramSchmidtSubspaceBasis, PreloadedQwen35Model, ProverVaultKey,
    QwenBpeTokenizer, ZkContinualUpdateProof, ZkUnlearningCertificate, LIMB_RADIX, M_GS, S_BND_HALF,
    TAU_ZERO, UHI_HALF, ULO_HALF,
};
use qwen35audit::ext4::{bb_from_i64, P};
use qwen35audit::safetensors_mmap::{
    MmapSafetensors, QWEN35_SAFETENSORS_FILE, QWEN35_TOKENIZER_FILE,
};

#[test]
fn test_real_qwen35_and_qwen38_continual_learning_rank_r_unlearning_and_all_planted_attacks() {
    let mmap = MmapSafetensors::open(QWEN35_SAFETENSORS_FILE).expect("mmap Qwen3.5 safetensors");
    let tok = QwenBpeTokenizer::from_file(QWEN35_TOKENIZER_FILE).expect("load Qwen3.5 tokenizer");
    let model = PreloadedQwen35Model::load(&mmap).expect("preload 24L Qwen3.5");
    let specs = canonical_three_episodes();

    let (ep_a, ep_a48) = model
        .extract_episode_dual_16_and_48(&tok, specs[0].0, specs[0].1, &specs[0].2)
        .expect("extract Episode A");
    let (ep_b, ep_b48) = model
        .extract_episode_dual_16_and_48(&tok, specs[1].0, specs[1].1, &specs[1].2)
        .expect("extract Episode B");
    let (ep_c, ep_c48) = model
        .extract_episode_dual_16_and_48(&tok, specs[2].0, specs[2].1, &specs[2].2)
        .expect("extract Episode C");

    let gain = 192.0f32;
    let vault_key = ProverVaultKey::random();

    // 1. Baseline `S_0 = 0` before adaptation:
    let s0 = FastWeightMemoryState::zero(16);
    let base_a = evaluate_episode_recall(&model, &s0, &ep_a, gain);
    let base_b = evaluate_episode_recall(&model, &s0, &ep_b, gain);
    let base_c = evaluate_episode_recall(&model, &s0, &ep_c, gain);
    assert_eq!(base_b.recall_rate, 0.0, "S_0 must not know private Episode B facts");
    assert_eq!(base_a.mean_readout_l2, 0.0);
    assert_eq!(base_c.mean_readout_l2, 0.0);

    let vault_key_other = ProverVaultKey::random();
    let basis_a = build_gram_schmidt_subspace_basis(&ep_a);
    let basis_b = build_gram_schmidt_subspace_basis(&ep_b);
    let basis_c = build_gram_schmidt_subspace_basis(&ep_c);
    assert_eq!(basis_b.rank_r, 6);

    let wit1 = apply_continual_wy_episode(&s0, &ep_a);
    let mut mmr_alt = ContinualEpisodeMmr::new();
    let (_, s0_root_alt, _, _, f_req_alt) =
        prove_continual_wy_update_zk(&vault_key_other, &wit1, &basis_a, &[0x11; 32], &mut mmr_alt)
            .unwrap();

    // 2. Continual division-free `C = 64` WY adaptation `S_0 -> S_1 -> S_2 -> S_3` (`0` backprop!)
    let mut mmr = ContinualEpisodeMmr::new();
    let nonce_a = [0x11u8; 32];
    let nonce_b = [0x22u8; 32];
    let nonce_c = [0x33u8; 32];

    let (up_pf1, s0_root, mmr_root1, s1_root, f_req_a) =
        prove_continual_wy_update_zk(&vault_key, &wit1, &basis_a, &nonce_a, &mut mmr)
            .expect("prove S0->S1");
    assert_ne!(s0_root, s0_root_alt, "S_0 root salted by ProverVaultKey");
    assert_ne!(f_req_a, f_req_alt, "u_pcs_root salted by ProverVaultKey");
    verify_continual_wy_update_zk(&s0_root, &mmr_root1, &s1_root, &up_pf1)
        .expect("standalone verify S0->S1");

    let wit2 = apply_continual_wy_episode(&wit1.s_post, &ep_b);
    let (up_pf2, s1_root_chk, mmr_root2, s2_root, forget_req_b) =
        prove_continual_wy_update_zk(&vault_key, &wit2, &basis_b, &nonce_b, &mut mmr)
            .expect("prove S1->S2");
    assert_eq!(s1_root, s1_root_chk);
    verify_continual_wy_update_zk(&s1_root, &mmr_root2, &s2_root, &up_pf2)
        .expect("standalone verify S1->S2");

    let wit3 = apply_continual_wy_episode(&wit2.s_post, &ep_c);
    let (up_pf3, s2_root_chk, mmr_root3, s3_root, _f_req_c) =
        prove_continual_wy_update_zk(&vault_key, &wit3, &basis_c, &nonce_c, &mut mmr)
            .expect("prove S2->S3");
    assert_eq!(s2_root, s2_root_chk);
    verify_continual_wy_update_zk(&s2_root, &mmr_root3, &s3_root, &up_pf3)
        .expect("standalone verify S2->S3");

    let s3 = &wit3.s_post;
    let rec3_a = evaluate_episode_recall(&model, s3, &ep_a, gain);
    let rec3_b = evaluate_episode_recall(&model, s3, &ep_b, gain);
    let rec3_c = evaluate_episode_recall(&model, s3, &ep_c, gain);
    assert_eq!(rec3_a.recall_rate, 1.0, "S_3 must recall 100% of Episode A");
    assert_eq!(rec3_b.recall_rate, 1.0, "S_3 must recall 100% of Episode B");
    assert_eq!(rec3_c.recall_rate, 1.0, "S_3 must recall 100% of Episode C");
    assert!(
        rec3_a.mean_cosine > 0.85 && rec3_b.mean_cosine > 0.85 && rec3_c.mean_cosine > 0.85,
        "cosines ({:.4}, {:.4}, {:.4}) must exceed 0.85",
        rec3_a.mean_cosine,
        rec3_b.mean_cosine,
        rec3_c.mean_cosine
    );

    // 3. Counterfactual gold-standard `Train(A + C)` (`0` exposure to Episode B):
    let s_counterfactual = apply_continual_wy_episode(&wit1.s_post, &ep_c).s_post;

    // 4. Fixed-Point Integer Gram–Schmidt Rank-`r` (`r = 6`) Subspace Unlearning of Episode B:
    let unl_wit =
        apply_rank_r_subspace_unlearning(s3, &basis_b).expect("apply rank-6 subspace unlearning");
    let rec_unl_a = evaluate_episode_recall(&model, &unl_wit.s_unlearned, &ep_a, gain);
    let rec_unl_b = evaluate_episode_recall(&model, &unl_wit.s_unlearned, &ep_b, gain);
    let rec_unl_c = evaluate_episode_recall(&model, &unl_wit.s_unlearned, &ep_c, gain);
    let snr_a = readout_snr_db_vs_counterfactual(&unl_wit.s_unlearned, &s_counterfactual, &ep_a);
    let snr_c = readout_snr_db_vs_counterfactual(&unl_wit.s_unlearned, &s_counterfactual, &ep_c);

    let rel_res_b = rec_unl_b.mean_readout_l2 / rec3_b.mean_readout_l2;
    assert_eq!(rec_unl_b.recall_rate, 0.0, "Episode B recall must drop to 0.000");
    assert!(
        rel_res_b < 1e-4,
        "Episode B relative residual norm {rel_res_b:.3e} must be < 10^-4"
    );
    assert!(
        rec_unl_a.recall_rate > 0.99 && rec_unl_c.recall_rate > 0.99,
        "Episodes A & C must preserve > 99% recall"
    );
    assert!(
        snr_a > 35.0 && snr_c > 35.0,
        "Episodes A & C SNR ({snr_a:.2} dB, {snr_c:.2} dB) must exceed 35 dB vs Train(A+C)"
    );

    // 5. Prove & Standalone-Verify Zero-Knowledge Unlearning Certificate tied to `mmr_root3`!
    let mmr_entry_b = mmr.entries[1].clone();
    let mmr_open_b = mmr.open(1);
    let (cert_bytes, sb_root, s_unl_root, f_req_chk) = prove_zk_unlearning_certificate(
        &vault_key,
        &unl_wit,
        &nonce_b,
        Some((mmr_entry_b, mmr_open_b, mmr_root3)),
    )
    .expect("prove ZK unlearning certificate");
    assert_eq!(sb_root, s3_root);
    assert_eq!(f_req_chk, forget_req_b);

    verify_zk_unlearning_certificate(
        &s3_root,
        &s_unl_root,
        &forget_req_b,
        Some(&mmr_root3),
        16,
        6,
        &cert_bytes,
    )
    .expect("standalone ZK unlearning certificate must verify");

    let parsed_cert = ZkUnlearningCertificate::from_bytes(&cert_bytes).unwrap();

    // =========================================================================
    // 6. DETERMINISTIC REJECTION OF ALL 5 CORE ATTACKS + 4 CROSS-AUDIT EXPLOITS
    // =========================================================================

    // Attack 1: Fake unlearning no-op (`S' = S_before`)
    assert!(
        verify_zk_unlearning_certificate(
            &s3_root,
            &s3_root,
            &forget_req_b,
            Some(&mmr_root3),
            16,
            6,
            &cert_bytes,
        )
        .is_err(),
        "Attack 1a (verifier no-op S' = S_before) must be rejected"
    );
    let mut noop_wit = unl_wit.clone();
    noop_wit.s_unlearned = s3.clone();
    let noop_res = ((0..128)
        .map(|ik| s3.s_int_lsb[ik << 4] * basis_b.u_int_lsb[ik << 4])
        .sum::<i64>()
        + M_GS / 2)
        .div_euclid(M_GS);
    noop_wit.res_shift_lsb_hja[0] = bb_from_i64(noop_res + TAU_ZERO);
    assert!(
        prove_zk_unlearning_certificate(&vault_key, &noop_wit, &nonce_b, None).is_err(),
        "Attack 1b (prover witnessing S' = S_before) rejected by D1b residual range check"
    );

    // Attack 2: Partial rank-1 erase leaving rank-`r - 1` secrets intact + `h_v = 1` downgrade
    let mut rank1_basis = basis_b.clone();
    rank1_basis.rank_r = 1;
    for h in 0..16 {
        for a in 1..8 {
            for ik in 0..128 {
                let idx = h + (ik << 4) + (a << 11);
                rank1_basis.u_int_lsb[idx] = 0;
                rank1_basis.u_bb_lsb[idx] = 0;
                rank1_basis.u_lo_shift_lsb[idx] = ULO_HALF as u32;
                rank1_basis.u_hi_shift_lsb[idx] = UHI_HALF as u32;
            }
        }
    }
    let partial_wit = apply_rank_r_subspace_unlearning(s3, &rank1_basis).unwrap();
    let rec_partial_b = evaluate_episode_recall(&model, &partial_wit.s_unlearned, &ep_b, gain);
    assert!(
        rec_partial_b.top1_hits >= 4,
        "Partial rank-1 erase leaves >= 4/6 confidential Episode B facts recoverable"
    );
    let (partial_cert_bytes, _, partial_unl_root, _) =
        prove_zk_unlearning_certificate(&vault_key, &partial_wit, &nonce_b, None).unwrap();
    assert!(
        verify_zk_unlearning_certificate(
            &s3_root,
            &partial_unl_root,
            &forget_req_b,
            Some(&mmr_root3),
            16,
            6,
            &partial_cert_bytes,
        )
        .is_err(),
        "Attack 2a (partial rank-1 erase against forget_request_root) must be rejected"
    );
    assert!(
        verify_zk_unlearning_certificate(&s3_root, &s_unl_root, &forget_req_b, Some(&mmr_root3), 1, 6, &cert_bytes)
            .is_err(),
        "Attack 2b (head count h_v mismatch) must be rejected"
    );

    // Attack 3: Corrupted `U` orthogonality (`u_1 := u_0`) + non-zero inactive column `a = 6`
    let mut bad_orth_basis: GramSchmidtSubspaceBasis = basis_b.clone();
    for h in 0..16 {
        for ik in 0..128 {
            let src = h + (ik << 4);
            let dst = src + (1 << 11);
            bad_orth_basis.u_int_lsb[dst] = bad_orth_basis.u_int_lsb[src];
            bad_orth_basis.u_bb_lsb[dst] = bad_orth_basis.u_bb_lsb[src];
            bad_orth_basis.u_lo_shift_lsb[dst] = bad_orth_basis.u_lo_shift_lsb[src];
            bad_orth_basis.u_hi_shift_lsb[dst] = bad_orth_basis.u_hi_shift_lsb[src];
        }
    }
    assert!(
        apply_rank_r_subspace_unlearning(s3, &bad_orth_basis).is_err(),
        "Attack 3a: corrupted non-orthogonal U rejected"
    );
    let mut bad_inact_basis = basis_b.clone();
    bad_inact_basis.u_int_lsb[6 << 11] = 15;
    bad_inact_basis.u_bb_lsb[6 << 11] = 15;
    assert!(
        apply_rank_r_subspace_unlearning(s3, &bad_inact_basis).is_err(),
        "Attack 3b: non-zero inactive U column rejected"
    );
    let mut bad_gram_cert = parsed_cert.clone();
    bad_gram_cert.gram_shift_at_zg =
        bad_gram_cert.gram_shift_at_zg.add(qwen35audit::ext4::Ext4::ONE);
    assert!(
        verify_zk_unlearning_certificate(
            &s3_root,
            &s_unl_root,
            &forget_req_b,
            Some(&mmr_root3),
            16,
            6,
            &bad_gram_cert.to_bytes(),
        )
        .is_err(),
        "Attack 3c: tampered Gram evaluation rejected"
    );

    // Attack 4: Forged `S_post_root` / `S_unlearned_root` & PCS Merkle tamper
    let mut forged_post_root = s_unl_root;
    forged_post_root[0] ^= 0x55;
    assert!(
        verify_zk_unlearning_certificate(
            &s3_root,
            &forged_post_root,
            &forget_req_b,
            Some(&mmr_root3),
            16,
            6,
            &cert_bytes,
        )
        .is_err(),
        "Attack 4a: forged S_unlearned_root rejected"
    );
    let mut bad_pcs_cert = parsed_cert.clone();
    bad_pcs_cert.s_unlearned_pcs.multiproof.aux_hashes[0][0] ^= 0x80;
    assert!(
        verify_zk_unlearning_certificate(
            &s3_root,
            &s_unl_root,
            &forget_req_b,
            Some(&mmr_root3),
            16,
            6,
            &bad_pcs_cert.to_bytes(),
        )
        .is_err(),
        "Attack 4b: forged PCS Merkle multiproof rejected"
    );
    let mut forged_s3_root = s3_root;
    forged_s3_root[3] ^= 0xAA;
    assert!(
        verify_continual_wy_update_zk(&s2_root, &mmr_root3, &forged_s3_root, &up_pf3).is_err(),
        "Attack 4c: forged continual WY S_post_root rejected"
    );

    // Attack 5: Unlearned-fact residual overflow + `#115` Item 3 single-entry `mod P` wraparound (`122,880 * 16,384 == P - 1`)!
    let mut overflow_wit = unl_wit.clone();
    overflow_wit.res_shift_lsb_hja[0] = (TAU_ZERO * 2 + 1) as u32;
    assert!(
        prove_zk_unlearning_certificate(&vault_key, &overflow_wit, &nonce_b, None).is_err(),
        "Attack 5a: residual >= 2*TAU_ZERO rejected"
    );
    let m_gs_inv_neg = ((P - 1) / (M_GS as u64)) as i64; // 122,880
    assert_eq!(((M_GS * m_gs_inv_neg) as u64 + 1) % P, 0);
    let mut wrap_wit = unl_wit.clone();
    let orig_s0 = wrap_wit.s_unlearned.s_int_lsb[0];
    let forged_s_unl = if orig_s0 >= 0 {
        orig_s0 + m_gs_inv_neg
    } else {
        orig_s0 - m_gs_inv_neg
    };
    // Case 5b-i: Prover updates only `S + 60000` (`< 131072`) leaving `60000 - S` stale -> verifier PCS weld rejects!
    let mut one_sided_wit = wrap_wit.clone();
    one_sided_wit.s_bnd_unl_packed[2 * 16 * 16384] = bb_from_i64(forged_s_unl + S_BND_HALF);
    if let Ok((bad_wrap_cert, sb_w, su_w, fr_w)) =
        prove_zk_unlearning_certificate(&vault_key, &one_sided_wit, &nonce_b, None)
    {
        assert!(
            verify_zk_unlearning_certificate(&sb_w, &su_w, &fr_w, None, 16, 6, &bad_wrap_cert)
                .is_err(),
            "Attack 5b-i: one-sided S_BND tamper must be rejected by standalone verifier!"
        );
    }
    // Case 5b-ii: Prover updates both two-sided slots `(S + 60000, 60000 - S)` -> `60000 - forged < 0` rejected by D1b!
    wrap_wit.s_bnd_unl_packed[2 * 16 * 16384] = bb_from_i64(forged_s_unl + S_BND_HALF);
    wrap_wit.s_bnd_unl_packed[3 * 16 * 16384] = bb_from_i64(S_BND_HALF - forged_s_unl);
    let _ = LIMB_RADIX;
    assert!(
        prove_zk_unlearning_certificate(&vault_key, &wrap_wit, &nonce_b, None).is_err(),
        "Attack 5b-ii (#115 Item 3): S_unlearned M_GS^{{-1}} = 61440 modular wraparound rejected by two-sided sbnd_unl_d1b!"
    );

    // Attack 6 (`#115` Item 1): Register orthogonal decoy `U = basis_a` when proving Episode B (`wit2`)!
    let mut decoy_mmr = ContinualEpisodeMmr::new();
    assert!(
        prove_continual_wy_update_zk(&vault_key, &wit2, &basis_a, &nonce_b, &mut decoy_mmr).is_err(),
        "Attack 6 (#115 Item 1): decoy orthogonal U != span(K) rejected at episode registration!"
    );

    // Attack 7 (`#115` Item 2): Zero out `L = 0` on correlated Episode B WY update (`bypassing (I+L)^{-1}`)!
    let mut bad_wy_pf = ZkContinualUpdateProof::from_bytes(&up_pf2).unwrap();
    bad_wy_pf.l_at_zkk = qwen35audit::ext4::Ext4::ZERO;
    assert!(
        verify_continual_wy_update_zk(&s1_root, &mmr_root2, &s2_root, &bad_wy_pf.to_bytes()).is_err(),
        "Attack 7 (#115 Item 2): forged L != round(K*K^T / M_wy) rejected by kk_gruen!"
    );

    // Attack 8 (`#115` Item 4): Mismatched `episode_idx != mmr_proof.leaf_index`!
    let mut bad_idx_pf = ZkContinualUpdateProof::from_bytes(&up_pf2).unwrap();
    bad_idx_pf.episode_idx = 0;
    assert!(
        verify_continual_wy_update_zk(&s1_root, &mmr_root2, &s2_root, &bad_idx_pf.to_bytes()).is_err(),
        "Attack 8 (#115 Item 4): episode_idx != mmr_proof.leaf_index rejected!"
    );

    // =========================================================================
    // 7. `Qwen3.8` Full `H_v = 48` (`-> 64`, `1,048,576` Memory Cells!) Suite
    // =========================================================================
    let s0_48 = FastWeightMemoryState::zero(48);
    let s1_48 = apply_continual_wy_episode(&s0_48, &ep_a48).s_post;
    let s2_48 = apply_continual_wy_episode(&s1_48, &ep_b48).s_post;
    let wit3_48 = apply_continual_wy_episode(&s2_48, &ep_c48);
    let s3_48 = &wit3_48.s_post;
    let s_cf48 = apply_continual_wy_episode(&s1_48, &ep_c48).s_post;

    let basis_b48 = build_gram_schmidt_subspace_basis(&ep_b48);
    let basis_c48 = build_gram_schmidt_subspace_basis(&ep_c48);

    let mut mmr48 = ContinualEpisodeMmr::new();
    let (up_pf48, s2_48_r, mmr48_r, s3_48_r, _) =
        prove_continual_wy_update_zk(&vault_key, &wit3_48, &basis_c48, &[0x77; 32], &mut mmr48)
            .expect("prove H_v=48 continual WY update");
    verify_continual_wy_update_zk(&s2_48_r, &mmr48_r, &s3_48_r, &up_pf48)
        .expect("verify H_v=48 continual WY update");

    let unl48 = apply_rank_r_subspace_unlearning(s3_48, &basis_b48).expect("unlearn H_v=48");
    let rec_b_before = evaluate_episode_recall(&model, s3_48, &ep_b48, gain);
    let rec_b_after = evaluate_episode_recall(&model, &unl48.s_unlearned, &ep_b48, gain);
    let rec_a_after = evaluate_episode_recall(&model, &unl48.s_unlearned, &ep_a48, gain);
    let rec_c_after = evaluate_episode_recall(&model, &unl48.s_unlearned, &ep_c48, gain);
    let snr_a48 = readout_snr_db_vs_counterfactual(&unl48.s_unlearned, &s_cf48, &ep_a48);
    let snr_c48 = readout_snr_db_vs_counterfactual(&unl48.s_unlearned, &s_cf48, &ep_c48);

    assert_eq!(rec_b_before.recall_rate, 1.0);
    assert_eq!(rec_b_after.recall_rate, 0.0);
    assert!(rec_b_after.mean_readout_l2 / rec_b_before.mean_readout_l2 < 1e-4);
    assert_eq!(rec_a_after.recall_rate, 1.0);
    assert_eq!(rec_c_after.recall_rate, 1.0);
    assert!(snr_a48 > 35.0 && snr_c48 > 35.0);

    let (cert48, sb48, su48, freq48) =
        prove_zk_unlearning_certificate(&vault_key, &unl48, &[0x88; 32], None)
            .expect("prove H_v=48 ZK unlearn");
    verify_zk_unlearning_certificate(&sb48, &su48, &freq48, None, 48, 6, &cert48)
        .expect("standalone verify H_v=48 ZK unlearn");
}
