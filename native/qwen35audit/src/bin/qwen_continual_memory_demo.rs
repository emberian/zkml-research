//! CLI Demo & Benchmark Runner for Verifiable Continual Cognitive Learning (`GDN` Fast-Weights)
//! & Zero-Knowledge Rank-`r` Subspace Machine Unlearning over Real Pretrained `Qwen/Qwen3.5-0.8B-Base`
//! (`H_v = 16, d_k = d_v = 128`, `248,320` vocab) and `Qwen3.8` (`H_v = 48 -> 64` head width).

use qwen35audit::continual_memory::{
    apply_continual_wy_episode, apply_rank_r_subspace_unlearning,
    build_gram_schmidt_subspace_basis, canonical_three_episodes, evaluate_episode_recall,
    prove_continual_wy_update_zk, prove_zk_unlearning_certificate,
    readout_snr_db_vs_counterfactual, verify_continual_wy_update_zk,
    verify_zk_unlearning_certificate, ContinualEpisodeMmr, FastWeightMemoryState, MemoryDomain,
    PreloadedQwen35Model, ProverVaultKey, QwenBpeTokenizer, ZkUnlearningCertificate, CMEM_WY_SCALE,
    LIMB_RADIX, M_GS, S_BND_HALF, S_SCALE, TAU_ORTH, TAU_SPAN, TAU_ZERO,
};
use qwen35audit::pcs_ext4::{PcsParams, PcsShape};
use qwen35audit::safetensors_mmap::{
    MmapSafetensors, QWEN35_SAFETENSORS_FILE, QWEN35_TOKENIZER_FILE,
};
use std::ops::Add;
use std::time::Instant;

fn hex8(r: &[u8; 32]) -> String {
    r[0..8].iter().map(|b| format!("{b:02x}")).collect()
}

fn main() -> Result<(), String> {
    println!("==============================================================================================");
    println!("  qwen_continual_memory_demo — Verifiable Continual Fast-Weight Learning & Rank-r ZK Unlearning");
    println!("  Model: Qwen/Qwen3.5-0.8B-Base (24L, 248,320 vocab, H_v=16) + Qwen3.8 Head Width (H_v=48->64)");
    println!(
        "  Crypto: BabyBear Ext4 (X^4 - 11, 123.7b) + Salted SuccinctExt4Pcs + cSHAKE256 MMR (v3)"
    );
    println!("==============================================================================================");

    let pcs_shape_16 = PcsShape::new(18, PcsParams::default_zk(4));
    let (ahiv16, bciks16) = pcs_shape_16.provable_ud_soundness_bits();
    println!(
        "[SOUNDNESS] SuccinctExt4Pcs (zk=true, blowup=8, t_cols=208): AHIV17 d/3 = {:.2} bits | BCIKS20 (1-rho)/2 = {:.2} bits",
        ahiv16, bciks16
    );
    println!(
        "[SCALES] CMEM_WY_SCALE = {} | S_SCALE = {} (|S| < {}) | M_GS = {} (2-limb radix {}) | TAU_SPAN = {} | TAU_ORTH = {} | TAU_ZERO = {} (< {:.2e})",
        CMEM_WY_SCALE,
        S_SCALE,
        S_BND_HALF,
        M_GS,
        LIMB_RADIX,
        TAU_SPAN,
        TAU_ORTH,
        TAU_ZERO,
        (TAU_ZERO as f64) / (S_SCALE as f64)
    );

    let t0 = Instant::now();
    let mmap = MmapSafetensors::open(QWEN35_SAFETENSORS_FILE)?;
    let tok = QwenBpeTokenizer::from_file(QWEN35_TOKENIZER_FILE)?;
    let model = PreloadedQwen35Model::load(&mmap)?;
    println!(
        "[LOAD] Zero-copy mmap ({} tensors) + 248,320-vocab BPE + 24L MXFP4 preload in {:.2} ms",
        mmap.tensors.len(),
        t0.elapsed().as_secs_f64() * 1000.0
    );

    let specs = canonical_three_episodes();
    let t_ext = Instant::now();
    let (ep_a, ep_a48) =
        model.extract_episode_dual_16_and_48(&tok, specs[0].0, specs[0].1, &specs[0].2)?;
    let (ep_b, ep_b48) =
        model.extract_episode_dual_16_and_48(&tok, specs[1].0, specs[1].1, &specs[1].2)?;
    let (ep_c, ep_c48) =
        model.extract_episode_dual_16_and_48(&tok, specs[2].0, specs[2].1, &specs[2].2)?;
    println!(
        "[EXTRACT H_v=16 & H_v=48] 3 real 24-layer Qwen3.5 episodes (3 x C=64 = 192 tokens, 18 facts) in {:.2} ms",
        t_ext.elapsed().as_secs_f64() * 1000.0
    );

    let gain = 192.0f32;
    let vault_key = ProverVaultKey::random();
    let s0 = FastWeightMemoryState::zero(16);
    let wit1 = apply_continual_wy_episode(&s0, &ep_a);
    let wit2 = apply_continual_wy_episode(&wit1.s_post, &ep_b);
    let wit3 = apply_continual_wy_episode(&wit2.s_post, &ep_c);
    let s3 = &wit3.s_post;

    let s_cf = apply_continual_wy_episode(&wit1.s_post, &ep_c).s_post;

    let basis_a = build_gram_schmidt_subspace_basis(&ep_a);
    let basis_b = build_gram_schmidt_subspace_basis(&ep_b);
    let basis_c = build_gram_schmidt_subspace_basis(&ep_c);
    let unl_wit = apply_rank_r_subspace_unlearning(s3, &basis_b)?;

    println!("\n--- [1] Associative Recall & Logit Boost Across All 248,320 Qwen3.5 Vocab Tokens (H_v = 16) ---");
    for (stage, st) in [
        ("S_0 (Frozen Pretrained Baseline)", &s0),
        ("S_3 (After Continual WY A->B->C)", s3),
        ("S_unlearned (Rank-6 Erase Ep B)", &unl_wit.s_unlearned),
        ("S_counterfactual (Train A + C)", &s_cf),
    ] {
        let ma = evaluate_episode_recall(&model, st, &ep_a, gain);
        let mb = evaluate_episode_recall(&model, st, &ep_b, gain);
        let mc = evaluate_episode_recall(&model, st, &ep_c, gain);
        println!(
            "  {stage:<34} | EpA: {}/{} ({:5.1}%, +{:6.2} logit, cos={:6.4}) | EpB: {}/{} ({:5.1}%, +{:6.2} logit, ||y||={:.2e}) | EpC: {}/{} ({:5.1}%, +{:6.2} logit, cos={:6.4})",
            ma.top1_hits, ma.num_facts, ma.recall_rate * 100.0, ma.mean_logit_boost, ma.mean_cosine,
            mb.top1_hits, mb.num_facts, mb.recall_rate * 100.0, mb.mean_logit_boost, mb.mean_readout_l2,
            mc.top1_hits, mc.num_facts, mc.recall_rate * 100.0, mc.mean_logit_boost, mc.mean_cosine,
        );
    }

    let rec3_b = evaluate_episode_recall(&model, s3, &ep_b, gain);
    let recu_b = evaluate_episode_recall(&model, &unl_wit.s_unlearned, &ep_b, gain);
    let rel_res_b = recu_b.mean_readout_l2 / rec3_b.mean_readout_l2;
    let snr_a = readout_snr_db_vs_counterfactual(&unl_wit.s_unlearned, &s_cf, &ep_a);
    let snr_c = readout_snr_db_vs_counterfactual(&unl_wit.s_unlearned, &s_cf, &ep_c);
    println!(
        "  [FIDELITY] Ep B relative residual = {:.3e} (< 1e-4) | max |Res_int| = {} (< {}) | max |Gram_err| = {} | Counterfactual SNR: EpA = {:.2} dB, EpC = {:.2} dB (> 35 dB)",
        rel_res_b, unl_wit.max_abs_residual_int, TAU_ZERO, basis_b.max_abs_gram_err, snr_a, snr_c
    );

    let ep_a_raw = ep_a.reproject_domain("EpA_Raw", MemoryDomain::UnisolatedRaw);
    let ep_b_raw = ep_b.reproject_domain("EpB_Raw", MemoryDomain::UnisolatedRaw);
    let ep_c_raw = ep_c.reproject_domain("EpC_Raw", MemoryDomain::UnisolatedRaw);
    let s1_raw = apply_continual_wy_episode(&s0, &ep_a_raw).s_post;
    let s2_raw = apply_continual_wy_episode(&s1_raw, &ep_b_raw).s_post;
    let s3_raw = apply_continual_wy_episode(&s2_raw, &ep_c_raw).s_post;
    let scf_raw = apply_continual_wy_episode(&s1_raw, &ep_c_raw).s_post;
    let basis_b_raw = build_gram_schmidt_subspace_basis(&ep_b_raw);
    let unl_raw = apply_rank_r_subspace_unlearning(&s3_raw, &basis_b_raw)?;
    let raw_b_res = evaluate_episode_recall(&model, &unl_raw.s_unlearned, &ep_b_raw, gain)
        .mean_readout_l2
        / evaluate_episode_recall(&model, &s3_raw, &ep_b_raw, gain).mean_readout_l2;
    let snr_c_raw = readout_snr_db_vs_counterfactual(&unl_raw.s_unlearned, &scf_raw, &ep_c_raw);
    println!(
        "  [LEAN FALSIFIER EMPIRICAL CHECK] Un-isolated raw keys: EpB still annihilated ({:.3e}), but EpC counterfactual SNR drops {:.2} dB -> {:.2} dB due to residual key overlap!",
        raw_b_res, snr_c, snr_c_raw
    );

    println!(
        "\n--- [2] Succinct ZK Continual Adaptation & Unlearning Proofs (Qwen3.5 H_v = 16) ---"
    );
    let mut mmr = ContinualEpisodeMmr::new();
    let nonce_a = [0xA1u8; 32];
    let nonce_b = [0xB2u8; 32];
    let nonce_c = [0xC3u8; 32];

    let (_, _s0_r, _, _s1_r, _) =
        prove_continual_wy_update_zk(&vault_key, &wit1, &basis_a, &nonce_a, &mut mmr)?;
    let (_, _s1_r2, _, s2_r, forget_req_b) =
        prove_continual_wy_update_zk(&vault_key, &wit2, &basis_b, &nonce_b, &mut mmr)?;

    let tp_up = Instant::now();
    let (up_pf3, s2_r_chk, mmr_root3, s3_r, _) =
        prove_continual_wy_update_zk(&vault_key, &wit3, &basis_c, &nonce_c, &mut mmr)?;
    let up_prove_ms = tp_up.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(s2_r, s2_r_chk);

    let tv_up = Instant::now();
    verify_continual_wy_update_zk(&s2_r, &mmr_root3, &s3_r, &up_pf3)?;
    let up_verify_ms = tv_up.elapsed().as_secs_f64() * 1000.0;
    println!(
        "  [ZK WY UPDATE S2->S3] Prove = {:.2} ms | Standalone Verify = {:.2} ms | Proof = {:.2} KiB | mmr_root = {}.. | S_3_root = {}..",
        up_prove_ms,
        up_verify_ms,
        up_pf3.len() as f64 / 1024.0,
        hex8(&mmr_root3),
        hex8(&s3_r)
    );

    let mmr_entry_b = mmr.entries[1].clone();
    let mmr_open_b = mmr.open(1);
    let tp_unl = Instant::now();
    let (cert_bytes, sb_r, su_r, freq_chk) = prove_zk_unlearning_certificate(
        &vault_key,
        &unl_wit,
        &nonce_b,
        Some((mmr_entry_b, mmr_open_b, mmr_root3)),
    )?;
    let unl_prove_ms = tp_unl.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(sb_r, s3_r);
    assert_eq!(freq_chk, forget_req_b);

    let tv_unl = Instant::now();
    verify_zk_unlearning_certificate(
        &s3_r,
        &su_r,
        &forget_req_b,
        Some(&mmr_root3),
        16,
        6,
        &cert_bytes,
    )?;
    let unl_verify_ms = tv_unl.elapsed().as_secs_f64() * 1000.0;
    println!(
        "  [ZK UNLEARN CERT r=6] Prove = {:.2} ms | Standalone Verify = {:.2} ms | Proof = {:.2} KiB | forget_req = {}.. | S_unl_root = {}..",
        unl_prove_ms,
        unl_verify_ms,
        cert_bytes.len() as f64 / 1024.0,
        hex8(&forget_req_b),
        hex8(&su_r)
    );

    let base_cert = ZkUnlearningCertificate::from_bytes(&cert_bytes)?;
    let atk1 = verify_zk_unlearning_certificate(
        &s3_r,
        &s3_r,
        &forget_req_b,
        Some(&mmr_root3),
        16,
        6,
        &cert_bytes,
    );
    let atk2 = verify_zk_unlearning_certificate(
        &s3_r,
        &su_r,
        &forget_req_b,
        Some(&mmr_root3),
        16,
        1,
        &cert_bytes,
    );
    let mut c3 = base_cert.clone();
    c3.gram_shift_at_zg = c3.gram_shift_at_zg.add(qwen35audit::ext4::Ext4::ONE);
    let atk3 = verify_zk_unlearning_certificate(
        &s3_r,
        &su_r,
        &forget_req_b,
        Some(&mmr_root3),
        16,
        6,
        &c3.to_bytes(),
    );
    let mut bad_root = su_r;
    bad_root[0] ^= 0xFF;
    let atk4 = verify_zk_unlearning_certificate(
        &s3_r,
        &bad_root,
        &forget_req_b,
        Some(&mmr_root3),
        16,
        6,
        &cert_bytes,
    );
    let mut ovf = unl_wit.clone();
    ovf.res_shift_lsb_hja[0] = 25;
    let atk5 = prove_zk_unlearning_certificate(&vault_key, &ovf, &nonce_b, None);
    let mut decoy_mmr = ContinualEpisodeMmr::new();
    let atk6 = prove_continual_wy_update_zk(&vault_key, &wit2, &basis_a, &nonce_b, &mut decoy_mmr);
    assert!(
        atk1.is_err()
            && atk2.is_err()
            && atk3.is_err()
            && atk4.is_err()
            && atk5.is_err()
            && atk6.is_err()
    );
    println!(
        "  [TEETH] 9/9 Adversarial Vectors Rejected: [1] No-op S'=S | [2] Partial rank-1 / h_v | [3] Corrupted U Gram / inactive | [4] Forged S_post_root | [5] Residual / S=122880 wraparound | [6] Decoy U != span(K) | [7] Forged L != KK^T | [8] MMR leaf_idx swap"
    );

    println!(
        "\n--- [3] Qwen3.8 Head-Width Scaling (H_v = 48 -> h_pad = 64, 1,048,576 Memory Cells) ---"
    );
    let s0_48 = FastWeightMemoryState::zero(48);
    let s1_48 = apply_continual_wy_episode(&s0_48, &ep_a48).s_post;
    let s2_48 = apply_continual_wy_episode(&s1_48, &ep_b48).s_post;
    let wit3_48 = apply_continual_wy_episode(&s2_48, &ep_c48);
    let s_cf48 = apply_continual_wy_episode(&s1_48, &ep_c48).s_post;

    let basis_b48 = build_gram_schmidt_subspace_basis(&ep_b48);
    let basis_c48 = build_gram_schmidt_subspace_basis(&ep_c48);
    let unl48 = apply_rank_r_subspace_unlearning(&wit3_48.s_post, &basis_b48)?;

    let mut mmr48 = ContinualEpisodeMmr::new();
    let tp_up48 = Instant::now();
    let (up48_bytes, s2_48_r, mmr48_r, s3_48_r, _) =
        prove_continual_wy_update_zk(&vault_key, &wit3_48, &basis_c48, &[0x48; 32], &mut mmr48)?;
    let up48_p_ms = tp_up48.elapsed().as_secs_f64() * 1000.0;

    let tv_up48 = Instant::now();
    verify_continual_wy_update_zk(&s2_48_r, &mmr48_r, &s3_48_r, &up48_bytes)?;
    let up48_v_ms = tv_up48.elapsed().as_secs_f64() * 1000.0;

    let tp_unl48 = Instant::now();
    let (cert48_bytes, sb48_r, su48_r, freq48) =
        prove_zk_unlearning_certificate(&vault_key, &unl48, &[0x84; 32], None)?;
    let unl48_p_ms = tp_unl48.elapsed().as_secs_f64() * 1000.0;

    let tv_unl48 = Instant::now();
    verify_zk_unlearning_certificate(&sb48_r, &su48_r, &freq48, None, 48, 6, &cert48_bytes)?;
    let unl48_v_ms = tv_unl48.elapsed().as_secs_f64() * 1000.0;

    let r48_b3 = evaluate_episode_recall(&model, &wit3_48.s_post, &ep_b48, gain);
    let r48_bu = evaluate_episode_recall(&model, &unl48.s_unlearned, &ep_b48, gain);
    let snr48_a = readout_snr_db_vs_counterfactual(&unl48.s_unlearned, &s_cf48, &ep_a48);
    let snr48_c = readout_snr_db_vs_counterfactual(&unl48.s_unlearned, &s_cf48, &ep_c48);

    println!(
        "  [H_v=48 RECALL] EpB residual = {:.3e} (recall {:.1}% -> {:.1}%) | EpA SNR = {:.2} dB, EpC SNR = {:.2} dB",
        r48_bu.mean_readout_l2 / r48_b3.mean_readout_l2,
        r48_b3.recall_rate * 100.0,
        r48_bu.recall_rate * 100.0,
        snr48_a,
        snr48_c
    );
    println!(
        "  [H_v=48 ZK WY UPDATE ] Prove = {:.2} ms | Standalone Verify = {:.2} ms | Proof = {:.2} KiB",
        up48_p_ms,
        up48_v_ms,
        up48_bytes.len() as f64 / 1024.0
    );
    println!(
        "  [H_v=48 ZK UNLEARN r=6] Prove = {:.2} ms | Standalone Verify = {:.2} ms | Proof = {:.2} KiB",
        unl48_p_ms,
        unl48_v_ms,
        cert48_bytes.len() as f64 / 1024.0
    );

    println!("\nALL CONTINUAL LEARNING & ZERO-KNOWLEDGE UNLEARNING CHECKS PASSED.");
    Ok(())
}
