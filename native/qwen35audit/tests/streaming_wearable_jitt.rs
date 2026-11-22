#![deny(warnings)]
//! End-to-End Wearable JITT Continuous 4-Chunk (`4 x 64 = 256` Tokens) Streaming GDN State-Carry
//! Benchmark & 10-Attack Adversarial Falsifier Suite on Real `Qwen/Qwen3.5-0.8B-Base` Weights.

use qwen35audit::continual_memory::QwenBpeTokenizer;
use qwen35audit::ext4::{badd, cshake256_32, Ext4};
use qwen35audit::safetensors_mmap::{
    MmapSafetensors, QWEN35_SAFETENSORS_FILE, QWEN35_TOKENIZER_FILE,
};
use qwen35audit::streaming_gdn_carry::{
    compute_chunk_token_commitment, execute_qwen35_monolithic_stateful,
    prove_streaming_gdn_carry_receipt, solve_stateful_gdn_wy_chunk64,
    verify_streaming_gdn_carry_receipt, GdnRecurrentState, PreloadedQwen35JittModel,
    SaltedGdnStateCommitment, StreamingGdnCarryReceipt, WearableJittCarryVerifier,
    WearableJittStreamingSession, JITT_CHUNK_LEN, JITT_D_K, JITT_D_V, JITT_H_V, JITT_M_WY,
};
use std::path::Path;
use std::time::Instant;

#[test]
fn test_wearable_jitt_4x64_real_qwen35_zero_bit_drift_and_10_attack_refusals() {
    let mmap = MmapSafetensors::open(Path::new(QWEN35_SAFETENSORS_FILE))
        .expect("mmap cached Qwen/Qwen3.5-0.8B-Base safetensors");
    let tokenizer = QwenBpeTokenizer::from_file(QWEN35_TOKENIZER_FILE)
        .expect("load Qwen3.5 248,320-vocab BPE tokenizer");

    let t_load = Instant::now();
    let model = PreloadedQwen35JittModel::load_from_mmap(&mmap)
        .expect("preload 24-layer Qwen3.5-0.8B JITT weights");
    let load_ms = t_load.elapsed().as_secs_f64() * 1000.0;

    // Build a realistic continuous all-day wearable JITT 256-token (`4 x 64`) cognitive session stream:
    let corpus = concat!(
        "Rainbows End wearable JITT ambient cognition log. ",
        "Morning lab note: Dregg-180 silicon vat sealed SPI-FRAM monotone slot counter at leaf 4096 with ToF bound 0.45m. ",
        "Midday library overlay: Chumash archive page 118 cross-indexed against formal Lean 4.35.0 CommRing WY recurrence ",
        "S_{c+1} = gamma_c * S_c + V_c^T * U_{wy,c} where U_{wy,c} subtracts incoming K_{dec,c} * S_c without field inversions. ",
        "Afternoon sensorium scrub: zero subliminal 15Hz flicker detected; dual-mask handoff (Delta_M, alpha * S_c(r) + M_c) ",
        "preserves exact TVD = 0 across chunk boundaries while evicting chunks 0, 1, and 2 from wearable SRAM. ",
        "Evening synthesis: verify standalone WhirExt4Pcs + GMaskExt4 state-carry receipt under 25 milliseconds and predict ",
        "the exact next token with zero bit drift relative to a monolithic 256-token Qwen3.5-0.8B forward execution: "
    );
    let mut tok_256 = tokenizer.encode(corpus);
    while tok_256.len() < 4 * JITT_CHUNK_LEN {
        let extra = tokenizer.encode("verified stateful Gated-DeltaNet carry holds across chunks; ");
        tok_256.extend(extra);
    }
    tok_256.truncate(4 * JITT_CHUNK_LEN);
    assert_eq!(tok_256.len(), 256);

    // 1. Ground-Truth Monolithic `1 x 256` Execution across all 24 layers:
    let t_mono = Instant::now();
    let (mono_final_h, mono_gdn_states) = execute_qwen35_monolithic_stateful(&model, &tok_256);
    let mono_ms = t_mono.elapsed().as_secs_f64() * 1000.0;
    let mono_next_tok = model.greedy_top1_token(&mono_final_h[255 * 1024..256 * 1024]);

    // 2. Streaming `4 x 64` Wearable JITT Session (Chunks 0..2 evicted immediately; `O(1)` 136-B Verifier!):
    let session_id = cshake256_32(b"TEST-JITT-SESSION-V1", b"wearable-jitt-day-01");
    let model_weight_root = cshake256_32(b"TEST-QW35-WROOT-V1", b"Qwen3.5-0.8B-Base-24L");
    let audited_layer = 8usize; // Mid-network GDN layer (`8 % 4 == 0 != 3`, non-trivial deep activations!)

    let mut session = WearableJittStreamingSession::new(
        session_id,
        model_weight_root,
        audited_layer,
        Some([0x10u8; 32]),
    );
    let genesis_root = session.genesis_state_root();
    let mut verifier = WearableJittCarryVerifier::new(
        session_id,
        model_weight_root,
        audited_layer as u32,
        genesis_root,
    );
    assert_eq!(WearableJittCarryVerifier::LIVE_STATE_BYTES, 136);

    let mut wire_receipts: Vec<Vec<u8>> = Vec::with_capacity(4);
    let mut prove_ms_vec = Vec::with_capacity(4);
    let mut verify_ms_vec = Vec::with_capacity(4);
    let mut retained_ram_vec = Vec::with_capacity(4);
    let mut evicted_bytes_total = 0usize;
    let mut last_chunk_final_h = Vec::new();

    for c in 0..4usize {
        let chunk_slice = &tok_256[c * JITT_CHUNK_LEN..(c + 1) * JITT_CHUNK_LEN];
        let seed_c = [0x20u8 + (c as u8); 32];

        let t_step = Instant::now();
        let step_out = session
            .step_chunk_64(&model, chunk_slice, Some(seed_c))
            .expect("streaming JITT chunk step + prove");
        let step_prove_ms = t_step.elapsed().as_secs_f64() * 1000.0;

        // Check `0` IEEE-754 bit drift on THIS chunk's 64 x 1024 final output BEFORE dropping it!
        let mono_slice = &mono_final_h[c * JITT_CHUNK_LEN * 1024..(c + 1) * JITT_CHUNK_LEN * 1024];
        for (idx, (&a, &b)) in step_out.chunk_final_h.iter().zip(mono_slice.iter()).enumerate() {
            assert_eq!(
                a.to_bits(),
                b.to_bits(),
                "bit drift at chunk {c} elem {idx}: streaming={a} ({:#x}) vs mono={b} ({:#x})",
                a.to_bits(),
                b.to_bits()
            );
        }

        let wire = step_out.receipt.to_bytes();
        let decoded = StreamingGdnCarryReceipt::from_bytes(&wire)
            .expect("round-trip deserialize StreamingGdnCarryReceipt");
        assert_eq!(decoded, step_out.receipt);

        // Standalone `< 25 ms` verification (median of 3 runs on deserialized wire proof, then advance `O(1)` state):
        let mut v_runs = [0.0f64; 3];
        for r in 0..3 {
            let tv = Instant::now();
            verify_streaming_gdn_carry_receipt(&decoded).expect("standalone receipt verify");
            v_runs[r] = tv.elapsed().as_secs_f64() * 1000.0;
        }
        v_runs.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let med_verify_ms = v_runs[1];
        assert!(
            med_verify_ms < 25.0,
            "chunk {c} standalone verify {med_verify_ms:.2} ms >= 25.0 ms budget!"
        );

        verifier
            .verify_and_advance(&decoded)
            .expect("advance O(1) WearableJittCarryVerifier");

        prove_ms_vec.push(step_prove_ms);
        verify_ms_vec.push(med_verify_ms);
        retained_ram_vec.push(step_out.retained_gdn_ram_bytes);
        if c < 3 {
            evicted_bytes_total += step_out.evicted_prover_scratch_bytes;
        } else {
            last_chunk_final_h = step_out.chunk_final_h;
        }
        wire_receipts.push(wire);
        // Note: `step_out` (except `wire` for adversarial tests below and `last_chunk_final_h` on c==3) is dropped here!
    }

    // Verify `O(1)` constant live GDN RAM across ALL 4 chunks (`c = 0, 1, 2, 3` identical byte count!):
    assert_eq!(retained_ram_vec[0], retained_ram_vec[1]);
    assert_eq!(retained_ram_vec[1], retained_ram_vec[2]);
    assert_eq!(retained_ram_vec[2], retained_ram_vec[3]);
    assert_eq!(session.evicted_chunks, 4);
    assert_eq!(verifier.expected_chunk_idx, 4);
    assert_eq!(verifier.current_state_root, session.current_state_root());

    // Verify `0` bit drift across ALL 18 GDN layers' terminal `16 x 128 x 128` fast-weight states (`4,718,592` cells)!
    assert_eq!(session.gdn_states().len(), 18);
    let mut min_nonzero_int = usize::MAX;
    let mut max_nonzero_int = 0usize;
    let mut layer8_nonzero_int = 0usize;
    for l_ord in 0..18 {
        assert_eq!(
            session.gdn_states()[l_ord],
            mono_gdn_states[l_ord],
            "GDN recurrent state drift at GDN layer ordinal {l_ord}"
        );
        let nonzero_int = session.gdn_states()[l_ord]
            .s_int_hvk
            .iter()
            .filter(|&&v| v != 0)
            .count();
        min_nonzero_int = min_nonzero_int.min(nonzero_int);
        max_nonzero_int = max_nonzero_int.max(nonzero_int);
        if l_ord == 6 {
            // Layer 8 is GDN ordinal 6 (`0,1,2, 4,5,6, 8 -> ordinal 6`)
            layer8_nonzero_int = nonzero_int;
        }
        assert!(
            nonzero_int > 1_000,
            "expected non-zero quantized GDN state at ordinal {l_ord}, got {nonzero_int}"
        );
    }

    let stream_next_tok = model.greedy_top1_token(&last_chunk_final_h[63 * 1024..64 * 1024]);
    assert_eq!(stream_next_tok, mono_next_tok);

    println!(
        "[JITT-256] Preload={:.1}ms, Mono256={:.1}ms | Retained GDN O(1) RAM = {:.2} MiB ({} B), Verifier RAM = {} B, Evicted Chunks 0..2 Scratch = {:.2} MiB, NonZero S_int/Layer = [{}..{}] (L8={})/262144",
        load_ms,
        mono_ms,
        retained_ram_vec[3] as f64 / (1024.0 * 1024.0),
        retained_ram_vec[3],
        WearableJittCarryVerifier::LIVE_STATE_BYTES,
        evicted_bytes_total as f64 / (1024.0 * 1024.0),
        min_nonzero_int,
        max_nonzero_int,
        layer8_nonzero_int,
    );
    for c in 0..4 {
        println!(
            "  Chunk {c} (`rt_{{S,{c}}} -> rt_{{S,{}}}`): wire = {:.2} KiB ({} B), step+prove = {:.2} ms, standalone verify = {:.2} ms (< 25 ms)",
            c + 1,
            wire_receipts[c].len() as f64 / 1024.0,
            wire_receipts[c].len(),
            prove_ms_vec[c],
            verify_ms_vec[c],
        );
    }
    println!(
        "  256-token 24L Qwen3.5-0.8B drift = 0 / 8,388,608 f32 bits, 0 / 4,718,592 GDN state cells; top-1 next token = {} ({:?})",
        stream_next_tok,
        tokenizer.token_debug_str(stream_next_tok),
    );

    // ============================================================================================
    // 3. Adversarial Falsifier Suite: Rejecting 10 Splice / Reset / Rollback / WY Forgery Attacks!
    // ============================================================================================
    let r0 = StreamingGdnCarryReceipt::from_bytes(&wire_receipts[0]).unwrap();
    let r1 = StreamingGdnCarryReceipt::from_bytes(&wire_receipts[1]).unwrap();
    let r2 = StreamingGdnCarryReceipt::from_bytes(&wire_receipts[2]).unwrap();
    let r3 = StreamingGdnCarryReceipt::from_bytes(&wire_receipts[3]).unwrap();

    // Attack 1: `S_init = 0` Silent Mid-Session Reset at Chunk 2!
    // Adversary runs Chunk 2 starting from `S_zero` (`genesis_root` or fresh `S_zero` commit) instead of `S_2`:
    {
        let mut reset_sess = WearableJittStreamingSession::new(
            session_id,
            model_weight_root,
            audited_layer,
            Some([0x99u8; 32]),
        );
        let mut reset_step = reset_sess
            .step_chunk_64(&model, &tok_256[2 * 64..3 * 64], Some([0x9Au8; 32]))
            .unwrap();
        // Even if adversary patches `chunk_idx = 2` on the valid `S_0 = 0` proof:
        reset_step.receipt.header.chunk_idx = 2;
        let mut v = WearableJittCarryVerifier::new(session_id, model_weight_root, audited_layer as u32, genesis_root);
        v.verify_and_advance(&r0).unwrap();
        v.verify_and_advance(&r1).unwrap();
        assert!(
            v.verify_and_advance(&reset_step.receipt).is_err(),
            "Attack 1 (S_init = 0 silent reset at chunk 2) MUST be rejected!"
        );
    }

    // Attack 2: Chunk-Reorder Splice (`[r0, r2, r1, r3]`):
    {
        let mut v = WearableJittCarryVerifier::new(session_id, model_weight_root, audited_layer as u32, genesis_root);
        v.verify_and_advance(&r0).unwrap();
        assert!(
            v.verify_and_advance(&r2).is_err(),
            "Attack 2 (chunk-reorder splice r2 before r1) MUST be rejected!"
        );
    }

    // Attack 3: State Rollback / Stale `rt_{S,1}` Replay at Chunk 2:
    {
        let mut v = WearableJittCarryVerifier::new(session_id, model_weight_root, audited_layer as u32, genesis_root);
        v.verify_and_advance(&r0).unwrap();
        v.verify_and_advance(&r1).unwrap();
        let mut replayed_r1_as_2 = r1.clone();
        replayed_r1_as_2.header.chunk_idx = 2;
        assert!(
            v.verify_and_advance(&replayed_r1_as_2).is_err(),
            "Attack 3 (stale rt_{{S,1}} rollback replay at chunk 2) MUST be rejected!"
        );
    }

    // Attack 4: Cross-Session Replay Attack (`session_id` from Session B):
    {
        let other_sess_id = cshake256_32(b"OTHER-SESSION", b"attacker");
        let mut other_sess = WearableJittStreamingSession::new(
            other_sess_id,
            model_weight_root,
            audited_layer,
            Some([0x10u8; 32]),
        );
        let other_r0 = other_sess
            .step_chunk_64(&model, &tok_256[0..64], Some([0x44u8; 32]))
            .unwrap()
            .receipt;
        verify_streaming_gdn_carry_receipt(&other_r0).expect("standalone valid in other session");
        let mut v = WearableJittCarryVerifier::new(session_id, model_weight_root, audited_layer as u32, genesis_root);
        assert!(
            v.verify_and_advance(&other_r0).is_err(),
            "Attack 4 (cross-session replay) MUST be rejected!"
        );
    }

    // Attack 5: Cross-Layer Splice Attack (valid proof for GDN Layer 4 injected into Layer 8 verifier):
    {
        let mut layer4_sess = WearableJittStreamingSession::new(
            session_id,
            model_weight_root,
            4,
            Some([0x10u8; 32]),
        );
        let layer4_r0 = layer4_sess
            .step_chunk_64(&model, &tok_256[0..64], Some([0x55u8; 32]))
            .unwrap()
            .receipt;
        let mut v = WearableJittCarryVerifier::new(session_id, model_weight_root, audited_layer as u32, genesis_root);
        assert!(
            v.verify_and_advance(&layer4_r0).is_err(),
            "Attack 5 (cross-layer splice layer 4 -> layer 8) MUST be rejected!"
        );
    }

    // Attack 6: Dropped `K_c · S_c` WY Coupling Attack (non-zero `S_c`, keeping `gamma_c * S_c` in `S_{c+1}`
    // while setting `W_ks = 0, R_ks = 256` inside WY `RHS`!):
    {
        let q_f32 = vec![0.25f32; JITT_CHUNK_LEN * JITT_H_V * JITT_D_K];
        let k_f32 = vec![0.35f32; JITT_CHUNK_LEN * JITT_H_V * JITT_D_K];
        let v_f32 = vec![1.20f32; JITT_CHUNK_LEN * JITT_H_V * JITT_D_V];
        let g_f32 = vec![-0.05f32; JITT_CHUNK_LEN * JITT_H_V];
        let beta_f32 = vec![0.75f32; JITT_CHUNK_LEN * JITT_H_V];

        // Non-zero incoming state `S_c`:
        let wit0 = solve_stateful_gdn_wy_chunk64(
            &q_f32,
            &k_f32,
            &v_f32,
            &g_f32,
            &beta_f32,
            &GdnRecurrentState::zero(),
        );
        let s_nonzero = wit0.s_out;
        let s_in_c = SaltedGdnStateCommitment::commit(s_nonzero.clone(), Some([0x61u8; 32]));

        // Compute zero-state WY witness (`W_ks = 0`), then forge `s_out = gamma_int * S_nonzero + K_tail^T * U_zero`:
        let mut bad_wit = solve_stateful_gdn_wy_chunk64(
            &q_f32,
            &k_f32,
            &v_f32,
            &g_f32,
            &beta_f32,
            &GdnRecurrentState::zero(),
        );
        // Note: `bad_wit` has `W_ks == 0` (dropped `K_c · S_c`!), which disagrees with non-zero `s_in_c`!
        let mut forged_s_out_int = bad_wit.s_out.s_int_hvk.clone();
        for idx in 0..forged_s_out_int.len() {
            let h = idx & 15;
            forged_s_out_int[idx] = (forged_s_out_int[idx]
                + ((bad_wit.gamma_int_16[h] as i64) * s_nonzero.s_int_hvk[idx]) / JITT_M_WY)
                .clamp(-8000, 8000);
        }
        bad_wit.s_out = GdnRecurrentState::from_int_hvk(forged_s_out_int).unwrap();
        let bad_s_out_c = SaltedGdnStateCommitment::commit(bad_wit.s_out.clone(), Some([0x62u8; 32]));
        let tok_c = compute_chunk_token_commitment(&session_id, 1, &tok_256[64..128]);
        let forged_prf = prove_streaming_gdn_carry_receipt(
            session_id,
            model_weight_root,
            audited_layer as u32,
            1,
            tok_c,
            &s_in_c,
            &bad_s_out_c,
            &bad_wit,
            Some([0x63u8; 32]),
        )
        .expect("prover builds inconsistent witness");
        assert!(
            verify_streaming_gdn_carry_receipt(&forged_prf).is_err(),
            "Attack 6 (dropped K_c · S_c WY coupling on non-zero S_c) MUST be rejected!"
        );
    }

    // Attack 7: Forged `s_out_root` Commitment Substitution on Chunk 1:
    {
        let mut bad_r1 = r1.clone();
        bad_r1.header.s_out_root = r2.header.s_out_root;
        assert!(
            verify_streaming_gdn_carry_receipt(&bad_r1).is_err(),
            "Attack 7 (forged s_out_root substitution) MUST be rejected!"
        );
    }

    // Attack 8: Tampered `TVD = 0` Blinded Handoff Scalar (`mu_wy` or `delta_masks[0]` +1):
    {
        let mut bad_mu = r2.clone();
        bad_mu.mu_wy = bad_mu.mu_wy.add(Ext4::ONE);
        assert!(
            verify_streaming_gdn_carry_receipt(&bad_mu).is_err(),
            "Attack 8a (tampered mu_wy) MUST be rejected!"
        );
        let mut bad_dm = r2.clone();
        bad_dm.delta_masks[0] = bad_dm.delta_masks[0].add(Ext4::ONE);
        assert!(
            verify_streaming_gdn_carry_receipt(&bad_dm).is_err(),
            "Attack 8b (tampered delta_masks[0]) MUST be rejected!"
        );
    }

    // Attack 9: Violated Strict-Lower-Triangular `L` Diagonal (`L[0, 0, 0] != 0`):
    {
        let q_f32 = vec![0.20f32; JITT_CHUNK_LEN * JITT_H_V * JITT_D_K];
        let k_f32 = vec![0.30f32; JITT_CHUNK_LEN * JITT_H_V * JITT_D_K];
        let v_f32 = vec![0.80f32; JITT_CHUNK_LEN * JITT_H_V * JITT_D_V];
        let g_f32 = vec![-0.02f32; JITT_CHUNK_LEN * JITT_H_V];
        let beta_f32 = vec![0.50f32; JITT_CHUNK_LEN * JITT_H_V];
        let s_in_c = SaltedGdnStateCommitment::commit(GdnRecurrentState::zero(), Some([0x91u8; 32]));
        let mut bad_slt_wit = solve_stateful_gdn_wy_chunk64(
            &q_f32,
            &k_f32,
            &v_f32,
            &g_f32,
            &beta_f32,
            &s_in_c.state,
        );
        // Inject non-zero entry on main diagonal `(h=0, i=0, j=0)` within `[-512, 512)` range!
        bad_slt_wit.l_lsb_hij[0] = badd(0, 7);
        let s_out_c = SaltedGdnStateCommitment::commit(bad_slt_wit.s_out.clone(), Some([0x92u8; 32]));
        let tok_c = compute_chunk_token_commitment(&session_id, 0, &tok_256[0..64]);
        let bad_slt_prf = prove_streaming_gdn_carry_receipt(
            session_id,
            model_weight_root,
            audited_layer as u32,
            0,
            tok_c,
            &s_in_c,
            &s_out_c,
            &bad_slt_wit,
            Some([0x93u8; 32]),
        )
        .unwrap();
        assert!(
            verify_streaming_gdn_carry_receipt(&bad_slt_prf).is_err(),
            "Attack 9 (non-strict-lower-triangular L diagonal forgery) MUST be rejected!"
        );
    }

    // Attack 10: Out-of-Bounds `gamma_int_16` Header / Non-GDN Layer Header / Truncated Wire Bytes:
    {
        let mut bad_gamma = r3.clone();
        bad_gamma.header.gamma_int_16[0] = (JITT_M_WY as u16) + 1;
        assert!(
            verify_streaming_gdn_carry_receipt(&bad_gamma).is_err(),
            "Attack 10a (gamma_int_16 > M_WY) MUST be rejected!"
        );
        let mut bad_layer = r3.clone();
        bad_layer.header.layer_idx = 3; // GQA layer (`3 % 4 == 3`)
        assert!(
            verify_streaming_gdn_carry_receipt(&bad_layer).is_err(),
            "Attack 10b (GQA layer_idx = 3 masquerading as GDN) MUST be rejected!"
        );
        let mut extra_wire = wire_receipts[3].clone();
        extra_wire.push(0x00);
        assert!(
            StreamingGdnCarryReceipt::from_bytes(&extra_wire).is_err(),
            "Attack 10c (trailing wire byte) MUST be rejected!"
        );
    }
}
