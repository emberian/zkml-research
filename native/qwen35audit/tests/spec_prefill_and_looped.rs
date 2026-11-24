//! Release Integration, Real-Weight Benchmark, & Adversarial Soundness Suite for:
//!   1. **Sequential Decode (`64 × T=1`) vs. Batched Speculative-Prefill (`1 × T=64`)** on Real
//!      `Qwen3.8-27B` Layer-0 `MXFP4` (`51,851` `-0.0` `8 -> 0` nibbles + Live Metal Receipt) AND
//!      Real `Qwen/Qwen3.5-0.8B-Base` (`MmapSafetensors` Layer-0 `C=64` `IntWY` + `MXFP4` `gate_proj`),
//!   2. **Exact Integer Argmax Dominance Certificate (`D1b` LogUp Positive-Gap Proof)** over `BabyBear Ext4`,
//!      catching `VERDICTS.md` §9 `"17 * 23 = 391." -> "17 × 23 = 391"` 1-token float-steering drift
//!      at exact index `t*` (`1` free corrected token!) and `"Canberra." -> "Canberra"` flat-tie tampering,
//!   3. **`3×` Depth-Looped MoE Weight-Opening Collapse (`Inkling-2-Mini` `R = 3` Shape)** + Post-Challenge
//!      Forgery Rejection.

use qwen35audit::ext4::Ext4;
use qwen35audit::qwen35_layer::{
    execute_qwen35_24_layers_mmap, prove_audited_gdn_layer, verify_audited_gdn_layer_standalone,
    AuditedGdnLayerVerifyStmt, AuditedGdnLayerWitness, PrecommittedMxfp4Pcs,
};
use qwen35audit::safetensors_mmap::{
    MmapSafetensors, Mxfp4Matrix, Qwen35WeightRegistry, QWEN35_SAFETENSORS_FILE,
};
use qwen35audit::spec_prefill::{
    audit_speculative_draft_prefill, benchmark_inkling2_looped_moe_r3,
    benchmark_seq_decode_vs_spec_prefill_mxfp4, canonical_greedy_tok_i64,
    compute_real_qwen35_shortlist_logits, load_qwen38_27b_slice_and_receipt,
    prove_argmax_dominance_d1b_ext4, prove_looped_moe_collapsed_ext4,
    verify_argmax_dominance_d1b_standalone, verify_looped_moe_collapsed_standalone,
    verify_raw_neg_zero_horner_invariance, ArgmaxDominanceExt4Proof, PrecommittedSliceWeights,
    SpeculativePrefillVerdict, QWEN38_27B_E2M1_NPZ_FILE, QWEN38_27B_METAL_RECEIPT_FILE,
};
use qwen35audit::u1_audit::commit_u1_pcs_boundaries;
use std::ops::{Add, Sub};
use std::path::Path;
use std::time::Instant;

#[test]
fn test_speculative_prefill_speedup_d1b_argmax_and_looped_moe_e2e() {
    println!("\n================================================================================");
    println!("  SPECULATE-IN-FLOAT, PROVE-IN-BATCHED-PREFILL + 3x LOOPED-MoE AUDIT SUITE");
    println!("================================================================================");

    // -------------------------------------------------------------------------
    // 1. Real `Qwen3.8-27B` Layer-0 `MXFP4` Slice (`51,851` `-0.0` Nibbles) + Live Metal Receipt
    // -------------------------------------------------------------------------
    let q38 = load_qwen38_27b_slice_and_receipt(
        Path::new(QWEN38_27B_E2M1_NPZ_FILE),
        Path::new(QWEN38_27B_METAL_RECEIPT_FILE),
    )
    .expect("load Qwen3.8-27B MXFP4 slice and Metal receipt");

    assert_eq!(
        q38.receipt.gguf_sha256,
        "2a5f3565f39cf885103da591182c1266da64745737b42b452fd3e675369f1211"
    );
    assert!(q38.receipt.json_run.metal_prefill_tok_s >= 80.0);
    assert!(q38.receipt.rust_lean_run.metal_prefill_tok_s >= 110.0);
    assert_eq!(
        q38.neg_zero_nibble_count, 51_851,
        "must detect all 51,851 MLX MXFP4 -0.0 (0b1000) nibbles"
    );
    assert!(
        (q38.cos_vs_bf16 - 0.993026).abs() < 1e-4 && q38.snr_db_vs_bf16 > 18.4,
        "unexpected MXFP4 vs BF16 fidelity: cos={} snr={}",
        q38.cos_vs_bf16,
        q38.snr_db_vs_bf16
    );
    verify_raw_neg_zero_horner_invariance(&q38)
        .expect("raw nibble=8 (-0.0) 0-mul Horner invariance");

    let x_q38_64: Vec<i16> = (0..(64 * 5120))
        .map(|i| (((i * 29 + 7) % 127) as i16) - 63)
        .collect();
    let bench_q38 = benchmark_seq_decode_vs_spec_prefill_mxfp4(
        "Qwen3.8-27B Layer-0 gate_proj [256x5120 MXFP4]",
        &q38.mat_mxfp4,
        &x_q38_64,
    )
    .expect("benchmark Qwen3.8-27B 64xT=1 vs 1xT=64");

    println!(
        "[1a] {} | Metal Draft: {:.1}-{:.1} tok/s prefill ({:.1}-{:.1} tok/s decode) | -0.0 nibbles canonicalized: {}",
        bench_q38.model_label,
        q38.receipt.json_run.metal_prefill_tok_s,
        q38.receipt.rust_lean_run.metal_prefill_tok_s,
        q38.receipt.rust_lean_run.metal_decode_tok_s,
        q38.receipt.json_run.metal_decode_tok_s,
        q38.neg_zero_nibble_count,
    );
    println!(
        "     64x T=1 Seq Decode : prove = {:8.2} ms | verify = {:7.2} ms | wire = {:8.2} KiB",
        bench_q38.seq_64_prove_ms, bench_q38.seq_64_verify_ms, bench_q38.seq_64_proof_kib
    );
    println!(
        "     1x  T=64 SpecPrefill: prove = {:8.2} ms | verify = {:7.2} ms | wire = {:8.2} KiB",
        bench_q38.batched_t64_prove_ms,
        bench_q38.batched_t64_verify_ms,
        bench_q38.batched_t64_proof_kib
    );
    println!(
        "     SPEEDUP             : prove = {:6.2}x    | verify = {:6.2}x   | wire = {:6.2}x smaller!",
        bench_q38.prove_speedup_x, bench_q38.verify_speedup_x, bench_q38.proof_compression_x
    );
    assert!(
        bench_q38.proof_compression_x >= 45.0 && bench_q38.prove_speedup_x >= 4.0,
        "expected >= 45x wire compression & >= 4x prove speedup under parallel load on Qwen3.8-27B slice, got wire={:.2}x prove={:.2}x",
        bench_q38.proof_compression_x,
        bench_q38.prove_speedup_x
    );

    // -------------------------------------------------------------------------
    // 2. Real `Qwen/Qwen3.5-0.8B-Base` (`MmapSafetensors`) 24-Layer Execution, Layer-0 `C=64`
    //    `IntWY + MXFP4` Proving, and Sequential `64 × T=1` vs Batched `1 × T=64` Benchmark
    // -------------------------------------------------------------------------
    let mmap = MmapSafetensors::open(QWEN35_SAFETENSORS_FILE).expect("open Qwen3.5-0.8B mmap");
    let prompt_ids: Vec<u32> = (0..64).map(|i| 512 + (i * 23) as u32).collect();
    let audited_layer = 0usize;
    let (turn, final_h) = execute_qwen35_24_layers_mmap(&mmap, &prompt_ids, audited_layer)
        .expect("24L Qwen3.5 forward");

    let bench_q35_gate = benchmark_seq_decode_vs_spec_prefill_mxfp4(
        "Qwen3.5-0.8B Layer-0 gate_proj [3584->4096 x 1024 MXFP4]",
        &turn.gate_proj_mat,
        &turn.x_ln2_i16,
    )
    .expect("benchmark Qwen3.5-0.8B gate_proj 64xT=1 vs 1xT=64");

    println!("[1b] {}", bench_q35_gate.model_label);
    println!(
        "     64x T=1 Seq Decode : prove = {:8.2} ms | verify = {:7.2} ms | wire = {:8.2} KiB",
        bench_q35_gate.seq_64_prove_ms,
        bench_q35_gate.seq_64_verify_ms,
        bench_q35_gate.seq_64_proof_kib
    );
    println!(
        "     1x  T=64 SpecPrefill: prove = {:8.2} ms | verify = {:7.2} ms | wire = {:8.2} KiB",
        bench_q35_gate.batched_t64_prove_ms,
        bench_q35_gate.batched_t64_verify_ms,
        bench_q35_gate.batched_t64_proof_kib
    );
    println!(
        "     SPEEDUP             : prove = {:6.2}x    | verify = {:6.2}x   | wire = {:6.2}x smaller!",
        bench_q35_gate.prove_speedup_x,
        bench_q35_gate.verify_speedup_x,
        bench_q35_gate.proof_compression_x
    );
    assert!(
        bench_q35_gate.proof_compression_x >= 50.0 && bench_q35_gate.prove_speedup_x >= 8.0,
        "expected >= 50x wire compression & >= 8x prove speedup on Qwen3.5-0.8B gate_proj, got wire={:.2}x prove={:.2}x",
        bench_q35_gate.proof_compression_x,
        bench_q35_gate.prove_speedup_x
    );

    // Also prove & standalone-verify full Layer-0 `C = 64` `IntWY` (`16 * 64 * 256` cells + `SLT` + `D1b`
    // + `MXFP4` `gate_proj` + `U1` boundary weld) in one batched speculative-prefill pass!
    let registry = Qwen35WeightRegistry::commit_all_24_layers(&mmap).expect("commit 24 layers");
    let u1_online = commit_u1_pcs_boundaries(&turn.boundaries_bb);
    let names = Qwen35WeightRegistry::layer_tensor_names(audited_layer);
    let mut digests = Vec::with_capacity(names.len());
    let mut gate_slot = 0usize;
    for (idx, nm) in names.iter().enumerate() {
        let m = Mxfp4Matrix::from_safetensors(&mmap, nm).unwrap();
        if nm.ends_with(".mlp.gate_proj.weight") {
            gate_slot = idx;
        }
        digests.push(m.digest);
    }
    let gate_pcs = PrecommittedMxfp4Pcs::build(&turn.gate_proj_mat);
    let mut qs_bind_in = [0u8; 96];
    qs_bind_in[0..32].copy_from_slice(&digests[gate_slot]);
    qs_bind_in[32..64].copy_from_slice(&gate_pcs.q_state.root);
    qs_bind_in[64..96].copy_from_slice(&gate_pcs.s_state.root);
    let qs_binding = qwen35audit::ext4::cshake256_32(b"QW35-QS-PCS-BIND-V1", &qs_bind_in);

    let wy_path = qwen35audit::ext4::merkle_open_single_cshake(
        b"QW35-GLOBAL-WEIGHT-TREE-V1",
        &registry.layer_digests,
        audited_layer,
    );
    let tl0 = Instant::now();
    let mut tr_l_prv = qwen35audit::ext4::CShakeTranscript::new(b"SPEC-FULL-GDN-WY-L0");
    let full_gdn_pf = prove_audited_gdn_layer(
        &registry.weight_root,
        audited_layer,
        AuditedGdnLayerWitness {
            layer_weight_path: wy_path,
            layer_tensor_digests: digests,
            gate_proj_tensor_slot: gate_slot,
            gate_pcs: &gate_pcs,
            b_in_state: &u1_online.boundary_states[audited_layer],
            b_out_state: &u1_online.boundary_states[audited_layer + 1],
            b_in_bb: &turn.boundaries_bb[audited_layer],
            b_out_bb: &turn.boundaries_bb[audited_layer + 1],
            delta_gdn_bb: &turn.delta_gdn_bb,
            delta_mlp_bb: &turn.delta_mlp_bb,
            wy: &turn.wy_witness,
            x_ln2_i16: &turn.x_ln2_i16,
            gate_y_raw: &turn.gate_proj_y_raw,
        },
        &mut tr_l_prv,
    )
    .expect("prove full Qwen3.5 Layer-0 C=64 IntWY + MXFP4");
    let full_gdn_prove_ms = tl0.elapsed().as_secs_f64() * 1000.0;
    let mut gdn_wire = Vec::new();
    full_gdn_pf.write_to(&mut gdn_wire);

    let tlv0 = Instant::now();
    let mut tr_l_ver = qwen35audit::ext4::CShakeTranscript::new(b"SPEC-FULL-GDN-WY-L0");
    verify_audited_gdn_layer_standalone(
        &AuditedGdnLayerVerifyStmt {
            expected_weight_root: &registry.weight_root,
            expected_b_in_root: &u1_online.boundary_roots[audited_layer],
            expected_b_out_root: &u1_online.boundary_roots[audited_layer + 1],
            expected_audited_layer: audited_layer,
            expected_q_s_binding: &qs_binding,
            bnd_vars: 16,
        },
        &full_gdn_pf,
        &mut tr_l_ver,
    )
    .expect("verify full Qwen3.5 Layer-0 C=64 IntWY + MXFP4 standalone");
    let full_gdn_verify_ms = tlv0.elapsed().as_secs_f64() * 1000.0;
    println!(
        "[1c] Full Qwen3.5-0.8B Layer-0 C=64 IntWY + MXFP4 + U1: prove = {:.2} ms | verify = {:.2} ms | wire = {:.2} KiB",
        full_gdn_prove_ms,
        full_gdn_verify_ms,
        (gdn_wire.len() as f64) / 1024.0
    );

    // -------------------------------------------------------------------------
    // 3. Exact Integer Argmax Dominance Certificate (`D1b` LogUp Positive-Gap Proof, `T=64, V=2048`)
    //    & `VERDICTS.md` §9 Float-Steering / Tie-Breaking Drift Detection
    // -------------------------------------------------------------------------
    let (vocab_ids, mut real_logits) = compute_real_qwen35_shortlist_logits(&mmap, &final_h, 64)
        .expect("compute real Qwen3.5 logits");
    assert_eq!(
        vocab_ids[0], 348,
        "slot 0 must be real Qwen token ' *' (348)"
    );
    assert_eq!(
        vocab_ids[1], 23985,
        "slot 1 must be real Qwen token ' ×' (23985)"
    );

    // Plant realistic close-margin competition (`VERDICTS.md` §9 `"17 * 23 = 391." -> "17 × 23 = 391"`)
    // at `t* = 19` (`slot 0 = " *"` beats `slot 1 = " ×"` by `1` integer unit — well inside float tolerance!)
    // AND exact flat integer tie (`"Canberra." -> "Canberra"`) at `t = 42` (`slot 0 == slot 1`)!
    let t_star_drift = 19usize;
    let max_t19 = *real_logits[t_star_drift * 2048..(t_star_drift + 1) * 2048]
        .iter()
        .max()
        .unwrap();
    real_logits[t_star_drift * 2048] = max_t19 + 4; // `" *"` (tok 348) wins by +1!
    real_logits[t_star_drift * 2048 + 1] = max_t19 + 3; // `" ×"` (tok 23985) is 1 unit behind!

    let t_tie = 42usize;
    let max_t42 = *real_logits[t_tie * 2048..(t_tie + 1) * 2048]
        .iter()
        .max()
        .unwrap();
    real_logits[t_tie * 2048] = max_t42 + 5; // `"Canberra."` (lower index 0)
    real_logits[t_tie * 2048 + 1] = max_t42 + 5; // `"Canberra"`  (higher index 1, exact tie!)

    let honest_draft: Vec<usize> = (0..64)
        .map(|t| canonical_greedy_tok_i64(&real_logits[t * 2048..(t + 1) * 2048]))
        .collect();
    assert_eq!(honest_draft[t_star_drift], 0);
    assert_eq!(honest_draft[t_tie], 0);
    assert_eq!(
        audit_speculative_draft_prefill(&real_logits, 64, 2048, &honest_draft),
        SpeculativePrefillVerdict::AcceptedAll
    );

    let td0 = Instant::now();
    let dom_pf = prove_argmax_dominance_d1b_ext4(&real_logits, 64, 2048, &honest_draft)
        .expect("prove honest D1b argmax dominance (incl. exact flat tie at t=42)");
    let dom_prove_ms = td0.elapsed().as_secs_f64() * 1000.0;
    let dom_bytes = dom_pf.to_bytes();

    let tdv0 = Instant::now();
    let decoded_dom = ArgmaxDominanceExt4Proof::from_bytes(&dom_bytes).expect("decode dom proof");
    verify_argmax_dominance_d1b_standalone(
        &dom_pf.logit_pcs_root,
        6,
        11,
        &honest_draft,
        &decoded_dom,
    )
    .expect("standalone verify D1b argmax dominance");
    let dom_verify_ms = tdv0.elapsed().as_secs_f64() * 1000.0;
    println!(
        "[2a] D1b Argmax Dominance Cert (T=64, V=2048, 2x131,072 D1b -> [0, 2^16)): prove = {:.2} ms | verify = {:.2} ms | wire = {:.2} KiB",
        dom_prove_ms,
        dom_verify_ms,
        (dom_bytes.len() as f64) / 1024.0
    );

    // Falsifier A: `VERDICTS.md` §9 `"17 * 23 = 391." -> "17 × 23 = 391"` 1-token float steering at `t* = 19`!
    let mut steered_draft = honest_draft.clone();
    steered_draft[t_star_drift] = 1; // swap `" *"` (slot 0, tok 348) -> `" ×"` (slot 1, tok 23985)
    steered_draft[35] = 7; // later downstream drift after `t* = 19`!
    assert_eq!(
        audit_speculative_draft_prefill(&real_logits, 64, 2048, &steered_draft),
        SpeculativePrefillVerdict::Diverged {
            first_bad_t: t_star_drift,
            drafted_tok: 1,
            corrected_greedy_tok: 0, // 1 free corrected token (`" *"`) at exact first diverging index `t* = 19`!
        }
    );
    assert!(
        prove_argmax_dominance_d1b_ext4(&real_logits, 64, 2048, &steered_draft).is_err(),
        "D1b argmax dominance prover must reject 1-unit steered ' ×' token at t* = 19"
    );
    assert!(
        verify_argmax_dominance_d1b_standalone(
            &dom_pf.logit_pcs_root,
            6,
            11,
            &steered_draft,
            &decoded_dom
        )
        .is_err(),
        "standalone verifier must reject replaying honest proof against steered y_hat"
    );

    // Falsifier B: `VERDICTS.md` §9 `"Canberra." -> "Canberra"` flat-tie index-tie-break tamper at `t = 42`!
    let mut tie_tampered_draft = honest_draft.clone();
    tie_tampered_draft[t_tie] = 1; // equal logit, higher index (`Delta[42, 0] = 0 - 1 = -1`!)
    assert_eq!(
        audit_speculative_draft_prefill(&real_logits, 64, 2048, &tie_tampered_draft),
        SpeculativePrefillVerdict::Diverged {
            first_bad_t: t_tie,
            drafted_tok: 1,
            corrected_greedy_tok: 0,
        }
    );
    assert!(
        prove_argmax_dominance_d1b_ext4(&real_logits, 64, 2048, &tie_tampered_draft).is_err(),
        "D1b argmax dominance prover must reject higher-index tie-break violation"
    );

    // Falsifier B2: Out-of-range / wraparound logit (`logit = P - 40_000`) rejected by prover AND
    // verifier-level `logit_d1b_proof` check against committed out-of-range table!
    let mut wrap_logits = real_logits.clone();
    wrap_logits[0] = (qwen35audit::ext4::P as i64) - 40_000;
    assert!(
        prove_argmax_dominance_d1b_ext4(&wrap_logits, 64, 2048, &honest_draft).is_err(),
        "out-of-range wraparound logit must be rejected by [0, 2^16) shifted-logit host guard"
    );
    let mut wrap_table_u32 = vec![32_768u32; 64 * 2048];
    wrap_table_u32[0] = (qwen35audit::ext4::P - 7_232) as u32; // > 65,535 (`[0, 2^16)` D1b violation!)
    let wrap_logit_state = qwen35audit::pcs_ext4::commit_table_pcs(
        &wrap_table_u32,
        qwen35audit::pcs_ext4::PcsParams::default_zk(3),
        None,
    );
    assert!(
        verify_argmax_dominance_d1b_standalone(
            &wrap_logit_state.root,
            6,
            11,
            &honest_draft,
            &decoded_dom
        )
        .is_err(),
        "standalone verifier must reject out-of-range committed logit_pcs_root"
    );
    let mut forged_d1b_dom = decoded_dom.clone();
    forged_d1b_dom.logit_d1b_proof.root_q = Ext4::ZERO;
    assert!(
        verify_argmax_dominance_d1b_standalone(
            &dom_pf.logit_pcs_root,
            6,
            11,
            &honest_draft,
            &forged_d1b_dom
        )
        .is_err(),
        "standalone verifier must reject zero D1b LogUp root_q"
    );

    // Falsifier C: Forged `gap_at_z` / inflated winning-logit claim rejected by `Gruen` selector sumcheck!
    let mut forged_dom = decoded_dom.clone();
    forged_dom.gap_at_z = forged_dom.gap_at_z.add(Ext4::ONE);
    assert!(
        verify_argmax_dominance_d1b_standalone(
            &dom_pf.logit_pcs_root,
            6,
            11,
            &honest_draft,
            &forged_dom
        )
        .is_err(),
        "forged gap_at_z must fail Gruen Mode-2 winning-logit selector equation"
    );

    // Falsifier C2: Malformed `win_sel_gruen.kappa = 0` rejected cleanly (`Err`, zero panic/OOM)!
    let mut bad_kappa_dom = decoded_dom.clone();
    bad_kappa_dom.win_sel_gruen.kappa = 0;
    assert!(
        verify_argmax_dominance_d1b_standalone(
            &dom_pf.logit_pcs_root,
            6,
            11,
            &honest_draft,
            &bad_kappa_dom
        )
        .is_err(),
        "mismatched win_sel_gruen.kappa must be rejected before public selector MLE evaluation"
    );

    // -------------------------------------------------------------------------
    // 4. `3×` Depth-Looped MoE Weight-Opening Collapse (`Inkling-2-Mini` `R = 3` Shape)
    //    & Pre-/Post-Challenge Forgery Defense
    // -------------------------------------------------------------------------
    let loop_bench =
        benchmark_inkling2_looped_moe_r3().expect("benchmark Inkling-2-Mini R=3 looped MoE");
    println!("[3] {}", loop_bench.shape_desc);
    println!(
        "     Unfolded (3x W open) : wt_prove = {:7.2} ms | total_prove = {:7.2} ms | verify = {:6.2} ms | wire = {:7.2} KiB",
        loop_bench.unfolded_weight_prove_ms,
        loop_bench.unfolded_total_prove_ms,
        loop_bench.unfolded_verify_ms,
        loop_bench.unfolded_proof_kib
    );
    println!(
        "     Collapsed (1x W open): wt_prove = {:7.2} ms | total_prove = {:7.2} ms | verify = {:6.2} ms | wire = {:7.2} KiB",
        loop_bench.collapsed_weight_prove_ms,
        loop_bench.collapsed_total_prove_ms,
        loop_bench.collapsed_verify_ms,
        loop_bench.collapsed_proof_kib
    );
    println!(
        "     WEIGHT-PROVING SPEEDUP: {:.2}x (total prove: {:.2}x, verify: {:.2}x, wire: {:.2}x smaller!)",
        loop_bench.weight_prove_speedup_x,
        loop_bench.total_prove_speedup_x,
        loop_bench.verify_speedup_x,
        loop_bench.unfolded_proof_kib / loop_bench.collapsed_proof_kib
    );
    assert!(
        (loop_bench.unfolded_proof_kib / loop_bench.collapsed_proof_kib) >= 2.35
            && loop_bench.weight_prove_speedup_x >= 1.8,
        "expected >= 2.35x wire compression & >= 1.8x weight-proving speedup on R=3 looped MoE, got wire={:.2}x wt={:.2}x",
        loop_bench.unfolded_proof_kib / loop_bench.collapsed_proof_kib,
        loop_bench.weight_prove_speedup_x
    );

    // Falsifier D: Pre-committed pass-1 output forgery (`Y^{(1)}[0, 0] += 1`) rejected!
    let small_weights = PrecommittedSliceWeights::build(&q38.mat_mxfp4);
    let x_p3: [Vec<i16>; 3] = [0usize, 1, 2].map(|r| {
        (0..(64 * 5120))
            .map(|i| (((i * (7 + r) + 3) % 31) as i16) - 15)
            .collect()
    });
    let honest_y_p3: [Vec<i64>; 3] = [
        qwen35audit::qwen35_layer::eval_mxfp4_int_contraction(&x_p3[0], 64, 5120, &q38.mat_mxfp4),
        qwen35audit::qwen35_layer::eval_mxfp4_int_contraction(&x_p3[1], 64, 5120, &q38.mat_mxfp4),
        qwen35audit::qwen35_layer::eval_mxfp4_int_contraction(&x_p3[2], 64, 5120, &q38.mat_mxfp4),
    ];
    let mut bad_y_p3 = honest_y_p3.clone();
    bad_y_p3[1][0] += 1;
    let (bad_loop_pf, _) = prove_looped_moe_collapsed_ext4(&small_weights, &x_p3, &bad_y_p3, 64);
    assert!(
        verify_looped_moe_collapsed_standalone(
            &small_weights.q_state.root,
            &small_weights.s_state.root,
            &bad_loop_pf.x_pcs_roots,
            &bad_loop_pf.y_pcs_roots,
            6,
            8,
            8,
            &bad_loop_pf,
        )
        .is_err(),
        "corrupted pass-1 output in R=3 looped MoE must be rejected with prob >= 1 - 2/|Ext4|"
    );

    // Falsifier E (`loopFold_postChallenge_forgery_tooth` defense): Post-challenge cancellation
    // `y_evals_at_r[0]' = y_0 - rho * 1, y_evals_at_r[1]' = y_1 + 1` rejected by pre-`rho` PCS binding!
    let (honest_loop_pf, _) =
        prove_looped_moe_collapsed_ext4(&small_weights, &x_p3, &honest_y_p3, 64);
    let mut tr_replay =
        qwen35audit::ext4::CShakeTranscript::new(b"INKLING2-LOOPED-MOE-COLLAPSE-V1");
    tr_replay.absorb_u32(b"log_t", 6);
    tr_replay.absorb_u32(b"log_j", 8);
    tr_replay.absorb_u32(b"log_k", 8);
    tr_replay.absorb_root(b"q_root", &small_weights.q_state.root);
    tr_replay.absorb_root(b"s_root", &small_weights.s_state.root);
    for r in &honest_loop_pf.x_pcs_roots {
        tr_replay.absorb_root(b"x_root", r);
    }
    for r in &honest_loop_pf.y_pcs_roots {
        tr_replay.absorb_root(b"y_root", r);
    }
    let rho_stolen = tr_replay.squeeze_ext4(b"loop_rho", true);
    let mut post_chal_pf = honest_loop_pf.clone();
    post_chal_pf.y_evals_at_r[0] = post_chal_pf.y_evals_at_r[0].sub(rho_stolen);
    post_chal_pf.y_evals_at_r[1] = post_chal_pf.y_evals_at_r[1].add(Ext4::ONE);
    assert!(
        verify_looped_moe_collapsed_standalone(
            &small_weights.q_state.root,
            &small_weights.s_state.root,
            &post_chal_pf.x_pcs_roots,
            &post_chal_pf.y_pcs_roots,
            6,
            8,
            8,
            &post_chal_pf,
        )
        .is_err(),
        "post-challenge rho-cancellation forgery must be rejected by pre-committed Y_r PCS roots"
    );
    println!("================================================================================\n");
}
