//! End-to-End `U1` Commit-Then-Audit + Output Policy Receipt CLI for Real Pretrained `Qwen/Qwen3.5-0.8B-Base`
//! (`24` layers = `18 × Gated DeltaNet + 6 × GQA`) & `Qwen/Qwen3.8-Flash-Next-FP8` (`H_v = 48` GDN + `QSA` + `512E` MoE).

use qwen35audit::ext4::P_U32;
use qwen35audit::pcs_ext4::{PcsParams, PcsShape};
use qwen35audit::py_bundle::{load_qwen38fn_range_bundle, verify_py_qwen35_bundle};
use qwen35audit::qwen35_layer::{execute_qwen35_24_layers_mmap, PrecommittedMxfp4Pcs};
use qwen35audit::qwen38fn_slice::{prove_and_verify_qwen38fn_real_slice, prove_qsa_top_kb_ext4};
use qwen35audit::safetensors_mmap::{
    MmapSafetensors, Mxfp4Matrix, Qwen35WeightRegistry, QWEN35_SAFETENSORS_FILE,
};
use qwen35audit::u1_audit::{
    broken_whole_word_complement_sk, commit_u1_fast_stream_boundaries, commit_u1_pcs_boundaries,
    derive_fiat_shamir_audited_gdn_layer, prove_padded_absence_zk, prove_u1_audit_bundle,
    redact_sk_secrets, verify_u1_audit_bundle_standalone, Qwen35U1AuditBundle,
};
use std::ops::Add;
use std::path::Path;
use std::time::Instant;

fn hex8(r: &[u8; 32]) -> String {
    r[0..8].iter().map(|b| format!("{b:02x}")).collect()
}

/// Real 64-token `Qwen/Qwen3.5-0.8B-Base` prompt IDs (`tokenizer.json`-verified technical + secret-redaction prompt).
fn default_real_64_token_prompt() -> Vec<u32> {
    vec![
        760, 6511, 314, 9338, 369, 11725, 13, 574, 279, 2578, 315, 3643, 1899, 264, 1515, 11, 584,
        1165, 6722, 4888, 198, 750, 4658, 62, 1831, 7, 1318, 25, 1140, 58, 396, 990, 1657, 25, 396,
        1447, 262, 2366, 11, 5944, 284, 220, 15, 11, 1181, 7, 1318, 8, 481, 220, 16, 198, 13824,
        318, 257, 6396, 3989, 25, 366, 2380, 12, 13847, 12, 9999,
    ]
}

fn main() -> Result<(), String> {
    println!("==========================================================================================");
    println!(
        "  qwen35audit — Real Pretrained Qwen3.5-0.8B (24L) & Qwen3.8-Flash-Next (48H) ZK-Audit"
    );
    println!(
        "  Field: BabyBear (p = 2013265921) -> Ext4 (X^4 - 11, 123.7b) | Hash/FS: NIST cSHAKE256"
    );
    println!("==========================================================================================");

    let shape_sample = PcsShape::new(18, PcsParams::default_zk(2));
    let (ahiv_bits, bciks_bits) = shape_sample.provable_ud_soundness_bits();
    println!(
        "[PCS] SuccinctExt4Pcs (m=18, blowup={}, t_cols={}, zk=true): AHIV17 d/3 UD = {:.2} bits | BCIKS20 (1-rho)/2 UD = {:.2} bits",
        shape_sample.blowup, shape_sample.t_cols, ahiv_bits, bciks_bits
    );

    // 1. Memory-map real cached `Qwen/Qwen3.5-0.8B-Base` safetensors (`1.66 GiB`, `488` tensors, `0` copies!)
    let t_mmap = Instant::now();
    let mmap = MmapSafetensors::open(QWEN35_SAFETENSORS_FILE)?;
    let mmap_ms = t_mmap.elapsed().as_secs_f64() * 1000.0;

    let t_reg = Instant::now();
    let registry = Qwen35WeightRegistry::commit_all_24_layers(&mmap)?;
    let reg_ms = t_reg.elapsed().as_secs_f64() * 1000.0;
    println!(
        "[MMAP] Zero-copy mmap ({} tensors, header={} B) in {:.2} ms | Offline 24-layer MXFP4 cSHAKE256 commitment ({} matrices, {:.2}M params) in {:.2} ms -> weight_root = {}..",
        mmap.tensors.len(),
        mmap.header_len,
        mmap_ms,
        registry.total_tensors_committed,
        registry.total_quantized_params as f64 / 1e6,
        reg_ms,
        hex8(&registry.weight_root)
    );

    // 2. Execute all 24 real pretrained layers on a 64-token prompt + commit 25 `U1` boundaries!
    let token_ids = default_real_64_token_prompt();
    let initial_audit_probe = 0usize;
    let t_exec = Instant::now();
    let (turn0, _final_h) = execute_qwen35_24_layers_mmap(&mmap, &token_ids, initial_audit_probe)?;
    let exec_ms = t_exec.elapsed().as_secs_f64() * 1000.0;

    // Benchmark BOTH online U1 boundary modes (`fast streaming cSHAKE256` vs `full 25-layer ZK SuccinctExt4Pcs`!)
    let t_u1_fast = Instant::now();
    let _fast_roots = commit_u1_fast_stream_boundaries(&turn0.boundaries_bb);
    let u1_fast_us_per_tok = (t_u1_fast.elapsed().as_secs_f64() * 1e6) / 64.0;

    let t_u1_pcs = Instant::now();
    let u1_online = commit_u1_pcs_boundaries(&turn0.boundaries_bb);
    let u1_pcs_ms = t_u1_pcs.elapsed().as_secs_f64() * 1000.0;
    let u1_pcs_us_per_tok = (u1_pcs_ms * 1000.0) / 64.0;
    println!(
        "[U1 ONLINE] 24-layer forward = {:.2} ms | Fast cSHAKE256 25-boundary stream = {:.2} us/tok | Full 25-boundary ZK SuccinctExt4Pcs = {:.2} ms ({:.2} us/tok)",
        exec_ms, u1_fast_us_per_tok, u1_pcs_ms, u1_pcs_us_per_tok
    );

    // 3. Deterministic `sk-...` redaction + VRF layer selection + Full Succinct Proof Generation!
    let raw_completion =
        b"OPENAI_API_KEY=sk-proj-9f8a7b6c5d4e3f2a1b0c9d8e\nStatus: verified safe completion.\n";
    let (redacted_completion, n_redacted) = redact_sk_secrets(raw_completion);
    assert_eq!(n_redacted, 1);
    assert!(broken_whole_word_complement_sk(raw_completion)); // P4 whole-word complement trap!

    let vrf_layer = derive_fiat_shamir_audited_gdn_layer(
        &registry.weight_root,
        &u1_online.boundary_roots,
        &[0xAA; 32],
    );
    let (turn, _) = if vrf_layer == initial_audit_probe {
        (turn0, Vec::new())
    } else {
        execute_qwen35_24_layers_mmap(&mmap, &token_ids, vrf_layer)?
    };

    // Precommit offline PCS for `vrf_layer`'s `mlp.gate_proj.weight` (`[3584 -> 4096, 1024]`)
    let layer_names = Qwen35WeightRegistry::layer_tensor_names(vrf_layer);
    let mut layer_digests = Vec::with_capacity(layer_names.len());
    let mut gate_slot = 0usize;
    for (idx, nm) in layer_names.iter().enumerate() {
        let m = Mxfp4Matrix::from_safetensors(&mmap, nm)?;
        if nm.ends_with(".mlp.gate_proj.weight") {
            gate_slot = idx;
        }
        layer_digests.push(m.digest);
    }
    let gate_pcs = PrecommittedMxfp4Pcs::build(&turn.gate_proj_mat);

    let t_prove = Instant::now();
    let (proof_bytes, out_content_root, qs_binding) = prove_u1_audit_bundle(
        &registry,
        layer_digests,
        gate_slot,
        &gate_pcs,
        &u1_online,
        &turn,
        &redacted_completion,
    )?;
    let prove_ms = t_prove.elapsed().as_secs_f64() * 1000.0;

    // Standalone Verification WITH cleartext redacted output AND in pure ZERO-CLEARTEXT ZK mode (`None`)!
    let t_ver = Instant::now();
    verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        vrf_layer,
        &qs_binding,
        &out_content_root,
        None, // Pure zero-knowledge standalone check (`0` cleartext output bytes seen by auditor!)
        &proof_bytes,
    )?;
    let verify_ms = t_ver.elapsed().as_secs_f64() * 1000.0;
    verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        vrf_layer,
        &qs_binding,
        &out_content_root,
        Some(&redacted_completion),
        &proof_bytes,
    )?;

    println!(
        "[AUDIT] VRF-selected real GDN+SwiGLU Layer L{} | Prove = {:.2} ms ({:.2} ms/tok) | Standalone Verify (0-cleartext ZK) = {:.2} ms | Proof = {:.2} KiB ({:.3} MiB)",
        vrf_layer,
        prove_ms,
        prove_ms / 64.0,
        verify_ms,
        proof_bytes.len() as f64 / 1024.0,
        proof_bytes.len() as f64 / (1024.0 * 1024.0)
    );

    // 4. Execute & Verify ALL 5 Planted Adversarial Soundness Attacks!
    let orig_bundle = Qwen35U1AuditBundle::from_bytes(&proof_bytes)?;

    // Attack 1: Swapping 1 pretrained MXFP4 weight nibble (`weight_root` / `qs_binding` mismatch)
    let mut bad_w_mat = turn.gate_proj_mat.clone();
    bad_w_mat.nibbles[0] ^= 0x01;
    bad_w_mat.digest = Mxfp4Matrix::compute_digest(
        &bad_w_mat.name,
        bad_w_mat.rows_orig,
        bad_w_mat.rows_pad,
        bad_w_mat.cols_orig,
        &bad_w_mat.nibbles,
        &bad_w_mat.scales,
    );
    let mut bad_b1 = orig_bundle.clone();
    bad_b1.layer_proof.layer_tensor_digests[gate_slot] = bad_w_mat.digest;
    let res1 = verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        vrf_layer,
        &qs_binding,
        &out_content_root,
        None,
        &bad_b1.to_bytes(),
    );
    assert!(res1.is_err(), "Attack 1 must be rejected");

    // Attack 2: Mutating 1 GDN WY `UW` cell evaluation / opened column
    let mut bad_b2 = orig_bundle.clone();
    bad_b2.layer_proof.uw_eval_at_z = bad_b2
        .layer_proof
        .uw_eval_at_z
        .add(qwen35audit::ext4::Ext4::ONE);
    let res2 = verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        vrf_layer,
        &qs_binding,
        &out_content_root,
        None,
        &bad_b2.to_bytes(),
    );
    assert!(res2.is_err(), "Attack 2 must be rejected");

    // Attack 3: Mutating 1 boundary activation (`boundary_roots[vrf_layer + 1]` / `b_out_eval`)
    let mut bad_b3 = orig_bundle.clone();
    bad_b3.layer_proof.b_out_eval = bad_b3
        .layer_proof
        .b_out_eval
        .add(qwen35audit::ext4::Ext4::ONE);
    let res3 = verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        vrf_layer,
        &qs_binding,
        &out_content_root,
        None,
        &bad_b3.to_bytes(),
    );
    assert!(res3.is_err(), "Attack 3 must be rejected");

    // Attack 4: Forging a PCS Merkle column / sibling hash
    let mut bad_b4 = orig_bundle.clone();
    bad_b4.layer_proof.uw_pcs_proof.opened_cols[0] =
        (bad_b4.layer_proof.uw_pcs_proof.opened_cols[0] + 1) % P_U32;
    let res4 = verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        vrf_layer,
        &qs_binding,
        &out_content_root,
        None,
        &bad_b4.to_bytes(),
    );
    assert!(res4.is_err(), "Attack 4 must be rejected");

    // Attack 5: Leaking unredacted `sk-proj-...` secret (both prover refusal AND verifier rejection!)
    let mut leak_tr = qwen35audit::ext4::CShakeTranscript::new(b"leak");
    let res5_prv = prove_padded_absence_zk(raw_completion, &mut leak_tr);
    let res5_ver = verify_u1_audit_bundle_standalone(
        &registry.weight_root,
        &u1_online.boundary_roots,
        vrf_layer,
        &qs_binding,
        &out_content_root,
        Some(raw_completion),
        &proof_bytes,
    );
    assert!(
        res5_prv.is_err() && res5_ver.is_err(),
        "Attack 5 must be rejected"
    );

    println!(
        "[TEETH] 5/5 Planted Soundness Attacks Rejected:\n  [1] MXFP4 nibble swap -> {}\n  [2] GDN WY UW mutation -> {}\n  [3] Boundary activation tamper -> {}\n  [4] PCS Merkle column forgery -> {}\n  [5] Unredacted sk-proj-... leak -> {} / {}",
        res1.unwrap_err(),
        res2.unwrap_err(),
        res3.unwrap_err(),
        res4.unwrap_err(),
        res5_prv.unwrap_err(),
        res5_ver.unwrap_err()
    );

    // 5. Cross-Language Verification #1: `/tmp/qwen35_real_layer_turn.bin` (`QW35AUD1` from PyTorch `real_qwen35_gdn_eval.py`)
    let py35_path = Path::new("/tmp/qwen35_real_layer_turn.bin");
    if py35_path.exists() {
        let (sum35, _py_wy) = verify_py_qwen35_bundle(py35_path)?;
        println!(
            "[PY<->RS QWEN3.5] Verified PyTorch QW35AUD1 bundle: real P5 completion {:?} -> {:?} ({} redactions, ZK Absent prove={:.2}ms / verify={:.2}ms)",
            sum35.gen_text_raw.trim(),
            sum35.gen_text_redacted.trim(),
            sum35.redaction_count,
            sum35.absence_prove_ms,
            sum35.absence_verify_ms
        );
        for (nm, r_orig, c_in, p_ms, v_ms) in &sum35.mxfp4_verified_names {
            println!(
                "  * Layer 0 {nm} ({r_orig}x{c_in} MXFP4 E2M1): Ext4 0-mul Horner + PCS Prove = {p_ms:.2} ms | Standalone Verify = {v_ms:.2} ms"
            );
        }
    }

    // 6. Cross-Language Verification #2: `/tmp/qwen38fn_real_4layer_slice.bin` (`QW38FNS1` from real `Qwen/Qwen3.8-Flash-Next-FP8` HTTP Range)
    let q38_path = Path::new("/tmp/qwen38fn_real_4layer_slice.bin");
    if q38_path.exists() {
        let (wy48, x_in, nibs, scs, y_raw, qsa, top1_eid, top1_tok) =
            load_qwen38fn_range_bundle(q38_path)?;
        let q38_res =
            prove_and_verify_qwen38fn_real_slice(&wy48, &x_in, &nibs, &scs, &y_raw, &qsa)?;
        let b1a_forge = prove_qsa_top_kb_ext4(&qsa, Some((31, (8u32 << 27) + 15)));
        assert!(b1a_forge.is_err());
        println!(
            "[QWEN3.8-FLASH-NEXT REAL SLICE] L0 H_v=48 (1.05M cells) GDN WY + Top-1 Expert #{} (tok {}): Prove = {:.2} ms | Verify = {:.2} ms | Proof = {:.2} KiB || L3 QSA C3+C5 Top-K_B: Prove = {:.2} ms | Verify = {:.2} ms | Proof = {:.2} KiB (Trap B1a rejected: {})",
            top1_eid,
            top1_tok,
            q38_res.wy_prove_ms,
            q38_res.wy_verify_ms,
            q38_res.wy_proof_bytes.len() as f64 / 1024.0,
            q38_res.qsa_prove_ms,
            q38_res.qsa_verify_ms,
            q38_res.qsa_proof_bytes.len() as f64 / 1024.0,
            b1a_forge.unwrap_err()
        );
    }

    Ok(())
}
