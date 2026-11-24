//! Live Verifiable Exact-Integer `Qwen3.5-0.8B` (24L) + `Qwen3.8-27B` Slice Agent Runner CLI.
//!
//! Executes:
//!   1. `Qwen3.8-27B` real cached `MXFP4` `[256, 5120]` `.npz` slice audit (`8 -> 0` `-0.0` nibble canonicalization + `Ext4` proof),
//!   2. 100%-integer 24-layer `Qwen/Qwen3.5-0.8B-Base` live multi-token `CotToolCall` generation,
//!   3. `1` vs `12` `rayon` thread determinism audit (bit-identical SHA-256 & `cSHAKE256` boundary/logit digests),
//!   4. `U1` VRF layer proof + 0-cleartext ZK `Absent("sk-...")` + canonical `VAGENT01` / `VASTMT01` byte verification,
//!   5. Optional `--emit-dir <dir>` writing `vagent01_stmt.bin`, `vagent01_receipt.bin`, and `vagent01_bundle.bin`.

use qwen35audit::agent_runner::{
    audit_qwen38_27b_mxfp4_npz_slice, run_live_verifiable_qwen_agent_turn,
    verify_public_redacted_vagent01_bytes, verify_vagent01_bytes_pinned, ExactIntDecodeCache,
    ExactIntQwen35Engine, QwenBpeTokenizer, QWEN38_27B_NPZ_PATH,
};
use qwen35audit::safetensors_mmap::QWEN35_TOKENIZER_FILE;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

fn hex32(d: &[u8; 32]) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}

fn main() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    let mut emit_dir: Option<PathBuf> = None;
    let mut skip_thread_check = false;
    let mut i = 1usize;
    while i < args.len() {
        match args[i].as_str() {
            "--emit-dir" => {
                i += 1;
                if i >= args.len() {
                    return Err("--emit-dir requires a path".to_string());
                }
                emit_dir = Some(PathBuf::from(&args[i]));
            }
            "--fast" => {
                skip_thread_check = true;
            }
            other => return Err(format!("unknown argument: {other}")),
        }
        i += 1;
    }

    println!("==========================================================================================");
    println!(
        "  verifiable_qwen_agent — 100% Native Exact-Integer Qwen3.5-0.8B (24L) + Qwen3.8-27B E2E"
    );
    println!(
        "  Zero Python | Zero Float Online Path | StreamCodec VAGENT01 + BabyBear Ext4 U1 ZK Audit"
    );
    println!("==========================================================================================");

    // 1. Audit real cached `Qwen3.8-27B` Layer-0 `MXFP4` `.npz` slice (`8 -> 0` `-0.0` canonicalization!)
    let q38_rep = audit_qwen38_27b_mxfp4_npz_slice(QWEN38_27B_NPZ_PATH)?;
    println!(
        "[QWEN3.8-27B SLICE] [{}x{}] MXFP4 (.npz): raw `-0.0` (nib=8) = {} -> canonical = {} | max|Y_raw| = {} (< P/2) | Ext4 Prove = {:.2} ms | Verify = {:.2} ms | Proof = {:.2} KiB",
        q38_rep.rows,
        q38_rep.cols,
        q38_rep.raw_neg_zero_nibble_count,
        q38_rep.canonical_neg_zero_nibble_count,
        q38_rep.max_abs_y_raw,
        q38_rep.prove_ms,
        q38_rep.verify_ms,
        q38_rep.proof_bytes_len as f64 / 1024.0
    );

    // 2. Load pure-Rust BPE tokenizer & zero-copy mmap 24-layer integer `Qwen3.5-0.8B` engine (12-thread pool)
    let pool12 = rayon::ThreadPoolBuilder::new()
        .num_threads(12)
        .build()
        .map_err(|e| format!("pool12 error: {e}"))?;

    let t_load = Instant::now();
    let tok = Arc::new(QwenBpeTokenizer::from_file(QWEN35_TOKENIZER_FILE)?);
    let engine = Arc::new(pool12.install(ExactIntQwen35Engine::load_default)?);
    let load_ms = t_load.elapsed().as_secs_f64() * 1000.0;
    println!(
        "[LOAD] Pure-Rust BPE Tokenizer + 24L Mixed-MXFP4/FP8 IntEngine ({:.2}M quantized params, {} tensors) in {:.2} ms | weight_root = {}",
        engine.registry.total_quantized_params as f64 / 1e6,
        engine.registry.total_tensors_committed,
        load_ms,
        &hex32(&engine.registry.weight_root)[..16]
    );

    // 3. Run full live verifiable agent turn on 12 threads!
    let rep12 = pool12.install(|| run_live_verifiable_qwen_agent_turn(&engine, &tok, 56))?;
    println!(
        "[INFER 12T] Prefill (64 tok, C=64 IntWY): {:.2} ms ({:.2} tok/s) | Greedy Decode ({} tok): {:.2} ms ({:.2} tok/s) | U1 Fast Stream: {:.2} us/tok",
        rep12.prefill_ms,
        rep12.prefill_tok_s,
        rep12.generated_token_ids.len() - 1,
        rep12.decode_ms,
        rep12.decode_tok_s,
        rep12.u1_stream_fast_us_per_tok
    );
    println!(
        "  Raw Output   ({} B): {}",
        rep12.w_raw.len(),
        String::from_utf8_lossy(&rep12.w_raw)
    );
    println!(
        "  Clean Output ({} B): {}",
        rep12.w_clean.len(),
        String::from_utf8_lossy(&rep12.w_clean)
    );
    println!("  Extracted LL(1) AST: {}", rep12.claimed_ast);
    println!(
        "[WELD & ZK] VRF Layer L{} | Prove = {:.2} ms | Verify = {:.2} ms | VASTMT01 = {} B | VAGENT01 = {} B | Full Bundle = {} B ({:.2} KiB)",
        rep12.audited_layer,
        rep12.prove_ms,
        rep12.verify_ms,
        rep12.bundle.stmt_bytes.len(),
        rep12.bundle.receipt_bytes.len(),
        rep12.bundle_bytes.len(),
        rep12.bundle_bytes.len() as f64 / 1024.0
    );

    // 4. Verify `1` thread vs `12` threads bit-for-bit SHA-256 & cSHAKE256 determinism across BOTH prefill AND multi-token decode!
    if !skip_thread_check {
        let pool1 = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .map_err(|e| format!("pool1 error: {e}"))?;
        type SingleThreadDetSummary = ([u8; 32], [u8; 32], [u8; 32], [u8; 32], Vec<u32>);
        let (sha_p1, csh_p1, sha_d1, csh_d1, gen1) =
            pool1.install(|| -> Result<SingleThreadDetSummary, String> {
                let mut c1 = ExactIntDecodeCache::new();
                let (t1, mut h1) =
                    engine.prefill_chunk64_int(&rep12.prompt_token_ids, 0, &mut c1)?;
                let (first1, _, lsha1) = engine.argmax_lm_head_int(&h1)?;
                use sha2::{Digest, Sha256};
                let mut sha = Sha256::new();
                let mut flat = Vec::with_capacity(25 * 64 * 1024 * 4 + 32);
                for b in &t1.boundaries_bb {
                    for &v in b {
                        let le = v.to_le_bytes();
                        sha.update(le);
                        flat.extend_from_slice(&le);
                    }
                }
                sha.update(lsha1);
                flat.extend_from_slice(&lsha1);
                let sp: [u8; 32] = sha.finalize().into();
                let cp = qwen35audit::ext4::cshake256_32(b"QW35-DET-PREFILL-V1", &flat);

                let mut g1 = vec![first1];
                let mut dsha = Sha256::new();
                let mut dflat = Vec::new();
                let mut cur = first1;
                for _ in 1..rep12.generated_token_ids.len() {
                    let (hs, sbnds) = engine.decode_step_int(cur, &mut c1)?;
                    h1 = hs;
                    let (nt, _, slsha) = engine.argmax_lm_head_int(&h1)?;
                    for sb in &sbnds {
                        dsha.update(sb);
                        dflat.extend_from_slice(sb);
                    }
                    dsha.update(slsha);
                    dflat.extend_from_slice(&slsha);
                    g1.push(nt);
                    cur = nt;
                }
                let sd: [u8; 32] = dsha.finalize().into();
                let cd = qwen35audit::ext4::cshake256_32(b"QW35-DET-DECODE-STREAM-V1", &dflat);
                Ok((sp, cp, sd, cd, g1))
            })?;
        assert_eq!(
            sha_p1, rep12.prefill_boundaries_sha256,
            "1T vs 12T prefill SHA-256 mismatch!"
        );
        assert_eq!(
            csh_p1, rep12.prefill_boundaries_cshake256,
            "1T vs 12T prefill cSHAKE256 mismatch!"
        );
        assert_eq!(
            sha_d1, rep12.decode_stream_sha256,
            "1T vs 12T decode SHA-256 mismatch!"
        );
        assert_eq!(
            csh_d1, rep12.decode_stream_cshake256,
            "1T vs 12T decode cSHAKE256 mismatch!"
        );
        assert_eq!(
            gen1, rep12.generated_token_ids,
            "1T vs 12T generated token sequence mismatch!"
        );
        println!(
            "[DETERMINISM 1T == 12T] BIT-IDENTICAL across 25 prefill boundaries + {} decode steps + 248,320 logits!\n  Prefill SHA-256   = {}\n  Prefill cSHAKE256 = {}\n  Decode  SHA-256   = {}\n  Decode  cSHAKE256 = {}",
            rep12.generated_token_ids.len() - 1,
            hex32(&rep12.prefill_boundaries_sha256),
            hex32(&rep12.prefill_boundaries_cshake256),
            hex32(&rep12.decode_stream_sha256),
            hex32(&rep12.decode_stream_cshake256)
        );
    }

    if let Some(dir) = emit_dir {
        fs::create_dir_all(&dir).map_err(|e| format!("create_dir_all failed: {e}"))?;
        let stmt_path = dir.join("vagent01_stmt.bin");
        let rcpt_path = dir.join("vagent01_receipt.bin");
        let bndl_path = dir.join("vagent01_bundle.bin");
        fs::write(&stmt_path, &rep12.bundle.stmt_bytes).map_err(|e| e.to_string())?;
        fs::write(&rcpt_path, &rep12.bundle.receipt_bytes).map_err(|e| e.to_string())?;
        fs::write(&bndl_path, &rep12.bundle_bytes).map_err(|e| e.to_string())?;
        // Re-read & verify BOTH local quarantine bundle AND zero-secret public redacted bundle!
        let disk_bytes = fs::read(&bndl_path).map_err(|e| e.to_string())?;
        let exp_qsb = engine.compute_layer_qs_binding(rep12.audited_layer);
        verify_vagent01_bytes_pinned(&disk_bytes, &engine.registry.weight_root, &exp_qsb)?;
        let pub_red_bytes = rep12.bundle.to_public_redacted_bytes()?;
        assert!(
            !pub_red_bytes.windows(7).any(|w| w == b"sk-proj"),
            "PublicRedactedVAgent01Bundle must contain zero leaked `sk-proj` credential slices!"
        );
        verify_public_redacted_vagent01_bytes(
            &pub_red_bytes,
            Some(&engine.registry.weight_root),
            Some(&exp_qsb),
        )?;
        let pub_path = dir.join("vagent01_public_redacted.bin");
        fs::write(&pub_path, &pub_red_bytes).map_err(|e| e.to_string())?;
        println!(
            "[EMIT] Wrote & re-verified VASTMT01 ({} B), VAGENT01 ({} B), Bundle ({} B), PublicRedacted ({} B, 0 `sk-` leaks) in {}",
            rep12.bundle.stmt_bytes.len(),
            rep12.bundle.receipt_bytes.len(),
            rep12.bundle_bytes.len(),
            pub_red_bytes.len(),
            dir.display()
        );
    }

    Ok(())
}
