//! End-to-End Integration, Thread-Determinism (`1T == 12T`), & Soundness Falsifier Tests for:
//!   1. `Qwen3.8-27B` real cached `MXFP4` `[256, 5120]` `.npz` slice (`8 -> 0` `-0.0` canonicalization + `Ext4` proof),
//!   2. 100%-Integer 24-Layer `Qwen/Qwen3.5-0.8B-Base` Live Multi-Token `CotToolCall` Generation,
//!   3. `VAGENT01` / `VASTMT01` `StreamCodec` Wire Format + `U1` Boundary Weld + 139-Rule LL(1) `miniJsonCfg` AST Extraction.

use qwen35audit::agent_runner::{
    audit_qwen38_27b_mxfp4_npz_slice, build_accepting_sk_dfa_public_table_stride4096,
    compute_u1_turn_head_cshake, compute_u1_vrf_layer_cshake, content_commit_cshake,
    ll1_parse_mini_json, run_live_verifiable_qwen_agent_turn, stream_decode_mini_value,
    stream_decode_nat, stream_encode_nat, verify_agent_turn_weld_bytes,
    verify_public_redacted_vagent01_bytes, verify_vagent01_bytes, verify_vagent01_bytes_pinned,
    ExactIntDecodeCache, ExactIntQwen35Engine, MiniValue, QwenBpeTokenizer,
    VerifiableAgentTurnReceipt, VerifiableAgentTurnStmt, QWEN38_27B_NPZ_PATH, U1_PF_DIGEST_CUST,
};
use qwen35audit::ext4::cshake256_32;
use qwen35audit::safetensors_mmap::QWEN35_TOKENIZER_FILE;
use sha2::{Digest, Sha256};
use std::sync::Arc;

#[test]
fn test_qwen38_27b_npz_neg_zero_canonicalization_and_ext4_proof() {
    let rep = audit_qwen38_27b_mxfp4_npz_slice(QWEN38_27B_NPZ_PATH)
        .expect("load & prove real Qwen3.8-27B [256x5120] MXFP4 .npz slice");
    assert_eq!(rep.rows, 256);
    assert_eq!(rep.cols, 5120);
    assert_eq!(
        rep.raw_neg_zero_nibble_count, 51_851,
        "expected 51,851 non-canonical `-0.0` (nib=8) entries in Qwen3.8-27B mx_u32"
    );
    assert_eq!(rep.canonical_neg_zero_nibble_count, 0);
    assert_ne!(rep.noncanonical_digest, rep.canonical_digest);
    assert!(rep.proof_bytes_len > 100_000);
}

#[test]
fn test_stream_codec_canonical_and_duplicate_key_splice_refused() {
    // Non-canonical `0` spelled `[0, 255]` must be rejected by `stream_decode_nat`!
    let mut pos = 0usize;
    assert!(stream_decode_nat(&[0u8, 255u8], &mut pos).is_err());

    // Canonical `0` (`[255]`) and `255` (`[0, 1, 255]`) must round-trip!
    let mut p0 = 0usize;
    assert_eq!(stream_decode_nat(&[255u8], &mut p0).unwrap(), 0);
    let mut p255 = 0usize;
    assert_eq!(stream_decode_nat(&[0u8, 1u8, 255u8], &mut p255).unwrap(), 255);

    // Duplicate-key JSON splice payload (`ambigSplicePayload` from `VerifiedAstTransducer.lean`) MUST be refused!
    let dup_key_splice =
        br#"{"tool":"read_status","tool":"wipe_prod","target":"db_main","amount":1}"#;
    assert!(
        ll1_parse_mini_json(dup_key_splice).is_err(),
        "139-rule LL(1) miniJsonCfg must refuse duplicate-key JSON splice!"
    );

    // Decimal `2^64 + 10` overflow (`18446744073709551626`) MUST be refused (no mod-2^64 wraparound to `10`!)
    let overflow_amount =
        br#"{"tool":"audit_cfg","target":"db_stage","amount":18446744073709551626}"#;
    assert!(
        ll1_parse_mini_json(overflow_amount).is_err(),
        "MiniOp::NatPos must reject >= 2^64 overflow instead of wrapping mod 2^64!"
    );

    // Deep `BatchCons` (`0x07`) wire bomb and huge `Digits` (`0x02`) count MUST fail cleanly without stack overflow or OOM!
    let mut deep_batch = vec![7u8; 1024];
    deep_batch.push(6u8);
    let mut p_deep = 0usize;
    assert!(stream_decode_mini_value(&deep_batch, &mut p_deep).is_err());

    let mut huge_digits = vec![2u8];
    stream_encode_nat(1_000_000_000, &mut huge_digits);
    let mut p_huge = 0usize;
    assert!(stream_decode_mini_value(&huge_digits, &mut p_huge).is_err());
}

#[test]
fn test_live_integer_qwen35_agent_turn_determinism_and_vagent01_teeth() {
    let pool12 = rayon::ThreadPoolBuilder::new()
        .num_threads(12)
        .build()
        .unwrap();
    let tok = Arc::new(QwenBpeTokenizer::from_file(QWEN35_TOKENIZER_FILE).expect("load BPE"));
    let engine = Arc::new(
        pool12
            .install(ExactIntQwen35Engine::load_default)
            .expect("load 24L integer Qwen3.5"),
    );

    let rep = pool12
        .install(|| run_live_verifiable_qwen_agent_turn(&engine, &tok, 56))
        .expect("run live verifiable Qwen3.5 agent turn");

    let raw_str = String::from_utf8_lossy(&rep.w_raw);
    let clean_str = String::from_utf8_lossy(&rep.w_clean);
    assert!(
        raw_str.contains("sk-proj-"),
        "raw model output must contain inline sk-proj-... credential: {raw_str}"
    );
    assert!(
        clean_str.contains("[REDACTED_API_KEY]") && !clean_str.contains("sk-"),
        "sanitized output must scrub sk-proj-... into [REDACTED_API_KEY]: {clean_str}"
    );
    match &rep.claimed_ast {
        MiniValue::CotToolCall { cot, tool, .. } => {
            assert!(String::from_utf8_lossy(cot).contains("[REDACTED_API_KEY]"));
            assert!(!tool.is_empty());
        }
        other => panic!("expected CotToolCall AST, got {other:?}"),
    }

    // Verify `VASTMT01`, `VAGENT01`, and `VAgent01Bundle` round-trip & standalone verification!
    assert_eq!(
        VerifiableAgentTurnStmt::from_stream_bytes(&rep.bundle.stmt_bytes).unwrap(),
        rep.stmt
    );
    assert_eq!(
        VerifiableAgentTurnReceipt::from_stream_bytes(&rep.bundle.receipt_bytes).unwrap(),
        rep.receipt
    );
    verify_vagent01_bytes(&rep.bundle_bytes).expect("standalone VAgent01Bundle verify");

    // Cross-check shared Lean `#eval` golden conformance vectors on disk + deterministic field identity!
    let vec_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../research/afp_and_unified_wave_2026_11_21/formal_weld/vectors");
    let disk_stmt_bytes = std::fs::read(vec_dir.join("vagent01_stmt.bin"))
        .expect("read formal_weld/vectors/vagent01_stmt.bin");
    let disk_rcpt_bytes = std::fs::read(vec_dir.join("vagent01_receipt.bin"))
        .expect("read formal_weld/vectors/vagent01_receipt.bin");
    verify_agent_turn_weld_bytes(&disk_stmt_bytes, &disk_rcpt_bytes)
        .expect("Rust verify_agent_turn_weld_bytes must accept shared Lean golden VAGENT01 vector");
    let disk_stmt = VerifiableAgentTurnStmt::from_stream_bytes(&disk_stmt_bytes).unwrap();
    let disk_rcpt = VerifiableAgentTurnReceipt::from_stream_bytes(&disk_rcpt_bytes).unwrap();
    assert_eq!(rep.stmt.weight_root, disk_stmt.weight_root);
    assert_eq!(rep.stmt.prompt_length, disk_stmt.prompt_length);
    assert_eq!(rep.stmt.prompt_root, disk_stmt.prompt_root);
    assert_eq!(rep.stmt.num_layers, disk_stmt.num_layers);
    assert_eq!(rep.stmt.raw_length, disk_stmt.raw_length);
    assert_eq!(rep.stmt.raw_root, disk_stmt.raw_root);
    assert_eq!(rep.stmt.clean_length, disk_stmt.clean_length);
    assert_eq!(rep.stmt.clean_root, disk_stmt.clean_root);
    assert_eq!(rep.stmt.claimed_ast, disk_stmt.claimed_ast);
    assert_eq!(rep.receipt.prompt_bytes, disk_rcpt.prompt_bytes);
    assert_eq!(rep.receipt.w_raw, disk_rcpt.w_raw);
    assert_eq!(rep.receipt.w_clean, disk_rcpt.w_clean);
    assert_eq!(rep.receipt.rule_indices, disk_rcpt.rule_indices);
    // ZK PCS boundary roots & proof digest use fresh zero-knowledge randomness on each prove!
    assert_ne!(rep.receipt.u1_proof_digest, disk_rcpt.u1_proof_digest);

    // Verify `1` thread vs `12` threads bit-identical SHA-256 & cSHAKE256 across prefill + multi-token decode!
    let pool1 = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    let (sp1, cp1, sd1, cd1, gen1) = pool1.install(|| {
        let mut c1 = ExactIntDecodeCache::new();
        let (t1, mut h1) = engine
            .prefill_chunk64_int(&rep.prompt_token_ids, 0, &mut c1)
            .unwrap();
        let (first1, _, lsha1) = engine.argmax_lm_head_int(&h1).unwrap();
        let mut sha = Sha256::new();
        let mut flat = Vec::new();
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
        let cp = cshake256_32(b"QW35-DET-PREFILL-V1", &flat);

        let mut g1 = vec![first1];
        let mut dsha = Sha256::new();
        let mut dflat = Vec::new();
        let mut cur = first1;
        for _ in 1..rep.generated_token_ids.len() {
            let (hs, sbnds) = engine.decode_step_int(cur, &mut c1).unwrap();
            h1 = hs;
            let (nt, _, slsha) = engine.argmax_lm_head_int(&h1).unwrap();
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
        let cd = cshake256_32(b"QW35-DET-DECODE-STREAM-V1", &dflat);
        (sp, cp, sd, cd, g1)
    });
    assert_eq!(sp1, rep.prefill_boundaries_sha256);
    assert_eq!(cp1, rep.prefill_boundaries_cshake256);
    assert_eq!(sd1, rep.decode_stream_sha256);
    assert_eq!(cd1, rep.decode_stream_cshake256);
    assert_eq!(gen1, rep.generated_token_ids);

    // --- Planted Attack 1: `TK` Prompt Mismatch (`prompt_bytes` mutated) ---
    let mut bad_r1 = rep.receipt.clone();
    bad_r1.prompt_bytes[0] ^= 0x01;
    assert!(verify_agent_turn_weld_bytes(&rep.bundle.stmt_bytes, &bad_r1.to_stream_bytes()).is_err());

    // --- Planted Attack 2: `TK` Boundary Chain Splice (`boundary_roots[3]` mutated) ---
    let mut bad_r2 = rep.receipt.clone();
    bad_r2.boundary_roots[3][0] ^= 0xFF;
    assert!(verify_agent_turn_weld_bytes(&rep.bundle.stmt_bytes, &bad_r2.to_stream_bytes()).is_err());

    // --- Planted Attack 3: Unredacted `sk-proj-...` CoT Splice (`w_clean = w_raw`, VRF-aligned) ---
    let mut bad_s3 = rep.stmt.clone();
    let mut bad_r3 = rep.receipt.clone();
    bad_s3.clean_length = rep.w_raw.len();
    bad_s3.clean_root = content_commit_cshake(&rep.w_raw);
    bad_r3.w_clean = rep.w_raw.clone();
    bad_r3.audited_layer = compute_u1_vrf_layer_cshake(
        &bad_s3.weight_root,
        &bad_r3.boundary_roots,
        &bad_s3.clean_root,
        bad_s3.num_layers,
    );
    bad_r3.audited_b_in_root = bad_r3.boundary_roots[bad_r3.audited_layer];
    bad_r3.audited_b_out_root = bad_r3.boundary_roots[bad_r3.audited_layer + 1];
    assert!(
        verify_agent_turn_weld_bytes(&bad_s3.to_stream_bytes(), &bad_r3.to_stream_bytes()).is_err()
    );

    // --- Planted Attack 4: Trailing Byte Appended to `VAGENT01` Receipt ---
    let mut trailing = rep.bundle.receipt_bytes.clone();
    trailing.push(0x00);
    assert!(verify_agent_turn_weld_bytes(&rep.bundle.stmt_bytes, &trailing).is_err());

    // --- Planted Attack 5: Tampering with `QW35U1P1` Succinct ZK Proof (with recomputed digest & chain root!) ---
    let mut bad_bndl = rep.bundle.clone();
    bad_bndl.u1_zk_audit_bytes[24] ^= 0x55;
    let mut bad_r5 = rep.receipt.clone();
    let mut bad_s5 = rep.stmt.clone();
    bad_r5.u1_proof_digest = cshake256_32(U1_PF_DIGEST_CUST, &bad_bndl.u1_zk_audit_bytes);
    bad_s5.turn_chain_root = compute_u1_turn_head_cshake(
        &bad_s5.weight_root,
        &bad_s5.prompt_root,
        bad_s5.prompt_length,
        &bad_r5.boundary_roots,
        &bad_r5.u1_proof_digest,
        bad_s5.raw_length,
        &bad_s5.raw_root,
    );
    bad_bndl.stmt_bytes = bad_s5.to_stream_bytes();
    bad_bndl.receipt_bytes = bad_r5.to_stream_bytes();
    assert!(verify_vagent01_bytes(&bad_bndl.to_bytes()).is_err());

    // --- Planted Attack 6: `num_layers = 1` (`2` boundary roots) Downgrade Refused by `verify_vagent01_bytes` ---
    let mut bad_s6 = rep.stmt.clone();
    let mut bad_r6 = rep.receipt.clone();
    bad_s6.num_layers = 1;
    bad_r6.boundary_roots.truncate(2);
    bad_r6.audited_layer = 0;
    bad_r6.audited_b_in_root = bad_r6.boundary_roots[0];
    bad_r6.audited_b_out_root = bad_r6.boundary_roots[1];
    bad_s6.turn_chain_root = compute_u1_turn_head_cshake(
        &bad_s6.weight_root,
        &bad_s6.prompt_root,
        bad_s6.prompt_length,
        &bad_r6.boundary_roots,
        &bad_r6.u1_proof_digest,
        bad_s6.raw_length,
        &bad_s6.raw_root,
    );
    let mut bad_bndl6 = rep.bundle.clone();
    bad_bndl6.stmt_bytes = bad_s6.to_stream_bytes();
    bad_bndl6.receipt_bytes = bad_r6.to_stream_bytes();
    assert!(verify_vagent01_bytes(&bad_bndl6.to_bytes()).is_err());

    // --- Planted Attack 7 (#112 2a): Third-Party Re-Pointing Forgery (`wipe_prod` 95B w/ VRF Grinding) ---
    // Attacker without weights intercepts an honest `VAgent01Bundle`, keeps `u1_zk_audit_bytes` unchanged,
    // replaces `(w_raw, w_clean, claimed_ast)` with a malicious 95-byte `"wipe_prod"` JSON (`q_end == 0`),
    // grinds `boundary_roots[0]` / `prompt_bytes` until `compute_u1_vrf_layer_cshake` hits `rep.receipt.audited_layer`,
    // and recomputes `turn_chain_root`! Must be 100% REFUSED by BOTH 248-bit `w_clean` MLE binding AND statement-bound transcript!
    let evil_raw =
        br#"{"cot":"Evil [REDACTED_API_KEY] wipe_prod!","tool":"wipe_prod","target":"db_stage","amount":99}"#
            .to_vec();
    assert_eq!(evil_raw.len(), 95);
    let (evil_rules, evil_ast) = ll1_parse_mini_json(&evil_raw).expect("parse evil 95B JSON");
    let evil_clean_root = content_commit_cshake(&evil_raw);
    // Case 7a: Same `w_clean` kept, ONLY `prompt_bytes` replaced (`prompt` re-pointing with zero VRF change!)
    let mut bad_s7a = rep.stmt.clone();
    let mut bad_r7a = rep.receipt.clone();
    bad_r7a.prompt_bytes = b"FORGED PROMPT WITHOUT MODEL EXECUTION!".to_vec();
    bad_s7a.prompt_length = bad_r7a.prompt_bytes.len();
    bad_s7a.prompt_root = content_commit_cshake(&bad_r7a.prompt_bytes);
    bad_s7a.turn_chain_root = compute_u1_turn_head_cshake(
        &bad_s7a.weight_root,
        &bad_s7a.prompt_root,
        bad_s7a.prompt_length,
        &bad_r7a.boundary_roots,
        &bad_r7a.u1_proof_digest,
        bad_s7a.raw_length,
        &bad_s7a.raw_root,
    );
    verify_agent_turn_weld_bytes(&bad_s7a.to_stream_bytes(), &bad_r7a.to_stream_bytes())
        .expect("standalone weld only checks self-consistent chain; U1 bundle must reject!");
    let mut bad_bndl7a = rep.bundle.clone();
    bad_bndl7a.stmt_bytes = bad_s7a.to_stream_bytes();
    bad_bndl7a.receipt_bytes = bad_r7a.to_stream_bytes();
    assert!(
        verify_vagent01_bytes(&bad_bndl7a.to_bytes()).is_err(),
        "statement-bound QW35U1P2 transcript must reject prompt re-pointing forgery!"
    );

    // Case 7b: Full `w_clean` swap (`wipe_prod`) grinding non-audited `boundary_roots[24]` until VRF hits `audited_layer`!
    let mut bad_r7b = rep.receipt.clone();
    let mut bad_s7b = rep.stmt.clone();
    bad_r7b.w_raw = evil_raw.clone();
    bad_r7b.w_clean = evil_raw.clone();
    bad_r7b.rule_indices = evil_rules;
    bad_s7b.raw_length = 95;
    bad_s7b.raw_root = evil_clean_root;
    bad_s7b.clean_length = 95;
    bad_s7b.clean_root = evil_clean_root;
    bad_s7b.claimed_ast = evil_ast;
    for nonce in 0u64..10_000 {
        bad_r7b.boundary_roots[24][0..8].copy_from_slice(&nonce.to_le_bytes());
        if compute_u1_vrf_layer_cshake(
            &bad_s7b.weight_root,
            &bad_r7b.boundary_roots,
            &bad_s7b.clean_root,
            24,
        ) == rep.receipt.audited_layer
        {
            break;
        }
    }
    assert_eq!(
        compute_u1_vrf_layer_cshake(
            &bad_s7b.weight_root,
            &bad_r7b.boundary_roots,
            &bad_s7b.clean_root,
            24,
        ),
        rep.receipt.audited_layer
    );
    bad_s7b.turn_chain_root = compute_u1_turn_head_cshake(
        &bad_s7b.weight_root,
        &bad_s7b.prompt_root,
        bad_s7b.prompt_length,
        &bad_r7b.boundary_roots,
        &bad_r7b.u1_proof_digest,
        bad_s7b.raw_length,
        &bad_s7b.raw_root,
    );
    let mut bad_bndl7b = rep.bundle.clone();
    bad_bndl7b.stmt_bytes = bad_s7b.to_stream_bytes();
    bad_bndl7b.receipt_bytes = bad_r7b.to_stream_bytes();
    assert!(
        verify_vagent01_bytes(&bad_bndl7b.to_bytes()).is_err(),
        "248-bit w_clean MLE check + statement-bound transcript must reject VRF-ground wipe_prod re-pointing!"
    );

    // --- Planted Attack 8 (#117 B.1 & B.3): Stride-4096 DFA Table Injectivity & Pinned Weight/QS Rejection ---
    let tab4096 = build_accepting_sk_dfa_public_table_stride4096();
    // Verify `(q=0, b=256, q_next=0) == 2048` and `(q=0, b=0, q_next=1) == 4096` do NOT collide!
    assert!(tab4096.contains(&2048));
    assert!(!tab4096.contains(&(0 + 8 * 0 + 4096 * 1))); // `'s'` is `115`, `b=0` goes `0 -> 0` (`tuple = 0`), never `2048`!
    let mut unique_check = tab4096.clone();
    unique_check.sort_unstable();
    unique_check.dedup();
    // 1,283 distinct valid transitions (`4*256 - 3*64 + 4` = `836`... wait: `3*256 + (256 - 64) + 4 = 964` distinct + `0` filler)
    assert_eq!(unique_check.len(), 3 * 256 + (256 - 64) + 4);

    let honest_qsb = engine.compute_layer_qs_binding(rep.audited_layer);
    verify_vagent01_bytes_pinned(&rep.bundle_bytes, &engine.registry.weight_root, &honest_qsb)
        .expect("pinned verify must accept honest (weight_root, qs_binding)");
    let mut wrong_wr = engine.registry.weight_root;
    wrong_wr[0] ^= 0x01;
    assert!(verify_vagent01_bytes_pinned(&rep.bundle_bytes, &wrong_wr, &honest_qsb).is_err());
    let mut wrong_qsb = honest_qsb;
    wrong_qsb[0] ^= 0x01;
    assert!(
        verify_vagent01_bytes_pinned(&rep.bundle_bytes, &engine.registry.weight_root, &wrong_qsb)
            .is_err()
    );

    // --- External Zero-Secret `PublicRedactedVAgent01Bundle` Audit (`0` leaked `>= 6B` secret slices!) ---
    let pub_red_bytes = rep
        .bundle
        .to_public_redacted_bytes()
        .expect("build PublicRedactedVAgent01Bundle");
    for secret in [&b"sk-proj-demo01"[..], &b"sk-proj-9f8a7b6c5d4e"[..]] {
        for win6 in secret.windows(6) {
            assert!(
                !pub_red_bytes.windows(6).any(|w| w == win6),
                "external PublicRedactedVAgent01Bundle leaked >=6B secret slice {:?}!",
                String::from_utf8_lossy(win6)
            );
        }
    }
    let pub_stmt = verify_public_redacted_vagent01_bytes(
        &pub_red_bytes,
        Some(&engine.registry.weight_root),
        Some(&honest_qsb),
    )
    .expect("verify external PublicRedactedVAgent01Bundle");
    assert_eq!(pub_stmt, rep.stmt);
}
