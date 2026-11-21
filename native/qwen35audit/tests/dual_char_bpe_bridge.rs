//! Integration, scale benchmark (`K = 64, 256, 512` Qwen tokens -> `~250..2,048` raw bytes),
//! real `Qwen` `248,320`-vocab BPE split-token secret-smuggling suite, and 5-attack fail-closed
//! soundness tests for `qwen35audit::bpe_bridge`.

use qwen35audit::bpe_bridge::{
    commit_t256_pcs, eval_bytes_ext4, eval_bytes_t256, make_packed_ext4_pcs_claim, open_t256_pcs,
    pack_ext4_col_to_bb, prove_dual_char_bpe_bridge, prove_dual_char_bpe_bridge_with_explicit_bytes,
    redact_default_secret_classes, verify_dual_char_bpe_bridge,
    verify_dual_char_bpe_bridge_with_salts, verify_t256_pcs, warm_t256_pcs_basis,
    DualCharBridgeProof, QwenBpeRom, Tower256, Tower256MleClaim, PAD_TOK_ID, QWEN_DEFINED_TOKENS,
    QWEN_VOCAB_SIZE, ROM_PADDED_SIZE,
};
use qwen35audit::ext4::{CShakeTranscript, Ext4};
use qwen35audit::pcs_ext4::{commit_table_pcs, open_pcs_claims, PcsParams};
use qwen35audit::u1_audit::{
    prove_padded_absence_zk, redact_sk_secrets, run_padded_complement_sk_dfa,
    verify_padded_absence_zk,
};
use std::collections::HashSet;
use std::time::Instant;

#[test]
fn real_qwen_248320_rom_and_dual_char_bpe_bridge_scale_and_soundness() {
    // =========================================================================
    // 1. Tower256 fast L1-table vs bit-recursive reference & Frobenius sanity
    // =========================================================================
    let a = Tower256([
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
        0x0f0f_f0f0_55aa_aa55,
        0x8000_0000_0000_0001,
    ]);
    let b = Tower256([
        0xdead_beef_cafe_babe,
        0x1122_3344_5566_7788,
        0xaaaa_5555_ffff_0000,
        0x0102_0304_0506_0708,
    ]);
    assert_eq!(a.mul(b), a.mul_ref_recursive(b));
    assert_eq!(a.mul(a.inverse().unwrap()), Tower256::ONE);
    assert_eq!(a.inv_pow256().pow256(), a);
    for byte_val in 0..=255u8 {
        let emb = Tower256::from_byte_gf256(byte_val);
        assert_eq!(emb.pow256(), emb, "GF(2^8) element must satisfy x^256 == x");
    }
    assert_ne!(
        Tower256([256, 0, 0, 0]).pow256(),
        Tower256([256, 0, 0, 0]),
        "y_3 outside GF(2^8) must fail x^256 == x"
    );

    // =========================================================================
    // 2. Load & cSHAKE256-Merkle-commit real 248,320-entry Qwen tokenizer.json
    // =========================================================================
    let t_rom = Instant::now();
    let rom = QwenBpeRom::load_default().expect("load real Qwen3.5 248,320-vocab tokenizer.json");
    let rom_ms = t_rom.elapsed().as_secs_f64() * 1000.0;

    assert_eq!(rom.vocab_size, QWEN_VOCAB_SIZE);
    assert_eq!(rom.bpe_vocab_count, 248_044);
    assert_eq!(rom.added_tokens_count, 22);
    assert_eq!(rom.defined_count, QWEN_DEFINED_TOKENS);
    assert_eq!(rom.entries.len(), ROM_PADDED_SIZE);
    assert_eq!(rom.max_token_byte_len, 128);

    // Empirical Qwen BPE census: verify NO single token in Qwen's entire 248,066 defined tokens contains `b"sk-"`!
    let mut sk_dash_tokens = 0usize;
    for tid in 0..QWEN_DEFINED_TOKENS as u32 {
        let bs = rom.token_bytes(tid).unwrap();
        if bs.windows(3).any(|w| w == b"sk-") {
            sk_dash_tokens += 1;
        }
    }
    assert_eq!(
        sk_dash_tokens, 0,
        "empirical Qwen3.5 finding: 0/248,066 tokens contain b\"sk-\""
    );

    println!(
        "[QwenBpeRom] Loaded & cSHAKE256-Merkle-committed {}/{} Qwen tokens (padded to {}) in {:.2} ms | root = {:02x?}",
        rom.defined_count,
        rom.vocab_size,
        ROM_PADDED_SIZE,
        rom_ms,
        &rom.rom_merkle_root[..8]
    );

    // =========================================================================
    // 3. Scale Benchmarks: K = 64, 256, 512 Qwen Tokens (~260 .. ~2,050 raw UTF-8 bytes)
    // =========================================================================
    let t_basis = Instant::now();
    warm_t256_pcs_basis(&[9, 10, 11], 5);
    let basis_ms = t_basis.elapsed().as_secs_f64() * 1000.0;
    println!("[Tower256Pcs] Parallel Lagrange-to-coset basis warmup (m=9..11, t_cols=208): {:.2} ms", basis_ms);

    let base_clean_turn = concat!(
        "{\"tool\":\"query_cluster_telemetry\",\"arguments\":{\"region\":\"us-east-1\",\"service\":\"verification_gateway\",",
        "\"statement\":\"SELECT hostname, request_latency_microseconds, throughput_bytes FROM production_metrics ",
        "WHERE response_status = 200 ORDER BY request_latency_microseconds DESC LIMIT 32\",",
        "\"description\":\"Deterministic algebraic rolling polynomial evaluation across variable-length BPE tokens.\"}}\n"
    );
    let repeated_text = base_clean_turn.repeat(12);
    let all_clean_toks = rom.encode_qwen_bpe(repeated_text.as_bytes());
    assert!(
        all_clean_toks.len() >= 512,
        "expected >= 512 Qwen BPE tokens, got {}",
        all_clean_toks.len()
    );
    assert_eq!(
        rom.detokenize(&all_clean_toks).unwrap(),
        repeated_text.as_bytes()
    );

    for &k in &[64usize, 256usize, 512usize] {
        let slice_toks = &all_clean_toks[..k];
        let expected_bytes = rom.detokenize(slice_toks).unwrap();

        let t_p = Instant::now();
        let (proof, out_bytes) =
            prove_dual_char_bpe_bridge(&rom, slice_toks, None).expect("honest dual-char prove");
        let prove_ms = t_p.elapsed().as_secs_f64() * 1000.0;
        assert_eq!(out_bytes, expected_bytes);

        let wire = proof.to_bytes();
        let decoded = DualCharBridgeProof::from_bytes(&wire).expect("wire round-trip");
        assert_eq!(decoded, proof);

        let t_v = Instant::now();
        verify_dual_char_bpe_bridge(&rom, Some(&expected_bytes), &decoded)
            .expect("standalone dual-char verify (with byte weld)");
        let verify_ms = t_v.elapsed().as_secs_f64() * 1000.0;

        // Also verify standalone zero-cleartext mode (`None`) AND compose with ZK `Absent("sk-...")` DFA!
        verify_dual_char_bpe_bridge(&rom, None, &decoded)
            .expect("standalone dual-char verify (zero-cleartext mode)");

        if k == 64 {
            let mut abs_tr = CShakeTranscript::new(b"QW35-BPE-ABSENT-WELD-TEST");
            let abs_receipt =
                prove_padded_absence_zk(&expected_bytes, &mut abs_tr).expect("clean bytes pass Absent");
            let mut ver_tr = CShakeTranscript::new(b"QW35-BPE-ABSENT-WELD-TEST");
            verify_padded_absence_zk(&abs_receipt.content_root, None, &abs_receipt, &mut ver_tr)
                .expect("zero-cleartext ZK Absent receipt verified");
        }

        println!(
            "[Scale K={:3}] raw_bytes={:4} B | prove={:7.2} ms ({:6.2} us/tok) | verify={:6.2} ms | proof={:7.2} KiB",
            k,
            expected_bytes.len(),
            prove_ms,
            (prove_ms * 1000.0) / (k as f64),
            verify_ms,
            (wire.len() as f64) / 1024.0
        );
    }

    // =========================================================================
    // 4. Real Qwen BPE Split-Token Secret Smuggling Demonstration (`K >= 64`)
    // =========================================================================
    let secret_span = b"sk-proj-9f8a7b6c5d4e";
    let secret_splits = rom.enumerate_valid_splits(secret_span, 8);
    assert!(
        secret_splits.len() >= 4,
        "expected >= 4 distinct Qwen BPE splits for sk-proj-..."
    );

    // Also include explicit adversarial splits bypassing banned token IDs `4729 ("sk")` and `25555 ("Bearer")`:
    let tok_s = rom.lookup_bpe_id(b"s").unwrap(); // 82
    let tok_k = rom.lookup_bpe_id(b"k").unwrap(); // 74
    let tok_sk = rom.lookup_bpe_id(b"sk").unwrap(); // 4729
    let tok_dash = rom.lookup_bpe_id(b"-").unwrap(); // 12
    let tok_dash_pro = rom.lookup_bpe_id(b"-pro").unwrap(); // 9546
    let tok_j = rom.lookup_bpe_id(b"j").unwrap(); // 73
    let tok_proj = rom.lookup_bpe_id(b"proj").unwrap(); // 29397
    let tok_bearer_full = rom.lookup_bpe_id(b"Bearer").unwrap(); // 25555
    let tok_bear = rom.lookup_bpe_id(b"Bear").unwrap(); // 85536
    let tok_er = rom.lookup_bpe_id(b"er").unwrap(); // 261
    assert_eq!(
        (tok_s, tok_k, tok_sk, tok_dash_pro, tok_proj, tok_bearer_full, tok_bear, tok_er),
        (82, 74, 4729, 9546, 29397, 25555, 85536, 261)
    );

    let prefix_toks = rom.encode_qwen_bpe(
        b"{\"status\":\"ok\",\"trace\":\"checking deployment env; auth=",
    );
    let suffix_toks = rom.encode_qwen_bpe(
        b"\",\"region\":\"eu-central-1\",\"retries\":0,\"healthy\":true,\"latency_ms\":14}\n",
    );
    let key_tail_toks = rom.encode_qwen_bpe(b"-9f8a7b6c5d4e; hdr=");

    // Build 4 distinct >=64-token Qwen sequences that ALL detokenize to the EXACT same dirty UTF-8 byte string!
    let build_smuggled_turn = |sk_part: &[u32], bearer_part: &[u32]| -> Vec<u32> {
        let mut ts = prefix_toks.clone();
        ts.extend_from_slice(sk_part);
        ts.extend_from_slice(&key_tail_toks);
        ts.extend_from_slice(bearer_part);
        ts.extend_from_slice(&rom.encode_qwen_bpe(b" eyJhbGciOiJFZERTQSJ9.payload"));
        ts.extend_from_slice(&suffix_toks);
        ts
    };

    let canonical_turn = build_smuggled_turn(&[tok_sk, tok_dash_pro, tok_j], &[tok_bearer_full]);
    let split_turn_1 = build_smuggled_turn(&[tok_s, tok_k, tok_dash_pro, tok_j], &[tok_bear, tok_er]);
    let split_turn_2 = build_smuggled_turn(&[tok_s, tok_k, tok_dash, tok_proj], &[tok_bear, tok_er]);
    let mut char_sk_proj = Vec::new();
    for &b in b"sk-proj" {
        char_sk_proj.push(rom.lookup_bpe_id(&[b]).unwrap());
    }
    let split_turn_3 = build_smuggled_turn(&char_sk_proj, &[tok_bear, tok_er]);

    let banned_token_ids: HashSet<u32> = [tok_sk, tok_bearer_full].into_iter().collect();
    let expected_dirty_bytes = rom.detokenize(&canonical_turn).unwrap();
    assert!(canonical_turn.len() >= 64 && split_turn_1.len() >= 64);

    for (idx, split_ts) in [&split_turn_1, &split_turn_2, &split_turn_3].iter().enumerate() {
        assert_ne!(*split_ts, &canonical_turn);
        // 1. Naive token-ID ban (`4729 "sk"`, `25555 "Bearer"`) AND per-token `Absent("sk-")` BOTH PASS!
        assert!(
            split_ts.iter().all(|t| !banned_token_ids.contains(t)),
            "split #{idx} bypasses token-ID blocklist completely"
        );
        assert!(
            split_ts
                .iter()
                .all(|&t| !rom.token_bytes(t).unwrap().windows(3).any(|w| w == b"sk-")),
            "no individual token in split #{idx} contains b\"sk-\""
        );

        // 2. DualCharTokenBridge maps EVERY non-canonical split to the EXACT SAME `expected_dirty_bytes`!
        let (pf_split, detok_split) =
            prove_dual_char_bpe_bridge(&rom, split_ts, None).expect("prove split tokenization");
        assert_eq!(detok_split, expected_dirty_bytes);
        verify_dual_char_bpe_bridge(&rom, Some(&expected_dirty_bytes), &pf_split)
            .expect("DualCharTokenBridge welds split tokenization to identical raw_bytes");

        // 3. Byte-level `Absent("sk-...")` DFA & `redact_default_secret_classes` catch it 100% of the time!
        let (dfa_final, _) = run_padded_complement_sk_dfa(&detok_split);
        assert_eq!(dfa_final, 4, "byte-level DFA enters sink state 4 on split #{idx}");
        let mut abs_tr = CShakeTranscript::new(b"SPLIT-REJECT");
        assert!(
            prove_padded_absence_zk(&detok_split, &mut abs_tr).is_err(),
            "ZK Absent prover refuses unredacted split #{idx}"
        );
        let (redacted, red_hits) = redact_default_secret_classes(&detok_split);
        assert_eq!(red_hits, 2, "scrubbed both sk-proj-... and Bearer ... on split #{idx}");
        assert!(!redacted.windows(3).any(|w| w == b"sk-"));
        assert!(!redacted.windows(7).any(|w| w == b"Bearer "));
        let (sk_redacted, sk_hits) = redact_sk_secrets(&detok_split);
        assert_eq!(sk_hits, 1);
        let mut clean_tr = CShakeTranscript::new(b"POST-REDACT-OK");
        let clean_rcpt =
            prove_padded_absence_zk(&sk_redacted, &mut clean_tr).expect("redacted bytes pass Absent");
        let mut clean_vtr = CShakeTranscript::new(b"POST-REDACT-OK");
        verify_padded_absence_zk(&clean_rcpt.content_root, None, &clean_rcpt, &mut clean_vtr)
            .expect("post-redaction ZK Absent receipt verifies");
    }
    println!(
        "[Smuggling Suite] Verified 4 distinct Qwen BPE tokenizations ({}..{} tokens) -> identical {} B stream; 100% caught & scrubbed!",
        canonical_turn.len(),
        split_turn_3.len(),
        expected_dirty_bytes.len()
    );

    // =========================================================================
    // 5. Five Planted Adversarial Soundness Attacks (All 5 Deterministically Rejected!)
    // =========================================================================
    let base_toks = all_clean_toks[..64].to_vec();
    let base_bytes = rom.detokenize(&base_toks).unwrap();
    let (honest_proof, _) =
        prove_dual_char_bpe_bridge(&rom, &base_toks, None).expect("baseline honest 64-tok proof");
    verify_dual_char_bpe_bridge(&rom, Some(&base_bytes), &honest_proof)
        .expect("baseline honest proof verifies");

    // --- Attack (1): 1-token swap in `BabyBear` vs `Tower256` bytes (equal byte length!) ---
    let mut swapped_toks = base_toks.clone();
    // Replace token at index 5 with a DIFFERENT Qwen token of the EXACT SAME byte length!
    let orig_t5 = swapped_toks[5];
    let orig_len5 = rom.token_bytes(orig_t5).unwrap().len();
    let replacement_tok = (0..QWEN_DEFINED_TOKENS as u32)
        .find(|&cand| cand != orig_t5 && rom.token_bytes(cand).unwrap().len() == orig_len5)
        .expect("equal-length replacement token exists");
    swapped_toks[5] = replacement_tok;

    // (1a) Prover commits `swapped_toks` in BabyBear while committing `base_bytes` in byte columns:
    let (atk1a_proof, _) =
        prove_dual_char_bpe_bridge_with_explicit_bytes(&rom, &swapped_toks, &base_bytes, None)
            .expect("construct mismatched BabyBear-tokens vs bytes proof");
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&base_bytes), &atk1a_proof).is_err(),
        "Attack 1a (1-token swap vs Tower256/byte commitment) MUST be rejected!"
    );
    assert!(
        verify_dual_char_bpe_bridge(&rom, None, &atk1a_proof).is_err(),
        "Attack 1a MUST ALSO be rejected in zero-cleartext mode (None)!"
    );
    // (1b) Prover runs honestly on `swapped_toks` and tries to verify against `base_bytes`:
    let (atk1b_proof, _) = prove_dual_char_bpe_bridge(&rom, &swapped_toks, None).unwrap();
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&base_bytes), &atk1b_proof).is_err(),
        "Attack 1b (honest swapped token proof verified against original Tower256 bytes) MUST be rejected!"
    );

    // --- Attack (2): Forged `len_i` / `pow_i` ROM tuple ---
    let mut atk2_proof = honest_proof.clone();
    atk2_proof.pow_at_rom_leaf = atk2_proof.pow_at_rom_leaf.add(Ext4::ONE);
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&base_bytes), &atk2_proof).is_err(),
        "Attack 2a (forged pow_i ROM leaf opening) MUST be rejected!"
    );
    let mut atk2b_proof = honest_proof.clone();
    atk2b_proof.len_at_rom_leaf = atk2b_proof.len_at_rom_leaf.add(Ext4::ONE);
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&base_bytes), &atk2b_proof).is_err(),
        "Attack 2b (forged len_i ROM leaf opening) MUST be rejected!"
    );

    // --- Attack (3): Leading-`\0` length-mismatch alias (`[0x00] ++ bytes` vs `bytes`) ---
    // Qwen token `188` (`'Ā'`) decodes to `[0x00]`! Verify algebraically that `[0x00] ++ base_bytes`
    // collides on `evalBytes` in BOTH `Ext4` AND `Tower256` at EVERY base, yet our bridge rejects!
    let tok_null_byte = rom.lookup_bpe_id(&[0x00]).expect("Qwen ByteLevel null byte token 188");
    assert_eq!(tok_null_byte, 188);
    let mut leading_zero_toks = vec![tok_null_byte];
    leading_zero_toks.extend_from_slice(&base_toks[..61]); // 62 tokens <= 64 pad_len
    let clean_tail_bytes = rom.detokenize(&base_toks[..61]).unwrap();
    let null_prefixed_bytes = rom.detokenize(&leading_zero_toks).unwrap();
    assert_eq!(null_prefixed_bytes.len(), clean_tail_bytes.len() + 1);
    assert_eq!(
        eval_bytes_ext4(rom.rom_base_ext4, &null_prefixed_bytes),
        eval_bytes_ext4(rom.rom_base_ext4, &clean_tail_bytes),
        "Falsifier Tooth: leading 0x00 aliases eval_bytes_ext4!"
    );
    assert_eq!(
        eval_bytes_t256(rom.rom_base_t256, &null_prefixed_bytes),
        eval_bytes_t256(rom.rom_base_t256, &clean_tail_bytes),
        "Falsifier Tooth: leading 0x00 aliases eval_bytes_t256!"
    );

    // (3a) Prover commits `leading_zero_toks` (len = L + 1) against `clean_tail_bytes` (len = L):
    let (atk3a_proof, _) = prove_dual_char_bpe_bridge_with_explicit_bytes(
        &rom,
        &leading_zero_toks,
        &clean_tail_bytes,
        None,
    )
    .unwrap();
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&clean_tail_bytes), &atk3a_proof).is_err(),
        "Attack 3a (leading-\\0 length-mismatch alias, internal cum_len != byte_len) MUST be rejected!"
    );
    assert!(
        verify_dual_char_bpe_bridge(&rom, None, &atk3a_proof).is_err(),
        "Attack 3a MUST ALSO be rejected in zero-cleartext mode via cum_len shift check!"
    );
    // (3b) Prover proves `leading_zero_toks` honestly and presents receipt against `clean_tail_bytes`:
    let (atk3b_proof, _) = prove_dual_char_bpe_bridge(&rom, &leading_zero_toks, None).unwrap();
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&clean_tail_bytes), &atk3b_proof).is_err(),
        "Attack 3b (leading-\\0 receipt verified against unprefixed bytes) MUST be rejected!"
    );

    // --- Attack (4): Forged intermediate rolling `acc_i` (tested on BOTH `Ext4` and `Tower256`!) ---
    let mut atk4a_proof = honest_proof.clone();
    atk4a_proof.acc_next_at_zroll = atk4a_proof.acc_next_at_zroll.add(Ext4::ONE);
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&base_bytes), &atk4a_proof).is_err(),
        "Attack 4a (forged Ext4 intermediate rolling acc_i) MUST be rejected!"
    );
    // Also forge an actual committed `acc` witness cell at intermediate step `i = 17` and re-open PCS honestly!
    {
        let m_tok = honest_proof.stmt.tok_pad_len.trailing_zeros() as usize;
        let mut forged_acc = vec![Ext4::ZERO; honest_proof.stmt.tok_pad_len];
        forged_acc[17] = Ext4::from_bb(999_999);
        let forged_packed = pack_ext4_col_to_bb(&forged_acc);
        let forged_state = commit_table_pcs(&forged_packed, PcsParams::default_zk(3), None);
        let mut atk4_reopen = honest_proof.clone();
        atk4_reopen.acc_ext4_pcs_root = forged_state.root;
        let dummy_pt = vec![Ext4::ONE; m_tok];
        let mut dummy_tr = CShakeTranscript::new(b"DUMMY");
        atk4_reopen.acc_ext4_pcs_proof = open_pcs_claims(
            &forged_state,
            &[
                make_packed_ext4_pcs_claim(&vec![Ext4::ZERO; m_tok], Ext4::ZERO),
                make_packed_ext4_pcs_claim(&dummy_pt, Ext4::ZERO),
                make_packed_ext4_pcs_claim(&dummy_pt, Ext4::ZERO),
            ],
            &mut dummy_tr,
        );
        assert!(
            verify_dual_char_bpe_bridge(&rom, Some(&base_bytes), &atk4_reopen).is_err(),
            "Attack 4b (re-committed forged intermediate acc[17] column) MUST be rejected!"
        );
    }
    // Regression for Neon Audit R6 (`Tower256Pcs` `s_mask` post-hoc claim shift forgery) & R2 (`salted_root` tamper):
    {
        let tab = vec![Tower256::from_byte_gf256(42); 64];
        let st = commit_t256_pcs(&tab, 1, Some([7u8; 32]));
        let pt = vec![Tower256::ONE; 6];
        let mut ptr = CShakeTranscript::new(b"R6-TEST");
        let mut pcs_pf = open_t256_pcs(
            &st,
            &[Tower256MleClaim {
                point: pt.clone(),
                value: Tower256::from_byte_gf256(42),
            }],
            &mut ptr,
        );
        let fake_val = Tower256::from_byte_gf256(99);
        pcs_pf.s_masks[0] = pcs_pf.s_masks[0]
            .add(Tower256::from_byte_gf256(42))
            .add(fake_val);
        let mut vtr = CShakeTranscript::new(b"R6-TEST");
        assert!(
            verify_t256_pcs(
                &st.root,
                &[Tower256MleClaim {
                    point: pt,
                    value: fake_val,
                }],
                &pcs_pf,
                &mut vtr,
            )
            .is_err(),
            "Neon R6 regression: beta_zk MUST reject s_mask shift forgery in Tower256Pcs!"
        );

        let explicit_salts = vec![[0x5Au8; 31]; honest_proof.stmt.byte_pad_len];
        let (salted_pf, _) =
            prove_dual_char_bpe_bridge(&rom, &base_toks, Some(&explicit_salts)).unwrap();
        verify_dual_char_bpe_bridge_with_salts(
            &rom,
            Some(&base_bytes),
            Some(&explicit_salts),
            &salted_pf,
        )
        .expect("honest salted Tower256 root verifies");
        let mut bad_salts = explicit_salts.clone();
        bad_salts[0][0] ^= 1;
        assert!(
            verify_dual_char_bpe_bridge_with_salts(
                &rom,
                Some(&base_bytes),
                Some(&bad_salts),
                &salted_pf,
            )
            .is_err(),
            "Neon R2 regression: tampered Tower256 salt/root MUST be rejected!"
        );
    }
    let mut atk4c_proof = honest_proof.clone();
    atk4c_proof.t256_h_next_at_zstep = atk4c_proof.t256_h_next_at_zstep.add(Tower256::ONE);
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&base_bytes), &atk4c_proof).is_err(),
        "Attack 4c (forged Tower256 intermediate Horner h_j) MUST be rejected!"
    );

    // --- Attack (5): Split-token `"s" + "k" + "-pro" + "j"` bypass attempt against clean/redacted byte policy ---
    let (redacted_dirty_bytes, _) = redact_sk_secrets(&expected_dirty_bytes);
    // (5a) Prover emits unredacted split-token `"s"+"k"+"-pro"+"j"` in BabyBear while claiming redacted bytes in Tower256:
    let (atk5a_proof, _) = prove_dual_char_bpe_bridge_with_explicit_bytes(
        &rom,
        &split_turn_1,
        &redacted_dirty_bytes,
        None,
    )
    .unwrap();
    assert!(
        verify_dual_char_bpe_bridge(&rom, Some(&redacted_dirty_bytes), &atk5a_proof).is_err(),
        "Attack 5a (split-token sk-proj in BabyBear welded to redacted bytes without redactor) MUST be rejected!"
    );
    assert!(
        verify_dual_char_bpe_bridge(&rom, None, &atk5a_proof).is_err(),
        "Attack 5a MUST ALSO be rejected in zero-cleartext mode!"
    );
    // (5b) Prover proves `split_turn_1` honestly (with pre-challenge salted opening!) and tries to pass unredacted bytes through `Absent("sk-...")`:
    let (honest_split_pf, split_raw, split_salts) =
        qwen35audit::bpe_bridge::prove_dual_char_bpe_bridge_salted(&rom, &split_turn_1).unwrap();
    qwen35audit::bpe_bridge::verify_dual_char_bpe_bridge_with_salts(
        &rom,
        Some(&split_raw),
        Some(&split_salts),
        &honest_split_pf,
    )
    .unwrap();
    let mut atk5b_tr = CShakeTranscript::new(b"ATK5B");
    assert!(
        prove_padded_absence_zk(&split_raw, &mut atk5b_tr).is_err(),
        "Attack 5b (welded split-token stream fails Absent(\"sk-...\") policy 100%)!"
    );
    // Also ensure undefined Qwen padding token ID `248_100` (`>= 248,066`), `PAD_TOK_ID` inside active stream,
    // and verifier-side `num_tokens` tail-PAD manipulation are all rejected:
    let mut bad_unalloc_toks = base_toks.clone();
    bad_unalloc_toks[2] = 248_100;
    assert!(
        prove_dual_char_bpe_bridge(&rom, &bad_unalloc_toks, None).is_err(),
        "unallocated token ID 248_100 (>= 248,066) MUST be rejected!"
    );
    let mut bad_pad_toks = base_toks.clone();
    bad_pad_toks[3] = PAD_TOK_ID;
    assert!(
        prove_dual_char_bpe_bridge(&rom, &bad_pad_toks, None).is_err(),
        "PAD_TOK_ID inside active token stream MUST be rejected!"
    );
    let mut tampered_k_pf = honest_split_pf.clone();
    tampered_k_pf.stmt.num_tokens += 1; // shifts verifier's public active/PAD boundary `K`!
    assert!(
        verify_dual_char_bpe_bridge(&rom, None, &tampered_k_pf).is_err(),
        "standalone verifier MUST reject tampered active/PAD boundary num_tokens!"
    );

    println!("[Soundness Suite] All 5/5 planted cross-characteristic & BPE smuggling attacks deterministically rejected!");
}
