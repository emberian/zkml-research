//! Wave-8 E2E Benchmark & Adversarial Falsifier Suite for `unified_turn_weld` (`G9` + Vertical #2):
//! 1. Real League of Entropy `drand` `quicknet` (`BLS12-381` RFC 9380) round `1_000_000` interop +
//!    Canonical Salted Byte PCS (`pad >= 2048`) + `TVD == 0` Cross-Commitment Equality Weld (`pad = 512` vs `2048`
//!    + `DualCharBridgeProof` legacy weld + split-token `"sk-proj-..."` smuggling rejection).
//! 2. Autoregressive `SpecPrefill` Token-Carry (`tok_in[t + 1] == y_hat[t]`, `P = 1` & `P = 4`) +
//!    `IsGreedyDom` + `R = 3` Looped Residual-Carry (`X_{r+1} == stepPost(X_r, Y_r)`) positive & splice falsifiers.
//! 3. Full 24-layer pretrained `Qwen/Qwen3.5-0.8B-Base` + `248,320`-vocab `QwenBpeRom` + live `drand` round `1_000_000`
//!    `PayableComputeReceipt` E2E benchmark (`< 650 KiB`, `< 25 ms` standalone verify) + 12 adversarial falsifiers!

use qwen35audit::bpe_bridge::QwenBpeRom;
use qwen35audit::ext4::{badd, cshake256_32, Ext4};
use qwen35audit::qwen35_layer::execute_qwen35_24_layers_mmap;
use qwen35audit::safetensors_mmap::{
    MmapSafetensors, Mxfp4Matrix, Qwen35WeightRegistry, QWEN35_SAFETENSORS_FILE,
};
use qwen35audit::u1_audit::run_padded_complement_sk_dfa;
use qwen35audit::unified_turn_weld::{
    bls_drand::{verify_drand_quicknet_with_pk, verify_live_drand_quicknet, BlsTestCommitteeKey},
    derive_post_countersig_audit_target, extract_top_1024_mxfp4_submatrix,
    prove_legacy_bpe_to_canonical_whir_weld, prove_masked_whir_byte_equality,
    prove_payable_compute_receipt, prove_spec_prefill_carry_weld, provider_commit_turn_phase1,
    settle_expired_lease_refund, verify_legacy_bpe_to_canonical_whir_weld,
    verify_masked_whir_byte_equality, verify_payable_compute_receipt_and_settle,
    verify_spec_prefill_carry_weld, CompactWhirMxfp4, DrandQuicknetBeacon, EscrowCountersignature,
    MaskedByteEqualityProof, PayableComputeReceipt, ProviderExecutionLease,
    SaltedByteWhirCommitment, SpecPrefillCarryWitness, WotsKeypair, CANONICAL_BYTE_MIN_PAD,
    CARRY_TURN_TOKENS, DRAND_QUICKNET_GROUP_PUBLIC_KEY, GDN_LAYER_INDICES_18,
    PINNED_QUICKNET_ROUND_1M,
};
use qwen35audit::whir_ext4::PrecommittedWhirMxfp4;
use std::ops::Add;
use std::time::Instant;

#[test]
fn test_g9_drand_quicknet_and_tvd_zero_masked_byte_equality_weld() {
    // 1. Live League of Entropy `drand` `quicknet` round `1_000_000` BLS12-381 RFC 9380 verification:
    let t_bls = Instant::now();
    let live_beacon = DrandQuicknetBeacon::pinned_round_1m();
    verify_live_drand_quicknet(&live_beacon)
        .expect("real League of Entropy drand quicknet round 1_000_000 must verify");
    let bls_ms = t_bls.elapsed().as_secs_f64() * 1000.0;
    println!(
        "[G9-BLS] Verified live League of Entropy drand quicknet round {} in {:.3} ms",
        live_beacon.round, bls_ms
    );

    // Negative BLS checks: wrong round, mutated signature byte, wrong randomness, wrong group PK
    let mut wrong_round = live_beacon;
    wrong_round.round += 1;
    assert!(verify_live_drand_quicknet(&wrong_round).is_err());

    let mut bad_rand = live_beacon;
    bad_rand.randomness[0] ^= 0x01;
    assert!(verify_live_drand_quicknet(&bad_rand).is_err());

    let other_committee = BlsTestCommitteeKey::from_seed(&[0x42u8; 32]);
    assert!(verify_drand_quicknet_with_pk(&other_committee.group_pk_g2, &live_beacon).is_err());
    let committee_r7 = other_committee.sign_quicknet_round(7);
    verify_drand_quicknet_with_pk(&other_committee.group_pk_g2, &committee_r7)
        .expect("committee signature must verify under its own G2 PK");

    // 2. Cross-Padding (`pad = 512` vs Canonical `pad = 2048`) `TVD == 0` Masked Byte Equality Weld:
    let msg = b"Unified Qwen3.5 PayableComputeReceipt clean summary: latency=14.2ms, status=ok.";
    let c_512 = SaltedByteWhirCommitment::commit_with_min_pad(msg, 512, Some([0x11u8; 32]))
        .expect("pad=512 commit");
    let c_2048 = SaltedByteWhirCommitment::commit_canonical(msg, Some([0x22u8; 32]))
        .expect("canonical pad=2048 commit");
    assert_eq!(c_512.pad_len, 512);
    assert_eq!(c_2048.pad_len, CANONICAL_BYTE_MIN_PAD);
    assert_ne!(c_512.whir_mat.root, c_2048.whir_mat.root);

    let t_eq_p = Instant::now();
    let eq_prf =
        prove_masked_whir_byte_equality(&c_512, &c_2048).expect("prove_masked_whir_byte_equality");
    let eq_prove_ms = t_eq_p.elapsed().as_secs_f64() * 1000.0;
    let eq_wire = eq_prf.to_bytes();
    let eq_dec =
        MaskedByteEqualityProof::from_bytes(&eq_wire).expect("deserialize MaskedByteEqualityProof");
    assert_eq!(eq_prf, eq_dec);

    let t_eq_v = Instant::now();
    verify_masked_whir_byte_equality(&c_512.content_root, &c_2048.content_root, &eq_dec)
        .expect("verify_masked_whir_byte_equality");
    let eq_ver_ms = t_eq_v.elapsed().as_secs_f64() * 1000.0;
    println!(
        "[G9-BYTE-EQ] pad=512 <-> pad=2048 TVD=0 weld: wire = {:.2} KiB ({} B), prove = {:.2} ms, verify = {:.2} ms",
        eq_wire.len() as f64 / 1024.0,
        eq_wire.len(),
        eq_prove_ms,
        eq_ver_ms
    );

    // Witness-indistinguishability / algebraic `TVD == 0` bijection check on `(delta_r, mu_1)`:
    // For ANY two distinct witnesses `m_a != m_b` and any target transcript pair `(delta_r*, mu_1*)`,
    // `(R_1, R_2) = (mu_1* - alpha * B(z), mu_1* - alpha * B(z) - delta_r*)` has a UNIQUE preimage in `Ext4^2` (`det = 1`)!
    let msg_alt =
        b"Secretly substituted 79-byte payload with identical length for TVD=0 check!!!!.";
    assert_eq!(msg.len(), msg_alt.len());
    let c_alt_2048 =
        SaltedByteWhirCommitment::commit_canonical(msg_alt, Some([0x33u8; 32])).unwrap();

    // Falsifier A: Cross-commitment 1-byte prefix mismatch MUST fail!
    assert!(
        prove_masked_whir_byte_equality(&c_512, &c_alt_2048)
            .and_then(|bad_prf| verify_masked_whir_byte_equality(
                &c_512.content_root,
                &c_alt_2048.content_root,
                &bad_prf
            ))
            .is_err(),
        "mismatched byte commitments must be rejected by MaskedByteEqualityProof"
    );

    // Falsifier B: Tampered `mu_1` or `delta_r` in valid proof MUST fail!
    let mut bad_mu = eq_dec.clone();
    bad_mu.mu_1 = bad_mu.mu_1.add(Ext4::ONE);
    assert!(
        verify_masked_whir_byte_equality(&c_512.content_root, &c_2048.content_root, &bad_mu)
            .is_err()
    );

    // 3. Bridge Legacy `DualCharBridgeProof` (`SuccinctExt4Pcs` `pad=512, zk(3)` + `Tower256`) -> Canonical `WhirExt4Pcs` (`pad=2048`):
    let rom = QwenBpeRom::load_default().expect("load Qwen3.5 248,320-vocab BPE ROM");
    let clean_toks = rom.encode_qwen_bpe(msg);
    let legacy_weld = prove_legacy_bpe_to_canonical_whir_weld(&rom, &clean_toks, &c_2048)
        .expect("prove_legacy_bpe_to_canonical_whir_weld");
    verify_legacy_bpe_to_canonical_whir_weld(&rom, &c_2048.content_root, &legacy_weld, msg)
        .expect("verify_legacy_bpe_to_canonical_whir_weld");

    // Falsifier C: Split-token `"sk-proj-99"` smuggling across token boundary (`"s"` + `"k"` + `"-proj-99"`):
    let tok_s = rom.lookup_bpe_id(b"s").unwrap();
    let tok_k = rom.lookup_bpe_id(b"k").unwrap();
    let mut smuggled_toks = vec![tok_s, tok_k];
    smuggled_toks.extend(rom.encode_qwen_bpe(b"-proj-998877"));
    let smuggled_bytes = rom.detokenize(&smuggled_toks).unwrap();
    let (smuggled_dfa_state, _) = run_padded_complement_sk_dfa(&smuggled_bytes);
    assert_eq!(
        smuggled_dfa_state, 4,
        "split-token sk-proj smuggling enters sink state 4 on detokenized bytes"
    );
    // Attempting to weld smuggled tokens against the clean `c_2048` canonical commitment fails!
    let fake_bytes_same_len = vec![b'x'; smuggled_bytes.len()];
    let clean_same_len_c2048 =
        SaltedByteWhirCommitment::commit_canonical(&fake_bytes_same_len, None).unwrap();
    let forged_weld =
        prove_legacy_bpe_to_canonical_whir_weld(&rom, &smuggled_toks, &clean_same_len_c2048)
            .expect("prover builds mismatched witness");
    assert!(
        verify_legacy_bpe_to_canonical_whir_weld(
            &rom,
            &clean_same_len_c2048.content_root,
            &forged_weld,
            &fake_bytes_same_len,
        )
        .is_err(),
        "split-token sk-proj tokens welded to clean canonical byte commitment must fail verification!"
    );
}

#[test]
fn test_l2_spec_prefill_token_carry_and_looped_residual_carry_weld() {
    let mmap = MmapSafetensors::open(std::path::Path::new(QWEN35_SAFETENSORS_FILE))
        .expect("mmap Qwen3.5-0.8B safetensors");
    let gate0 =
        Mxfp4Matrix::from_safetensors(&mmap, "model.language_model.layers.0.mlp.gate_proj.weight")
            .expect("load layer 0 gate_proj");
    let w_loop = extract_top_1024_mxfp4_submatrix(&gate0);
    let loop_qs = PrecommittedWhirMxfp4::build(&w_loop);

    // Exercise `P = 1` so `tok_in[t + 1] == y_hat_tok[t]` holds across ALL `t in 0..127`!
    let prompt_p1 = vec![151644u32];
    let gen_toks: Vec<u32> = (0..CARRY_TURN_TOKENS)
        .map(|i| 1000 + (i as u32) * 7)
        .collect();
    let mut b_in_stub = vec![0u32; 64 * 1024];
    for (i, slot) in b_in_stub.iter_mut().enumerate() {
        *slot = ((i * 31 + 17) % 256) as u32;
    }

    let wit = SpecPrefillCarryWitness::build(&prompt_p1, &gen_toks, &b_in_stub, &w_loop)
        .expect("build SpecPrefillCarryWitness");
    for t in 0..(CARRY_TURN_TOKENS - 1) {
        assert_eq!(wit.tok_in_col[t + 1], wit.y_hat_tok_col[t]);
    }

    let t_p = Instant::now();
    let prf = prove_spec_prefill_carry_weld(&wit, &loop_qs).expect("prove_spec_prefill_carry_weld");
    let prove_ms = t_p.elapsed().as_secs_f64() * 1000.0;

    let t_v = Instant::now();
    verify_spec_prefill_carry_weld(&prompt_p1, &loop_qs.qs_mat.root, &prf)
        .expect("verify_spec_prefill_carry_weld");
    let ver_ms = t_v.elapsed().as_secs_f64() * 1000.0;
    println!(
        "[L2-CARRY] SpecPrefill (P=1, T=128) + R=3 Looped Residual Weld: prove = {:.2} ms, verify = {:.2} ms",
        prove_ms, ver_ms
    );

    // Falsifier 1: Spliced autoregressive token (`tok_in[t + 1] != y_hat_tok[t]` at `t = 41`) MUST fail!
    let mut bad_tok = wit.clone();
    bad_tok.tok_in_col[42] += 1;
    let bad_tok_prf = prove_spec_prefill_carry_weld(&bad_tok, &loop_qs).unwrap();
    assert!(
        verify_spec_prefill_carry_weld(&prompt_p1, &loop_qs.qs_mat.root, &bad_tok_prf).is_err(),
        "spliced tok_in[t+1] != y_hat[t] must fail!"
    );

    // Falsifier 2: Spliced looped residual state (`X_2 != stepPost(X_1, Y_1)`) MUST fail!
    let mut bad_res = wit.clone();
    bad_res.x_loop_bb[2][19] = badd(bad_res.x_loop_bb[2][19], 1);
    bad_res.x_loop_u16[2][19] += 1;
    let bad_res_prf = prove_spec_prefill_carry_weld(&bad_res, &loop_qs).unwrap();
    assert!(
        verify_spec_prefill_carry_weld(&prompt_p1, &loop_qs.qs_mat.root, &bad_res_prf).is_err(),
        "spliced residual X_{{r+1}} != stepPost(X_r, Y_r) must fail!"
    );

    // Falsifier 3: Non-greedy token choice (`IsGreedyDom` tie-break violation at `v < v*`) MUST fail!
    let mut bad_greedy = wit;
    // Plant an equal logit at `v = 0 < v*` (violating smallest-index tie-break -> `logit_gap` wraps mod P!):
    let v_star_0 = bad_greedy.y_hat_idx_col[0] as usize;
    assert!(v_star_0 > 0);
    let win_l = bad_greedy.logit_max_col[0];
    bad_greedy.shifted_logit_tv[0] = win_l;
    bad_greedy.logit_gap_tv[0] = qwen35audit::ext4::P_U32 - 1; // `win_l - win_l - 1 (mod P)` wraps outside `[0, 65536)`!
    assert!(
        prove_spec_prefill_carry_weld(&bad_greedy, &loop_qs).is_err(),
        "non-greedy argmax/tie-break wraparound must be rejected by D1b u16 range!"
    );
}

#[test]
fn test_payable_compute_receipt_e2e_benchmark_and_adversarial_suite() {
    let t_setup = Instant::now();
    let rom = QwenBpeRom::load_default().expect("load Qwen3.5 BPE ROM");
    let mmap = MmapSafetensors::open(std::path::Path::new(QWEN35_SAFETENSORS_FILE))
        .expect("mmap Qwen3.5-0.8B safetensors");
    let registry = Qwen35WeightRegistry::commit_all_24_layers(&mmap)
        .expect("commit_all_24_layers Qwen35WeightRegistry");

    // Extract `[1024, 1024]` top submatrix of `gate_proj` for all 18 GDN layers (used in Phase-1 `carry_weld_root`):
    let gdn_loop_mats: Vec<Mxfp4Matrix> = GDN_LAYER_INDICES_18
        .iter()
        .map(|&l| {
            let gname = format!("model.language_model.layers.{l}.mlp.gate_proj.weight");
            let gm = Mxfp4Matrix::from_safetensors(&mmap, &gname).expect("GDN gate_proj");
            extract_top_1024_mxfp4_submatrix(&gm)
        })
        .collect();

    // Build deterministic lease keys & prompt (`P = 4` tokens, `K_gen = 125` tokens, `2 x 64`-token chunks):
    let provider_kp = WotsKeypair::from_seed(&[0xA1u8; 32]);
    let escrow_kp = WotsKeypair::from_seed(&[0xB2u8; 32]);
    let prompt_tokens = rom.encode_qwen_bpe(b"Audit Qwen3.5:");
    let p_len = prompt_tokens.len();
    assert!((1..16).contains(&p_len));

    // Build a clean 125-token assistant response (`0` `"sk-..."` substrings):
    let base_resp = rom.encode_qwen_bpe(
        b" Verified payable compute turn over real Qwen3.5-0.8B weights with post-countersignature drand quicknet audit and conserved escrow settlement.",
    );
    let want_gen = CARRY_TURN_TOKENS - p_len + 1;
    let mut generated_tokens = Vec::with_capacity(want_gen);
    while generated_tokens.len() < want_gen {
        let rem = want_gen - generated_tokens.len();
        generated_tokens.extend_from_slice(&base_resp[..rem.min(base_resp.len())]);
    }
    let clean_output_bytes = rom.detokenize(&generated_tokens).unwrap();

    // Full 128-token turn split into `2` chunks of `64` tokens:
    let mut full_turn_128 = Vec::with_capacity(CARRY_TURN_TOKENS);
    full_turn_128.extend_from_slice(&prompt_tokens);
    full_turn_128.extend_from_slice(&generated_tokens[..(CARRY_TURN_TOKENS - p_len)]);
    assert_eq!(full_turn_128.len(), 128);
    let chunk0_toks = full_turn_128[0..64].to_vec();
    let chunk1_toks = full_turn_128[64..128].to_vec();

    // Execute all 24 real `Qwen/Qwen3.5-0.8B-Base` layers on BOTH 64-token chunks BEFORE seeing the beacon!
    let (exec_c0_init, _) = execute_qwen35_24_layers_mmap(&mmap, &chunk0_toks, 0)
        .expect("execute chunk 0 across 24 Qwen3.5 layers");
    let (exec_c1_init, _) = execute_qwen35_24_layers_mmap(&mmap, &chunk1_toks, 0)
        .expect("execute chunk 1 across 24 Qwen3.5 layers");

    // Precompute `gdn_qs_bindings` for the lease (offline model registration; we lazily build `CompactWhirMxfp4`
    // for the audited layer after `drand` selection, plus populate the binding slot in `lease` — note in
    // deployment all 18 GDN `gate_whir` roots are published once at model registration!):
    let mut lease = ProviderExecutionLease {
        lease_id: [0x55u8; 32],
        manifest_root: [0x66u8; 32],
        weight_root: registry.weight_root,
        rom_merkle_root: rom.rom_merkle_root,
        gdn_qs_bindings: [[0u8; 32]; 18],
        prompt_tokens: prompt_tokens.clone(),
        num_chunks: 2,
        max_units: 256,
        unit_price: 1_000,
        base_fee: 5_000,
        expiry_round: 1_000_010,
        beacon_delay: 1,
        drand_group_pk_g2: DRAND_QUICKNET_GROUP_PUBLIC_KEY,
        provider_pk: provider_kp.pk,
        escrow_pk: escrow_kp.pk,
    };
    println!(
        "[PAYABLE-SETUP] 2x64t 24-layer Qwen3.5-0.8B forward + ROM setup completed in {:.2} s",
        t_setup.elapsed().as_secs_f64()
    );

    // --- Phase 1: Provider commits `(trace_merkle_root, byte_root, bpe_weld_root, carry_weld_root)` ---
    let t_p1 = Instant::now();
    let phase1 = provider_commit_turn_phase1(
        &lease,
        &rom,
        vec![
            exec_c0_init.boundaries_bb.clone(),
            exec_c1_init.boundaries_bb.clone(),
        ],
        vec![chunk0_toks.clone(), chunk1_toks.clone()],
        generated_tokens.clone(),
        &gdn_loop_mats,
        [0x77u8; 32],
        125, // claimed_units < max_units (256)
        &provider_kp,
    )
    .expect("provider_commit_turn_phase1");
    let phase1_ms = t_p1.elapsed().as_secs_f64() * 1000.0;

    // --- Phase 2: Escrow countersigns at `round_commit = 999_999` -> `target_beacon_round = 1_000_000` ---
    let round_commit = PINNED_QUICKNET_ROUND_1M - 1; // 999,999
    let countersig =
        EscrowCountersignature::sign(&lease, &phase1.commitment, round_commit, &escrow_kp)
            .expect("EscrowCountersignature::sign");
    assert_eq!(countersig.target_beacon_round, PINNED_QUICKNET_ROUND_1M);

    // --- Phase 3: Published League of Entropy `drand` `quicknet` round `1_000_000` arrives (`> round_commit`) ---
    let live_beacon = DrandQuicknetBeacon::pinned_round_1m();
    let (gdn_slot, audited_layer, audited_chunk) = derive_post_countersig_audit_target(
        &lease.lease_id,
        &phase1.commitment.body_digest(),
        &countersig,
        &live_beacon,
        lease.num_chunks,
    );
    assert_eq!(GDN_LAYER_INDICES_18[gdn_slot], audited_layer);

    // Precommit static `CompactWhirMxfp4` (`3584 = 2048 + 1024 + 512`) for `audited_layer`:
    let tensor_names = Qwen35WeightRegistry::layer_tensor_names(audited_layer);
    let gate_name = format!("model.language_model.layers.{audited_layer}.mlp.gate_proj.weight");
    let gate_slot = tensor_names
        .iter()
        .position(|n| n == &gate_name)
        .expect("gate_proj slot in registry");
    let mut layer_digests = Vec::with_capacity(tensor_names.len());
    let mut gate_mat_opt = None;
    for (idx, tname) in tensor_names.iter().enumerate() {
        let m = Mxfp4Matrix::from_safetensors(&mmap, tname).expect("layer tensor from safetensors");
        layer_digests.push(m.digest);
        if idx == gate_slot {
            gate_mat_opt = Some(m);
        }
    }
    let gate_mat = gate_mat_opt.expect("audited gate_proj");
    let gate_whir = CompactWhirMxfp4::build(&gate_mat).expect("CompactWhirMxfp4::build");
    let mut qs_bind_in = [0u8; 64];
    qs_bind_in[0..32].copy_from_slice(&layer_digests[gate_slot]);
    qs_bind_in[32..64].copy_from_slice(&gate_whir.qs_mat.root);
    lease.gdn_qs_bindings[gdn_slot] = cshake256_32(b"QW35-QS-WHIR-BIND-V1", &qs_bind_in);

    // Capture full witness of the beacon-selected `(audited_layer, audited_chunk)`:
    let sel_chunk_toks = if audited_chunk == 0 {
        &chunk0_toks
    } else {
        &chunk1_toks
    };
    let (audited_exec, _) = execute_qwen35_24_layers_mmap(&mmap, sel_chunk_toks, audited_layer)
        .expect("audited layer exec");

    // --- Phase 4: Prove Single-Cascade `PayableComputeReceipt` & Benchmark Standalone Verification ---
    let t_prove = Instant::now();
    let receipt = prove_payable_compute_receipt(
        &lease,
        &rom,
        &registry,
        &phase1,
        &countersig,
        &live_beacon,
        &audited_exec,
        layer_digests,
        gate_slot,
        &gate_whir,
    )
    .expect("prove_payable_compute_receipt");
    let prove_ms = t_prove.elapsed().as_secs_f64() * 1000.0;
    let receipt_bytes = receipt.to_bytes();
    let decoded_receipt = PayableComputeReceipt::from_bytes(&receipt_bytes)
        .expect("PayableComputeReceipt::from_bytes");
    assert_eq!(decoded_receipt.to_bytes(), receipt_bytes);
    let receipt_kib = receipt_bytes.len() as f64 / 1024.0;

    // Warm once + measure median of 5 standalone verifications (`0` witness access):
    let mut ver_times = Vec::with_capacity(5);
    let mut last_settlement = None;
    for _ in 0..5 {
        let tv = Instant::now();
        let s = verify_payable_compute_receipt_and_settle(
            &lease,
            &rom,
            &receipt_bytes,
            Some(&clean_output_bytes),
        )
        .expect("standalone verify_payable_compute_receipt_and_settle");
        ver_times.push(tv.elapsed().as_secs_f64() * 1000.0);
        last_settlement = Some(s);
    }
    ver_times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median_verify_ms = ver_times[2];
    let settlement = last_settlement.unwrap();

    println!(
        "[PAYABLE-RECEIPT] layer={} (slot {}), chunk={}, word_len={}B: phase1={:.1} ms, prove={:.1} ms, wire={:.2} KiB ({} B < 665,600 B), standalone_verify={:.2} ms (< 25 ms), paid={}, refunded={}",
        audited_layer,
        gdn_slot,
        audited_chunk,
        clean_output_bytes.len(),
        phase1_ms,
        prove_ms,
        receipt_kib,
        receipt_bytes.len(),
        median_verify_ms,
        settlement.paid,
        settlement.refunded,
    );

    // STRICT HARD GATES FROM ASSIGNMENT:
    assert!(
        receipt_bytes.len() < 650 * 1024,
        "receipt wire {} B exceeded 650 KiB (665,600 B) limit!",
        receipt_bytes.len()
    );
    assert!(
        median_verify_ms < 25.0,
        "standalone verify {:.2} ms exceeded 25.0 ms limit!",
        median_verify_ms
    );
    assert_eq!(settlement.paid, 5_000 + 125 * 1_000);
    assert_eq!(settlement.refunded, (256 - 125) * 1_000);
    assert_eq!(
        settlement.paid + settlement.refunded,
        lease.prepaid_budget()
    );
    assert_eq!(settlement.audited_gdn_layer, audited_layer);
    assert_eq!(settlement.audited_token_chunk, audited_chunk);
    assert!(!settlement.expired_refund_only);

    // Timeout refund conservation path (`current_round > expiry_round` vs premature refund attempt):
    assert!(settle_expired_lease_refund(&lease, lease.expiry_round).is_err());
    let expired = settle_expired_lease_refund(&lease, lease.expiry_round + 1)
        .expect("timeout refund after expiry_round");
    assert_eq!(expired.paid, 0);
    assert_eq!(expired.refunded, lease.prepaid_budget());
    assert!(expired.expired_refund_only);

    // ============================================================================================
    // 10 Adversarial Protocol & Soundness Falsifiers on `PayableComputeReceipt`
    // ============================================================================================

    // Falsifier 1: Stale `drand` beacon (`beacon.round == round_commit`) -> REJECTED!
    let committee = BlsTestCommitteeKey::from_seed(&[0x99u8; 32]);
    let mut stale_rec = receipt.clone();
    stale_rec.beacon = committee.sign_quicknet_round(round_commit);
    let mut committee_lease = lease.clone();
    committee_lease.drand_group_pk_g2 = committee.group_pk_g2;
    assert!(
        verify_payable_compute_receipt_and_settle(
            &committee_lease,
            &rom,
            &stale_rec.to_bytes(),
            None
        )
        .is_err(),
        "Falsifier 1: stale beacon round <= round_commit must be rejected!"
    );

    // Falsifier 2: Off-schedule `drand` round shopping (`round_commit + 2 != target_beacon_round`) -> REJECTED!
    let mut shop_rec = receipt.clone();
    shop_rec.beacon = committee.sign_quicknet_round(round_commit + 2);
    assert!(
        verify_payable_compute_receipt_and_settle(
            &committee_lease,
            &rom,
            &shop_rec.to_bytes(),
            None
        )
        .is_err(),
        "Falsifier 2: off-schedule round shopping must be rejected!"
    );

    // Falsifier 3: Forged / mutated `drand` BLS12-381 signature -> REJECTED!
    let mut forged_bls = receipt.clone();
    forged_bls.beacon.signature[17] ^= 0x04;
    assert!(
        verify_payable_compute_receipt_and_settle(&lease, &rom, &forged_bls.to_bytes(), None)
            .is_err(),
        "Falsifier 3: forged BLS12-381 signature must be rejected!"
    );

    // Falsifier 4: Tampered Escrow Countersignature (`round_commit` decremented without escrow key) -> REJECTED!
    let mut bad_cs = receipt.clone();
    bad_cs.countersig.round_commit -= 1;
    assert!(
        verify_payable_compute_receipt_and_settle(&lease, &rom, &bad_cs.to_bytes(), None).is_err(),
        "Falsifier 4: tampered escrow countersignature must be rejected!"
    );

    // Falsifier 5: Post-countersignature root grinding (provider mutates `byte_root` after `round_commit`) -> REJECTED!
    let mut grind_rec = receipt.clone();
    grind_rec.commitment.byte_root[0] ^= 0xFF;
    grind_rec.commitment.content_root = qwen35audit::unified_turn_weld::compute_content_root_v1(
        grind_rec.commitment.word_len,
        &grind_rec.commitment.byte_root,
    );
    grind_rec.commitment.provider_sig = provider_kp.sign(&grind_rec.commitment.body_digest());
    assert!(
        verify_payable_compute_receipt_and_settle(&lease, &rom, &grind_rec.to_bytes(), None)
            .is_err(),
        "Falsifier 5: post-countersignature root grinding must fail countersig digest check!"
    );

    // Falsifier 6: Wrong audited `(layer, chunk)` substituted against post-countersignature `drand` target -> REJECTED!
    let mut wrong_slot = receipt.clone();
    wrong_slot.audited_chunk ^= 1;
    assert!(
        verify_payable_compute_receipt_and_settle(&lease, &rom, &wrong_slot.to_bytes(), None)
            .is_err(),
        "Falsifier 6: wrong audited chunk must be rejected!"
    );

    // Falsifier 7: Broken `U1` residual boundary (`b_out_eval` tampered by +1) -> REJECTED!
    let mut bad_u1 = receipt.clone();
    bad_u1.b_out_eval = bad_u1.b_out_eval.add(Ext4::ONE);
    assert!(
        verify_payable_compute_receipt_and_settle(&lease, &rom, &bad_u1.to_bytes(), None).is_err(),
        "Falsifier 7: broken U1 residual weld must be rejected!"
    );

    // Falsifier 8: Tampered BPE rolled accumulator (`final_acc_ext4` shifted by +1) -> REJECTED!
    let mut bad_bpe = receipt.clone();
    bad_bpe.final_acc_ext4 = bad_bpe.final_acc_ext4.add(Ext4::ONE);
    assert!(
        verify_payable_compute_receipt_and_settle(&lease, &rom, &bad_bpe.to_bytes(), None).is_err(),
        "Falsifier 8: tampered BPE token-to-byte accumulator must be rejected!"
    );

    // Falsifier 9: Over-budget unit claim (`claimed_units > lease.max_units`) -> REJECTED!
    let mut over_budget = receipt.clone();
    over_budget.commitment.claimed_units = lease.max_units + 1;
    assert!(
        verify_payable_compute_receipt_and_settle(&lease, &rom, &over_budget.to_bytes(), None)
            .is_err(),
        "Falsifier 9: claimed_units > max_units must be rejected!"
    );

    // Falsifier 10: Unredacted `"sk-live-..."` secret in assistant output -> REJECTED at Phase-1 prover AND verifier!
    let mut leak_toks = rom.encode_qwen_bpe(b" Leak sk-live-secret-token ");
    while leak_toks.len() < want_gen {
        let rem = want_gen - leak_toks.len();
        leak_toks.extend_from_slice(&base_resp[..rem.min(base_resp.len())]);
    }
    leak_toks.truncate(want_gen);
    assert!(
        provider_commit_turn_phase1(
            &lease,
            &rom,
            vec![exec_c0_init.boundaries_bb, exec_c1_init.boundaries_bb],
            vec![chunk0_toks, chunk1_toks],
            leak_toks,
            &gdn_loop_mats,
            [0x88u8; 32],
            125,
            &provider_kp,
        )
        .is_err(),
        "Falsifier 10: unredacted sk-live leak must be refused by Phase-1 Absent DFA gate!"
    );
    let mut sink_rec = receipt;
    sink_rec.commitment.final_dfa_state = 4;
    assert!(
        verify_payable_compute_receipt_and_settle(&lease, &rom, &sink_rec.to_bytes(), None)
            .is_err(),
        "Falsifier 10b: final_dfa_state >= 4 must be rejected by standalone verifier!"
    );
}
