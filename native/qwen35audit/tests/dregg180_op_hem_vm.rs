//! End-to-End Conformance, `< 16 KiB` Zero-Heap Silicon VM Benchmark, & 10+ Adversarial
//! Falsifier Suite for Wearable SHE Organ #1 (`qwen35audit::dregg180_hem_bridge`).
#![deny(warnings)]

use qwen35audit::dregg180_hem_bridge::{
    bridge_wearable_she_bundle_to_dregg180_stream, canonical_trustless_vk,
    compute_expected_trustless_program_hash, cshake256_canopy_node, fp5_mul, gf128_mul,
    p2_canopy_node, p2_canopy_path, p2_ordered_compress, p2_sponge12_rate6, p2_sponge_hash_limbs,
    pack_bytes_7_limbs, poseidon2_perm12, prove_child_babybear_ext4_cubic_sumcheck,
    prove_trustless_hem_with_tamper, prove_trustless_hem_with_wbb_override,
    prove_trustless_nonnative_babybear_and_dfa_hem, run_no_sk_dash_dfa_4state,
    turboshake256_32_stack, verify_trustless_dregg180_hem_stream, BabyBearWitnessCommitment,
    DeferredLeafClaim, DeferredLeafKind, Dregg180HvmAssembler, Dregg180StreamError,
    Dregg180StreamVm, Goldilocks, GoldilocksExt4, PayloadBytesCommitment,
    SimplexFinCertLeafReceipt, SimplexFinalizedClaims, SimplexQuorumCfg, Tower256AbsentLeafReceipt,
    TrustlessHemTamper, VerifierExpectedTrustlessStatement, WearableQwenWhirLeafReceipt,
    BABYBEAR_PRIME_U64, DREGG180_VM_MAX_STATIC_BYTES, FS_INIT_CAP, GOLDILOCKS_PRIME,
    HEM_MAX_BB_ROUNDS, H_ASSERT_POW, H_HASH, H_LOAD, OP_FOLD, OP_HEM, P2_DOMAIN_FS_ABSORB_LIMBS,
    P2_DOMAIN_FS_POW_T1, P2_DOMAIN_FS_POW_T2, R_A, R_B, R_CH, R_T0, R_X, R_Y, UD100_BLOWUP,
    UD100_NUM_QUERIES, UD100_POW_BITS,
};
use qwen35audit::ext4::Ext4 as BbExt4;
use std::alloc::{GlobalAlloc, Layout, System};
use std::ops::{Add, Mul};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

struct CountingAllocator;
static HEAP_ALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        HEAP_ALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL_ALLOC: CountingAllocator = CountingAllocator;

#[test]
fn test_dregg180_lean_oracle_kat_vectors_and_static_ram_bound() {
    // 1. Static zero-SRAM-macro silicon stack bound `<= 16 KiB`:
    let vm_bytes = Dregg180StreamVm::static_ram_bytes();
    println!(
        "[DREGG180-RAM] sizeof(Dregg180StreamVm) = {} B ({:.2} KiB <= 16.00 KiB)",
        vm_bytes,
        vm_bytes as f64 / 1024.0
    );
    assert!(vm_bytes <= DREGG180_VM_MAX_STATIC_BYTES);
    assert!(
        vm_bytes < 4_096,
        "Dregg180StreamVm fits in < 4 KiB (< 25% of 16 KiB budget)"
    );

    // 2. Exact KAT parity with `qsag/hardware/gf180mcu/tb/fixtures/lean_external_oracle_vectors.json`:
    let gl_edges: &[(u64, u64, u64, u64, u64, u64, u64)] = &[
        (0, 0, 0, 0, 0, 0, 0),
        (1, 1, 2, 0, 1, 1, 1),
        (
            4_294_967_295,
            4_294_967_295,
            8_589_934_590,
            0,
            18_446_744_065_119_617_025,
            18_446_744_065_119_617_025,
            4_294_967_295,
        ),
        (
            4_294_967_296,
            18_446_744_069_414_584_320,
            4_294_967_295,
            4_294_967_297,
            18_446_744_065_119_617_025,
            18_446_744_065_119_617_026,
            4_294_967_296,
        ),
        (
            1_311_768_467_463_790_320,
            18_364_758_544_493_064_723,
            1_229_782_942_542_270_722,
            1_393_753_992_385_309_918,
            3_569_103_298_414_925_731,
            14_736_413_637_906_284_881,
            11_853_639_751_010_147_186,
        ),
    ];
    for &(a_raw, b_raw, add_w, sub_w, mul_w, inv_w, pow7_w) in gl_edges {
        let a = Goldilocks::from_u64_reduced(a_raw);
        let b = Goldilocks::from_u64_reduced(b_raw);
        assert_eq!((a + b).0, add_w);
        assert_eq!((a - b).0, sub_w);
        assert_eq!((a * b).0, mul_w);
        assert_eq!(a.inv().0, inv_w);
        assert_eq!(a.sbox7().0, pow7_w);
    }
    assert!(Goldilocks::from_canonical_u64(GOLDILOCKS_PRIME).is_none());
    assert!(Goldilocks::from_canonical_u64(u64::MAX).is_none());

    // 3. `GoldilocksExt4` (`v^4 = 7`, `[1, v^2, v, v^3]` basis) KATs (`mul`, `inv_x`, `frob_x`):
    let x1 = GoldilocksExt4::from_u64_limbs([1, 2, 3, 4]);
    let y1 = GoldilocksExt4::from_u64_limbs([5, 6, 7, 8]);
    assert_eq!((x1 * y1).to_u64_limbs(), [453, 261, 302, 60]);
    assert_eq!(
        x1.inv().to_u64_limbs(),
        [
            6_251_233_170_369_050_463,
            11_326_969_264_342_763_568,
            2_352_199_790_817_746_857,
            10_096_736_221_518_351_014
        ]
    );
    assert_eq!((x1 * x1.inv()), GoldilocksExt4::ONE);
    assert_eq!(
        x1.frobenius().to_u64_limbs(),
        [
            1,
            18_446_744_069_414_584_319,
            844_424_930_131_968,
            18_445_618_169_507_741_697
        ]
    );
    assert_eq!(
        GoldilocksExt4::V.pow(4),
        GoldilocksExt4::from_base(Goldilocks(7))
    );

    let x2 = GoldilocksExt4::from_u64_limbs([
        18_446_744_069_414_584_320,
        4_294_967_295,
        4_294_967_296,
        7,
    ]);
    let y2 = GoldilocksExt4::from_u64_limbs([
        14_627_333_965_257_922_168,
        1_147_797_409_030_816_545,
        42,
        99,
    ]);
    assert_eq!(
        (x2 * y2).to_u64_limbs(),
        [
            16_773_126_692_020_832_778,
            163_971_232_514_424_476,
            16_840_946_237_093_125_041,
            2_614_948_903_979_618_572
        ]
    );

    // 4. Width-12 `Poseidon2` KATs (`[0; 12]` and `[0..12]`):
    let mut st0 = [Goldilocks::ZERO; 12];
    poseidon2_perm12(&mut st0);
    assert_eq!(
        st0.map(|g| g.0),
        [
            17_528_629_447_354_354_351,
            5_014_055_130_248_055_117,
            10_679_077_121_839_038_553,
            431_078_547_345_611_051,
            7_807_009_921_345_120_310,
            2_413_869_689_279_715_014,
            11_875_300_792_986_830_377,
            1_872_634_884_137_602_556,
            15_069_512_080_271_275_672,
            14_253_608_580_209_913_153,
            14_550_618_143_248_480_092,
            107_036_164_978_639_472,
        ]
    );

    let mut st1 = core::array::from_fn(|i| Goldilocks(i as u64));
    poseidon2_perm12(&mut st1);
    assert_eq!(
        st1.map(|g| g.0),
        [
            13_782_584_570_844_608_145,
            13_136_387_643_152_332_171,
            7_171_133_015_474_200_819,
            7_643_370_872_200_861_694,
            14_144_755_201_299_840_503,
            16_470_027_036_684_692_562,
            1_748_465_969_625_202_405,
            1_718_729_118_078_964_347,
            6_141_020_819_996_733_037,
            16_322_330_185_628_708_898,
            11_650_380_702_735_067_362,
            2_734_959_974_607_798_415,
        ]
    );

    // 5. RFC 9861 `TurboSHAKE256("")` & `GF(2^128)` KAT + `Fp5` (`X^5 - 3`) + Canopy path check:
    let ts_empty = turboshake256_32_stack(&[]);
    assert_eq!(
        &ts_empty[0..8],
        &[0x36, 0x7a, 0x32, 0x9d, 0xaf, 0xea, 0x87, 0x1c]
    );
    assert_eq!(gf128_mul(1, 0xDEAD_BEEF_CAFE_BABE), 0xDEAD_BEEF_CAFE_BABE);

    let x_fp5 = [0, 1, 0, 0, 0];
    let x2_fp5 = fp5_mul(&x_fp5, &x_fp5);
    let x4_fp5 = fp5_mul(&x2_fp5, &x2_fp5);
    assert_eq!(fp5_mul(&x4_fp5, &x_fp5), [3, 0, 0, 0, 0]);

    let key3 = [11, 22, 33];
    let l4 = [1, 2, 3, 4];
    let r4 = [5, 6, 7, 8];
    let root1 = p2_canopy_node(l4, r4, key3, 1);
    assert_eq!(p2_canopy_path(l4, &[r4], key3, 0), root1);
    assert_eq!(p2_canopy_path(r4, &[l4], key3, 1), root1);

    // 6. `zk-Hem v2` Quintic `Fp5` + `sponge12_rate6` streamed VM execution (`flags = 0x18`):
    let mut asm5 = Dregg180HvmAssembler::new(OP_HEM, true, true);
    let stmt5 = [10u64, 20, 30, 40, 50];
    asm5.hash_rate6(R_CH, &stmt5, &[], 0, 0);
    let ch5: [u64; 5] = p2_sponge12_rate6(&stmt5)[..5].try_into().unwrap();
    let c0_5 = [2u64, 3, 4, 5, 6];
    let c2_5 = [7u64, 8, 9, 10, 11];
    let mut sc_in = Vec::new();
    sc_in.extend_from_slice(&ch5);
    sc_in.extend_from_slice(&c0_5);
    sc_in.extend_from_slice(&c2_5);
    let r5: [u64; 5] = p2_sponge12_rate6(&sc_in)[..5].try_into().unwrap();
    let c1_5 = [12u64, 13, 14, 15, 16];
    let r_c2 = fp5_mul(&r5, &c2_5);
    let mut c1_plus = [0u64; 5];
    for i in 0..5 {
        c1_plus[i] = c1_5[i] + r_c2[i];
    }
    let r_inner = fp5_mul(&r5, &c1_plus);
    let mut claim5 = [0u64; 5];
    for i in 0..5 {
        claim5[i] = (Goldilocks(c0_5[i]) + Goldilocks(r_inner[i])).0;
    }
    asm5.load(R_A, &claim5, true);
    asm5.load(R_X, &c0_5, false);
    asm5.load(R_Y, &c2_5, false);
    asm5.hash_rate6(R_B, &[], &sc_in, 0, 0);
    asm5.load(R_T0, &c1_5, false);
    asm5.emul(R_Y, R_Y, R_B);
    asm5.eadd(R_Y, R_Y, R_T0);
    asm5.emul(R_Y, R_Y, R_B);
    asm5.eadd(R_Y, R_Y, R_X);
    asm5.assert_eq(R_A, R_Y);
    let (wire5, pdig5) = asm5.build_wire_bytes_and_pdig(None);
    let mut vm5 = Dregg180StreamVm::new_unkeyed(Some(pdig5));
    let verdict5 = vm5
        .verify_stream(&wire5)
        .expect("Fp5 zk-Hem v2 stream must verify");
    assert!(verdict5.accepted && verdict5.zk_pin.is_some());
}

#[test]
fn test_wearable_she_heterogeneous_bundle_e2e_zero_heap_stream_and_adversarial_suite() {
    let lease_id = [0x91u8; 32];
    let clean_msg =
        b"Wearable SHE Organ #1 clean assistant summary: ToF=1.18m, HR=64bpm, status=ok.";

    // 1. Prove the 3 heterogeneous child receipts across `BabyBear Ext4`, `Tower256`, and `Simplex`:
    let t_leaves = Instant::now();
    let qwen_leaf = WearableQwenWhirLeafReceipt::prove(lease_id, clean_msg, [0x11u8; 32])
        .expect("prove BabyBear Ext4 Qwen WhirExt4 leaf");
    let absent_leaf =
        Tower256AbsentLeafReceipt::prove(qwen_leaf.content_root, clean_msg, [0x22u8; 32])
            .expect("prove Tower256 Absent(\"sk-...\") leaf");
    let (kps, roster_root, roster_leaves) = SimplexFinCertLeafReceipt::build_committee(4, 0xC3);
    let qwen_dig = qwen_leaf.verify().unwrap();
    let absent_dig = absent_leaf.verify(&qwen_leaf.content_root).unwrap();
    let fincert_leaf = SimplexFinCertLeafReceipt::sign_quorum(
        SimplexQuorumCfg {
            n_validators: 4,
            max_faulty_f: 1, // n = 4, f = 1 => quorum = n - f = 3
            view: 9,         // view = 9 > 0
        },
        &kps,
        roster_root,
        &roster_leaves,
        &[0, 2, 3],
        SimplexFinalizedClaims {
            content_root: qwen_leaf.content_root,
            qwen_claim: qwen_dig,
            absent_claim: absent_dig,
        },
    );
    let leaves_ms = t_leaves.elapsed().as_secs_f64() * 1000.0;

    // 2. Compile into a single `GoldilocksExt4` `Hem` stream (`OP_HEM` `0x31`, `K_MAC` + `pin_mode = false`):
    let k_mac = [0x5Au8; 16];
    let t_comp = Instant::now();
    let compiled = bridge_wearable_she_bundle_to_dregg180_stream(
        &qwen_leaf,
        &absent_leaf,
        &fincert_leaf,
        &roster_root,
        false,
        Some(k_mac),
    )
    .expect("bridge heterogeneous SHE bundle into Dregg-180 OP_HEM stream");
    let comp_ms = t_comp.elapsed().as_secs_f64() * 1000.0;

    // 3. Verify inside `< 16 KiB` `Dregg180StreamVm` with ZERO heap allocations!
    HEAP_ALLOC_COUNT.store(0, Ordering::SeqCst);
    let t_ver = Instant::now();
    let mut vm_full = Dregg180StreamVm::new_keyed(k_mac, Some(compiled.pinned_program_digest));
    let verdict_full = vm_full
        .verify_stream(&compiled.wire_bytes)
        .expect("Dregg180StreamVm full-slice verify");
    let ver_ms = t_ver.elapsed().as_secs_f64() * 1000.0;
    let allocs_during_vm = HEAP_ALLOC_COUNT.load(Ordering::SeqCst);
    assert_eq!(
        allocs_during_vm, 0,
        "Dregg180StreamVm MUST perform 0 heap allocations during verification!"
    );

    // 4. Verify exact bit-for-bit equivalence across 48-byte `RX_CREDIT_OK` SPI bursts AND 1-byte streaming!
    HEAP_ALLOC_COUNT.store(0, Ordering::SeqCst);
    let mut vm_spi48 = Dregg180StreamVm::new_keyed(k_mac, Some(compiled.pinned_program_digest));
    for frame48 in compiled.wire_bytes.chunks(48) {
        vm_spi48
            .feed_bytes(frame48)
            .expect("48-byte SPI burst feed");
    }
    let verdict_spi48 = vm_spi48.finalize().expect("48-byte SPI burst finalize");
    assert_eq!(HEAP_ALLOC_COUNT.load(Ordering::SeqCst), 0);
    assert_eq!(verdict_full, verdict_spi48);

    HEAP_ALLOC_COUNT.store(0, Ordering::SeqCst);
    let mut vm_1b = Dregg180StreamVm::new_keyed(k_mac, Some(compiled.pinned_program_digest));
    for b1 in compiled.wire_bytes.chunks(1) {
        vm_1b.feed_bytes(b1).expect("1-byte stream feed");
    }
    let verdict_1b = vm_1b.finalize().expect("1-byte stream finalize");
    assert_eq!(HEAP_ALLOC_COUNT.load(Ordering::SeqCst), 0);
    assert_eq!(verdict_full, verdict_1b);

    let m = verdict_full.metrics;
    println!(
        "[DREGG180-SHE-E2E] Heterogeneous 3-leaf prove={:.2} ms, Hem compile={:.2} ms, VM verify={:.3} ms (0 heap allocs!)",
        leaves_ms, comp_ms, ver_ms
    );
    println!(
        "[DREGG180-METRICS] stream={} B ({:.2} KiB), records={}, core_cycles={} ({:.2} ms @25MHz, {:.2} ms @12.93MHz TT), P2_perms={}, Keccak_perms={}, Ext4_muls={}, Ext4_addsubs={}, GF128_steps={}, P2_Canopy_nodes={}, cSHAKE_Canopy_nodes={}, imm_words={}, proof_words={}",
        compiled.wire_bytes.len(),
        compiled.wire_bytes.len() as f64 / 1024.0,
        m.records_executed,
        m.core_cycles,
        m.latency_ms_at_mhz(25.0),
        m.latency_ms_at_mhz(12.93),
        m.poseidon2_perms,
        m.keccak_perms,
        m.ext4_muls,
        m.ext4_addsubs,
        m.gf128_steps,
        m.canopy_p2_nodes,
        m.canopy_cshake_nodes,
        m.immediate_words,
        m.proof_words
    );

    // ============================================================================================
    // §5. 10+ Adversarial Falsifiers (`[REFUTED: scope]`)
    // ============================================================================================

    // Attack 1: 0-assertion `LOAD R_CH` exploit (`Dregg-180` D6 #2 regression) MUST be rejected!
    let mut asm_zero_assert = Dregg180HvmAssembler::new(OP_FOLD, false, false);
    asm_zero_assert.load(R_CH, &[1, 2, 3, 4], false);
    let (bad_zero_wire, _) = asm_zero_assert.build_wire_bytes_and_pdig(None);
    let mut vm = Dregg180StreamVm::new_unkeyed(None);
    assert!(
        matches!(
            vm.verify_stream(&bad_zero_wire),
            Err(Dregg180StreamError::Rejected { .. })
        ),
        "Attack 1: 0-assertion LOAD R_CH stream must be rejected!"
    );

    // Attack 2: `LOAD R_CH` in `pin_mode = true` MUST be rejected!
    let mut asm_pin_ch = Dregg180HvmAssembler::new(OP_HEM, true, false);
    asm_pin_ch.load(R_CH, &[1, 2, 3, 4], false);
    asm_pin_ch.assert_eq(R_CH, R_CH);
    let (bad_pin_wire, bad_pin_pdig) = asm_pin_ch.build_wire_bytes_and_pdig(None);
    let mut vm = Dregg180StreamVm::new_unkeyed(Some(bad_pin_pdig));
    assert!(
        matches!(
            vm.verify_stream(&bad_pin_wire),
            Err(Dregg180StreamError::Rejected { .. })
        ),
        "Attack 2: LOAD R_CH in pin_mode must be rejected!"
    );

    // Attack 3: Non-canonical proof word (`>= GOLDILOCKS_PRIME`, alias `[p, 2^64)`) MUST be rejected!
    let mut asm_alias = Dregg180HvmAssembler::new(OP_FOLD, false, false);
    asm_alias.load(R_A, &[GOLDILOCKS_PRIME, 0, 0, 0], false); // proof word `== p` (alias of 0!)
    asm_alias.load(R_B, &[0, 0, 0, 0], true);
    asm_alias.assert_eq(R_A, R_B);
    let (alias_wire, _) = asm_alias.build_wire_bytes_and_pdig(None);
    let mut vm = Dregg180StreamVm::new_unkeyed(None);
    match vm.verify_stream(&alias_wire) {
        Err(Dregg180StreamError::Rejected {
            non_canonical_word: true,
            ..
        }) => {}
        other => panic!(
            "Attack 3: non-canonical Goldilocks alias must set non_canonical_word, got {other:?}"
        ),
    }

    // Attack 4: Unabsorbed / swapped child `DeferredLeafClaim` immediate (`program_digest_mismatch`)!
    let mut forged_claims = compiled.leaf_claims;
    forged_claims[1].claim_digest[0] ^= 0xFF;
    let recompiled_forged =
        qwen35audit::dregg180_hem_bridge::compile_deferred_leaves_to_dregg180_hem_stream(
            forged_claims,
            false,
            Some(k_mac),
        )
        .unwrap();
    let mut vm = Dregg180StreamVm::new_keyed(k_mac, Some(compiled.pinned_program_digest));
    match vm.verify_stream(&recompiled_forged.wire_bytes) {
        Err(Dregg180StreamError::Rejected {
            program_digest_mismatch: true,
            ..
        }) => {}
        other => panic!(
            "Attack 4: swapped DeferredLeafClaim immediate must fail pdig pin, got {other:?}"
        ),
    }

    // Attack 5: Bit-flip in streamed proof body (sumcheck / Canopy sibling / duet-fold witness)!
    let mut flipped_wire = compiled.wire_bytes.clone();
    let mid_byte = (flipped_wire.len() / 2) | 1;
    flipped_wire[mid_byte] ^= 0x04;
    let mut vm = Dregg180StreamVm::new_keyed(k_mac, Some(compiled.pinned_program_digest));
    assert!(
        vm.verify_stream(&flipped_wire).is_err(),
        "Attack 5: 1-bit flip in proof stream must fail verification!"
    );

    // Attack 6: Forged `H_BIND_IDX` Merkle leaf index substitution!
    let mut asm_idx_bypass = Dregg180HvmAssembler::new(OP_HEM, false, false);
    let key4 = [1u64, 2, 3, 4];
    let l0 = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, key4, &[10, 20, 30, 40]);
    let l1 = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, key4, &[50, 60, 70, 80]);
    let r_can = p2_canopy_node(l0, l1, [1, 2, 3], 1);
    asm_idx_bypass.load(R_B, &r_can, true);
    asm_idx_bypass.load(R_A, &key4, true);
    asm_idx_bypass.load(R_T0, &[0, 0, 0, 0], true); // transcript says index = 0
    asm_idx_bypass.bind_idx(R_T0, 0, 1);
    asm_idx_bypass.load(R_X, &l1, false);
    asm_idx_bypass.merkle(R_A, 1, &[l0]); // prover tries opening valid leaf 1 instead of bound index 0!
    asm_idx_bypass.assert_eq(R_X, R_B);
    let (idx_wire, _) = asm_idx_bypass.build_wire_bytes_and_pdig(None);
    let mut vm = Dregg180StreamVm::new_unkeyed(None);
    assert!(
        matches!(
            vm.verify_stream(&idx_wire),
            Err(Dregg180StreamError::Rejected { .. })
        ),
        "Attack 6: opening Merkle path at index != bound_idx must be rejected!"
    );

    // Attack 7: Corrupted `cSHAKE256("QSAG.PCS.CANOPY/v2")` sibling in `H_CSHAKE_MERKLE`!
    let d0 = [0x11u8; 32];
    let d1 = [0x22u8; 32];
    let cs_r = cshake256_canopy_node(&d0, &d1, 1);
    let cs_r_pin = p2_sponge_hash_limbs(
        P2_DOMAIN_FS_ABSORB_LIMBS,
        FS_INIT_CAP,
        &qwen35audit::dregg180_hem_bridge::pack_digest32_to_5_limbs(&cs_r),
    );
    let d0_pin = p2_sponge_hash_limbs(
        P2_DOMAIN_FS_ABSORB_LIMBS,
        FS_INIT_CAP,
        &qwen35audit::dregg180_hem_bridge::pack_digest32_to_5_limbs(&d0),
    );
    let mut asm_cs_bad = Dregg180HvmAssembler::new(OP_HEM, false, false);
    asm_cs_bad.load(R_B, &cs_r_pin, true);
    asm_cs_bad.load(R_X, &d0_pin, false);
    asm_cs_bad.load(R_T0, &[0, 0, 0, 0], true);
    asm_cs_bad.bind_idx(R_T0, 0, 1);
    let mut bad_d1 = d1;
    bad_d1[7] ^= 0x01;
    asm_cs_bad.cshake_merkle(0, &d0, &[bad_d1]);
    asm_cs_bad.assert_eq(R_X, R_B);
    let (cs_bad_wire, _) = asm_cs_bad.build_wire_bytes_and_pdig(None);
    let mut vm = Dregg180StreamVm::new_unkeyed(None);
    assert!(
        vm.verify_stream(&cs_bad_wire).is_err(),
        "Attack 7: tampered cSHAKE256 Canopy sibling must be rejected!"
    );

    // Attack 8: Secret `"sk-live-..."` leaked in assistant bytes -> `Tower256` `Absent` sink rejection!
    let leaked_msg = b"Summary: token sk-live-99887766 leaked in assistant output.";
    assert!(
        Tower256AbsentLeafReceipt::prove(qwen_leaf.content_root, leaked_msg, [0x33u8; 32]).is_err(),
        "Attack 8a: prover must refuse sk-live-... sink state"
    );
    let mut forged_absent = absent_leaf.clone();
    forged_absent.final_dfa_state = 4;
    assert!(
        bridge_wearable_she_bundle_to_dregg180_stream(
            &qwen_leaf,
            &forged_absent,
            &fincert_leaf,
            &roster_root,
            false,
            Some(k_mac),
        )
        .is_err(),
        "Attack 8b: bridge must reject Absent receipt in sink state >= 4"
    );

    // Attack 9: Sub-quorum (`2 < n - f = 3`) OR duplicate validator index in `Simplex` `FinCert`!
    let sub_quorum_fincert = SimplexFinCertLeafReceipt::sign_quorum(
        SimplexQuorumCfg {
            n_validators: 4,
            max_faulty_f: 1,
            view: 9,
        },
        &kps,
        roster_root,
        &roster_leaves,
        &[0, 2], // only 2 signers < quorum 3!
        SimplexFinalizedClaims {
            content_root: qwen_leaf.content_root,
            qwen_claim: qwen_dig,
            absent_claim: absent_dig,
        },
    );
    assert!(
        bridge_wearable_she_bundle_to_dregg180_stream(
            &qwen_leaf,
            &absent_leaf,
            &sub_quorum_fincert,
            &roster_root,
            false,
            Some(k_mac),
        )
        .is_err(),
        "Attack 9a: sub-quorum (2 < n - f = 3) FinCert must be rejected!"
    );
    let dup_signer_fincert = SimplexFinCertLeafReceipt::sign_quorum(
        SimplexQuorumCfg {
            n_validators: 4,
            max_faulty_f: 1,
            view: 9,
        },
        &kps,
        roster_root,
        &roster_leaves,
        &[0, 2, 2], // duplicate signer 2!
        SimplexFinalizedClaims {
            content_root: qwen_leaf.content_root,
            qwen_claim: qwen_dig,
            absent_claim: absent_dig,
        },
    );
    assert!(
        bridge_wearable_she_bundle_to_dregg180_stream(
            &qwen_leaf,
            &absent_leaf,
            &dup_signer_fincert,
            &roster_root,
            false,
            Some(k_mac),
        )
        .is_err(),
        "Attack 9b: duplicate validator index in FinCert must be rejected!"
    );

    // Attack 10: Cross-leaf `content_root` splice (welding clean `Absent` receipt to a different `Qwen` turn)!
    let other_qwen = WearableQwenWhirLeafReceipt::prove(
        lease_id,
        b"Different assistant output turn!",
        [0x44u8; 32],
    )
    .unwrap();
    assert!(
        bridge_wearable_she_bundle_to_dregg180_stream(
            &other_qwen,
            &absent_leaf,
            &fincert_leaf,
            &roster_root,
            false,
            Some(k_mac),
        )
        .is_err(),
        "Attack 10: cross-leaf content_root splice must be rejected!"
    );

    // Attack 11: Truncated stream & trailing-word overrun splice MUST be rejected!
    let mut vm_trunc = Dregg180StreamVm::new_keyed(k_mac, Some(compiled.pinned_program_digest));
    assert_eq!(
        vm_trunc.verify_stream(&compiled.wire_bytes[..compiled.wire_bytes.len() - 8]),
        Err(Dregg180StreamError::TruncatedStream)
    );
    let mut overrun_bytes = compiled.wire_bytes.clone();
    overrun_bytes.extend_from_slice(&0u64.to_le_bytes());
    let mut vm_over = Dregg180StreamVm::new_keyed(k_mac, Some(compiled.pinned_program_digest));
    assert_eq!(
        vm_over.verify_stream(&overrun_bytes),
        Err(Dregg180StreamError::StreamOverrun)
    );

    // Unused helper sanity check (`pack_bytes_7_limbs` parity):
    assert_eq!(pack_bytes_7_limbs(b"abc"), vec![3, 0x0063_6261]);
    let dummy_claim = DeferredLeafClaim {
        kind: DeferredLeafKind::BabyBearWhirExt4,
        content_root: [0u8; 32],
        leaf_root: [0u8; 32],
        claim_digest: [0u8; 32],
    };
    assert_eq!(dummy_claim.to_immediate_limbs()[0], 1);
}

#[test]
fn test_trustless_ud100_nonnative_babybear_ext4_and_absent_sk_dfa_no_kmac_zero_heap() {
    // 1. Verify post-audit `UD-100` parameter constants (`H2` fix: bare query-only two-table bound
    //    `2 * (9/16)^122 = 2^{-100.27} < 2^{-100}` WITHOUT PoW credit, + 16-bit bound PoW = `2^{-116.27}`):
    assert_eq!(UD100_BLOWUP, 8);
    assert_eq!(UD100_NUM_QUERIES, 122);
    assert_eq!(UD100_POW_BITS, 16);
    let vm_bytes = Dregg180StreamVm::static_ram_bytes();
    assert!(vm_bytes <= DREGG180_VM_MAX_STATIC_BYTES);
    assert!(
        vm_bytes < 4_096,
        "Dregg180StreamVm must stay < 4 KiB, got {vm_bytes} B"
    );

    // 2. Fetch verifier-owned canonical preprocessed VK for `m = 6` full cubic `BabyBear Ext4` (`X^4 - 11`)
    //    sumcheck rounds + full in-circuit `chi(x)` / `W_bb(r)` / `eq(tau, r)` terminal evaluation
    //    + `4 x 256` `Absent("sk-")` 4-state DFA transition ROM (`H4` fix, ZERO `Option` terminal oracle!):
    let m_rounds = HEM_MAX_BB_ROUNDS; // 6 rounds -> 64-entry committed W_bb = (A_bb, B_bb) in N_exec = 4,096
    let t_vk = Instant::now();
    let vk =
        canonical_trustless_vk(m_rounds).expect("build verifier-owned canonical TrustlessHemVk");
    let vk_ms = t_vk.elapsed().as_secs_f64() * 1000.0;

    // 3. Commit clean payload bytes (NO `"sk-"`) under public dual Canopy (`Poseidon2-12` + `cSHAKE256`):
    let clean_payload = b"Wave 10 Trustless UD-100 Dregg-180 OP_HEM: clean output with sk_safe and s-k-ok, zero secret leak.";
    assert!(run_no_sk_dash_dfa_4state(clean_payload).0 < 3);
    let payload_comm = PayloadBytesCommitment::commit(clean_payload).expect("commit clean payload");

    // 4. Construct a REAL `m = 6`-round (`64`-entry) degree-3 cubic `BabyBear Ext4` (`X^4 - 11`) sumcheck instance
    //    `sum_{x in {0,1}^6} eq(tau_bb, x) * A(x) * B(x) == initial_claim`
    //    tuned so `initial_claim.0[0] == 0`, guaranteeing an honest MAC row with `q_honest >= 1 && r_honest == 0`
    //    so `NonCanonicalBabyBearExactPbbAlias` exercises ZERO MAC residual and ONLY canonical slack rejection (`M3` fix!).
    let n_bb = 1usize << m_rounds;
    let mut a_vals = Vec::with_capacity(n_bb);
    let mut b_vals = Vec::with_capacity(n_bb);
    for i in 0..n_bb {
        a_vals.push(((i as u64 * 7_812_345 + 1_900_000_003) % BABYBEAR_PRIME_U64) as u32);
        b_vals.push(((i as u64 * 11_331_771 + 1_500_000_007) % BABYBEAR_PRIME_U64) as u32);
    }
    let tau_bb: Vec<BbExt4> = (0..m_rounds)
        .map(|j| {
            BbExt4([
                ((j as u64 * 123_456_789 + 42) % BABYBEAR_PRIME_U64) as u32,
                ((j as u64 * 987_654_321 + 17) % BABYBEAR_PRIME_U64) as u32,
                ((j as u64 * 555_111_222 + 99) % BABYBEAR_PRIME_U64) as u32,
                ((j as u64 * 333_777_888 + 7) % BABYBEAR_PRIME_U64) as u32,
            ])
        })
        .collect();
    let eq_bb = qwen35audit::ext4::build_eq_table_lsb_ext4(&tau_bb);
    let mut raw_sum = BbExt4::ZERO;
    for i in 0..n_bb {
        raw_sum = raw_sum.add(
            eq_bb[i]
                .mul(BbExt4::from_bb(a_vals[i]))
                .mul(BbExt4::from_bb(b_vals[i])),
        );
    }
    let coeff0 = ((eq_bb[0].0[0] as u64 * b_vals[0] as u64) % BABYBEAR_PRIME_U64) as u32;
    assert_ne!(coeff0, 0);
    let inv_coeff0 = qwen35audit::ext4::binv(coeff0).expect("invert coeff0 mod p_BB");
    let neg_sum0 = (BABYBEAR_PRIME_U64 - raw_sum.0[0] as u64) % BABYBEAR_PRIME_U64;
    let delta_a0 = ((neg_sum0 * inv_coeff0 as u64) % BABYBEAR_PRIME_U64) as u32;
    a_vals[0] = ((a_vals[0] as u64 + delta_a0 as u64) % BABYBEAR_PRIME_U64) as u32;

    // Commit `W_bb = (A_bb, B_bb)` under public dual Canopy (`Stage0MatrixCanopy`, `w_bb_p2_root` + `w_bb_cs_root`)!
    let w_bb_comm = BabyBearWitnessCommitment::commit(m_rounds, &a_vals, &b_vals)
        .expect("commit W_bb witness table in Stage0MatrixCanopy");

    let mut tau_arr = [BbExt4::ZERO; HEM_MAX_BB_ROUNDS];
    tau_arr[..m_rounds].copy_from_slice(&tau_bb[..m_rounds]);
    let mut verifier_init_claim = BbExt4::ZERO;
    for i in 0..n_bb {
        verifier_init_claim = verifier_init_claim.add(
            eq_bb[i]
                .mul(BbExt4::from_bb(a_vals[i]))
                .mul(BbExt4::from_bb(b_vals[i])),
        );
    }
    assert_eq!(
        verifier_init_claim.0[0], 0,
        "M3 fixture: initial_claim.0[0] == 0"
    );

    let bb_transcript = prove_child_babybear_ext4_cubic_sumcheck(
        m_rounds,
        vk,
        &w_bb_comm,
        &payload_comm,
        &a_vals,
        &b_vals,
        &tau_bb,
    )
    .expect("prove real 6-round cubic BabyBear Ext4 sumcheck");
    assert_eq!(bb_transcript.initial_claim, verifier_init_claim);

    // 5. Honest trustless prover (`pin_mode = false`, `k_mac = None`) proves BOTH BabyBear Ext4 sumcheck
    //    + in-circuit `eq(tau, r) * A_bb(r) * B_bb(r) == claim_m` against `W_bb` AND `Absent("sk-")` DFA
    //    algebraically inside `GoldilocksExt4` + `[0, 2^16)` LogUp + `UD-100` BaseFold:
    let t_prove = Instant::now();
    let bundle = prove_trustless_nonnative_babybear_and_dfa_hem(
        vk,
        &w_bb_comm,
        &payload_comm,
        &bb_transcript,
    )
    .expect("prove trustless UD-100 non-native BabyBear + W_bb(r) + DFA OP_HEM stream");
    let prove_ms = t_prove.elapsed().as_secs_f64() * 1000.0;

    // 6. Compute keyless `public_program_hash` from `stmt` ALONE (zero witness, zero `K_MAC`, `pin_mode = false`)!
    let expected_prog_hash = compute_expected_trustless_program_hash(&bundle.stmt)
        .expect("compute keyless program hash");
    assert_eq!(expected_prog_hash, bundle.public_program_hash);

    // 7. Standalone trustless verification inside `< 16 KiB` `Dregg180StreamVm` with ZERO heap allocations
    //    across full-slice, `48 B` SPI `RX_CREDIT_OK` bursts, AND `1 B` streaming (scoped to VM streaming with
    //    precomputed trusted `expected_prog_hash` per `L1`):
    HEAP_ALLOC_COUNT.store(0, Ordering::SeqCst);
    let t_ver = Instant::now();
    let mut vm_full = Dregg180StreamVm::new_unkeyed_pinned_program(expected_prog_hash);
    let verdict_full = vm_full
        .verify_stream(&bundle.wire_bytes)
        .expect("trustless UD-100 full-slice verify");
    let ver_ms = t_ver.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(
        HEAP_ALLOC_COUNT.load(Ordering::SeqCst),
        0,
        "Trustless UD-100 Dregg180StreamVm MUST perform 0 heap allocations (full slice)!"
    );
    assert!(verdict_full.accepted && verdict_full.zk_pin.is_none());
    assert_eq!(
        verdict_full.program_digest_gf128, 0,
        "NO K_MAC / pin_mode = false"
    );
    assert_eq!(verdict_full.public_program_hash, expected_prog_hash);

    HEAP_ALLOC_COUNT.store(0, Ordering::SeqCst);
    let mut vm_spi48 = Dregg180StreamVm::new_unkeyed_pinned_program(expected_prog_hash);
    for chunk48 in bundle.wire_bytes.chunks(48) {
        vm_spi48.feed_bytes(chunk48).expect("48B SPI burst feed");
    }
    let verdict_spi48 = vm_spi48.finalize().expect("48B SPI burst finalize");
    assert_eq!(
        HEAP_ALLOC_COUNT.load(Ordering::SeqCst),
        0,
        "0 heap allocs on 48B SPI feed!"
    );
    assert_eq!(verdict_full, verdict_spi48);

    HEAP_ALLOC_COUNT.store(0, Ordering::SeqCst);
    let mut vm_1b = Dregg180StreamVm::new_unkeyed_pinned_program(expected_prog_hash);
    for chunk1 in bundle.wire_bytes.chunks(1) {
        vm_1b.feed_bytes(chunk1).expect("1B stream feed");
    }
    let verdict_1b = vm_1b.finalize().expect("1B stream finalize");
    assert_eq!(
        HEAP_ALLOC_COUNT.load(Ordering::SeqCst),
        0,
        "0 heap allocs on 1B feed!"
    );
    assert_eq!(verdict_full, verdict_1b);

    // 8. Standalone `verify_trustless_dregg180_hem_stream` using verifier-owned expected statement &
    //    verifier-owned canonical VK (`H4`) — ZERO host callback, ZERO `Option` terminal oracle!
    let expected_clean = VerifierExpectedTrustlessStatement {
        bb_num_rounds: m_rounds,
        bb_tau: tau_arr,
        bb_initial_claim: verifier_init_claim,
        w_bb_p2_root: w_bb_comm.p2_root(),
        w_bb_cs_root: w_bb_comm.cshake_root(),
        bytes_p2_root: payload_comm.p2_root(),
        bytes_cs_root: payload_comm.cshake_root(),
    };
    let verdict_api =
        verify_trustless_dregg180_hem_stream(&expected_clean, &bundle.stmt, &bundle.wire_bytes)
            .expect(
                "verify_trustless_dregg180_hem_stream (100% self-contained on Dregg180StreamVm)",
            );
    assert_eq!(verdict_full, verdict_api);

    let m = verdict_full.metrics;
    println!(
        "[W10-UD100-TRUSTLESS] VK={:.2} ms, Prove={:.2} ms, VM Verify={:.2} ms (0 heap allocs, sizeof(VM)={} B <= 16384 B)",
        vk_ms, prove_ms, ver_ms, vm_bytes
    );
    println!(
        "[W10-UD100-METRICS] stream={} B ({:.2} KiB), records={}, core_cycles={} ({:.2} ms @25MHz), P2_perms={}, Keccak_perms={}, Ext4_muls={}, P2_Canopy={}, cSHAKE_Canopy={}, imm_words={}, proof_words={}",
        bundle.wire_bytes.len(),
        bundle.wire_bytes.len() as f64 / 1024.0,
        m.records_executed,
        m.core_cycles,
        m.latency_ms_at_mhz(25.0),
        m.poseidon2_perms,
        m.keccak_perms,
        m.ext4_muls,
        m.canopy_p2_nodes,
        m.canopy_cshake_nodes,
        m.immediate_words,
        m.proof_words
    );

    // ============================================================================================
    // Untrusted-Prover (NO `K_MAC`, `pin_mode = false`, ZERO host callback) Falsifier Suite!
    // Every VM falsifier asserts the EXACT intended rejection boundary (`M3` fix: not just `.is_err()`)!
    // ============================================================================================
    let assert_vm_algebraic_reject = |name: &str, res: Result<_, String>| {
        let err = res.expect_err(&format!(
            "Falsifier {name} MUST be rejected by trustless UD-100 Dregg180StreamVm without K_MAC!"
        ));
        assert!(
            err.contains("Dregg180StreamVm trustless UD-100 rejection: Rejected {")
                && err.contains("non_canonical_word: false")
                && err.contains("program_digest_mismatch: false"),
            "Falsifier {name} rejected for wrong reason: {err}"
        );
        println!("[W10-FALSIFIER-PASS] {name} -> VM_REJECTED ({err})");
    };

    let clean_tampers = [
        (
            "WrongBabyBearRoundSum",
            TrustlessHemTamper::WrongBabyBearRoundSum,
        ),
        (
            "WrongBabyBearHornerEval",
            TrustlessHemTamper::WrongBabyBearHornerEval,
        ),
        (
            "NonCanonicalBabyBearAliasGtPbb",
            TrustlessHemTamper::NonCanonicalBabyBearAliasGtPbb,
        ),
        (
            "NonCanonicalBabyBearExactPbbAlias",
            TrustlessHemTamper::NonCanonicalBabyBearExactPbbAlias,
        ),
        (
            "WrongBabyBearQuotient",
            TrustlessHemTamper::WrongBabyBearQuotient,
        ),
        (
            "ForgedRange16Multiplicity",
            TrustlessHemTamper::ForgedRange16Multiplicity,
        ),
        (
            "TamperedStage1BaseFoldFiber",
            TrustlessHemTamper::TamperedStage1BaseFoldFiber,
        ),
        (
            "TamperedStage0CShakeSibling",
            TrustlessHemTamper::TamperedStage0CShakeSibling,
        ),
    ];
    for (name, tamper) in clean_tampers {
        let forged =
            prove_trustless_hem_with_tamper(vk, &w_bb_comm, &payload_comm, &bb_transcript, tamper)
                .expect("adversarial prover builds tampered stream");
        let res =
            verify_trustless_dregg180_hem_stream(&expected_clean, &forged.stmt, &forged.wire_bytes);
        assert_vm_algebraic_reject(name, res);
    }

    // ============================================================================================
    // MANDATORY #211 FALSIFIER: Fake `W_bb` Witness Table Same-Sum Attack (ZERO Host Callback!)
    // Cheating prover builds `(A_fake, B_fake)` with `A_fake[0] = 2*A[0]`, `B_fake[0] = inv2*B[0]`:
    //   - `A_fake[x]*B_fake[x] == A[x]*B[x]` on every hypercube point -> IDENTICAL `bb_initial_claim`!
    //   - Prover runs a 100% INTERNALLY CONSISTENT 6-round cubic `BabyBear Ext4` sumcheck over `(A_fake, B_fake)`!
    //   - Yet `w_bb_p2_root` / `w_bb_cs_root` stay pinned to honest `w_bb_comm` -> `Dregg180StreamVm` MUST REJECT
    //     under BOTH cheating strategies (honest `r_val` -> terminal `sel_eq` fails; forged `r_val` -> `C_wbb` fails)!
    // ============================================================================================
    let mut a_fake = a_vals.clone();
    let mut b_fake = b_vals.clone();
    a_fake[0] = ((a_fake[0] as u64 * 2) % BABYBEAR_PRIME_U64) as u32;
    b_fake[0] =
        ((b_fake[0] as u64 * qwen35audit::ext4::INV2_BB as u64) % BABYBEAR_PRIME_U64) as u32;
    assert_ne!(a_fake[0], a_vals[0]);
    let fake_bb_tr = prove_child_babybear_ext4_cubic_sumcheck(
        m_rounds,
        vk,
        &w_bb_comm,
        &payload_comm,
        &a_fake,
        &b_fake,
        &tau_bb,
    )
    .expect("cheating prover runs internally consistent sumcheck over fake witness table");
    assert_eq!(
        fake_bb_tr.initial_claim, verifier_init_claim,
        "same bb_initial_claim on fake table!"
    );
    assert_ne!(
        fake_bb_tr.expected_terminal_eval, bb_transcript.expected_terminal_eval,
        "fake table has different off-hypercube MLE evaluation A_fake(r)*B_fake(r) != A_honest(r)*B_honest(r)"
    );
    // Strategy A: prover leaves honest `w_bb` in `r_val[32..]` -> terminal `sel_eq` fails inside `Dregg180StreamVm`!
    let fake_bundle_a =
        prove_trustless_nonnative_babybear_and_dfa_hem(vk, &w_bb_comm, &payload_comm, &fake_bb_tr)
            .expect("build fake-table Strategy A stream");
    let res_fake_a = verify_trustless_dregg180_hem_stream(
        &expected_clean,
        &fake_bundle_a.stmt,
        &fake_bundle_a.wire_bytes,
    );
    assert_vm_algebraic_reject("FakeWitnessTableSameSum_TerminalWeld", res_fake_a);

    // Strategy B: prover overrides `r_val[32..]` with `fake_w_bb` so ALL MACs & terminal `sel_eq` pass locally,
    // while Stage-0 Canopy opens pinned `w_bb_comm` -> `C_wbb = sel_wbb * (r_val - w_bb)` fails inside `Dregg180StreamVm`!
    let fake_w_bb_comm =
        BabyBearWitnessCommitment::commit(m_rounds, &a_fake, &b_fake).expect("commit fake table");
    let fake_bundle_b = prove_trustless_hem_with_wbb_override(
        vk,
        &w_bb_comm,
        &fake_w_bb_comm.w_bb_col,
        &payload_comm,
        &fake_bb_tr,
        TrustlessHemTamper::None,
    )
    .expect("build fake-table Strategy B stream");
    let res_fake_b = verify_trustless_dregg180_hem_stream(
        &expected_clean,
        &fake_bundle_b.stmt,
        &fake_bundle_b.wire_bytes,
    );
    assert_vm_algebraic_reject("FakeWitnessTableSameSum_CanopyBinding", res_fake_b);

    // Strategy C: non-canonical `W_bb` committed entry `== p_BB` (alias of 0) -> canonical slack `r_val + d_val = p_BB - 1` fails!
    let mut a_noncanon_u64: Vec<u64> = a_vals.iter().map(|&x| x as u64).collect();
    let b_u64: Vec<u64> = b_vals.iter().map(|&x| x as u64).collect();
    a_noncanon_u64[1] = BABYBEAR_PRIME_U64; // exact `p_BB` alias of 0!
    let noncanon_w_bb =
        BabyBearWitnessCommitment::commit_unchecked_raw(m_rounds, &a_noncanon_u64, &b_u64)
            .expect("commit unchecked non-canonical W_bb");
    let mut a_zero1 = a_vals.clone();
    a_zero1[1] = 0;
    let noncanon_tr = prove_child_babybear_ext4_cubic_sumcheck(
        m_rounds,
        vk,
        &noncanon_w_bb,
        &payload_comm,
        &a_zero1,
        &b_vals,
        &tau_bb,
    )
    .expect("prove sumcheck for aliased table");
    let noncanon_expected = VerifierExpectedTrustlessStatement {
        bb_num_rounds: m_rounds,
        bb_tau: tau_arr,
        bb_initial_claim: noncanon_tr.initial_claim,
        w_bb_p2_root: noncanon_w_bb.p2_root(),
        w_bb_cs_root: noncanon_w_bb.cshake_root(),
        bytes_p2_root: payload_comm.p2_root(),
        bytes_cs_root: payload_comm.cshake_root(),
    };
    let noncanon_bundle = prove_trustless_nonnative_babybear_and_dfa_hem(
        vk,
        &noncanon_w_bb,
        &payload_comm,
        &noncanon_tr,
    )
    .expect("build non-canonical W_bb stream");
    let res_noncanon_wbb = verify_trustless_dregg180_hem_stream(
        &noncanon_expected,
        &noncanon_bundle.stmt,
        &noncanon_bundle.wire_bytes,
    );
    assert_vm_algebraic_reject("NonCanonicalCommittedWbbEntry", res_noncanon_wbb);

    // Secret `"sk-"` leak falsifiers on a committed payload containing `"sk-live-999"`:
    let leaked_payload =
        b"Assistant output accidentally leaked api_key=sk-live-999888777 in plaintext!";
    assert_eq!(run_no_sk_dash_dfa_4state(leaked_payload).0, 3);
    let leaked_comm =
        PayloadBytesCommitment::commit(leaked_payload).expect("commit leaked payload");
    let leaked_bb_tr = prove_child_babybear_ext4_cubic_sumcheck(
        m_rounds,
        vk,
        &w_bb_comm,
        &leaked_comm,
        &a_vals,
        &b_vals,
        &tau_bb,
    )
    .expect("prove child sumcheck against leaked payload commitment");
    let expected_leaked = VerifierExpectedTrustlessStatement {
        bb_num_rounds: m_rounds,
        bb_tau: tau_arr,
        bb_initial_claim: verifier_init_claim,
        w_bb_p2_root: w_bb_comm.p2_root(),
        w_bb_cs_root: w_bb_comm.cshake_root(),
        bytes_p2_root: leaked_comm.p2_root(),
        bytes_cs_root: leaked_comm.cshake_root(),
    };

    // Honest prover refuses `"sk-"` payload:
    assert!(
        prove_trustless_nonnative_babybear_and_dfa_hem(vk, &w_bb_comm, &leaked_comm, &leaked_bb_tr)
            .is_err(),
        "Honest prover must refuse payload reaching DFA sink state 3"
    );

    // Untrusted prover trying ALL 3 ways to sneak `"sk-"` past the DFA circuit -> ALL 3 VM-REJECTED!
    for (name, tamper) in [
        (
            "ForgedDfaTerminalState",
            TrustlessHemTamper::ForgedDfaTerminalState,
        ),
        (
            "ForgedDfaTransitionBypass",
            TrustlessHemTamper::ForgedDfaTransitionBypass,
        ),
        (
            "ForgedDfaShiftBreak",
            TrustlessHemTamper::ForgedDfaShiftBreak,
        ),
    ] {
        let forged =
            prove_trustless_hem_with_tamper(vk, &w_bb_comm, &leaked_comm, &leaked_bb_tr, tamper)
                .expect("adversarial prover builds forged sk- stream");
        let res = verify_trustless_dregg180_hem_stream(
            &expected_leaked,
            &forged.stmt,
            &forged.wire_bytes,
        );
        assert_vm_algebraic_reject(name, res);
    }

    // Cross-payload splice: untrusted prover proves clean payload but submits against `leaked_comm` expected roots!
    let res_splice =
        verify_trustless_dregg180_hem_stream(&expected_leaked, &bundle.stmt, &bundle.wire_bytes)
            .expect_err("Cross-payload root splice MUST be rejected!");
    assert!(
        res_splice.contains("payload Canopy roots"),
        "wrong splice err: {res_splice}"
    );
    println!("[W10-FALSIFIER-PASS] CrossPayloadRootSplice -> REJECTED ({res_splice})");

    // Cross-W_bb root splice: submit honest proof against `fake_w_bb_comm` expected roots -> REJECTED!
    let mut bad_wbb_stmt = bundle.stmt;
    bad_wbb_stmt.w_bb_p2_root = fake_w_bb_comm.p2_root();
    let err_wbb_splice =
        verify_trustless_dregg180_hem_stream(&expected_clean, &bad_wbb_stmt, &bundle.wire_bytes)
            .expect_err("Cross-W_bb root splice MUST be rejected!");
    assert!(
        err_wbb_splice.contains("W_bb Canopy roots"),
        "wrong W_bb splice err: {err_wbb_splice}"
    );
    println!("[W10-FALSIFIER-PASS] CrossWbbRootSplice -> REJECTED ({err_wbb_splice})");

    // H4 regression: forged VK roots in statement rejected against verifier-owned canonical VK!
    let mut bad_vk_stmt = bundle.stmt;
    bad_vk_stmt.vk_p2_root[0] = (bad_vk_stmt.vk_p2_root[0] + 1) % GOLDILOCKS_PRIME;
    let err_h4 =
        verify_trustless_dregg180_hem_stream(&expected_clean, &bad_vk_stmt, &bundle.wire_bytes)
            .expect_err("H4 forged VK root MUST be rejected!");
    assert!(
        err_h4.contains("verifier-owned canonical VK"),
        "H4 wrong err: {err_h4}"
    );
    println!("[W10-FALSIFIER-PASS] H4_ForgedVkRoot -> REJECTED ({err_h4})");

    // L3 regression: non-canonical (`>= GOLDILOCKS_PRIME`) public Poseidon root limb rejected at ingress!
    let mut noncanon_stmt = bundle.stmt;
    noncanon_stmt.bytes_p2_root[0] = GOLDILOCKS_PRIME;
    let err_l3_hash = compute_expected_trustless_program_hash(&noncanon_stmt).expect_err(
        "L3 non-canonical public root MUST fail compute_expected_trustless_program_hash",
    );
    assert!(
        err_l3_hash.contains("non-canonical Goldilocks limb"),
        "L3 wrong err: {err_l3_hash}"
    );
    let err_l3_ver =
        verify_trustless_dregg180_hem_stream(&expected_clean, &noncanon_stmt, &bundle.wire_bytes)
            .expect_err("L3 non-canonical public root MUST fail verifier ingress");
    assert!(
        err_l3_ver.contains("non-canonical Goldilocks limb"),
        "L3 wrong err: {err_l3_ver}"
    );
    println!("[W10-FALSIFIER-PASS] L3_NonCanonicalPublicRoot -> REJECTED ({err_l3_ver})");

    // L2 regression: unarmed `H_MERKLE` (no preceding `H_BIND_IDX`) MUST fail closed!
    let mut asm_unarmed = Dregg180HvmAssembler::new(OP_HEM, false, false);
    let key4 = [1u64, 2, 3, 4];
    let l0 = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, key4, &[10, 20, 30, 40]);
    let l1 = p2_sponge_hash_limbs(P2_DOMAIN_FS_ABSORB_LIMBS, key4, &[50, 60, 70, 80]);
    let r_can = p2_canopy_node(l0, l1, [1, 2, 3], 1);
    asm_unarmed.load(R_B, &r_can, true);
    asm_unarmed.load(R_A, &key4, true);
    asm_unarmed.load(R_X, &l0, false);
    asm_unarmed.merkle(R_A, 0, &[l1]); // valid path, but `idx_armed == false`!
    asm_unarmed.assert_eq(R_X, R_B);
    let (unarmed_wire, _) = asm_unarmed.build_wire_bytes_and_pdig(None);
    let mut vm_l2 = Dregg180StreamVm::new_unkeyed(None);
    assert!(
        matches!(
            vm_l2.verify_stream(&unarmed_wire),
            Err(Dregg180StreamError::Rejected { .. })
        ),
        "L2 regression: unarmed H_MERKLE without H_BIND_IDX must fail closed!"
    );
    println!("[W10-FALSIFIER-PASS] L2_UnarmedMerkle -> VM_REJECTED");

    // ============================================================================================
    // C1 Regression (Unit + Live Wire Splice): Additive-Sum Collision Defeated by `BF_AUX_COMPRESS_REG`!
    // ============================================================================================
    let v1 = [100u64, 200, 300, 400];
    let v2 = [500u64, 600, 700, 800];
    let v1_alt = [101u64, 200, 300, 400]; // `+1`
    let v2_alt = [499u64, 600, 700, 800]; // `-1` -> SAME sum `v1 + v2 == v1_alt + v2_alt`!
    let d_honest = p2_ordered_compress(p2_ordered_compress([0; 4], v1, 1), v2, 2);
    let d_alt = p2_ordered_compress(p2_ordered_compress([0; 4], v1_alt, 1), v2_alt, 2);
    assert_ne!(
        d_honest, d_alt,
        "C1 fix: ordered Davies-Meyer compress must separate equal-sum pairs"
    );
    let mut asm_c1 = Dregg180HvmAssembler::new(OP_HEM, false, false);
    asm_c1.load(R_A, &[0, 0, 0, 0], true);
    asm_c1.load(R_X, &v1, false);
    asm_c1.bf_compress_reg(R_A, R_A, R_X, 1);
    asm_c1.load(R_X, &v2, false);
    asm_c1.bf_compress_reg(R_A, R_A, R_X, 2);
    asm_c1.load(R_B, &[0, 0, 0, 0], true);
    asm_c1.load(R_X, &v1_alt, false);
    asm_c1.bf_compress_reg(R_B, R_B, R_X, 1);
    asm_c1.load(R_X, &v2_alt, false);
    asm_c1.bf_compress_reg(R_B, R_B, R_X, 2);
    asm_c1.assert_eq(R_A, R_B);
    let (c1_unit_wire, _) = asm_c1.build_wire_bytes_and_pdig(None);
    let mut vm_c1 = Dregg180StreamVm::new_unkeyed(None);
    assert!(
        matches!(
            vm_c1.verify_stream(&c1_unit_wire),
            Err(Dregg180StreamError::Rejected { .. })
        ),
        "C1 unit regression: VM BF_AUX_COMPRESS_REG must reject equal-sum pair collision!"
    );

    // Live wire-level C1 splice & H1 structural + live wire splice directly on `bundle.wire_bytes`!
    let words: Vec<u64> = bundle
        .wire_bytes
        .chunks_exact(8)
        .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
        .collect();
    let mut pos = 1usize; // skip wire_hdr
    let mut pass2_load_word_offsets: Vec<usize> = Vec::new();
    let mut pow_t1_nonce_offsets: Vec<usize> = Vec::new();
    let mut pow_t2_nonce_offsets: Vec<usize> = Vec::new();
    let mut saw_t1_assert_pow = false;
    let mut saw_t2_assert_pow = false;
    let mut prev_pow_domain: Option<u64> = None;

    while pos < words.len() {
        let hdr = words[pos];
        let hop = (hdr & 0xFF) as u8;
        let a = ((hdr >> 8) & 0xFF) as u8;
        let b = ((hdr >> 16) & 0xFF) as u8;
        let c = ((hdr >> 24) & 0xFF) as u8;
        let n = ((hdr >> 32) & 0xFFFF) as usize;
        let k = ((hdr >> 48) & 0xFFFF) as usize;
        let data_start = pos + 1;
        if hop == H_LOAD && n == 4 && k == 3 && pass2_load_word_offsets.len() < 2 {
            pass2_load_word_offsets.push(data_start + 3);
        }
        if hop == H_HASH && n == 3 && k == 1 {
            let dom = words[data_start];
            if dom == P2_DOMAIN_FS_POW_T1 {
                assert_eq!(
                    a, R_CH,
                    "H1 invariant: T1 PoW hash MUST write directly to R_CH"
                );
                pow_t1_nonce_offsets.push(data_start + 1);
                prev_pow_domain = Some(P2_DOMAIN_FS_POW_T1);
            } else if dom == P2_DOMAIN_FS_POW_T2 {
                assert_eq!(
                    a, R_CH,
                    "H1 invariant: T2 PoW hash MUST write directly to R_CH"
                );
                pow_t2_nonce_offsets.push(data_start + 1);
                prev_pow_domain = Some(P2_DOMAIN_FS_POW_T2);
            } else {
                prev_pow_domain = None;
            }
        } else if hop == H_ASSERT_POW && b == R_CH && c == UD100_POW_BITS {
            if prev_pow_domain == Some(P2_DOMAIN_FS_POW_T1) {
                saw_t1_assert_pow = true;
            } else if prev_pow_domain == Some(P2_DOMAIN_FS_POW_T2) {
                saw_t2_assert_pow = true;
            }
            prev_pow_domain = None;
        } else {
            prev_pow_domain = None;
        }
        pos = data_start + n;
    }
    assert_eq!(
        pass2_load_word_offsets.len(),
        2,
        "must locate Pass 2 replay loads"
    );
    assert_eq!(
        pow_t1_nonce_offsets.len(),
        1,
        "H1 invariant: exactly 1 T1 PoW nonce record"
    );
    assert_eq!(
        pow_t2_nonce_offsets.len(),
        1,
        "H1 invariant: exactly 1 T2 PoW nonce record"
    );
    assert!(
        saw_t1_assert_pow && saw_t2_assert_pow,
        "H1 invariant: H_ASSERT_POW(R_CH, 16) immediately follows single PoW hash"
    );

    // C1 live wire splice: perturb two Pass-2 replayed proof words by `+1` / `-1` (same program hash!):
    let mut c1_spliced = words.clone();
    let o0 = pass2_load_word_offsets[0];
    let o1 = pass2_load_word_offsets[1];
    c1_spliced[o0] = (c1_spliced[o0] + 1) % GOLDILOCKS_PRIME;
    c1_spliced[o1] = (c1_spliced[o1] + GOLDILOCKS_PRIME - 1) % GOLDILOCKS_PRIME;
    let c1_wire: Vec<u8> = c1_spliced.iter().flat_map(|w| w.to_le_bytes()).collect();
    let res_c1_wire = verify_trustless_dregg180_hem_stream(&expected_clean, &bundle.stmt, &c1_wire);
    assert_vm_algebraic_reject("C1_LiveWireReplaySplice", res_c1_wire);

    // H1 live wire splice: flip 1 bit in the single T1 PoW nonce proof word (same program hash!):
    let mut h1_spliced = words;
    h1_spliced[pow_t1_nonce_offsets[0]] ^= 1;
    let h1_wire: Vec<u8> = h1_spliced.iter().flat_map(|w| w.to_le_bytes()).collect();
    let res_h1_wire = verify_trustless_dregg180_hem_stream(&expected_clean, &bundle.stmt, &h1_wire);
    assert_vm_algebraic_reject("H1_LiveWirePowNonceSplice", res_h1_wire);
}
