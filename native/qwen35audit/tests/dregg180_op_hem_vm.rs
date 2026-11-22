//! End-to-End Conformance, `< 16 KiB` Zero-Heap Silicon VM Benchmark, & 10+ Adversarial
//! Falsifier Suite for Wearable SHE Organ #1 (`qwen35audit::dregg180_hem_bridge`).
#![deny(warnings)]

use qwen35audit::dregg180_hem_bridge::{
    bridge_wearable_she_bundle_to_dregg180_stream, cshake256_canopy_node, fp5_mul, gf128_mul,
    p2_canopy_node, p2_canopy_path, p2_sponge12_rate6, p2_sponge_hash_limbs, pack_bytes_7_limbs,
    poseidon2_perm12, turboshake256_32_stack, DeferredLeafClaim, DeferredLeafKind,
    Dregg180HvmAssembler, Dregg180StreamError, Dregg180StreamVm, Goldilocks, GoldilocksExt4,
    SimplexFinCertLeafReceipt, Tower256AbsentLeafReceipt, WearableQwenWhirLeafReceipt,
    DREGG180_VM_MAX_STATIC_BYTES, FS_INIT_CAP, GOLDILOCKS_PRIME, OP_FOLD, OP_HEM,
    P2_DOMAIN_FS_ABSORB_LIMBS, R_A, R_B, R_CH, R_T0, R_X, R_Y,
};
use std::alloc::{GlobalAlloc, Layout, System};
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
    assert!(vm_bytes < 4_096, "Dregg180StreamVm fits in < 4 KiB (< 25% of 16 KiB budget)");

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
    assert_eq!(GoldilocksExt4::V.pow(4), GoldilocksExt4::from_base(Goldilocks(7)));

    let x2 = GoldilocksExt4::from_u64_limbs([18_446_744_069_414_584_320, 4_294_967_295, 4_294_967_296, 7]);
    let y2 = GoldilocksExt4::from_u64_limbs([14_627_333_965_257_922_168, 1_147_797_409_030_816_545, 42, 99]);
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
    assert_eq!(&ts_empty[0..8], &[0x36, 0x7a, 0x32, 0x9d, 0xaf, 0xea, 0x87, 0x1c]);
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
    let verdict5 = vm5.verify_stream(&wire5).expect("Fp5 zk-Hem v2 stream must verify");
    assert!(verdict5.accepted && verdict5.zk_pin.is_some());
}

#[test]
fn test_wearable_she_heterogeneous_bundle_e2e_zero_heap_stream_and_adversarial_suite() {
    let lease_id = [0x91u8; 32];
    let clean_msg = b"Wearable SHE Organ #1 clean assistant summary: ToF=1.18m, HR=64bpm, status=ok.";

    // 1. Prove the 3 heterogeneous child receipts across `BabyBear Ext4`, `Tower256`, and `Simplex`:
    let t_leaves = Instant::now();
    let qwen_leaf = WearableQwenWhirLeafReceipt::prove(lease_id, clean_msg, [0x11u8; 32])
        .expect("prove BabyBear Ext4 Qwen WhirExt4 leaf");
    let absent_leaf = Tower256AbsentLeafReceipt::prove(qwen_leaf.content_root, clean_msg, [0x22u8; 32])
        .expect("prove Tower256 Absent(\"sk-...\") leaf");
    let (kps, roster_root, roster_leaves) = SimplexFinCertLeafReceipt::build_committee(4, 0xC3);
    let qwen_dig = qwen_leaf.verify().unwrap();
    let absent_dig = absent_leaf.verify(&qwen_leaf.content_root).unwrap();
    let fincert_leaf = SimplexFinCertLeafReceipt::sign_quorum(
        4,
        1, // n = 4, f = 1 => quorum = n - f = 3
        9, // view = 9 > 0
        &kps,
        roster_root,
        &roster_leaves,
        &[0, 2, 3],
        qwen_leaf.content_root,
        qwen_dig,
        absent_dig,
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
        vm_spi48.feed_bytes(frame48).expect("48-byte SPI burst feed");
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
        matches!(vm.verify_stream(&bad_zero_wire), Err(Dregg180StreamError::Rejected { .. })),
        "Attack 1: 0-assertion LOAD R_CH stream must be rejected!"
    );

    // Attack 2: `LOAD R_CH` in `pin_mode = true` MUST be rejected!
    let mut asm_pin_ch = Dregg180HvmAssembler::new(OP_HEM, true, false);
    asm_pin_ch.load(R_CH, &[1, 2, 3, 4], false);
    asm_pin_ch.assert_eq(R_CH, R_CH);
    let (bad_pin_wire, bad_pin_pdig) = asm_pin_ch.build_wire_bytes_and_pdig(None);
    let mut vm = Dregg180StreamVm::new_unkeyed(Some(bad_pin_pdig));
    assert!(
        matches!(vm.verify_stream(&bad_pin_wire), Err(Dregg180StreamError::Rejected { .. })),
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
        Err(Dregg180StreamError::Rejected { non_canonical_word: true, .. }) => {}
        other => panic!("Attack 3: non-canonical Goldilocks alias must set non_canonical_word, got {other:?}"),
    }

    // Attack 4: Unabsorbed / swapped child `DeferredLeafClaim` immediate (`program_digest_mismatch`)!
    let mut forged_claims = compiled.leaf_claims;
    forged_claims[1].claim_digest[0] ^= 0xFF;
    let recompiled_forged = qwen35audit::dregg180_hem_bridge::compile_deferred_leaves_to_dregg180_hem_stream(
        forged_claims,
        false,
        Some(k_mac),
    )
    .unwrap();
    let mut vm = Dregg180StreamVm::new_keyed(k_mac, Some(compiled.pinned_program_digest));
    match vm.verify_stream(&recompiled_forged.wire_bytes) {
        Err(Dregg180StreamError::Rejected { program_digest_mismatch: true, .. }) => {}
        other => panic!("Attack 4: swapped DeferredLeafClaim immediate must fail pdig pin, got {other:?}"),
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
        matches!(vm.verify_stream(&idx_wire), Err(Dregg180StreamError::Rejected { .. })),
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
        4,
        1,
        9,
        &kps,
        roster_root,
        &roster_leaves,
        &[0, 2], // only 2 signers < quorum 3!
        qwen_leaf.content_root,
        qwen_dig,
        absent_dig,
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
        4,
        1,
        9,
        &kps,
        roster_root,
        &roster_leaves,
        &[0, 2, 2], // duplicate signer 2!
        qwen_leaf.content_root,
        qwen_dig,
        absent_dig,
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
    let other_qwen =
        WearableQwenWhirLeafReceipt::prove(lease_id, b"Different assistant output turn!", [0x44u8; 32])
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
