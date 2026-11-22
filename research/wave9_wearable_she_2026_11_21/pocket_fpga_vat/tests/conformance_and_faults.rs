#![forbid(unsafe_code)]
#![deny(warnings)]

use pocket_fpga_vat::*;

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

fn parse_hex_u64(json: &str, key: &str) -> Option<u64> {
    let pat = format!("\"{}\": \"0x", key);
    let start = json.find(&pat)? + pat.len();
    let end = start + json[start..].find('"')?;
    u64::from_str_radix(&json[start..end], 16).ok()
}

#[test]
fn lean_golden_vectors_and_crc64_bit_exact_parity() {
    let crc_gen1 = compute_fram_crc_tag(&GOLDEN_POLICY_DIGEST, 0, 0, 1);
    let crc_gen2 = compute_fram_crc_tag(&GOLDEN_POLICY_DIGEST, 42, 7, 2);
    assert_ne!(crc_gen1, 0);
    assert_ne!(crc_gen1, crc_gen2);

    let bs = vat_golden_bitstream();
    let trojan_pip = trojan_pip_bitstream();
    let trojan_lut = trojan_lut_bitstream();

    // If `LEAN_GOLDEN_JSON` is provided by `build_and_verify.sh`, cross-check live Lean kernel output!
    if let Ok(path) = std::env::var("LEAN_GOLDEN_JSON") {
        let txt = std::fs::read_to_string(&path).expect("failed to read LEAN_GOLDEN_JSON");
        assert_eq!(parse_hex_u64(&txt, "crc_epoch1_leaf0"), Some(crc_gen1));
        assert_eq!(parse_hex_u64(&txt, "crc_epoch2_leaf42"), Some(crc_gen2));
        for i in 0..8 {
            let key = format!("golden_bs_w{}", i);
            assert_eq!(parse_hex_u64(&txt, &key), Some(bs.w[i]), "mismatch on {key}");
        }
        assert_eq!(parse_hex_u64(&txt, "trojan_pip_w3"), Some(trojan_pip.w[3]));
        assert_eq!(parse_hex_u64(&txt, "trojan_pip_w7"), Some(trojan_pip.w[7]));
        assert_eq!(parse_hex_u64(&txt, "trojan_lut_w6"), Some(trojan_lut.w[6]));
        assert_eq!(parse_hex_u64(&txt, "trojan_lut_w7"), Some(trojan_lut.w[7]));
    }
}

#[test]
fn compromised_host_cannot_sign_without_touch_and_tof_fuzz() {
    let base_policy = CapPolicyRegs {
        rights_mask: 0xFFFF,
        guards_mask: GUARD_STATEFUL_FRAM | GUARD_PHYS_TOUCH | GUARD_TOF_DIST,
        max_tof_cycles: 64,
        epoch_floor: 10,
        epoch_ceil: 100,
        spend_limit: 1_000,
        spend_used: 0,
        policy_digest: GOLDEN_POLICY_DIGEST,
    };
    let secret = SecretKeyRegs {
        k0: 0xDEAD_BEEF_CAFE_BAB1,
        k1: 0x1234_5678_9ABC_DEF0,
        k2: 0x0FED_CBA9_8765_4321,
        k3: 0xA5A5_5A5A_F0F0_0F0F,
    };

    let mut rng = 0x51A7_E900_D180_0001u64;
    let mut st = init_vat_rtl_state(base_policy);

    // 10,000-cycle adversarial SPI command fuzzing from root-compromised ARM64 host OS
    // without simultaneous physical touch + ToF proximity.
    for _ in 0..10_000 {
        let r = xorshift64(&mut rng);
        let cmd = match r % 9 {
            0 => SPI_OP_KEY_LOAD,
            1 => SPI_OP_PREP_SIGN,
            2 => SPI_OP_FRAM_COMMIT,
            3 => SPI_OP_TRIGGER_SIGN,
            4 => SPI_OP_ATTENUATE,
            5 => SPI_OP_READ_DIAG,
            6 => SPI_OP_NOP,
            _ => (r >> 8) as u8,
        };
        // Adversarial presence configurations where `!(touch && tof)` holds:
        let (touch, tof) = match (r >> 16) % 3 {
            0 => (false, false),
            1 => (true, false),
            _ => (false, true),
        };
        let inp = VatCycleInput {
            spi_cmd_byte: cmd,
            spi_arg_word: (r >> 24) % 8,
            spi_candidate_policy: base_policy,
            spi_candidate_key: secret,
            req_epoch: 25,
            req_spend: 1,
            req_right_bit: 1,
            measured_tof_cycles: 16,
            fram_readback_ok: true,
            public_diag_bit: ((r >> 3) & 1) == 1,
            msg_challenge_bit: ((r >> 4) & 1) == 1,
            phys_touch_ack: touch,
            tof_within_radius: tof,
            tamper_canary_tripped: false,
        };
        let out = eval_vat_rtl_output(&st, &inp);
        assert!(
            !out.vat_sign_enable,
            "compromised host enabled signing without BOTH touch and ToF!"
        );
        assert_eq!(
            out.spi_miso, inp.public_diag_bit,
            "secret key leaked onto spi_miso while signing disabled!"
        );
        st = step_vat_rtl(&st, &inp);
    }

    // Verify `#tooth` software CSR override vulnerability vs hardware wire gate:
    let mut armed_st = st;
    armed_st.key_valid = true;
    armed_st.fsm = VatFsmState::SignArmed;
    let no_touch_inp = VatCycleInput {
        spi_cmd_byte: SPI_OP_NOP,
        spi_arg_word: 0,
        spi_candidate_policy: base_policy,
        spi_candidate_key: secret,
        req_epoch: 25,
        req_spend: 1,
        req_right_bit: 1,
        measured_tof_cycles: 16,
        fram_readback_ok: true,
        public_diag_bit: false,
        msg_challenge_bit: false,
        phys_touch_ack: false,
        tof_within_radius: false,
        tamper_canary_tripped: false,
    };
    assert!(broken_csr_sign_enable(true, &armed_st, &no_touch_inp));
    assert!(!vat_sign_enable(&armed_st, &no_touch_inp));
}

#[test]
fn one_cycle_tamper_zeroization_and_captp_attenuation_monotone() {
    let parent = CapPolicyRegs {
        rights_mask: 0x00FF,
        guards_mask: GUARD_STATEFUL_FRAM | GUARD_PHYS_TOUCH,
        max_tof_cycles: 80,
        epoch_floor: 10,
        epoch_ceil: 50,
        spend_limit: 100,
        spend_used: 0,
        policy_digest: GOLDEN_POLICY_DIGEST,
    };
    let legal_child = CapPolicyRegs {
        rights_mask: 0x000F,
        guards_mask: GUARD_STATEFUL_FRAM | GUARD_PHYS_TOUCH | GUARD_TOF_DIST,
        max_tof_cycles: 40,
        epoch_floor: 15,
        epoch_ceil: 40,
        spend_limit: 50,
        spend_used: 0,
        policy_digest: GOLDEN_POLICY_DIGEST,
    };
    assert!(attenuate_child_legal(&parent, &legal_child));

    // Guard-stripping child must be rejected!
    let stripped_guard_child = CapPolicyRegs {
        guards_mask: GUARD_STATEFUL_FRAM, // stripped GUARD_PHYS_TOUCH!
        ..legal_child
    };
    assert!(!attenuate_child_legal(&parent, &stripped_guard_child));

    // Rights-amplifying child must be rejected!
    let amplified_rights_child = CapPolicyRegs {
        rights_mask: 0x010F,
        ..legal_child
    };
    assert!(!attenuate_child_legal(&parent, &amplified_rights_child));

    // Provision key, arm sign with valid touch + ToF, then fire tamper canary:
    let secret = SecretKeyRegs {
        k0: 0xFFFF_FFFF_FFFF_FFFF,
        k1: 0xAAAA_AAAA_AAAA_AAAA,
        k2: 0x5555_5555_5555_5555,
        k3: 0x1111_2222_3333_4444,
    };
    let mk_inp = |cmd: u8, touch: bool, tof: bool, tamper: bool| VatCycleInput {
        spi_cmd_byte: cmd,
        spi_arg_word: 0,
        spi_candidate_policy: parent,
        spi_candidate_key: secret,
        req_epoch: 20,
        req_spend: 5,
        req_right_bit: 1,
        measured_tof_cycles: 20,
        fram_readback_ok: true,
        public_diag_bit: false,
        msg_challenge_bit: false,
        phys_touch_ack: touch,
        tof_within_radius: tof,
        tamper_canary_tripped: tamper,
    };

    let mut st = init_vat_rtl_state(parent);
    st = step_vat_rtl(&st, &mk_inp(SPI_OP_KEY_LOAD, false, false, false));
    assert_eq!(st.secret_key_regs, secret);
    st = step_vat_rtl(&st, &mk_inp(SPI_OP_PREP_SIGN, true, true, false));
    st = step_vat_rtl(&st, &mk_inp(SPI_OP_FRAM_COMMIT, true, true, false));
    st = step_vat_rtl(&st, &mk_inp(SPI_OP_TRIGGER_SIGN, true, true, false));
    assert_eq!(st.fsm, VatFsmState::SignArmed);
    assert!(vat_sign_enable(&st, &mk_inp(SPI_OP_NOP, true, true, false)));

    // Trip tamper canary while SignArmed: 0-cycle sign_enable drop + 1-cycle key zeroize!
    let trip_inp = mk_inp(SPI_OP_NOP, true, true, true);
    let trip_out = eval_vat_rtl_output(&st, &trip_inp);
    assert!(!trip_out.vat_sign_enable);
    assert!(trip_out.tamper_fault);

    let st_after_1clk = step_vat_rtl(&st, &trip_inp);
    assert_eq!(st_after_1clk.secret_key_regs, SecretKeyRegs::ZERO);
    assert_eq!(st_after_1clk.fsm, VatFsmState::DeadZeroized);
    assert!(st_after_1clk.tamper_latched);

    // Even after tamper clears and host tries KEY_LOAD + PREP + COMMIT + SIGN with touch & ToF:
    let recovery_attempt = [
        mk_inp(SPI_OP_KEY_LOAD, true, true, false),
        mk_inp(SPI_OP_PREP_SIGN, true, true, false),
        mk_inp(SPI_OP_FRAM_COMMIT, true, true, false),
        mk_inp(SPI_OP_TRIGGER_SIGN, true, true, false),
        mk_inp(SPI_OP_NOP, true, true, false),
    ];
    let (outs, end_st) = run_vat_rtl_trace(st_after_1clk, &recovery_attempt);
    assert_eq!(end_st.secret_key_regs, SecretKeyRegs::ZERO);
    assert!(outs.iter().all(|o| !o.vat_sign_enable));
}

#[test]
fn exhaustive_0_to_512_bit_fram_power_cut_and_544_sck_wire_fuzzer() {
    let dual0 = genesis_dual_fram(GOLDEN_POLICY_DIGEST);
    let rec1 = mk_valid_fram_record(GOLDEN_POLICY_DIGEST, 1, 5, 2);
    let enc1 = encode_fram_slot(&rec1);

    // 1. Exhaustive bit-by-bit power-cut sweep `0..=512` on `slot0 -> slot1`:
    for cut_bit in 0..=512 {
        let torn_dual = write_standby_with_power_cut(&dual0, &enc1, cut_bit);
        let recovered = recover_dual_fram(&torn_dual)
            .expect("2-slot FRAM bricked on mid-bit power cut!");
        assert!(
            recovered.leaf_idx == 0 || recovered.leaf_idx == 1,
            "unexpected leaf_idx {} at cut_bit {}",
            recovered.leaf_idx,
            cut_bit
        );
        if cut_bit <= 384 {
            // Before `epoch_seq` (bits 384..447) starts writing, recovery MUST return old leaf 0!
            assert_eq!(recovered.leaf_idx, 0);
        } else if cut_bit == 512 {
            assert_eq!(recovered.leaf_idx, 1);
        }
    }

    // 2. Commit `slot1` (`epoch=2, leaf=10`), then exhaustively test `0..=512` on `slot1 -> slot0` (`epoch=3, leaf=11`):
    let dual1 = boot_resync_standby(&write_standby_with_power_cut(
        &dual0,
        &encode_fram_slot(&mk_valid_fram_record(GOLDEN_POLICY_DIGEST, 10, 5, 2)),
        512,
    ));
    assert_eq!(recover_dual_fram(&dual1).unwrap().leaf_idx, 10);
    let rec2 = mk_valid_fram_record(GOLDEN_POLICY_DIGEST, 11, 8, 3);
    let enc2 = encode_fram_slot(&rec2);
    for cut_bit in 0..=512 {
        let torn_dual = write_standby_with_power_cut(&dual1, &enc2, cut_bit);
        let recovered = recover_dual_fram(&torn_dual)
            .expect("2-slot FRAM bricked on reverse-direction cut!");
        assert!(recovered.leaf_idx >= 10, "leaf_idx regressed below 10 at cut_bit {cut_bit}");
    }

    // 3. Exhaustive SPI Mode-0 wire-clock cut `0..=544` (`WREN + WRITE + ADDR16 + 512b`):
    for sck_edge in 0..=544 {
        let mut dev = SpiFramDevice { dual: dual1 };
        dev.spi_write_standby_with_wire_cut(&rec2, sck_edge);
        let rec = recover_dual_fram(&dev.dual).expect("SPI wire power cut bricked FRAM!");
        assert!(rec.leaf_idx >= 10);
        if sck_edge == 544 {
            assert_eq!(rec.leaf_idx, 11);
        }
    }

    // 4. 5,000-step randomized multi-epoch power-cut & Cut-the-Hash leaf signing schedule:
    let mut rng = 0xCAFE_F00D_D180_5120u64;
    let mut events = Vec::with_capacity(5_000);
    let mut cur_leaf_target = 0u64;
    for _ in 0..5_000 {
        let r = xorshift64(&mut rng);
        if (r % 4) == 0 {
            events.push(FramPowerEvent::SignLeafComplete {
                req_leaf: cur_leaf_target,
                new_spend: r & 0xFF,
                new_policy: GOLDEN_POLICY_DIGEST,
            });
            cur_leaf_target += 1 + ((r >> 8) % 3);
        } else {
            let cut_bit = ((r >> 16) % 513) as usize;
            events.push(FramPowerEvent::InterruptedWrite {
                req_leaf: cur_leaf_target,
                new_spend: r & 0xFF,
                new_policy: GOLDEN_POLICY_DIGEST,
                cut_bit,
            });
        }
    }
    let (released_leaves, final_dual) = run_fram_events(dual0, &events);
    assert!(recover_dual_fram(&final_dual).is_some());
    assert!(released_leaves.len() > 1_000);
    assert!(
        released_leaves.windows(2).all(|w| w[0] < w[1]),
        "Cut-the-Hash one-time leaf reused or non-monotone across power cuts!"
    );

    // 5. Reproduce both `#tooth` vulnerabilities:
    // #tooth 2A: single-slot overwrite bricks at bit 288
    let single_old = encode_fram_slot(&mk_valid_fram_record(GOLDEN_POLICY_DIGEST, 5, 0, 1));
    let single_new = encode_fram_slot(&mk_valid_fram_record(GOLDEN_POLICY_DIGEST, 6, 0, 2));
    assert!(!fram_slot_valid(&tear_bits512(&single_old, &single_new, 288)));

    // #tooth 2B: commit-flag-before-payload rolls leaf 10 back to 3 at bit 64!
    let active_s0 = broken_commit_first_encode(2, 10);
    let standby_s1 = broken_commit_first_encode(1, 3);
    let next_s1 = broken_commit_first_encode(3, 11);
    let torn_s1 = tear_bits512(&standby_s1, &next_s1, 64);
    assert_eq!(broken_commit_first_recover(&active_s0, &standby_s1), 10);
    assert_eq!(broken_commit_first_recover(&active_s0, &torn_s1), 3);
}

#[test]
fn lut4_pip_bitstream_readback_equivalence_and_trojan_sweep() {
    let grid = vat_ordered_grid();
    let cert = vat_golden_cert();
    let golden_bs = vat_golden_bitstream();

    assert!(verify_vat_fabric_readback(&grid, &cert, &golden_bs));
    assert!(check_no_unauthorized_secret_pips(&grid, (1, 0), &golden_bs));
    assert!(check_semantic_miso_non_interference(&grid, &golden_bs));

    // 1. Exhaustive `16 x 512 = 8,192` cycle-step equivalence with `PocketCaptpVatRtl` core:
    for st_mask in 0u8..16 {
        let st = VatFabricState::from_mask(st_mask);
        for inp_mask in 0u16..512 {
            let inp = VatFabricInputs::from_mask(inp_mask);
            assert_eq!(
                eval_fabric_sign_enable(&grid, &golden_bs, &st, &inp),
                eval_vat_core_sign_enable(&st, &inp)
            );
            assert_eq!(
                eval_fabric_spi_miso(&grid, &golden_bs, &st, &inp),
                eval_vat_core_spi_miso(&st, &inp)
            );
            assert_eq!(
                step_fabric_state(&grid, &golden_bs, &st, &inp),
                step_vat_core_rtl(&st, &inp)
            );
        }
    }

    // 2. Multi-cycle cosimulation trace equivalence:
    let mut rng = 0x7788_99AA_BBCC_DDEEu64;
    let trace: Vec<VatFabricInputs> = (0..256)
        .map(|_| VatFabricInputs::from_mask((xorshift64(&mut rng) & 0x1FF) as u16))
        .collect();
    assert_eq!(
        run_fabric_trace(&grid, &golden_bs, VatFabricState::default(), &trace),
        run_vat_core_rtl_trace(VatFabricState::default(), &trace)
    );

    // 3. Exhaustive single-bit JTAG/SPI bitstream corruption sweep (`512 / 512` bits rejected):
    for bit_idx in 0..512 {
        let mut mutated = golden_bs;
        mutated.w[bit_idx / 64] ^= 1u64 << (bit_idx % 64);
        assert!(
            !verify_vat_fabric_readback(&grid, &cert, &mutated),
            "mutated bitstream bit {bit_idx} was accepted!"
        );
    }

    // 4. #tooth 3A: Subverted Routing-PIP Trojan exfiltrates `secret_key_reg` via spare tile X3Y0!
    let t_pip = trojan_pip_bitstream();
    let st_k0 = VatFabricState {
        tamper_latched: false,
        key_valid: true,
        secret_key_reg: false,
        sign_armed: false,
    };
    let st_k1 = VatFabricState {
        secret_key_reg: true,
        ..st_k0
    };
    let diag_inp = VatFabricInputs::default();
    assert!(!eval_fabric_sign_enable(&grid, &t_pip, &st_k1, &diag_inp));
    assert!(!eval_fabric_spi_miso(&grid, &t_pip, &st_k0, &diag_inp));
    assert!(eval_fabric_spi_miso(&grid, &t_pip, &st_k1, &diag_inp));
    assert!(!check_no_unauthorized_secret_pips(&grid, (1, 0), &t_pip));
    assert!(!check_semantic_miso_non_interference(&grid, &t_pip));
    assert!(!verify_vat_fabric_readback(&grid, &cert, &t_pip));

    // 5. #tooth 3B: Subverted LUT4-INIT Trojan keeps all PIPs valid (`check_no_unauthorized_secret_pips == true`),
    //    leaks `secret_key_reg` onto `spi_miso`, and is caught by `check_semantic_miso_non_interference` & `verify_vat_fabric_readback`!
    let t_lut = trojan_lut_bitstream();
    assert!(check_no_unauthorized_secret_pips(&grid, (1, 0), &t_lut));
    assert!(!eval_fabric_sign_enable(&grid, &t_lut, &st_k1, &diag_inp));
    assert!(!eval_fabric_spi_miso(&grid, &t_lut, &st_k0, &diag_inp));
    assert!(eval_fabric_spi_miso(&grid, &t_lut, &st_k1, &diag_inp));
    assert!(!check_semantic_miso_non_interference(&grid, &t_lut));
    assert!(!verify_vat_fabric_readback(&grid, &cert, &t_lut));
}
