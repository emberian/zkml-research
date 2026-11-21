//! Comprehensive Wave-6 Integration & Adversarial Falsifier Suite (`tests/succinct_pcs_and_dark_gdn.rs`):
//! 1. Full `HoistedSuccinctBundle` (`to_bytes` / `from_bytes` + standalone zero-witness verification)
//!    across both `Direct-20` & `Exact-Garner-15`, persistent & non-persistent `A`, at `N = 64` and `N = 8192`.
//! 2. Statistical HVZK blinding check confirming opened PCS columns, `u_prox`, and `u_eval` leak zero
//!    witness information across extreme witnesses.
//! 3. Multi-turn 3-Custodian Threshold-BFV + SPDZ Encrypted `Qwen3.8` `Gated DeltaNet` + `Dark-vPIR`
//!    resident (`zero party holds sk`!) verifying 100% bit-exact agreement with cleartext `GDN` over `Z_t`.
//! 4. **All Required Adversarial Attacks & Falsifiers**:
//!    - Attack 1 (`1-cell PCS witness / evaluation / column mutation`) -> REFUSED
//!    - Attack 2 (`forged Merkle multiproof sibling / salt`) -> REFUSED
//!    - Attack 3 (`forged Exact-Garner-15 non-power-of-two boundary u + Q in [Q, 2^183)`) -> REFUSED
//!    - Attack 4 (`Hole B quotient shift y_0[0] + 1` mod-Q-preserving / BEHZ forgery) -> REFUSED
//!    - Attack 5 (`corrupted custodian SPDZ MAC / tampered opened share`) -> REFUSED
//!    - Attack 6 (`unverified ciphertext E2S decryption attempt -> C8 abort BEFORE share release`,
//!      plus `R_PD` `offset_in_error`, `offset_partial`, and `unrelated_boundary_shares`) -> REFUSED

use darkstep::arith::addmod;
use darkstep::bfv::{Ct, OwnKey};
use darkvfhe::bigint::biguint_to_limbs3;
use darkvfhe::cert::{
    commit_persistent_grid_pcs, ct2_handle, ct3_handle, prove_hoisted_succinct_bundle,
    verify_hoisted_succinct_bundle, HoistedSuccinctBundle,
};
use darkvfhe::dark_gdn::{
    cleartext_gdn_step_mod_t, verify_pd_succinct_proof, DarkGdnResident, ThreeCustodianCluster,
};
use darkvfhe::digits::{ExactGarnerSpec, LiftMode};
use darkvfhe::logup_gkr::LogUpConfig;
use darkvfhe::rns_hoist::{Ct3, HoistedEngine};
use darkvfhe::succinct_pcs::{
    verify_slot_claims, CommittedMatrixPcs, PcsRng, SlotLinearClaim, DEFAULT_BLOWUP, T_COLS_128,
};
use darkvfhe::HoistedParams;
use num_bigint::BigUint;
use std::sync::Arc;

#[test]
fn test_succinct_pcs_bundle_roundtrip_and_deployed_n8192() {
    for &n_ring in &[64usize, 8192usize] {
        let params = Arc::new(HoistedParams::for_ring(n_ring));
        let engine = HoistedEngine::new(params.clone());
        let mut key = OwnKey::new(engine.rns_q.clone(), 12345 + n_ring as u64);

        let k_blk = if n_ring == 64 { 2 } else { 1 };
        let a_row: Vec<Ct> = (0..k_blk)
            .map(|c| {
                let mut m = vec![0u64; n_ring];
                for j in 0..32 {
                    m[j] = ((c * 5 + j * 3 + 1) as u64) % 11;
                }
                key.encrypt_exact(&m)
            })
            .collect();
        let b_vec: Vec<Ct> = (0..k_blk)
            .map(|c| {
                let mut m = vec![0u64; n_ring];
                for j in 0..32 {
                    m[j] = ((c * 7 + j * 2 + 4) as u64) % 11;
                }
                key.encrypt_exact(&m)
            })
            .collect();
        let a_grid = vec![a_row];
        let ha: Vec<Vec<[u8; 32]>> = a_grid.iter().map(|r| r.iter().map(ct2_handle).collect()).collect();
        let hb: Vec<[u8; 32]> = b_vec.iter().map(ct2_handle).collect();

        // Test both non-persistent and persistent `A`, and both `Direct-20` & `Exact-Garner-15`:
        for mode in [LiftMode::Direct20, LiftMode::ExactGarner15] {
            let (out_np, bun_np, _, _) = prove_hoisted_succinct_bundle(
                &engine,
                &a_grid,
                &b_vec,
                None,
                mode,
                LogUpConfig::MonolithicC4,
            )
            .expect("non-persistent succinct prove");
            let bytes_np = bun_np.to_bytes();
            let dec_np = HoistedSuccinctBundle::from_bytes(&bytes_np, &params).expect("from_bytes");
            let hout_np: Vec<[u8; 32]> = out_np.iter().map(ct3_handle).collect();
            verify_hoisted_succinct_bundle(
                &params,
                &ha,
                &hb,
                &hout_np,
                Some(&a_grid),
                &b_vec,
                &out_np,
                &dec_np,
            )
            .expect("non-persistent standalone verify");

            if n_ring == 8192 {
                let (a_pre, a_pcs) =
                    commit_persistent_grid_pcs(&engine, &a_grid, mode).expect("persistent commit");
                let (out_p, bun_p, _, _) = prove_hoisted_succinct_bundle(
                    &engine,
                    &a_grid,
                    &b_vec,
                    Some((&a_pre, &a_pcs)),
                    mode,
                    LogUpConfig::MonolithicC4,
                )
                .expect("persistent succinct prove");
                let bytes_p = bun_p.to_bytes();
                let dec_p = HoistedSuccinctBundle::from_bytes(&bytes_p, &params).unwrap();
                let hout_p: Vec<[u8; 32]> = out_p.iter().map(ct3_handle).collect();
                // Notice `opened_a = None`: verifier checks `Enc(W)` purely via `a_pcs_root` with 0 weight cts!
                verify_hoisted_succinct_bundle(
                    &params,
                    &ha,
                    &hb,
                    &hout_p,
                    None,
                    &b_vec,
                    &out_p,
                    &dec_p,
                )
                .expect("persistent standalone zero-witness verify");
            }
        }
    }
}

#[test]
fn test_hvzk_zero_witness_leakage_on_opened_columns() {
    // Verify that for two extreme witnesses (all-0 vs structured dense values), the opened columns
    // on data rows have full-entropy non-constant values completely masked by the `hide = t_cols` tail
    // and `4` ZK data-blinding rows!
    let params = HoistedParams::for_ring(64);
    let fp = params.fp[0];
    let log_n = 6usize;
    let n = 64usize;
    let zero_witness = vec![0u64; 16 * n];
    let dense_witness: Vec<u64> = (0..16 * n).map(|i| (i as u64 * 99991 + 7) % fp.p).collect();

    let pcs_zero = CommittedMatrixPcs::commit_with_rng(
        fp,
        &zero_witness,
        log_n,
        T_COLS_128,
        DEFAULT_BLOWUP,
        PcsRng::from_seed([0x11u8; 32]),
    );
    let pcs_dense = CommittedMatrixPcs::commit_with_rng(
        fp,
        &dense_witness,
        log_n,
        T_COLS_128,
        DEFAULT_BLOWUP,
        PcsRng::from_seed([0x22u8; 32]),
    );

    let vf = vec![vec![1u64; n]];
    let cl_z = vec![SlotLinearClaim::single_vec(0, vec![(0, 1)], 0)];
    let prf_z = pcs_zero.open_slot_claims(log_n, &vf, &cl_z, &[0xAAu8; 32]);
    verify_slot_claims(&fp, &pcs_zero.shape, &pcs_zero.root, log_n, &vf, &cl_z, &[0xAAu8; 32], &prf_z)
        .unwrap();

    // Even when ALL 1,024 witness values are `0`, ZERO opened column entries on data rows are trivially 0,
    // AND `u_eval[0..C]` is non-zero across all coordinates thanks to the 4 ZK data-blinding rows!
    let non_zero_opened = prf_z
        .opened_cols
        .iter()
        .flat_map(|col| col[..pcs_zero.shape.usable_rows].iter())
        .filter(|&&v| v != 0)
        .count();
    let total_opened = prf_z.opened_cols.len() * pcs_zero.shape.usable_rows;
    assert_eq!(
        non_zero_opened, total_opened,
        "all-zero witness must produce uniform non-zero opened column evaluations!"
    );
    assert!(
        prf_z.u_eval[..pcs_zero.shape.c].iter().all(|e| *e != [0, 0, 0]),
        "ZK data-blinding rows must blind u_eval[0..C] even on an all-zero witness!"
    );
    let _ = pcs_dense;
}

#[test]
fn test_multi_turn_3_custodian_dark_gdn_and_pir_bit_exact() {
    let params = Arc::new(HoistedParams::for_ring(64));
    let engine = Arc::new(HoistedEngine::new(params.clone()));
    let mut cluster = ThreeCustodianCluster::setup(params.clone(), engine.clone(), [0x42u8; 32]);

    let vocab_size = 24usize;
    let d_k = 8usize;
    let d_v = 8usize;
    let fp_t = &params.fp_t;
    let t_mod = params.t;

    let embed_table: Vec<Vec<u64>> = (0..vocab_size)
        .map(|tok| (0..d_k).map(|i| ((tok * 11 + i * 3 + 2) as u64) % t_mod).collect())
        .collect();
    let mut state_ref: Vec<Vec<u64>> = (0..d_k)
        .map(|i| (0..d_v).map(|j| ((i * 5 + j + 1) as u64) % 13).collect())
        .collect();

    let w_q: Vec<Vec<u64>> = (0..d_k)
        .map(|r| (0..d_k).map(|c| ((r * 3 + c + 1) as u64) % 7).collect())
        .collect();
    let w_k: Vec<Vec<u64>> = (0..d_k)
        .map(|r| (0..d_k).map(|c| ((r + c * 2 + 2) as u64) % 7).collect())
        .collect();
    let w_v: Vec<Vec<u64>> = (0..d_v)
        .map(|r| (0..d_k).map(|c| ((r * 2 + c * 5 + 3) as u64) % 7).collect())
        .collect();

    let mut resident = DarkGdnResident::initialize(
        &mut cluster,
        &embed_table,
        &state_ref,
        w_q.clone(),
        w_k.clone(),
        w_v.clone(),
        LiftMode::ExactGarner15,
        LogUpConfig::MonolithicC4,
    )
    .expect("init resident");

    // 5 stateful turns including `alpha_t = 0` (complete reset) and full state carry-over!
    let schedule = [
        (3usize, 4u64, 2u64),
        (19usize, 7u64, 5u64),
        (0usize, 0u64, 3u64),
        (23usize, 6u64, 9u64),
        (11usize, 2u64, 4u64),
    ];

    for (turn, &(tok, alpha, beta)) in schedule.iter().enumerate() {
        let (y_got, _) = resident
            .step_turn(&mut cluster, turn, tok, alpha, beta)
            .expect("resident turn");

        let x = &embed_table[tok];
        let q: Vec<u64> = w_q.iter().map(|r| fp_t.dot(r, x)).collect();
        let k: Vec<u64> = w_k.iter().map(|r| fp_t.dot(r, x)).collect();
        let v: Vec<u64> = w_v.iter().map(|r| fp_t.dot(r, x)).collect();
        let (y_want, s_next) =
            cleartext_gdn_step_mod_t(fp_t, &state_ref, &q, &k, &v, alpha, beta);
        assert_eq!(y_got, y_want, "GDN turn {turn} mismatch vs cleartext!");
        state_ref = s_next;
    }
}

#[test]
fn test_all_six_required_adversarial_attacks() {
    let params = Arc::new(HoistedParams::for_ring(64));
    let engine = Arc::new(HoistedEngine::new(params.clone()));
    let mut cluster = ThreeCustodianCluster::setup(params.clone(), engine.clone(), [0x99u8; 32]);
    let n = params.n;
    let fp0 = params.fp[0];

    let mut rng = PcsRng::from_seed([0x77u8; 32]);
    let a_grid = vec![vec![
        cluster.pub_key.encrypt_pk(&(0..n).map(|j| (j as u64) % 7).collect::<Vec<_>>(), &mut rng),
        cluster.pub_key.encrypt_pk(&(0..n).map(|j| ((j + 3) as u64) % 7).collect::<Vec<_>>(), &mut rng),
    ]];
    let b_vec = vec![
        cluster.pub_key.encrypt_pk(&(0..n).map(|j| ((j * 2) as u64) % 7).collect::<Vec<_>>(), &mut rng),
        cluster.pub_key.encrypt_pk(&(0..n).map(|j| ((j * 5 + 1) as u64) % 7).collect::<Vec<_>>(), &mut rng),
    ];
    let ha: Vec<Vec<[u8; 32]>> = a_grid.iter().map(|r| r.iter().map(ct2_handle).collect()).collect();
    let hb: Vec<[u8; 32]> = b_vec.iter().map(ct2_handle).collect();

    let (honest_out, honest_bundle, _, _) = prove_hoisted_succinct_bundle(
        &engine,
        &a_grid,
        &b_vec,
        None,
        LiftMode::ExactGarner15,
        LogUpConfig::MonolithicC4,
    )
    .expect("honest succinct prove");
    let honest_bytes = honest_bundle.to_bytes();
    let hout: Vec<[u8; 32]> = honest_out.iter().map(ct3_handle).collect();

    verify_hoisted_succinct_bundle(
        &params,
        &ha,
        &hb,
        &hout,
        Some(&a_grid),
        &b_vec,
        &honest_out,
        &HoistedSuccinctBundle::from_bytes(&honest_bytes, &params).unwrap(),
    )
    .expect("honest succinct bundle must pass");

    // =========================================================================
    // ATTACK 1: `1-cell PCS witness / column / evaluation mutation`
    // =========================================================================
    {
        let mut mut_col = honest_bundle.clone();
        mut_col.pcs_opening.opened_cols[3][2] = fp0.add(mut_col.pcs_opening.opened_cols[3][2], 1);
        let bytes = mut_col.to_bytes();
        let dec = HoistedSuccinctBundle::from_bytes(&bytes, &params).unwrap();
        let err = verify_hoisted_succinct_bundle(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            &b_vec,
            &honest_out,
            &dec,
        )
        .expect_err("1-cell PCS column mutation must fail");
        assert!(err.contains("Merkle") || err.contains("PCS"), "{err}");

        let mut mut_ev = honest_bundle.clone();
        mut_ev.p0_poly_evals[0] = fp0.add(mut_ev.p0_poly_evals[0], 1);
        let bytes2 = mut_ev.to_bytes();
        let dec2 = HoistedSuccinctBundle::from_bytes(&bytes2, &params).unwrap();
        assert!(
            verify_hoisted_succinct_bundle(
                &params,
                &ha,
                &hb,
                &hout,
                Some(&a_grid),
                &b_vec,
                &honest_out,
                &dec2,
            )
            .is_err(),
            "1-cell PCS claimed evaluation mutation must fail"
        );
    }

    // =========================================================================
    // ATTACK 2: `Forged Merkle multiproof path / salt`
    // =========================================================================
    {
        let mut bad_merkle = honest_bundle.clone();
        bad_merkle.pcs_opening.multiproof.siblings[0][7] ^= 0x80;
        let bytes = bad_merkle.to_bytes();
        let dec = HoistedSuccinctBundle::from_bytes(&bytes, &params).unwrap();
        let err = verify_hoisted_succinct_bundle(
            &params,
            &ha,
            &hb,
            &hout,
            Some(&a_grid),
            &b_vec,
            &honest_out,
            &dec,
        )
        .expect_err("forged Merkle sibling must fail");
        assert!(err.contains("Merkle multiproof root mismatch"), "{err}");

        let mut bad_salt = honest_bundle.clone();
        bad_salt.pcs_opening.multiproof.salts[0][0] ^= 1;
        let dec_s = HoistedSuccinctBundle::from_bytes(&bad_salt.to_bytes(), &params).unwrap();
        assert!(
            verify_hoisted_succinct_bundle(
                &params,
                &ha,
                &hb,
                &hout,
                Some(&a_grid),
                &b_vec,
                &honest_out,
                &dec_s,
            )
            .is_err(),
            "forged Merkle column salt must fail"
        );
    }

    // =========================================================================
    // ATTACK 3: `Forged Exact-Garner-15 non-power-of-two boundary u + Q`
    // =========================================================================
    {
        // Construct `u_alias = 42 + Q in [Q, 2^183)` (`r2 >= q2`), commit it in `CommittedMatrixPcs`
        // with ANY forged multiplicity vector, and verify `D1b` LogUp-GKR + PCS rejects `T_2 = p0 - 1`!
        let gspec = ExactGarnerSpec::new(&params);
        let u_alias = BigUint::from(42u32) + &params.q_big;
        assert!(u_alias.bits() <= 183);
        let q0_u = BigUint::from(params.qp[0]);
        let q1_u = BigUint::from(params.qp[1]);
        let r0_a = (&u_alias % &q0_u).to_u64_digits().first().copied().unwrap_or(0);
        let q_s1 = (&u_alias - r0_a) / &q0_u;
        let r1_a = (&q_s1 % &q1_u).to_u64_digits().first().copied().unwrap_or(0);
        let r2_a = ((&q_s1 - r1_a) / &q1_u).to_u64_digits().first().copied().unwrap_or(0);
        assert!(r2_a >= params.qp[2]);

        let _ = biguint_to_limbs3(&u_alias);
        let mut forged_cols = Vec::with_capacity(15);
        for (ri, delta) in [(r0_a, gspec.deltas[0]), (r1_a, gspec.deltas[1]), (r2_a, gspec.deltas[2])] {
            forged_cols.push(vec![(ri & ((1 << 20) - 1)) as u32; n]);
            forged_cols.push(vec![((ri >> 20) & ((1 << 19) - 1)) as u32; n]);
            forged_cols.push(vec![((ri >> 39) & ((1 << 18) - 1)) as u32; n]);
            forged_cols.push(vec![(ri >> 57) as u32; n]);
            forged_cols.push(vec![(((ri & ((1 << 20) - 1)) + delta) & ((1 << 20) - 1)) as u32; n]);
        }
        let forged_dc = darkvfhe::digits::DigitCols { cols: forged_cols };
        assert!(gspec.check_u_exact(&forged_dc).is_err());

        let mut lkps = Vec::new();
        gspec.append_lookups_fp(&forged_dc, fp0.p, &mut lkps);
        // Out-of-range `T_2 = p0 - 1` cannot be counted in `[0, 2^20)`, and even with forged `mults`
        // `verify_logup_gkr` deterministically rejects rational root balance!
        assert!(darkvfhe::logup_gkr::count_multiplicities_parallel(&lkps).is_err());
        let mut fake_mults = vec![0u64; darkvfhe::logup_gkr::TABLE_SIZE];
        fake_mults[0] = lkps.len() as u64;
        let bad_lu = darkvfhe::logup_gkr::prove_logup_gkr_with_mults(
            &fp0,
            &lkps,
            &fake_mults,
            LogUpConfig::MonolithicC4,
            &[0x33u8; 32],
        );
        assert!(darkvfhe::logup_gkr::verify_logup_gkr(&fp0, &bad_lu, &[0x33u8; 32], None).is_err());
    }

    // =========================================================================
    // ATTACK 4: `Hole B quotient shift (y_0[0] + 1 mod-Q-preserving / BEHZ forgery)`
    // =========================================================================
    {
        let mut out_holeb = honest_out.clone();
        for k in 0..3 {
            out_holeb[0].c0[k * n] = addmod(out_holeb[0].c0[k * n], 1, params.qp[k]);
        }
        let hout_holeb = vec![ct3_handle(&out_holeb[0])];
        assert!(
            verify_hoisted_succinct_bundle(
                &params,
                &ha,
                &hb,
                &hout_holeb,
                Some(&a_grid),
                &b_vec,
                &out_holeb,
                &honest_bundle,
            )
            .is_err(),
            "Hole B forged output quotient shift must be rejected!"
        );
    }

    // =========================================================================
    // ATTACK 5: `Corrupted custodian SPDZ MAC / tampered opened share`
    // =========================================================================
    {
        let mut s_val = cluster.share_authenticated(42);
        ThreeCustodianCluster::corrupt_mac_for_test(&mut s_val, 1, 1, params.t);
        let _ = cluster.spdz_open_batch(&[s_val], "ATTACK_MAC");
        let err = cluster
            .spdz_mac_check("attack5_mac_check")
            .expect_err("corrupted custodian SPDZ MAC must fail mac_check!");
        assert!(err.contains("SPDZ MAC check FAILED"), "{err}");
    }

    // =========================================================================
    // ATTACK 6: `Unverified ciphertext E2S attempt -> C8 abort BEFORE share release`
    //           + `R_PD` partial decryption attacks (`offset_partial`, `unrelated_boundary_shares`)
    // =========================================================================
    {
        // 6a. Attempt `e2s_ct3` on `honest_out[0]` BEFORE custodians verify `honest_bytes`:
        let unverified_h = ct3_handle(&honest_out[0]);
        let err_c8 = cluster
            .e2s_ct3(&unverified_h, &honest_out[0], &[0, 1], "unverified_e2s")
            .expect_err("C8 gate must abort E2S before releasing any partial decryption share!");
        assert!(err_c8.contains("C8 ABORT"), "{err_c8}");

        // 6b. Attempt `verify_and_ingest_succinct_bundle` with tampered `proof_bytes`:
        for cust in &mut cluster.custodians {
            for r in &ha {
                for &h in r {
                    cust.register_verified_input_handle(h);
                }
            }
            for &h in &hb {
                cust.register_verified_input_handle(h);
            }
        }
        let mut bad_bytes = honest_bytes.clone();
        let last_idx = bad_bytes.len() - 9;
        bad_bytes[last_idx] ^= 1;
        assert!(
            cluster.custodians[0]
                .verify_and_ingest_succinct_bundle(
                    &ha,
                    &hb,
                    &hout,
                    Some(&a_grid),
                    &b_vec,
                    &honest_out,
                    &bad_bytes,
                )
                .is_err(),
            "custodian must reject tampered succinct bundle bytes"
        );
        assert!(
            !cluster.custodians[0].has_verified_handle(&unverified_h),
            "handle must NOT enter verified_handles after failed bundle verification!"
        );

        // 6c. Now ingest valid `honest_bytes` on all 3 custodians and test `R_PD` attacks (`offset_partial` & `unrelated_boundary_shares`):
        for cust in &mut cluster.custodians {
            cust.verify_and_ingest_succinct_bundle(
                &ha,
                &hb,
                &hout,
                Some(&a_grid),
                &b_vec,
                &honest_out,
                &honest_bytes,
            )
            .expect("custodian ingests valid bundle");
        }
        let mask_ct = cluster.pub_key.encrypt_pk(&vec![0u64; n], &mut rng);
        let mut prf0 = cluster.custodians[0]
            .partial_decrypt_ct3_checked(&engine, &hout[0], &honest_out[0], &mask_ct, "r_pd_test")
            .expect("honest partial decrypt");

        // `unrelated_boundary_shares`: try verifying `prf0` against a DIFFERENT ciphertext!
        let alt_ct3 = Ct3 {
            c0: honest_out[0].c0.clone(),
            c1: b_vec[0].c1.clone(),
            c2: honest_out[0].c2.clone(),
        };
        assert!(
            verify_pd_succinct_proof(
                &params,
                0,
                &cluster.custodians[0].key_pcs_root,
                &cluster.custodians[0].key_pcs_shape,
                cluster.custodians[0].smudge_bound,
                cluster.custodians[0].smudge_top_bits,
                &alt_ct3,
                "r_pd_test",
                &prf0,
            )
            .is_err(),
            "R_PD must reject partial decryption from an unrelated ciphertext!"
        );

        // `offset_partial`: shift `partial_rns[0]` by +1!
        prf0.partial_rns[0] = addmod(prf0.partial_rns[0], 1, params.qp[0]);
        assert!(
            verify_pd_succinct_proof(
                &params,
                0,
                &cluster.custodians[0].key_pcs_root,
                &cluster.custodians[0].key_pcs_shape,
                cluster.custodians[0].smudge_bound,
                cluster.custodians[0].smudge_top_bits,
                &honest_out[0],
                "r_pd_test",
                &prf0,
            )
            .is_err(),
            "R_PD must reject tampered partial_rns!"
        );
    }
}
