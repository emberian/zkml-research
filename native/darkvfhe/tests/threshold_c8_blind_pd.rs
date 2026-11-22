#![deny(warnings)]
//! Comprehensive Release Integration, Benchmark, `TVD == 0` HVZK Audit, and Adversarial Falsifier Suite
//! for `darkvfhe::threshold_custody` (`G10` / `L6` R1-4 Closure):
//! 1. Standard RFC 8032 Ed25519 Test Vector + Hybrid-PQ (`Ed25519 + SHA-256 Merkle-Lamport`) Quorum Envelope;
//! 2. Crash-Tolerant `2-of-3` (`NoSingleViewer = 2`) & `3-of-5` (`NoSingleViewer = 3`) Distributed Bivariate-VSS +
//!    BDLOP Lattice-Anchored DKG & 2-Round Distributed Relin over Deployed `N = 8192, Qp, ExactGarner15`;
//! 3. Algebraic Full-Rank (`TVD == 0`) & Statistical Witness-Indistinguishability Audit of `WhirBlindPdProof`;
//! 4. `15/15` Deterministic Adversarial Attack Refusals (`t<2`/`t>=n`, hostile VSS row, equivocating bivariate
//!    dealer, sealed-envelope tamper, `epoch == 0`, `stale_epoch`, `double_open` across custodian disk restart,
//!    torn audit-log tail, `R_refresh > 1` in `tvd_40b_strict_mode`, policy mismatch, under-quorum / corrupted
//!    PQ signature, tampered `WhirPcs61` compute proof, forged decryption share, unbound secret share `s'_i != s_i`,
//!    and `+1` `BlindedRPdEvals` weld tamper!).

use darkvfhe::cert::{ct2_handle, ct3_handle};
use darkvfhe::dark_block::{os_csprng_seed32, params_n8192_homo, params_ring_homo};
use darkvfhe::digits::LiftMode;
use darkvfhe::logup_gkr::LogUpConfig;
use darkvfhe::rns_hoist::HoistedEngine;
use darkvfhe::succinct_pcs::PcsRng;
use darkvfhe::threshold_custody::{
    aggregate_relin_round_1, assemble_distributed_relin_key, combine_verified_threshold_shares,
    compute_ct_opening_commitment, ed25519_public_key_from_seed, ed25519_sign,
    ed25519_verify_strict, finalize_unbiased_crp_seed, lagrange_coeff_at_zero_mod_q,
    verify_blind_r_pd_whir61, CustodianCrpCoin, DistributedRelinDealer, DistributedThresholdDkg,
    EnrolledThresholdRoster, HybridPqCustodianIdentity, OpeningAuthorization,
    ThresholdCustodianParty, ThresholdCustodyError, VerifiedThresholdDkgTranscript,
    WhirBlindPdProof, WhirComputeProvenance,
};
use darkvfhe::whir_pcs::{commit_persistent_whir_grid, prove_hoisted_whir};
use darkvfhe::{FastPrime61, HoistedParams};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};
use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

fn decode_hex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn temp_test_dir(tag: &str) -> PathBuf {
    let rnd = os_csprng_seed32();
    let hex_id: String = rnd[0..8].iter().map(|b| format!("{b:02x}")).collect();
    let dir = std::env::temp_dir().join(format!("darkvfhe_g10_{tag}_{hex_id}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Stand up a complete `t`-of-`n` distributed committee (`0` central dealer secret; independent `/dev/urandom` per party!).
fn run_distributed_committee_setup(
    params: Arc<HoistedParams>,
    n_parties: usize,
    threshold: usize,
    policy_digest: [u8; 32],
    tvd_40b_strict: bool,
    dir: &std::path::Path,
) -> (
    Arc<HoistedEngine>,
    EnrolledThresholdRoster,
    Vec<ThresholdCustodianParty>,
    darkvfhe::dark_gdn::ThresholdPubKey,
    VerifiedThresholdDkgTranscript,
    Arc<darkvfhe::rns_hoist::RelinearizationKey>,
    f64,
    f64,
) {
    std::fs::create_dir_all(dir).unwrap();
    let engine = Arc::new(HoistedEngine::new(params.clone()));

    let t_dkg0 = Instant::now();
    let mut identities: Vec<HybridPqCustodianIdentity> = (0..n_parties)
        .map(|i| {
            HybridPqCustodianIdentity::generate_from_os(
                i,
                8,
                Some(dir.join(format!("pq_leaf_p{i}.state"))),
            )
            .unwrap()
        })
        .collect();
    let enrollments = identities.iter().map(|id| id.enrollment()).collect();
    let roster = EnrolledThresholdRoster::new(threshold, enrollments).unwrap();

    // Unbiased 2-round commit-reveal CRP coin:
    let coins: Vec<CustodianCrpCoin> = (0..n_parties)
        .map(CustodianCrpCoin::sample_from_os)
        .collect();
    let commits: Vec<[u8; 32]> = coins
        .iter()
        .map(|c| c.commitment(&roster.roster_digest))
        .collect();
    let reveals: Vec<_> = coins.into_iter().map(|c| c.reveal()).collect();
    let crp_seed = finalize_unbiased_crp_seed(&roster, &commits, &reveals).unwrap();

    let dkg = DistributedThresholdDkg::new(params.clone(), roster.clone(), crp_seed).unwrap();

    // Phase 1: Each dealer independently deals and seals private rows to peers:
    let mut broadcasts = Vec::with_capacity(n_parties);
    let mut inbox: Vec<Vec<(usize, Vec<u8>)>> = (0..n_parties).map(|_| Vec::new()).collect();
    let mut own_rows = Vec::with_capacity(n_parties);
    let mut relin_secrets = Vec::with_capacity(n_parties);

    for d in 0..n_parties {
        let (bcast, own_row, sealed, rsec) = dkg.deal_from_os(&mut identities[d]).unwrap();
        for (rec, env) in sealed {
            inbox[rec].push((d, env));
        }
        broadcasts.push(bcast);
        own_rows.push(Some(own_row));
        relin_secrets.push(rsec);
    }

    let mut accepted_per_party: Vec<Vec<_>> = Vec::with_capacity(n_parties);
    for rec in 0..n_parties {
        let mut by_dealer: std::collections::BTreeMap<usize, _> = std::collections::BTreeMap::new();
        by_dealer.insert(rec, own_rows[rec].take().unwrap());
        for (d, env) in &inbox[rec] {
            let row = dkg
                .accept_dealing(&identities[rec], &broadcasts[*d], env)
                .unwrap();
            by_dealer.insert(*d, row);
        }
        accepted_per_party.push((0..n_parties).map(|d| by_dealer.remove(&d).unwrap()).collect());
    }

    // Phase 2: Pairwise bivariate cross-evaluation check across all `(i, j)`:
    let mut cross_msgs: Vec<Vec<(usize, Vec<u8>)>> = (0..n_parties).map(|_| Vec::new()).collect();
    for sender in 0..n_parties {
        for peer in 0..n_parties {
            if sender == peer {
                continue;
            }
            let env = dkg
                .seal_cross_evaluations(&mut identities[sender], &accepted_per_party[sender], peer)
                .unwrap();
            cross_msgs[peer].push((sender, env));
        }
    }
    let mut cross_receipts_per_party: Vec<Vec<_>> = Vec::with_capacity(n_parties);
    for rec in 0..n_parties {
        let mut rcs = Vec::with_capacity(n_parties - 1);
        for (sender, env) in &cross_msgs[rec] {
            rcs.push(
                dkg.verify_cross_evaluations(
                    &identities[rec],
                    &accepted_per_party[rec],
                    *sender,
                    env,
                )
                .unwrap(),
            );
        }
        cross_receipts_per_party.push(rcs);
    }
    let dkg_ms = t_dkg0.elapsed().as_secs_f64() * 1e3;

    // 2-Round Distributed Relinearization Key Ceremony:
    let t_rlk0 = Instant::now();
    let mut relin_dealers: Vec<DistributedRelinDealer> = relin_secrets
        .into_iter()
        .map(|sec| DistributedRelinDealer::new_from_os(&params, sec))
        .collect();
    let r1_shares: Vec<_> = (0..n_parties)
        .map(|d| relin_dealers[d].round_1(&mut identities[d]).unwrap())
        .collect();
    let r1_agg =
        aggregate_relin_round_1(&params, &roster, &dkg.session_domain, &r1_shares).unwrap();
    let r2_shares: Vec<_> = relin_dealers
        .into_iter()
        .enumerate()
        .map(|(d, dealer)| {
            dealer
                .round_2(&params, &roster, &r1_shares, &mut identities[d])
                .unwrap()
        })
        .collect();
    let rlk = Arc::new(
        assemble_distributed_relin_key(&params, &roster, &r1_agg, &r2_shares).unwrap(),
    );
    let rlk_ms = t_rlk0.elapsed().as_secs_f64() * 1e3;

    // Phase 3: Local custody assembly per custodian (each deriving identical `pub_key` and `dkg_transcript`):
    let mut parties = Vec::with_capacity(n_parties);
    let mut pub_key_opt = None;
    let mut tr_opt = None;

    for (i, ((id, rows), cross_rcs)) in identities
        .into_iter()
        .zip(accepted_per_party.into_iter())
        .zip(cross_receipts_per_party.into_iter())
        .enumerate()
    {
        let log_path = dir.join(format!("custodian_{i}.audit.log"));
        let (party, pk, tr) = dkg
            .assemble_custodian_party(
                engine.clone(),
                id,
                rows,
                &cross_rcs,
                rlk.clone(),
                policy_digest,
                tvd_40b_strict,
                &log_path,
            )
            .unwrap();
        if let Some(ref prev_tr) = tr_opt {
            let prev: &VerifiedThresholdDkgTranscript = prev_tr;
            assert_eq!(prev.digest, tr.digest, "every custodian must derive identical DKG digest");
        } else {
            pub_key_opt = Some(pk);
            tr_opt = Some(tr);
        }
        parties.push(party);
    }

    (
        engine,
        roster,
        parties,
        pub_key_opt.unwrap(),
        tr_opt.unwrap(),
        rlk,
        dkg_ms,
        rlk_ms,
    )
}

#[allow(clippy::too_many_arguments)]
fn sign_quorum_opening_auth(
    parties: &mut [ThresholdCustodianParty],
    signers: &[usize],
    dkg_digest: [u8; 32],
    epoch: u64,
    sequence: u64,
    policy_digest: [u8; 32],
    ct_commitment: [u8; 32],
    compute_proof_digest: [u8; 32],
    refresh_cadence: u32,
    turns_since_refresh: u32,
    selected_parties: Vec<usize>,
) -> OpeningAuthorization {
    let mut auth = OpeningAuthorization {
        dkg_transcript_digest: dkg_digest,
        epoch,
        sequence,
        policy_digest,
        ct_commitment,
        compute_proof_digest,
        refresh_cadence,
        turns_since_refresh,
        selected_parties,
        quorum_signatures: Vec::new(),
    };
    let pre = auth.signing_preimage();
    for &s_idx in signers {
        let sig = parties[s_idx].identity.sign(&pre).unwrap();
        auth.quorum_signatures.push(sig);
    }
    auth
}

/// 1. Standard RFC 8032 §7.1 Test Vector 1 + Hybrid-PQ (`Ed25519 + SHA-256 Merkle-Lamport`) Envelope Verification.
#[test]
fn test_rfc8032_ed25519_and_hybrid_pq_quorum_envelope() {
    // Official RFC 8032 §7.1 TEST 1 (empty message `""`):
    let sk_seed: [u8; 32] =
        decode_hex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
            .try_into()
            .unwrap();
    let want_pk: [u8; 32] =
        decode_hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
            .try_into()
            .unwrap();
    let want_sig: [u8; 64] = decode_hex(
        "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155\
         5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    )
    .try_into()
    .unwrap();

    let got_pk = ed25519_public_key_from_seed(&sk_seed);
    assert_eq!(got_pk, want_pk, "RFC 8032 §7.1 public key mismatch");
    let got_sig = ed25519_sign(&sk_seed, b"");
    assert_eq!(got_sig, want_sig, "RFC 8032 §7.1 signature mismatch");
    assert!(ed25519_verify_strict(&got_pk, b"", &got_sig));
    assert!(!ed25519_verify_strict(&got_pk, b"x", &got_sig));

    // Non-canonical `S + L` malleability rejection:
    let l_big = (BigUint::from(1u32) << 252usize)
        + BigUint::parse_bytes(b"27742317777372353535851937790883648493", 10).unwrap();
    let s_orig = BigUint::from_bytes_le(&got_sig[32..64]);
    let s_mal = (&s_orig + &l_big).to_bytes_le();
    if s_mal.len() <= 32 {
        let mut mal_sig = got_sig;
        mal_sig[32..64].fill(0);
        mal_sig[32..32 + s_mal.len()].copy_from_slice(&s_mal);
        assert!(
            !ed25519_verify_strict(&got_pk, b"", &mal_sig),
            "non-canonical S >= L signature must be rejected"
        );
    }

    // Hybrid-PQ dual signature: corrupting EITHER Ed25519 OR PQ Merkle-Lamport half must fail!
    let dir = temp_test_dir("hpq");
    let mut id =
        HybridPqCustodianIdentity::generate_from_os(0, 6, Some(dir.join("leaf.st"))).unwrap();
    let enr = id.enrollment();
    let msg = b"G10 OpeningAuthorization Hybrid-PQ Payload";
    let sig = id.sign(msg).unwrap();
    assert_eq!(sig.verify(&enr, 0, msg).unwrap(), 0);
    assert!(
        sig.verify(&enr, 1, msg).is_err(),
        "replaying stateful PQ Lamport leaf < min_leaf must be rejected"
    );

    let mut bad_ed = sig.clone();
    bad_ed.ed25519_sig[10] ^= 0x01;
    assert!(bad_ed.verify(&enr, 0, msg).is_err());

    let mut bad_pq = sig;
    bad_pq.pq_lamport_sig[40] ^= 0x80;
    assert!(bad_pq.verify(&enr, 0, msg).is_err());

    let _ = std::fs::remove_dir_all(&dir);
}

/// 2. Full Deployed `N = 8192` (`Qp` `L = 3` 61-bit Crandall primes, Blum `t = 4,355,803,843`, `ExactGarner15`)
///    Crash-Tolerant `2-of-3` (`NoSingleViewer = 2`) & `3-of-5` (`NoSingleViewer = 3`) Distributed DKG + Relin +
///    `WhirPcs61` Compute Gate + `GMask61`-Blinded Partial Decryption Benchmark!
#[test]
fn test_deployed_n8192_2of3_and_3of5_threshold_dkg_relin_c8_and_blind_pd() {
    let dir = temp_test_dir("n8192_bench");
    let params = Arc::new(params_n8192_homo());
    let n = params.n;
    assert_eq!(n, 8192);
    let policy_digest: [u8; 32] = Sha256::digest(b"OBEND_SELVAGE_DARKVFHE_G10_STRICT_POLICY").into();

    println!("\n==================== G10 DEPLOYED N=8192 THRESHOLD CUSTODY & BLIND R_PD ====================");

    // --- PART A: Deployed `N = 8192` `2-of-3` (`t = 2, n = 3`, `NoSingleViewer = 2`, 1 custodian offline!) ---
    let (engine, _roster23, mut parties23, pk23, dkg_tr23, rlk23, dkg23_ms, rlk23_ms) =
        run_distributed_committee_setup(
            params.clone(),
            3,
            2,
            policy_digest,
            true,
            &dir.join("c2of3"),
        );

    // Encrypt `A` (persistent weight `1 x 1` block) and `B` (input activation) under the 2-of-3 joint `pk` (`0` `sk`!):
    let mut enc_rng = PcsRng::from_seed(os_csprng_seed32());
    let mut a_plain = vec![0u64; n];
    let mut b_plain = vec![0u64; n];
    a_plain[0] = 42_000;
    a_plain[1] = 12_345;
    b_plain[0] = 1_000;
    b_plain[1] = 7_777;
    // Exact negacyclic product mod `(X^8192 + 1, t)`:
    let want_c0 = (a_plain[0] * b_plain[0]) % params.t;
    let want_c1 = (a_plain[0] * b_plain[1] + a_plain[1] * b_plain[0]) % params.t;
    let want_c2 = (a_plain[1] * b_plain[1]) % params.t;

    let ct_a = pk23.encrypt_pk(&a_plain, &mut enc_rng);
    let ct_b = pk23.encrypt_pk(&b_plain, &mut enc_rng);
    let a_grid = vec![vec![ct_a]];
    let b_vec = vec![ct_b];
    let ha_grid = vec![vec![ct2_handle(&a_grid[0][0])]];
    let hb_vec = vec![ct2_handle(&b_vec[0])];

    let (a_pre, a_whir_pcs) =
        commit_persistent_whir_grid(&engine, &a_grid, LiftMode::ExactGarner15).unwrap();
    for p in &mut parties23 {
        p.register_verified_persistent_whir_root(a_whir_pcs.pcs.root);
    }

    // Prove `HoistedB61 + ExactGarner15` inside `WhirPcs61` (`DVFHEWH1`) and relinearize `Ct3 -> Ct`:
    let t_comp0 = Instant::now();
    let (out_cts, whir_bundle, _, _) = prove_hoisted_whir(
        &engine,
        &a_grid,
        &b_vec,
        Some((&a_pre, &a_whir_pcs)),
        LiftMode::ExactGarner15,
        LogUpConfig::BatchedC3 { chunk_log2: 19 },
    )
    .unwrap();
    let whir_bytes = whir_bundle.to_bytes();
    let hout_vec = vec![ct3_handle(&out_cts[0])];
    let target_ct2 = engine.relinearize_ct3(&out_cts[0], &rlk23);
    let comp_prove_ms = t_comp0.elapsed().as_secs_f64() * 1e3;

    let compute_prf_digest: [u8; 32] = Sha256::digest(&whir_bytes).into();
    let whir_prov = WhirComputeProvenance {
        ha_grid: &ha_grid,
        hb_vec: &hb_vec,
        hout_vec: &hout_vec,
        opened_a: None,
        expected_persistent_a_root: Some(&a_whir_pcs.pcs.root),
        opened_b: &b_vec,
        out_cts: &out_cts,
        target_output_row: 0,
        whir_proof_bytes: &whir_bytes,
    };

    // Open with `2-of-3` quorum `selected = [0, 2]` while Custodian `1` is COMPLETELY OFFLINE!
    let selected_23 = vec![0usize, 2usize];
    let raw_h23 = ct2_handle(&target_ct2);
    let ct_com_23 = compute_ct_opening_commitment(&raw_h23, None, &selected_23);
    let auth_23 = sign_quorum_opening_auth(
        &mut parties23,
        &selected_23,
        dkg_tr23.digest,
        1,
        1,
        policy_digest,
        ct_com_23,
        compute_prf_digest,
        1,
        0,
        selected_23.clone(),
    );

    let mut pd_proofs_23 = Vec::with_capacity(2);
    let mut pd_prove_tot_ms = 0.0;
    for &p_idx in &selected_23 {
        let t0 = Instant::now();
        let prf = parties23[p_idx]
            .partial_decrypt_relinearized_ct2_gated(&auth_23, &whir_prov, &target_ct2, None)
            .unwrap();
        pd_prove_tot_ms += t0.elapsed().as_secs_f64() * 1e3;
        pd_proofs_23.push(prf);
    }

    // Wire roundtrip + standalone zero-witness verify + `2-of-3` Lagrange combine:
    let pd0_wire = pd_proofs_23[0].to_bytes(&params);
    let pd0_rt = WhirBlindPdProof::from_bytes(&pd0_wire, &params).unwrap();
    assert_eq!(pd0_rt.to_bytes(&params), pd0_wire);

    let auth23_stmt = auth_23.statement_digest();
    let t_vfy0 = Instant::now();
    verify_blind_r_pd_whir61(
        &params,
        selected_23[0],
        &selected_23,
        &auth23_stmt,
        &dkg_tr23,
        parties23[0].smudge_bound,
        parties23[0].smudge_top_bits,
        &target_ct2,
        &ct_com_23,
        &pd0_rt,
    )
    .unwrap();
    let single_pd_vfy_ms = t_vfy0.elapsed().as_secs_f64() * 1e3;

    let t_comb0 = Instant::now();
    let plain_23 = combine_verified_threshold_shares(
        &params,
        &auth23_stmt,
        &dkg_tr23,
        parties23[0].smudge_bound,
        parties23[0].smudge_top_bits,
        &target_ct2,
        &ct_com_23,
        &selected_23,
        &pd_proofs_23,
    )
    .unwrap();
    let combine_23_ms = t_comb0.elapsed().as_secs_f64() * 1e3;

    assert_eq!(plain_23[0], want_c0);
    assert_eq!(plain_23[1], want_c1);
    assert_eq!(plain_23[2], want_c2);
    assert!(plain_23[3..64].iter().all(|&x| x == 0));

    println!(
        "[2-of-3 @ N=8192] DKG={:.2} ms | DistRelin={:.2} ms | HoistedWhirProve={:.2} ms ({:.2} KiB) | \
         BlindPdProve/party={:.2} ms | BlindPdWire={:.2} KiB ({} B) | BlindPdVerify={:.2} ms | Combine2of3={:.2} ms | max|diff|=0",
        dkg23_ms,
        rlk23_ms,
        comp_prove_ms,
        whir_bytes.len() as f64 / 1024.0,
        pd_prove_tot_ms / 2.0,
        pd0_wire.len() as f64 / 1024.0,
        pd0_wire.len(),
        single_pd_vfy_ms,
        combine_23_ms,
    );

    // --- PART B: Deployed `N = 8192` `3-of-5` (`t = 3, n = 5`, `NoSingleViewer = 3`, 2 custodians offline!) ---
    let (_eng35, _roster35, mut parties35, pk35, dkg_tr35, rlk35, dkg35_ms, rlk35_ms) =
        run_distributed_committee_setup(
            params.clone(),
            5,
            3,
            policy_digest,
            true,
            &dir.join("c3of5"),
        );

    let ct_a35 = pk35.encrypt_pk(&a_plain, &mut enc_rng);
    let ct_b35 = pk35.encrypt_pk(&b_plain, &mut enc_rng);
    let a_grid35 = vec![vec![ct_a35]];
    let b_vec35 = vec![ct_b35];
    let ha_grid35 = vec![vec![ct2_handle(&a_grid35[0][0])]];
    let hb_vec35 = vec![ct2_handle(&b_vec35[0])];
    let (a_pre35, a_whir35) =
        commit_persistent_whir_grid(&engine, &a_grid35, LiftMode::ExactGarner15).unwrap();
    for p in &mut parties35 {
        p.register_verified_persistent_whir_root(a_whir35.pcs.root);
    }
    let (out35, bun35, _, _) = prove_hoisted_whir(
        &engine,
        &a_grid35,
        &b_vec35,
        Some((&a_pre35, &a_whir35)),
        LiftMode::ExactGarner15,
        LogUpConfig::BatchedC3 { chunk_log2: 19 },
    )
    .unwrap();
    let whir35_bytes = bun35.to_bytes();
    let hout35 = vec![ct3_handle(&out35[0])];
    let target35 = engine.relinearize_ct3(&out35[0], &rlk35);
    let comp35_dig: [u8; 32] = Sha256::digest(&whir35_bytes).into();

    // Open with non-contiguous 3-of-5 quorum `[1, 3, 4]` while Custodians `0` and `2` are OFFLINE!
    let selected_35 = vec![1usize, 3usize, 4usize];
    let ct_com_35 = compute_ct_opening_commitment(&ct2_handle(&target35), None, &selected_35);
    let auth_35 = sign_quorum_opening_auth(
        &mut parties35,
        &selected_35,
        dkg_tr35.digest,
        1,
        1,
        policy_digest,
        ct_com_35,
        comp35_dig,
        1,
        0,
        selected_35.clone(),
    );
    let prov35 = WhirComputeProvenance {
        ha_grid: &ha_grid35,
        hb_vec: &hb_vec35,
        hout_vec: &hout35,
        opened_a: None,
        expected_persistent_a_root: Some(&a_whir35.pcs.root),
        opened_b: &b_vec35,
        out_cts: &out35,
        target_output_row: 0,
        whir_proof_bytes: &whir35_bytes,
    };

    let t35_0 = Instant::now();
    let mut prfs35 = Vec::with_capacity(3);
    for &p_idx in &selected_35 {
        prfs35.push(
            parties35[p_idx]
                .partial_decrypt_relinearized_ct2_gated(&auth_35, &prov35, &target35, None)
                .unwrap(),
        );
    }
    let pd35_ms = t35_0.elapsed().as_secs_f64() * 1e3;

    let t35_c = Instant::now();
    let plain_35 = combine_verified_threshold_shares(
        &params,
        &auth_35.statement_digest(),
        &dkg_tr35,
        parties35[1].smudge_bound,
        parties35[1].smudge_top_bits,
        &target35,
        &ct_com_35,
        &selected_35,
        &prfs35,
    )
    .unwrap();
    let comb35_ms = t35_c.elapsed().as_secs_f64() * 1e3;

    assert_eq!(plain_35[0], want_c0);
    assert_eq!(plain_35[1], want_c1);
    assert_eq!(plain_35[2], want_c2);
    assert!(plain_35[3..64].iter().all(|&x| x == 0));

    println!(
        "[3-of-5 @ N=8192] DKG={:.2} ms | DistRelin={:.2} ms | BlindPdProve/party={:.2} ms | \
         Combine3of5={:.2} ms | OfflineParties=[0,2] | max|diff|=0",
        dkg35_ms,
        rlk35_ms,
        pd35_ms / 3.0,
        comb35_ms,
    );
    println!("============================================================================================\n");

    let _ = std::fs::remove_dir_all(&dir);
}

/// 3. Exact Algebraic Rank (`TVD == 0`) & Statistical Witness-Indistinguishability Audit of `BlindedRPdEvals`
///    + Information-Theoretic `t - 1` Coalition Secrecy (`NoSingleViewer >= 2`).
#[test]
fn test_gmask61_blind_r_pd_exact_tvd_zero_and_t_minus_1_secrecy() {
    let dir = temp_test_dir("tvd0");
    let params = Arc::new(params_ring_homo(64));
    let fp0: FastPrime61 = params.fp[0];

    // (a) Prove algebraic `TVD == 0` on `BlindedRPdEvals = (s_{i,0}(r) + mu_0(r), ..., e(r) + mu_3(r)) mod p_0`:
    //     For ANY Fiat-Shamir challenge `r in F_{p_0}`, the `4 x (4 * N)` linear map from the auxiliary blinding
    //     row `(mu_0, mu_1, mu_2, mu_3) in (F_{p_0}^N)^4` to `BlindedRPdEvals in F_{p_0}^4` has the `4 x 4`
    //     identity submatrix on constant terms `(mu_0[0], mu_1[0], mu_2[0], mu_3[0])` because `r^0 == 1` for EVERY
    //     `r in F_{p_0}` (including `r == 0`)! Verify full row rank == 4 explicitly by Gaussian elimination:
    for &r_test in &[0u64, 1u64, 123_456_789_012_345u64, fp0.p - 1] {
        let mut r_pows = vec![1u64; params.n];
        for j in 1..params.n {
            r_pows[j] = fp0.mul(r_pows[j - 1], r_test);
        }
        // Build `4 x (4 * N)` Jacobian over `F_{p_0}`:
        let cols = 4 * params.n;
        let mut jac = vec![vec![0u64; cols]; 4];
        for row in 0..4 {
            for j in 0..params.n {
                jac[row][row * params.n + j] = r_pows[j];
            }
        }
        let mut rank = 0usize;
        for col in 0..cols {
            if rank == 4 {
                break;
            }
            if let Some(piv) = (rank..4).find(|&r| jac[r][col] != 0) {
                jac.swap(rank, piv);
                let inv = fp0.inv(jac[rank][col]);
                for c in col..cols {
                    jac[rank][c] = fp0.mul(jac[rank][c], inv);
                }
                for r in 0..4 {
                    if r != rank && jac[r][col] != 0 {
                        let f = jac[r][col];
                        for c in col..cols {
                            let sub = fp0.mul(f, jac[rank][c]);
                            jac[r][c] = fp0.sub(jac[r][c], sub);
                        }
                    }
                }
                rank += 1;
            }
        }
        assert_eq!(rank, 4, "Auxiliary blinding map must have exact rank 4 => TVD == 0!");
    }

    // (b) Multi-trial empirical witness-indistinguishability across independent decryptions by the same custodian:
    //     Verify zero collision across 12 `BlindedRPdEvals` transcripts and balanced LSBs (`~0.50` density).
    let policy_digest = [0xAAu8; 32];
    let (engine, _, mut parties, pk, dkg_tr, rlk, _, _) = run_distributed_committee_setup(
        params.clone(),
        3,
        2,
        policy_digest,
        true,
        &dir.join("stat"),
    );

    let mut seen_masked_s0 = std::collections::BTreeSet::new();
    let mut lsb_ones = 0usize;
    let mut total_bits = 0usize;
    let mut rng = PcsRng::from_seed(os_csprng_seed32());

    for trial in 0..8usize {
        let mut m_a = vec![0u64; 64];
        let mut m_b = vec![0u64; 64];
        m_a[0] = (trial as u64 + 3) * 17;
        m_b[0] = (trial as u64 + 5) * 29;
        let a_grid = vec![vec![pk.encrypt_pk(&m_a, &mut rng)]];
        let b_vec = vec![pk.encrypt_pk(&m_b, &mut rng)];
        let ha = vec![vec![ct2_handle(&a_grid[0][0])]];
        let hb = vec![ct2_handle(&b_vec[0])];
        let (out_cts, bun, _, _) = prove_hoisted_whir(
            &engine,
            &a_grid,
            &b_vec,
            None,
            LiftMode::ExactGarner15,
            LogUpConfig::BatchedC3 { chunk_log2: 18 },
        )
        .unwrap();
        let wb = bun.to_bytes();
        let hout = vec![ct3_handle(&out_cts[0])];
        let ct2 = engine.relinearize_ct3(&out_cts[0], &rlk);
        let sel = vec![0usize, 1usize];
        let ct_com = compute_ct_opening_commitment(&ct2_handle(&ct2), None, &sel);
        let auth = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            (trial + 1) as u64,
            1,
            policy_digest,
            ct_com,
            Sha256::digest(&wb).into(),
            1,
            0,
            sel.clone(),
        );
        let prov = WhirComputeProvenance {
            ha_grid: &ha,
            hb_vec: &hb,
            hout_vec: &hout,
            opened_a: Some(&a_grid),
            expected_persistent_a_root: None,
            opened_b: &b_vec,
            out_cts: &out_cts,
            target_output_row: 0,
            whir_proof_bytes: &wb,
        };
        let prf0 = parties[0]
            .partial_decrypt_relinearized_ct2_gated(&auth, &prov, &ct2, None)
            .unwrap();
        let prf1 = parties[1]
            .partial_decrypt_relinearized_ct2_gated(&auth, &prov, &ct2, None)
            .unwrap();

        // Every proof must emit a fresh uniform `masked_s_evals[0]` EVEN THOUGH `parties[0]`'s secret share `s_0` is fixed!
        assert!(seen_masked_s0.insert(prf0.blinded_evals.masked_s_evals[0]));
        for &val in prf0
            .blinded_evals
            .masked_s_evals
            .iter()
            .chain(std::iter::once(&prf0.blinded_evals.masked_e_eval))
        {
            for bit in 0..32 {
                lsb_ones += ((val >> bit) & 1) as usize;
                total_bits += 1;
            }
        }

        let dec = combine_verified_threshold_shares(
            &params,
            &auth.statement_digest(),
            &dkg_tr,
            parties[0].smudge_bound,
            parties[0].smudge_top_bits,
            &ct2,
            &ct_com,
            &sel,
            &[prf0, prf1],
        )
        .unwrap();
        assert_eq!(dec[0], (m_a[0] * m_b[0]) % params.t);
    }
    let ratio = lsb_ones as f64 / total_bits as f64;
    assert!(
        (0.40..=0.60).contains(&ratio),
        "BlindedRPdEvals bit balance out of uniform band: {ratio}"
    );

    // (c) Information-Theoretic `t - 1` Secrecy (`NoSingleViewer = 3` in `3-of-5`):
    //     Verify that for ANY candidate constant `s_cand in F_q`, there exists a unique degree-`2` Shamir polynomial
    //     matching any `t - 1 = 2` colluding custodians' evaluations `(x_1 = 1, y_1)` and `(x_2 = 2, y_2)`!
    let q0 = fp0.p;
    let (y1, y2) = (777_777u64, 999_999u64);
    for &s_cand in &[0u64, 1u64, q0 - 1, 424_242_424u64] {
        // Interpolate `P(x)` of degree `<= 2` through `(0, s_cand), (1, y1), (2, y2)` via Lagrange:
        let eval_at = |x: u64| -> u64 {
            let pts = [(0u64, s_cand), (1u64, y1), (2u64, y2)];
            let mut acc = 0u64;
            for i in 0..3 {
                let (xi, yi) = pts[i];
                let mut num = 1u64;
                let mut den = 1u64;
                for j in 0..3 {
                    if i == j {
                        continue;
                    }
                    let xj = pts[j].0;
                    num = fp0.mul(num, fp0.sub(x, xj));
                    den = fp0.mul(den, fp0.sub(xi, xj));
                }
                acc = fp0.add(acc, fp0.mul(yi, fp0.mul(num, fp0.inv(den))));
            }
            acc
        };
        assert_eq!(eval_at(0), s_cand);
        assert_eq!(eval_at(1), y1);
        assert_eq!(eval_at(2), y2);
        // Verify Lagrange reconstruction on `{0, 1, 2}` -> `{x = 1, 2, 3}` recovers `s_cand`!
        let y3 = eval_at(3);
        let sel = [0usize, 1usize, 2usize];
        let rec = fp0.add(
            fp0.mul(lagrange_coeff_at_zero_mod_q(0, &sel, q0), y1),
            fp0.add(
                fp0.mul(lagrange_coeff_at_zero_mod_q(1, &sel, q0), y2),
                fp0.mul(lagrange_coeff_at_zero_mod_q(2, &sel, q0), y3),
            ),
        );
        assert_eq!(rec, s_cand);
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// 4. Complete `15/15` Adversarial Attack Falsifier Matrix Across DKG, Transport, Persisted `C8` Gate, & `WhirBlindPdProof`.
#[test]
fn test_15_adversarial_attacks_deterministically_refused() {
    let dir = temp_test_dir("adv15");
    let params = Arc::new(params_ring_homo(64));
    let policy_digest = [0x5Au8; 32];
    let mut rejected_attacks = 0usize;

    // --- ATTACK 1: `t < 2` (`1-of-3`, violating `NoSingleViewer >= 2`) & `t >= n` (`3-of-3`, non-crash-tolerant) ---
    {
        let ids: Vec<_> = (0..3)
            .map(|i| HybridPqCustodianIdentity::generate_from_os(i, 5, None).unwrap())
            .collect();
        let enrs: Vec<_> = ids.iter().map(|x| x.enrollment()).collect();
        assert!(matches!(
            EnrolledThresholdRoster::new(1, enrs.clone()),
            Err(ThresholdCustodyError::InvalidThreshold { threshold: 1, n_parties: 3 })
        ));
        assert!(matches!(
            EnrolledThresholdRoster::new(3, enrs),
            Err(ThresholdCustodyError::InvalidThreshold { threshold: 3, n_parties: 3 })
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 2: Malicious dealer corrupting private VSS row addressed to victim `1` ---
    {
        let mut ids: Vec<_> = (0..3)
            .map(|i| HybridPqCustodianIdentity::generate_from_os(i, 5, None).unwrap())
            .collect();
        let enrs: Vec<_> = ids.iter().map(|x| x.enrollment()).collect();
        let roster = EnrolledThresholdRoster::new(2, enrs).unwrap();
        let dkg = DistributedThresholdDkg::new(params.clone(), roster, [0x11u8; 32]).unwrap();
        let (bcast, _, sealed, _) = dkg
            .deal_adversarial_for_test(&mut ids[0], Some(1), None)
            .unwrap();
        let env_for_1 = &sealed.iter().find(|(r, _)| *r == 1).unwrap().1;
        assert!(matches!(
            dkg.accept_dealing(&ids[1], &bcast, env_for_1),
            Err(ThresholdCustodyError::VssRowCommitmentMismatch { dealer: 0, recipient: 1 })
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 3: Equivocating dealer breaking bivariate symmetry `F(i,j) != F(j,i)` ---
    {
        let mut ids: Vec<_> = (0..3)
            .map(|i| HybridPqCustodianIdentity::generate_from_os(i, 5, None).unwrap())
            .collect();
        let enrs: Vec<_> = ids.iter().map(|x| x.enrollment()).collect();
        let roster = EnrolledThresholdRoster::new(2, enrs).unwrap();
        let dkg = DistributedThresholdDkg::new(params.clone(), roster, [0x22u8; 32]).unwrap();

        let mut bcasts = Vec::new();
        let mut inbox: Vec<Vec<(usize, Vec<u8>)>> = (0..3).map(|_| Vec::new()).collect();
        let mut own = Vec::new();
        for d in 0..3 {
            let (bc, o, s, _) = if d == 0 {
                dkg.deal_adversarial_for_test(&mut ids[d], None, Some(1))
                    .unwrap()
            } else {
                dkg.deal_from_os(&mut ids[d]).unwrap()
            };
            for (r, e) in s {
                inbox[r].push((d, e));
            }
            bcasts.push(bc);
            own.push(Some(o));
        }
        let mut acc: Vec<Vec<_>> = Vec::new();
        for r in 0..3 {
            let mut m = std::collections::BTreeMap::new();
            m.insert(r, own[r].take().unwrap());
            for (d, e) in &inbox[r] {
                m.insert(*d, dkg.accept_dealing(&ids[r], &bcasts[*d], e).unwrap());
            }
            acc.push((0..3).map(|d| m.remove(&d).unwrap()).collect());
        }
        let cross_1_to_2 = dkg.seal_cross_evaluations(&mut ids[1], &acc[1], 2).unwrap();
        assert!(matches!(
            dkg.verify_cross_evaluations(&ids[2], &acc[2], 1, &cross_1_to_2),
            Err(ThresholdCustodyError::VssInconsistentRows { dealer: 0, left: 1, right: 2 })
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 4: Sealed confidential envelope rerouted or ciphertext-tampered in flight ---
    {
        let mut ids: Vec<_> = (0..3)
            .map(|i| HybridPqCustodianIdentity::generate_from_os(i, 5, None).unwrap())
            .collect();
        let enrs: Vec<_> = ids.iter().map(|x| x.enrollment()).collect();
        let roster = EnrolledThresholdRoster::new(2, enrs).unwrap();
        let dom = [0x33u8; 32];
        let mut env = roster
            .seal_to_peer(&mut ids[0], 1, &dom, 1, b"secret-vss-share")
            .unwrap();
        assert!(roster.open_from_peer(&ids[2], 0, &dom, 1, &env).is_err());
        env[56] ^= 0xFF;
        assert!(roster.open_from_peer(&ids[1], 0, &dom, 1, &env).is_err());
        rejected_attacks += 1;
    }

    // Stand up an honest `2-of-3` committee for Attacks 5..15:
    let (engine, _, mut parties, pk, dkg_tr, rlk, _, _) = run_distributed_committee_setup(
        params.clone(),
        3,
        2,
        policy_digest,
        true,
        &dir.join("honest"),
    );
    let mut rng = PcsRng::from_seed(os_csprng_seed32());
    let mut ma = vec![0u64; 64];
    let mut mb = vec![0u64; 64];
    ma[0] = 91;
    mb[0] = 37;
    let a_grid = vec![vec![pk.encrypt_pk(&ma, &mut rng)]];
    let b_vec = vec![pk.encrypt_pk(&mb, &mut rng)];
    let ha = vec![vec![ct2_handle(&a_grid[0][0])]];
    let hb = vec![ct2_handle(&b_vec[0])];
    let (out_cts, bun, _, _) = prove_hoisted_whir(
        &engine,
        &a_grid,
        &b_vec,
        None,
        LiftMode::ExactGarner15,
        LogUpConfig::BatchedC3 { chunk_log2: 18 },
    )
    .unwrap();
    let wb = bun.to_bytes();
    let wb_dig: [u8; 32] = Sha256::digest(&wb).into();
    let hout = vec![ct3_handle(&out_cts[0])];
    let ct2 = engine.relinearize_ct3(&out_cts[0], &rlk);
    let sel = vec![0usize, 1usize];
    let ct_com = compute_ct_opening_commitment(&ct2_handle(&ct2), None, &sel);
    let prov = WhirComputeProvenance {
        ha_grid: &ha,
        hb_vec: &hb,
        hout_vec: &hout,
        opened_a: Some(&a_grid),
        expected_persistent_a_root: None,
        opened_b: &b_vec,
        out_cts: &out_cts,
        target_output_row: 0,
        whir_proof_bytes: &wb,
    };

    // --- ATTACK 5: `epoch == 0` in `OpeningAuthorization` (`ZeroEpochRejected`) ---
    {
        let auth_zero = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            0,
            1,
            policy_digest,
            ct_com,
            wb_dig,
            1,
            0,
            sel.clone(),
        );
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(&auth_zero, &prov, &ct2, None),
            Err(ThresholdCustodyError::ZeroEpochRejected)
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 6: `R_refresh > 1` (`refresh_cadence = 3`) in `tvd_40b_strict_mode` ---
    {
        let auth_r3 = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            5,
            1,
            policy_digest,
            ct_com,
            wb_dig,
            3,
            0,
            sel.clone(),
        );
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(&auth_r3, &prov, &ct2, None),
            Err(ThresholdCustodyError::StrictRefreshCadenceViolation { got: 3, .. })
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 7: Wrong `policy_digest` in `OpeningAuthorization` ---
    {
        let auth_pol = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            5,
            1,
            [0xFFu8; 32],
            ct_com,
            wb_dig,
            1,
            0,
            sel.clone(),
        );
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(&auth_pol, &prov, &ct2, None),
            Err(ThresholdCustodyError::PolicyDigestMismatch)
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 8: Under-quorum (`1 < t = 2`) or tampered PQ signature on `OpeningAuthorization` ---
    {
        let auth_1sig = sign_quorum_opening_auth(
            &mut parties,
            &[0],
            dkg_tr.digest,
            5,
            1,
            policy_digest,
            ct_com,
            wb_dig,
            1,
            0,
            sel.clone(),
        );
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(&auth_1sig, &prov, &ct2, None),
            Err(ThresholdCustodyError::QuorumSignaturesInsufficient { have: 1, need: 2 })
        ));
        let mut auth_bad_pq = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            5,
            1,
            policy_digest,
            ct_com,
            wb_dig,
            1,
            0,
            sel.clone(),
        );
        auth_bad_pq.quorum_signatures[1].pq_lamport_sig[20] ^= 0x01;
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(&auth_bad_pq, &prov, &ct2, None),
            Err(ThresholdCustodyError::HybridSignatureInvalid(_))
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 9: Corrupted `WhirPcs61` (`DVFHEWH1`) compute proof OR forged relinearized `Ct` ---
    {
        let mut bad_wb = wb.clone();
        let mid = bad_wb.len() / 2;
        bad_wb[mid] ^= 0x40;
        let bad_wb_dig: [u8; 32] = Sha256::digest(&bad_wb).into();
        let bad_prov = WhirComputeProvenance {
            whir_proof_bytes: &bad_wb,
            ..prov
        };
        let auth_bad_comp = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            5,
            1,
            policy_digest,
            ct_com,
            bad_wb_dig,
            1,
            0,
            sel.clone(),
        );
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(&auth_bad_comp, &bad_prov, &ct2, None),
            Err(ThresholdCustodyError::InvalidWhirComputeProof(_))
        ));
        assert_eq!(
            parties[0].audit_log.entry_count, 0,
            "failed compute proof must NEVER pollute audit log"
        );

        let mut forged_ct2 = ct2.clone();
        forged_ct2.c0[0] = (forged_ct2.c0[0] + 1) % params.qp[0];
        let forged_com = compute_ct_opening_commitment(&ct2_handle(&forged_ct2), None, &sel);
        let auth_forged_relin = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            5,
            1,
            policy_digest,
            forged_com,
            wb_dig,
            1,
            0,
            sel.clone(),
        );
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(&auth_forged_relin, &prov, &forged_ct2, None),
            Err(ThresholdCustodyError::InvalidWhirComputeProof(_))
        ));
        rejected_attacks += 1;
    }

    // Now execute ONE valid opening at `epoch = 10, sequence = 1`:
    let auth_ok = sign_quorum_opening_auth(
        &mut parties,
        &sel,
        dkg_tr.digest,
        10,
        1,
        policy_digest,
        ct_com,
        wb_dig,
        1,
        0,
        sel.clone(),
    );
    let honest_pd0 = parties[0]
        .partial_decrypt_relinearized_ct2_gated(&auth_ok, &prov, &ct2, None)
        .unwrap();
    let _honest_pd1 = parties[1]
        .partial_decrypt_relinearized_ct2_gated(&auth_ok, &prov, &ct2, None)
        .unwrap();
    assert_eq!(parties[0].audit_log.entry_count, 1);

    // --- ATTACK 10: `stale_epoch` (`epoch = 9 < high_water = 10`) deterministically rejected ---
    {
        let mask_ct = pk.encrypt_pk(&vec![0u64; 64], &mut rng);
        let fresh_com =
            compute_ct_opening_commitment(&ct2_handle(&ct2), Some(&ct2_handle(&mask_ct)), &sel);
        let auth_stale = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            9,
            1,
            policy_digest,
            fresh_com,
            wb_dig,
            1,
            0,
            sel.clone(),
        );
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(&auth_stale, &prov, &ct2, Some(&mask_ct)),
            Err(ThresholdCustodyError::StaleEpoch { got: 9, high_water: 10 })
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 11: `double_open` across CUSTODIAN RESTART (even at HIGHER `epoch = 11` & fresh `ct_mask_r`!) ---
    {
        let log_path_0 = dir.join("honest").join("custodian_0.audit.log");
        parties[0].reload_audit_log_from_disk(&log_path_0).unwrap();
        assert_eq!(parties[0].audit_log.high_water_epoch, Some(10));

        let mask_ct = pk.encrypt_pk(&vec![1u64; 64], &mut rng);
        let masked_com =
            compute_ct_opening_commitment(&ct2_handle(&ct2), Some(&ct2_handle(&mask_ct)), &sel);
        let auth_smudge_avg = sign_quorum_opening_auth(
            &mut parties,
            &sel,
            dkg_tr.digest,
            11,
            1,
            policy_digest,
            masked_com,
            wb_dig,
            1,
            0,
            sel.clone(),
        );
        assert!(matches!(
            parties[0].partial_decrypt_relinearized_ct2_gated(
                &auth_smudge_avg,
                &prov,
                &ct2,
                Some(&mask_ct)
            ),
            Err(ThresholdCustodyError::DoubleOpen)
        ));
        rejected_attacks += 1;
    }

    // --- ATTACK 12: Torn / corrupted append-only audit log on disk refused on reload AND permanently poisons custodian (`CAP-07` closure) ---
    {
        let log_path_1 = dir.join("honest").join("custodian_1.audit.log");
        {
            let mut f = OpenOptions::new().append(true).open(&log_path_1).unwrap();
            f.write_all(b"torn_partial_record").unwrap();
        }
        assert!(matches!(
            parties[1].reload_audit_log_from_disk(&log_path_1),
            Err(ThresholdCustodyError::CorruptedAuditLog(_))
        ));
        assert!(matches!(
            parties[1].partial_decrypt_relinearized_ct2_gated(&auth_ok, &prov, &ct2, None),
            Err(ThresholdCustodyError::AuditLogPoisoned)
        ));
        rejected_attacks += 1;
    }

    let auth_ok_stmt = auth_ok.statement_digest();

    // --- ATTACK 13: Tampered `partial_rns` (`d_0[0] + 1`) OR detached `auth_statement_digest` rejected by `verify_blind_r_pd_whir61` ---
    {
        let mut forged_pd = honest_pd0.clone();
        forged_pd.partial_rns[0] = (forged_pd.partial_rns[0] + 1) % params.qp[0];
        assert!(verify_blind_r_pd_whir61(
            &params,
            0,
            &sel,
            &auth_ok_stmt,
            &dkg_tr,
            parties[0].smudge_bound,
            parties[0].smudge_top_bits,
            &ct2,
            &ct_com,
            &forged_pd,
        )
        .is_err());
        assert!(verify_blind_r_pd_whir61(
            &params,
            0,
            &sel,
            &[0xEEu8; 32],
            &dkg_tr,
            parties[0].smudge_bound,
            parties[0].smudge_top_bits,
            &ct2,
            &ct_com,
            &honest_pd0,
        )
        .is_err());
        rejected_attacks += 1;
    }

    // --- ATTACK 14: Tampered `BlindedRPdEvals` (`masked_s_evals[0] + 1` or `masked_e_eval + 1`) rejected (load-bearing weld!) ---
    {
        let mut bad_s = honest_pd0.clone();
        bad_s.blinded_evals.masked_s_evals[0] =
            (bad_s.blinded_evals.masked_s_evals[0] + 1) % params.qp[0];
        assert!(verify_blind_r_pd_whir61(
            &params,
            0,
            &sel,
            &auth_ok_stmt,
            &dkg_tr,
            parties[0].smudge_bound,
            parties[0].smudge_top_bits,
            &ct2,
            &ct_com,
            &bad_s,
        )
        .is_err());

        let mut bad_e = honest_pd0.clone();
        bad_e.blinded_evals.masked_e_eval = (bad_e.blinded_evals.masked_e_eval + 1) % params.qp[0];
        assert!(verify_blind_r_pd_whir61(
            &params,
            0,
            &sel,
            &auth_ok_stmt,
            &dkg_tr,
            parties[0].smudge_bound,
            parties[0].smudge_top_bits,
            &ct2,
            &ct_com,
            &bad_e,
        )
        .is_err());
        rejected_attacks += 1;
    }

    // --- ATTACK 15: Wrong secret share `s'_0 != s_0`, verifier-side BDLOP anchor tamper, AND verifier-side `|e| = E + 1` rejection! ---
    {
        let wrong_s = vec![1u64; 3 * 64];
        let zero_e = vec![0i128; 64];
        let fake_prf = parties[0].prove_unverified_custom_witness_for_test(
            &sel,
            &auth_ok_stmt,
            &ct2,
            &wrong_s,
            &zero_e,
            &ct_com,
        );
        assert!(
            fake_prf.is_err(),
            "prover/BDLOP check must refuse secret share s'_0 != s_0"
        );
        // Prover-side out-of-range smudge `|e| = E + 1` refusal:
        let big_e = vec![parties[0].smudge_bound as i128 + 1; 64];
        assert!(parties[0]
            .prove_unverified_custom_witness_for_test(
                &sel,
                &auth_ok_stmt,
                &ct2,
                &wrong_s,
                &big_e,
                &ct_com
            )
            .is_err());
        // TRUE VERIFIER-SIDE `|e| = E + 1` (`e_sh = 2E + 1`) rejection: bypasses prover check, satisfies LogUp & RingModQk,
        // and MUST be rejected by `verify_blind_r_pd_whir61`'s `e_sh + e_rev == 2E` pair-carry constraint!
        let forged_e_plus_1_prf = parties[0]
            .forge_e_plus_1_proof_bypassing_prover_for_test(&sel, &auth_ok_stmt, &ct2, &ct_com)
            .unwrap();
        assert!(
            verify_blind_r_pd_whir61(
                &params,
                0,
                &sel,
                &auth_ok_stmt,
                &dkg_tr,
                parties[0].smudge_bound,
                parties[0].smudge_top_bits,
                &ct2,
                &ct_com,
                &forged_e_plus_1_prf,
            )
            .is_err(),
            "verifier must reject smudge e = E + 1 (e_sh = 2E + 1)"
        );
        // Verifier-side BDLOP key-binding soundness (even when `digest` is recomputed for the mutated anchor!):
        let mut wrong_anchor_tr = dkg_tr.clone();
        wrong_anchor_tr.party_bdlop_anchors[0].t1_coeff[0] =
            (wrong_anchor_tr.party_bdlop_anchors[0].t1_coeff[0] + 1) % params.qp[0];
        wrong_anchor_tr.digest = VerifiedThresholdDkgTranscript::compute_canonical_digest(
            &wrong_anchor_tr.session_domain,
            wrong_anchor_tr.n_parties,
            wrong_anchor_tr.threshold,
            &wrong_anchor_tr.crp_seed,
            &wrong_anchor_tr.bcast_list_digest,
            &wrong_anchor_tr.a_pk_coeff,
            &wrong_anchor_tr.b_pk_coeff,
            &wrong_anchor_tr.bdlop_crs,
            &wrong_anchor_tr.party_bdlop_anchors,
        );
        assert!(
            verify_blind_r_pd_whir61(
                &params,
                0,
                &sel,
                &auth_ok_stmt,
                &wrong_anchor_tr,
                parties[0].smudge_bound,
                parties[0].smudge_top_bits,
                &ct2,
                &ct_com,
                &honest_pd0,
            )
            .is_err(),
            "verifier must reject proof whose committed s_0 disagrees with public BDLOP anchor"
        );
        rejected_attacks += 1;
    }

    assert_eq!(rejected_attacks, 15);
    println!("[ADVERSARIAL SUITE] 15/15 attack families deterministically refused!");
    let _ = std::fs::remove_dir_all(&dir);
}
