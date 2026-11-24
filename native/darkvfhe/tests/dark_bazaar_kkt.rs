#![deny(warnings)]
//! End-to-end integration, benchmark, Lean golden-parity, and adversarial security-gate suite for
//! `darkvfhe::dark_clearing` (`FHSDD001`, `FHQPB001`, `DBNET001`, `DBWHIR61` `N = 8192` `DarkBazaar` & Private `{0,1}` Tally).

use darkvfhe::dark_block::{params_n8192_homo, params_ring_homo};
use darkvfhe::dark_clearing::{
    bfv_ct_handle, canonical_qp_program_digest, compress_multilateral_legs,
    encrypt_and_prove_submission_whir, execute_dark_bazaar_clearing_epoch,
    execute_private_voting_tally_epoch, prove_submission_from_raw_witness,
    solve_certified_call_auction_qp, verify_encrypted_submission_whir,
    verify_fhsdd001_row_dominant, BfvSubmissionWhirProof61, CallAuctionQpConfig, ClearingError,
    DarkClearingCommittee, ExactQpCertificateBundle, ExactSddFactorCertificate,
    MultilateralNettingCertificate, OpeningAuthorization, SddFactorEdgeInt, SettlementLeg,
    SubmissionSpec,
};
use darkvfhe::succinct_pcs::PcsRng;
use std::time::Instant;

#[test]
fn fhqpb001_and_dbnet001_lean_golden_parity_and_adversarial_teeth() {
    // 1. Exact parity with `auctionQpWitness` in `Theory/ExactKktClearingCert.lean` (`Q = [[2,-1],[-1,2]]`,
    // `x* = [3, 3]`, `nu* = 9`, `eps = 0`):
    let q_mat = vec![vec![2, -1], vec![-1, 2]];
    let q_vec = vec![-12, 6];
    let a_mat = vec![vec![1, -1]];
    let b_vec = vec![0];
    let l_vec = vec![0, 0];
    let u_vec = vec![10, 8];

    verify_fhsdd001_row_dominant(1, &q_mat)
        .expect("[[2,-1],[-1,2]] is row-diagonally-dominant SDD");

    let digest =
        canonical_qp_program_digest(1, &q_mat, &q_vec, &a_mat, &b_vec, &[], &[], &l_vec, &u_vec);
    let witness_bundle = ExactQpCertificateBundle {
        scale_denom: 1,
        sdd: ExactSddFactorCertificate {
            n: 2,
            scale_denom: 1,
            edges: vec![SddFactorEdgeInt {
                u: 0,
                v: 1,
                alpha: 1,
                beta: -1,
                weight: 1,
            }],
            diag_slack: vec![1, 1],
            admitted_q: q_mat.clone(),
        },
        q_mat: q_mat.clone(),
        q_vec,
        a_mat,
        b_vec,
        g_mat: vec![],
        h_vec: vec![],
        l_vec,
        u_vec,
        x_vec: vec![3, 3],
        nu_vec: vec![9],
        mu_vec: vec![],
        lam_l_vec: vec![0, 0],
        lam_u_vec: vec![0, 0],
        eps_int: 0,
        program_digest: digest,
    };

    let t0 = Instant::now();
    let summary = witness_bundle
        .verify_zero_gap()
        .expect("Lean golden witness must verify");
    let verify_ns = t0.elapsed().as_nanos();
    assert_eq!(summary.comp_gap_scaled, 0);
    assert_eq!(summary.two_primal_scaled, summary.two_dual_scaled);

    let wire = witness_bundle.to_wire_bytes();
    let (decoded, summary2) = ExactQpCertificateBundle::from_wire_bytes_and_verify(&wire)
        .expect("FHQPB001 wire roundtrip");
    assert_eq!(decoded, witness_bundle);
    assert_eq!(summary2, summary);
    println!(
        "[FHQPB001] 2-var SDD-Laplacian KKT verify={} ns, wire={} B",
        verify_ns,
        wire.len()
    );

    // Tooth A2 (`indefinite2Int = [[1, 2], [2, 1]]`):
    assert_eq!(
        verify_fhsdd001_row_dominant(1, &[vec![1, 2], vec![2, 1]]),
        Err(ClearingError::RowDominanceRejected { row: 0 })
    );

    // Tooth A1 (negative edge weight):
    let mut neg_edge_bundle = witness_bundle.clone();
    neg_edge_bundle.sdd.edges[0].weight = -1;
    assert!(matches!(
        neg_edge_bundle.verify(),
        Err(ClearingError::NegativeEdgeWeight { .. })
    ));

    // Tooth B1 (`unpinnedConcaveBundle`: valid SDD `+1` paired with concave `Q = -1` rejected by Matrix Pin!):
    let mut unpinned = witness_bundle.clone();
    unpinned.q_mat = vec![vec![-2, 1], vec![1, -2]];
    assert_eq!(unpinned.verify(), Err(ClearingError::MatrixPinMismatch));

    // Tooth B2 (wrong-sign dual multiplier):
    let mut bad_dual = witness_bundle.clone();
    bad_dual.lam_l_vec[0] = -1;
    assert!(matches!(
        bad_dual.verify(),
        Err(ClearingError::NegativeDualMultiplier { .. })
    ));

    // Tooth B3 (optimality gap exceeded + bit-flip tamper):
    let mut flipped_wire = wire.clone();
    let mid = flipped_wire.len() / 2;
    flipped_wire[mid] ^= 0x01;
    assert_eq!(
        ExactQpCertificateBundle::from_wire_bytes_and_verify(&flipped_wire),
        Err(ClearingError::ChecksumMismatch)
    );

    // 2. Exact parity with `witnessGrossLegs` / `witnessNetLegs` in `Theory/ExactKktClearingCert.lean`:
    let gross = vec![
        SettlementLeg {
            payer: 1,
            payee: 2,
            asset: 0,
            amount: 110,
        },
        SettlementLeg {
            payer: 2,
            payee: 3,
            asset: 0,
            amount: 80,
        },
        SettlementLeg {
            payer: 3,
            payee: 1,
            asset: 0,
            amount: 60,
        },
        SettlementLeg {
            payer: 2,
            payee: 4,
            asset: 0,
            amount: 30,
        },
    ];
    let net_cert = compress_multilateral_legs(&gross).expect("compress multilateral legs");
    assert_eq!(
        net_cert.net_legs,
        vec![
            SettlementLeg {
                payer: 1,
                payee: 3,
                asset: 0,
                amount: 20
            },
            SettlementLeg {
                payer: 1,
                payee: 4,
                asset: 0,
                amount: 30
            },
        ]
    );
    let net_summary = net_cert.verify().expect("netting cert verify");
    assert_eq!(net_summary.gross_volume, 280);
    assert_eq!(net_summary.net_volume, 50);

    // Tooth C1 (value creation `+1` unit refused):
    let bad_val = MultilateralNettingCertificate {
        gross_legs: gross.clone(),
        net_legs: vec![
            SettlementLeg {
                payer: 1,
                payee: 3,
                asset: 0,
                amount: 20,
            },
            SettlementLeg {
                payer: 1,
                payee: 4,
                asset: 0,
                amount: 31,
            },
        ],
    };
    assert!(matches!(
        bad_val.verify(),
        Err(ClearingError::NetBalanceMismatch { .. })
    ));

    // Tooth C2 (gross exposure inflation refused):
    let bad_vol = MultilateralNettingCertificate {
        gross_legs: vec![SettlementLeg {
            payer: 1,
            payee: 2,
            asset: 0,
            amount: 100,
        }],
        net_legs: vec![
            SettlementLeg {
                payer: 1,
                payee: 9,
                asset: 0,
                amount: 80,
            },
            SettlementLeg {
                payer: 9,
                payee: 2,
                asset: 0,
                amount: 80,
            },
            SettlementLeg {
                payer: 1,
                payee: 2,
                asset: 0,
                amount: 20,
            },
        ],
    };
    assert_eq!(
        bad_vol.verify(),
        Err(ClearingError::GrossVolumeInflated {
            net_vol: 180,
            gross_vol: 100,
        })
    );

    // Non-integer rational clearing QP (`gamma_prox = 3, w_lap = 2`, `scale_denom > 1` exact active-set):
    let frac_cfg = CallAuctionQpConfig {
        tick_prices: vec![101, 107, 113],
        surplus_weight: 5,
        gamma_prox: 3,
        w_lap: 2,
    };
    let frac_res = solve_certified_call_auction_qp(&frac_cfg, &[7, 11, 13], &[9, 8, 5])
        .expect("exact rational SDD-Laplacian QP solve");
    assert_eq!(frac_res.kkt_summary.comp_gap_scaled, 0);
}

#[test]
fn n8192_dark_bazaar_encrypted_call_auction_and_multilateral_netting_e2e() {
    // Production `N = 8192` (`log2 Q = 183`, Blum prime `t = 4,355,803,843`) + `NoSingleViewer = 2` (`2-of-3`):
    let params = params_n8192_homo();
    assert_eq!(params.n, 8192);
    let mut committee =
        DarkClearingCommittee::setup(params.clone(), 2, 3).expect("2-of-3 committee setup");

    let tick_prices = vec![100, 105, 110, 115];
    let spec = SubmissionSpec::DemandSupplyCurve {
        num_ticks: 4,
        tick_prices: tick_prices.clone(),
        max_qty_per_tick: 1_000,
    };
    let qp_cfg = CallAuctionQpConfig {
        tick_prices,
        surplus_weight: 64,
        gamma_prox: 2,
        w_lap: 1,
    };

    // 3 private institutional bidders submit encrypted demand/supply curves (`N = 8192` slots):
    let bidder_books: [([u64; 4], [u64; 4]); 3] = [
        ([0, 20, 50, 80], [60, 30, 0, 0]),
        ([10, 40, 60, 30], [20, 45, 25, 0]),
        ([5, 15, 30, 40], [40, 25, 35, 10]),
    ];

    let mut rng = PcsRng::from_seed([0x51u8; 32]);
    let mut submissions = Vec::with_capacity(3);
    let mut prove_ms_total = 0.0f64;

    for (b_idx, (bids, asks)) in bidder_books.iter().enumerate() {
        let mut plain = vec![0u64; params.n];
        plain[0..4].copy_from_slice(bids);
        plain[4..8].copy_from_slice(asks);
        let mut nullifier = [0u8; 32];
        nullifier[0] = (b_idx + 1) as u8;

        let t_p = Instant::now();
        let sub = encrypt_and_prove_submission_whir(
            &params,
            &committee.pk,
            &spec,
            1,
            nullifier,
            &plain,
            &mut rng,
        )
        .expect("honest N=8192 bidder WHIR proof");
        prove_ms_total += t_p.elapsed().as_secs_f64() * 1000.0;

        // Verify standalone wire roundtrip of `DBWHIR61`:
        let wire = sub.proof.to_wire_bytes(params.qp[0]);
        let proof_wire_bytes = wire.len();
        let unpacked = BfvSubmissionWhirProof61::from_wire_bytes(&wire, params.qp[0])
            .expect("DBWHIR61 unpack");
        let mut sub_rt = sub.clone();
        sub_rt.proof = unpacked;
        let t_v = Instant::now();
        verify_encrypted_submission_whir(&params, &committee.pk, &spec, 1, &sub_rt)
            .expect("standalone WHIR verify");
        if b_idx == 0 {
            println!(
                "[DarkBazaar N=8192] single-bidder WhirPcs61 verify={:.2} ms, wire={} B ({:.1} KiB)",
                t_v.elapsed().as_secs_f64() * 1000.0,
                proof_wire_bytes,
                proof_wire_bytes as f64 / 1024.0
            );
        }
        submissions.push(sub);
    }

    // Gross bilateral fills across 5 counterparties with cyclic exposure -> multilateral netting:
    let gross_legs = vec![
        SettlementLeg {
            payer: 10,
            payee: 20,
            asset: 1,
            amount: 450,
        },
        SettlementLeg {
            payer: 20,
            payee: 30,
            asset: 1,
            amount: 400,
        },
        SettlementLeg {
            payer: 30,
            payee: 10,
            asset: 1,
            amount: 350,
        },
        SettlementLeg {
            payer: 20,
            payee: 40,
            asset: 1,
            amount: 120,
        },
        SettlementLeg {
            payer: 40,
            payee: 50,
            asset: 1,
            amount: 90,
        },
        SettlementLeg {
            payer: 50,
            payee: 10,
            asset: 1,
            amount: 90,
        },
    ];

    let t_ep = Instant::now();
    let receipt = execute_dark_bazaar_clearing_epoch(
        &mut committee,
        1,
        &spec,
        &qp_cfg,
        &submissions,
        &[0, 2], // 2-of-3 quorum (custodian 1 offline!)
        &gross_legs,
    )
    .expect("execute N=8192 DarkBazaar epoch");
    let epoch_ms = t_ep.elapsed().as_secs_f64() * 1000.0;

    assert_eq!(receipt.num_bidders, 3);
    assert_eq!(receipt.aggregate_bids, vec![15, 75, 140, 150]);
    assert_eq!(receipt.aggregate_asks, vec![120, 100, 60, 10]);
    assert_eq!(receipt.auction_clearing.kkt_summary.comp_gap_scaled, 0);
    // Exact supply == demand conservation in cleared quantities:
    let sum_cleared_bids: i64 = receipt.auction_clearing.cleared_bids_scaled.iter().sum();
    let sum_cleared_asks: i64 = receipt.auction_clearing.cleared_asks_scaled.iter().sum();
    assert_eq!(sum_cleared_bids, sum_cleared_asks);
    assert!(sum_cleared_bids > 0);
    // Multilateral netting compressed 6 gross legs (`volume = 1500`) to <= 3 net legs (`volume = 80`, 94.7% reduction!):
    assert!(receipt.netting_summary.net_leg_count <= 3);
    assert_eq!(receipt.netting_summary.gross_volume, 1500);
    assert_eq!(receipt.netting_summary.net_volume, 80);

    println!(
        "[DarkBazaar N=8192] 3-bidder avg_prove={:.2} ms, epoch_clear={:.2} ms, FHQPB001_verify={} us ({} B), DBNET001_verify={} us ({} B, {} -> {} legs, {} -> {} vol)",
        prove_ms_total / 3.0,
        epoch_ms,
        receipt.kkt_verify_us,
        receipt.fhqpb001_wire_bytes.len(),
        receipt.netting_verify_us,
        receipt.dbnet001_wire_bytes.len(),
        receipt.netting_summary.gross_leg_count,
        receipt.netting_summary.net_leg_count,
        receipt.netting_summary.gross_volume,
        receipt.netting_summary.net_volume,
    );
}

#[test]
fn n8192_private_voting_tally_kills_1e6_forgery_and_enforces_c8_threshold_gates() {
    // 1. `NoSingleViewer >= 2` policy hard-rejects `threshold = 1`:
    let params8192 = params_n8192_homo();
    assert!(matches!(
        DarkClearingCommittee::setup(params8192.clone(), 1, 3),
        Err(ClearingError::ThresholdPolicyViolation(_))
    ));

    // 2. Deployed `N = 8192` `3-of-4` Private `{0, 1}` Ballot Tally (`3` candidates, `1` vote max):
    let mut vote_comm =
        DarkClearingCommittee::setup(params8192.clone(), 3, 4).expect("3-of-4 voting committee");
    let vote_spec = SubmissionSpec::BinaryBallot {
        num_choices: 3,
        min_votes: 1,
        max_votes: 1,
    };

    let mut rng = PcsRng::from_seed([0x77u8; 32]);
    let mut ballots = Vec::new();
    for (v_idx, choice) in [1usize, 0, 1, 2].iter().enumerate() {
        let mut plain = vec![0u64; params8192.n];
        plain[*choice] = 1;
        let mut nul = [0u8; 32];
        nul[0] = 0xA0 + (v_idx as u8);
        ballots.push(
            encrypt_and_prove_submission_whir(
                &params8192,
                &vote_comm.pk,
                &vote_spec,
                1,
                nul,
                &plain,
                &mut rng,
            )
            .expect("honest N=8192 binary ballot"),
        );
    }

    // Regression killing `starbridge-apps/privacy-voting/tests/tally_forgery.rs` (`1,000,000` votes in 1 ciphertext,
    // with cheating prover setting `slack[0] = (1 - 1_000_000) mod p_0` so EVERY linear WhirPcs61 claim passes!):
    let p0_8192 = params8192.qp[0];
    let mut forged_million = vec![0i64; params8192.n];
    forged_million[0] = 1_000_000;
    let u = vec![0i64; params8192.n];
    let e0 = vec![0i64; params8192.n];
    let e1 = vec![0i64; params8192.n];
    let mut slack = vec![0u64; params8192.n];
    slack[0] = (p0_8192 + 1) - 1_000_000;
    let forged_sub = prove_submission_from_raw_witness(
        &params8192,
        &vote_comm.pk,
        &vote_spec,
        1,
        [0xEEu8; 32],
        &forged_million,
        &slack,
        &u,
        &e0,
        &e1,
        &mut rng,
    )
    .expect("construct forged 10^6 ballot proof with valid linear WhirOpeningBundle61");
    assert!(
        vote_comm
            .verify_and_admit_submission(&vote_spec, 1, &forged_sub)
            .is_err(),
        "MUST reject privacy-voting 1,000,000 vote tally forgery at N=8192!"
    );

    // Honest 4-voter tally succeeds under 3-of-4 threshold quorum `[0, 2, 3]`:
    let t_vt = Instant::now();
    let tally =
        execute_private_voting_tally_epoch(&mut vote_comm, 1, &vote_spec, &ballots, &[0, 2, 3])
            .expect("execute N=8192 private voting tally");
    println!(
        "[PrivateVoting N=8192] 4-voter 3-of-4 epoch verify+tally={:.2} ms -> {:?}",
        t_vt.elapsed().as_secs_f64() * 1000.0,
        tally
    );
    assert_eq!(tally, vec![1, 2, 1]);

    // Duplicate voter nullifier replay rejected:
    assert_eq!(
        vote_comm.verify_and_admit_submission(&vote_spec, 2, &ballots[0]),
        Err(ClearingError::DuplicateNullifier(ballots[0].nullifier))
    );

    // 3. Fast `N = 64` exhaustive adversarial regression battery (negative `-1 mod t`, multi-vote `[1,1,0]`,
    // `q_1` RNS limb tamper, `< threshold` shares, `C8` unverified handle, `C8` individual bid decryption
    // refusal, and stale `epoch_latch` replay):
    let p64 = params_ring_homo(64);
    let p0_64 = p64.qp[0];
    let mut comm64 =
        DarkClearingCommittee::setup(p64.clone(), 2, 3).expect("2-of-3 N=64 committee");
    let spec64 = SubmissionSpec::BinaryBallot {
        num_choices: 3,
        min_votes: 1,
        max_votes: 1,
    };

    // 3a. Negative vote forgery `m_0 = -1` (`t - 1 mod t`, `slack[0] = 2` so `-1 + 2 == 1` linearly!):
    let mut neg_vote = vec![0i64; 64];
    neg_vote[0] = -1;
    let z64_i = vec![0i64; 64];
    let mut slack_neg = vec![0u64; 64];
    slack_neg[0] = 2;
    let bad_neg = prove_submission_from_raw_witness(
        &p64,
        &comm64.pk,
        &spec64,
        1,
        [0x01u8; 32],
        &neg_vote,
        &slack_neg,
        &z64_i,
        &z64_i,
        &z64_i,
        &mut rng,
    )
    .unwrap();
    assert!(verify_encrypted_submission_whir(&p64, &comm64.pk, &spec64, 1, &bad_neg).is_err());

    // 3b. Multi-vote inflation `m = [1, 1, 0]` on `max_votes = 1` (`slack[0] = p_0 - 1` so `2 - 1 == 1` linearly!):
    let mut multi_vote = vec![0i64; 64];
    multi_vote[0] = 1;
    multi_vote[1] = 1;
    let mut slack_multi = vec![0u64; 64];
    slack_multi[0] = p0_64 - 1;
    let bad_multi = prove_submission_from_raw_witness(
        &p64,
        &comm64.pk,
        &spec64,
        1,
        [0x02u8; 32],
        &multi_vote,
        &slack_multi,
        &z64_i,
        &z64_i,
        &z64_i,
        &mut rng,
    )
    .unwrap();
    assert!(verify_encrypted_submission_whir(&p64, &comm64.pk, &spec64, 1, &bad_multi).is_err());

    // 3c. Honest ballot + RNS limb `q_1` tamper (verifies full 3-prime RNS binding, not just `q_0`!):
    let mut ok_vote = vec![0u64; 64];
    ok_vote[2] = 1;
    let good_sub = encrypt_and_prove_submission_whir(
        &p64,
        &comm64.pk,
        &spec64,
        1,
        [0x03u8; 32],
        &ok_vote,
        &mut rng,
    )
    .unwrap();
    let mut limb1_tampered = good_sub.clone();
    limb1_tampered.ct.c0[64] = (limb1_tampered.ct.c0[64] + 1) % p64.qp[1]; // prime k=1!
    limb1_tampered.ct_handle = bfv_ct_handle(&p64, &limb1_tampered.ct);
    assert!(
        verify_encrypted_submission_whir(&p64, &comm64.pk, &spec64, 1, &limb1_tampered).is_err(),
        "3-prime BFV WHIR proof MUST reject tamper in RNS limb k=1!"
    );

    // 3d. `C8` Decryption-Oracle Gate & Individual-Bid Decryption Prohibition:
    let ind_handle = comm64
        .verify_and_admit_submission(&spec64, 1, &good_sub)
        .expect("admit valid ballot");

    // Attempt to decrypt the INDIVIDUAL ballot (even with a 2-of-3 quorum!) MUST be refused:
    let bad_ind_auth = OpeningAuthorization::new(1, spec64.spec_digest(), ind_handle, vec![0, 1]);
    assert_eq!(
        comm64.issue_partial_decryption_share(0, &bad_ind_auth, &good_sub.ct),
        Err(ClearingError::C8IndividualCiphertextForbidden(ind_handle))
    );

    // Attempt to decrypt a raw unverified client ciphertext MUST be refused (`C8UnverifiedHandle`):
    let raw_unverified_auth = OpeningAuthorization::new(
        1,
        spec64.spec_digest(),
        limb1_tampered.ct_handle,
        vec![0, 1],
    );
    assert_eq!(
        comm64.issue_partial_decryption_share(0, &raw_unverified_auth, &limb1_tampered.ct),
        Err(ClearingError::C8UnverifiedHandle(limb1_tampered.ct_handle))
    );

    // Aggregate the epoch, verify 1-of-3 single-custodian opening is refused, 2-of-3 succeeds,
    // and replaying epoch 1 is refused by `epoch_latch`:
    let (agg_h, _) = comm64.aggregate_verified_epoch(1).unwrap();
    let agg_ct = comm64.aggregate_ct(&agg_h).unwrap().clone();

    let single_auth = OpeningAuthorization::new(1, spec64.spec_digest(), agg_h, vec![0]);
    assert_eq!(
        comm64.issue_partial_decryption_share(0, &single_auth, &agg_ct),
        Err(ClearingError::InsufficientDecryptionShares {
            got: 1,
            threshold: 2,
        })
    );

    let valid_auth = OpeningAuthorization::new(1, spec64.spec_digest(), agg_h, vec![0, 1]);
    let s0 = comm64
        .issue_partial_decryption_share(0, &valid_auth, &agg_ct)
        .unwrap();
    // Insufficient shares passed to combiner (`1 < 2`):
    assert_eq!(
        comm64.combine_threshold_shares(&agg_h, std::slice::from_ref(&s0)),
        Err(ClearingError::InsufficientDecryptionShares {
            got: 1,
            threshold: 2,
        })
    );
    // Epoch replay on custodian 0 (`epoch 1 <= latch 1`) refused:
    assert_eq!(
        comm64.issue_partial_decryption_share(0, &valid_auth, &agg_ct),
        Err(ClearingError::EpochReplayOrStale { got: 1, latch: 1 })
    );
}
