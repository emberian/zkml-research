//! Assembly, owner check and verifier on a SYNTHETIC Transactions set (ideal sharings written in MP-SPDZ's
//! byte format, Montgomery residues included), positive and negative. The real-MASCOT runs are checked by
//! `darkprep run --verify` and by research/dark_learning_2026_11_06/run_tape_step.py.
use darkprep::field::Fp;
use darkprep::mpspdz::Transactions;
use darkprep::owner;
use darkprep::schedule::{tags, Inputs, Plan, Release, StepParams, Tag, DEG, KAPPA};
use darkprep::tape::{assemble, Tape};
use darkprep::verify::verify;
use pycompat::PyRandom;

const P: u64 = 2305843009210515457;

/// Ideal values for every section of the plan, then n additive (share, MAC) sharings, serialized like MP-SPDZ.
fn synth(sp: &StepParams, seed: u64) -> (Vec<Vec<u8>>, u64) {
    synth_plan(&Plan::of(sp), seed)
}

fn synth_plan(plan: &Plan, seed: u64) -> (Vec<Vec<u8>>, u64) {
    let fp = Fp::new(P);
    let mut rng = PyRandom::from_u64(seed);
    let mut r = |n: u64| rng.randbelow_u64(n);
    let sec = plan.sections();
    let mut vals = vec![0u64; sec.total];
    let mut put = |(base, _nc, m): (usize, usize, usize), comp: usize, k: usize, v: u64| vals[base + comp * m + k] = v;
    for (s, m) in [(sec.input, plan.n_in), (sec.tri, plan.n_tri)] {
        for k in 0..m {
            let (a, b) = (r(P), r(P));
            put(s, 0, k, a);
            put(s, 1, k, b);
            put(s, 2, k, fp.mul(a, b));
        }
    }
    for k in 0..plan.n_ar {
        put(sec.ar, 0, k, r(P));
    }
    for (c, &(_, kk, m)) in plan.trunc_classes.iter().enumerate() {
        for j in 0..(kk + KAPPA) as usize {
            for k in 0..m {
                put(sec.tr[c], j, k, r(2));
            }
        }
    }
    for k in 0..plan.n_lp {
        let x = r(P);
        for j in 0..DEG {
            put(sec.lp, j, k, fp.pow(x, j as u64 + 1));
        }
    }
    let alpha_sh: Vec<u64> = (0..3).map(|_| r(P)).collect();
    let alpha = alpha_sh.iter().fold(0, |a, &b| fp.add(a, b));
    let rm = ((1u128 << 64) % P as u128) as u64;
    let mont = |x: u64| fp.mul(x, rm);
    let mut files: Vec<Vec<u8>> = (0..3)
        .map(|i| {
            let mut h = b"SPDZ gfp\0".to_vec();
            h.extend_from_slice(&8u32.to_le_bytes());
            h.extend_from_slice(&P.to_be_bytes());
            h.extend_from_slice(&1u32.to_le_bytes());
            h.extend_from_slice(&mont(alpha_sh[i]).to_le_bytes());
            let mut f = (h.len() as u64).to_le_bytes().to_vec();
            f.extend_from_slice(&h);
            f
        })
        .collect();
    for &v in &vals {
        let (x0, x1, m0, m1) = (r(P), r(P), r(P), r(P));
        let xs = [x0, x1, fp.sub(fp.sub(v, x0), x1)];
        let mv = fp.mul(alpha, v);
        let ms = [m0, m1, fp.sub(fp.sub(mv, m0), m1)];
        for i in 0..3 {
            files[i].extend_from_slice(&mont(xs[i]).to_le_bytes());
            files[i].extend_from_slice(&mont(ms[i]).to_le_bytes());
        }
    }
    (files, alpha)
}

fn build(sp: &StepParams, files: &[Vec<u8>]) -> Result<(Vec<Tape>, Vec<u64>), String> {
    let txs: Vec<Transactions> = files.iter().map(|f| Transactions::parse(f, P)).collect::<Result<_, _>>()?;
    let tapes = txs.iter().enumerate().map(|(i, t)| assemble(sp, t, i as u32)).collect::<Result<Vec<_>, _>>()?;
    let msgs: Vec<_> = txs.iter().map(|t| owner::custodian_message(sp, t)).collect();
    Ok((tapes, owner::owner_masks(Fp::new(P), &msgs)?))
}

fn small() -> StepParams {
    StepParams { d: 4, inputs: Inputs::Harness, trunc: [(5, 13), (5, 13), (4, 8), (8, 13)], proof_atoms: false, proof_triples: 0, release: None }
}

#[test]
fn schedule_counts_match_the_python_dealer_at_d64() {
    // spdz.Dealer.count for run_he_outer.run(64) is 34438 (he_outer_results_64.json: prep_auth_values)
    let t = tags(&StepParams::at(64, Inputs::Harness));
    assert_eq!(t.len(), 34438);
    let n = |x: Tag| t.iter().filter(|&&y| y == x).count();
    assert_eq!((n(Tag::In), n(Tag::Ta), n(Tag::Lp), n(Tag::Trb), n(Tag::Ar)), (8320, 2562, 16320, 1408, 192));
}

#[test]
fn honest_synthetic_tapes_verify_and_roundtrip() {
    let sp = small();
    let (files, _) = synth(&sp, 1);
    let (tapes, rs) = build(&sp, &files).unwrap();
    let rep = verify(&tapes, &rs).unwrap();
    assert_eq!(rep.entries, tags(&sp).len());
    let mut buf = Vec::new();
    tapes[1].write_to(&mut buf).unwrap();
    assert_eq!(Tape::read_from(&mut &buf[..]).unwrap(), tapes[1]);
}

#[test]
fn corrupted_entries_are_refused() {
    let sp = small();
    let (files, _) = synth(&sp, 2);
    let (tapes, rs) = build(&sp, &files).unwrap();
    // a MAC share, a share, a tag, an owner mask: each refused
    for what in 0..4 {
        let mut t = tapes.clone();
        let mut r = rs.clone();
        match what {
            0 => t[1].entries[10].2 ^= 1,
            1 => t[2].entries[20].1 ^= 1,
            2 => t[0].entries[5].0 = Tag::Ar,
            _ => r[3] ^= 1,
        }
        assert!(verify(&t, &r).is_err(), "corruption {what} accepted");
    }
}

#[test]
fn owner_refuses_an_inconsistent_input_share() {
    let sp = small();
    let (mut files, _) = synth(&sp, 3);
    // custodian 1 shifts its share of the first input tuple's a (first share after the header)
    let hlen = 8 + u64::from_le_bytes(files[1][0..8].try_into().unwrap()) as usize;
    files[1][hlen] ^= 1;
    let e = build(&sp, &files).unwrap_err();
    assert!(e.contains("a b = c"), "{e}");
}

#[test]
fn a_wrong_prime_or_length_is_refused() {
    let sp = small();
    let (files, _) = synth(&sp, 4);
    assert!(Transactions::parse(&files[0], P - 2).is_err());
    let t = Transactions::parse(&files[0][..files[0].len() - 16], P).unwrap();
    assert!(assemble(&sp, &t, 0).is_err());
}

#[test]
fn schedule_with_proof_equals_darkstep_dealer_tags() {
    // darkstep's own dealer, with the proof atoms and the proof section, is the authority on the tag order
    for d in [4usize, 8] {
        let sp = StepParams::at(d, Inputs::Harness).with_proof();
        let inputs = vec![0u64; 2 * d * d + 2 * d];
        let (_, mut dl) = darkstep::tape::deal_step_dealer(P, d, 5, 9, &inputs, true);
        darkstep::tape::deal_proof_section(&mut dl, sp.proof_triples);
        let theirs: Vec<u8> = dl.tapes[0].tags.clone();
        let ours: Vec<u8> = tags(&sp).iter().map(|t| *t as u8 + 1).collect();
        assert_eq!(ours.len(), theirs.len(), "d = {d}");
        assert_eq!(ours, theirs, "d = {d}");
    }
}

#[test]
fn hadamard_count_matches_recorded_runs() {
    // cosnark_gates results: "hadamard" at d = 4, 16, 64, and 4096 (step_counts parameters)
    for (d, want) in [(4usize, 1992usize), (16, 7968), (64, 31872), (4096, 2260992)] {
        assert_eq!(StepParams::at(d, Inputs::Steady).n_had(), want, "d = {d}");
    }
    let sp = StepParams::at(4096, Inputs::Steady).with_proof();
    assert_eq!(sp.proof_triples, 13 * 4095 + 4 * (4194304 - 1));
}

#[test]
fn chunk_steps_assemble_disjoint_slices_that_verify() {
    let sp = StepParams { d: 4, inputs: Inputs::Steady, trunc: [(5, 13), (5, 13), (4, 8), (8, 13)], proof_atoms: true, proof_triples: 7, release: None };
    let steps = 3;
    // synthetic chunk: the plan of 3 steps, built through the same synth() with a chunk-sized StepParams stand-in
    let (files, _) = synth_plan(&Plan::of_chunk(&sp, steps), 5);
    let txs: Vec<Transactions> = files.iter().map(|f| Transactions::parse(f, P).unwrap()).collect();
    let mut firsts = Vec::new();
    for j in 0..steps {
        let tapes: Vec<Tape> = txs.iter().enumerate().map(|(i, t)| darkprep::tape::assemble_step(&sp, t, i as u32, j, steps).unwrap()).collect();
        let msgs: Vec<_> = txs.iter().map(|t| owner::custodian_message_step(&sp, t, j, steps)).collect();
        let rs = owner::owner_masks(Fp::new(P), &msgs).unwrap();
        darkprep::verify::verify_step(&sp, &tapes, &rs).unwrap();
        firsts.push(tapes[0].entries[0]);
    }
    assert!(firsts[0] != firsts[1] && firsts[1] != firsts[2], "steps of a chunk reuse preprocessing");
}

#[test]
fn genesis_chunk_equals_darkstep_multistep_dealer_tags() {
    // darkstep::tape::deal_steps_prog: step 0 inputs W1, W2, x, y; later steps x, y; one stream, back to back
    let d = 4;
    let base = StepParams::at(d, Inputs::Harness);
    let chunk: Vec<StepParams> = (0..3).map(|j| StepParams { inputs: if j == 0 { Inputs::Harness } else { Inputs::Steady }, ..base }).collect();
    let later = vec![vec![0u64; 2 * d]; 2];
    let (tapes, _) = darkstep::tape::deal_steps_prog(P, d, 5, 9, &vec![0u64; 2 * d * d + 2 * d], &later, false, &darkstep::step::Program::HARNESS);
    let ours: Vec<u8> = chunk.iter().flat_map(|sp| tags(sp)).map(|t| t as u8 + 1).collect();
    assert_eq!(ours, tapes[0].tags);
    // and the synthetic chunk assembles step by step, each verifying
    let (files, _) = synth_plan(&darkprep::schedule::plan_of_steps(&chunk), 6);
    let txs: Vec<Transactions> = files.iter().map(|f| Transactions::parse(f, P).unwrap()).collect();
    for j in 0..3 {
        let tp: Vec<Tape> = txs.iter().enumerate().map(|(i, t)| darkprep::tape::assemble_in_chunk(&chunk, t, i as u32, j).unwrap()).collect();
        let msgs: Vec<_> = txs.iter().map(|t| owner::custodian_message_in_chunk(&chunk, t, j)).collect();
        let rs = owner::owner_masks(Fp::new(P), &msgs).unwrap();
        darkprep::verify::verify_step(&chunk[j], &tp, &rs).unwrap();
    }
}

#[test]
fn gen6_program_chunk_equals_darkstep_dealer_tags() {
    // Program::GEN6's truncations ((11,19), (11,19), (7,8), (8,19)); its r3 = 128 is a public cadd (no tape entry)
    let d = 4;
    let pg = darkstep::step::Program::GEN6;
    let base = StepParams { d, inputs: Inputs::Harness, trunc: pg.truncs(), proof_atoms: false, proof_triples: 0, release: None };
    let chunk: Vec<StepParams> = (0..2).map(|j| StepParams { inputs: if j == 0 { Inputs::Harness } else { Inputs::Steady }, ..base }).collect();
    let (tapes, _) = darkstep::tape::deal_steps_prog(P, d, 5, 9, &vec![0u64; 2 * d * d + 2 * d], &[vec![0u64; 2 * d]], false, &pg);
    let ours: Vec<u8> = chunk.iter().flat_map(|sp| tags(sp)).map(|t| t as u8 + 1).collect();
    assert_eq!(ours, tapes[0].tags);
}

/// darkproof's deployed GEN6 program with RC + LB (the release's (s1, k1) = (11, 19)).
fn gen6_proof_params() -> darkproof::step::StepParams {
    let g = darkstep::step::Program::GEN6;
    darkproof::step::StepParams { s1: g.s1, k1: g.k1, s2: g.s2, k2: g.k2, s3: g.s3, k3: g.k3, he: true, rc: true, r3: g.r3, t_lo: g.t_lo, lb: true, pg: None }
}

#[test]
fn release_schedule_equals_darkproof_release_dealer_tags() {
    // darkproof::run::deal_release with proof_rng on is the authority on the release's tape order
    let pr = darkproof::Profile::ledger();
    let p = darkproof::wire::he_field(&pr).unwrap();
    darkproof::field::set_p(p);
    let lp = pr.ligero();
    let prm = gen6_proof_params();
    let tables = darkproof::step::tables_for(prm.t_lo);
    for (d, m) in [(4usize, 2usize), (8, 3)] {
        let (ncls, kc) = (d.min(10), 10u32);
        let pol = darkproof::run::Policy { x: vec![0; d * m], labels: vec![0; m], ncls, kc, ignore_range: false };
        let mut dl = darkstep::tape::Dealer::new(p, 3, 5);
        dl.proof_rng = Some(PyRandom::from_u64(1));
        darkproof::run::deal_release(&mut dl, d, m, ncls, prm, kc, &lp, &tables, &pol);
        let nrt = darkproof::run::release_section(&lp, d, m, prm, &pol);
        let g = darkstep::step::Program::GEN6;
        let base = StepParams { d, inputs: Inputs::Steady, trunc: g.truncs(), proof_atoms: false, proof_triples: 0, release: None };
        let sp = base.release(Release { m, ncls, kc }, nrt);
        let ours: Vec<u8> = tags(&sp).iter().map(|t| *t as u8 + 1).collect();
        assert_eq!(ours.len(), dl.tapes[0].tags.len(), "d = {d}, M = {m}");
        assert_eq!(ours, dl.tapes[0].tags, "d = {d}, M = {m}");
        // negative control: the release without its proof atoms is a different tape
        let bare: Vec<u8> = tags(&StepParams { proof_atoms: false, ..sp }).iter().map(|t| *t as u8 + 1).collect();
        assert_ne!(bare, dl.tapes[0].tags);
    }
}

#[test]
fn synthetic_release_chunk_assembles_and_verifies() {
    let g = darkstep::step::Program::GEN6;
    let base = StepParams { d: 4, inputs: Inputs::Steady, trunc: g.truncs(), proof_atoms: false, proof_triples: 0, release: None };
    let sp = base.release(Release { m: 2, ncls: 4, kc: 10 }, 11);
    let plan = Plan::of(&sp);
    // two truncation classes, (11, 19) then (10, 10); no inputs
    assert_eq!(plan.trunc_classes, vec![(11, 19, 4 * 2 + 4 * 2), (10, 10, 2 * 3)]);
    assert_eq!(plan.n_in, 0);
    let (files, _) = synth_plan(&plan, 7);
    let txs: Vec<Transactions> = files.iter().map(|f| Transactions::parse(f, P).unwrap()).collect();
    let tapes: Vec<Tape> = txs.iter().enumerate().map(|(i, t)| assemble(&sp, t, i as u32).unwrap()).collect();
    let rep = darkprep::verify::verify_step(&sp, &tapes, &[]).unwrap();
    assert_eq!(rep.entries, tags(&sp).len());
    assert!(verify(&tapes, &[]).is_err(), "a release tape verified as a step");
    let mut bad = tapes.clone();
    let k = bad[0].entries.iter().position(|e| e.0 == Tag::Trhb).unwrap();
    bad[0].entries[k].1 = (bad[0].entries[k].1 + 1) % P;
    bad[0].entries[k].2 = (bad[0].entries[k].2 + 1) % P;
    assert!(darkprep::verify::verify_step(&sp, &bad, &[]).is_err(), "a corrupted Trhb verified");
}
