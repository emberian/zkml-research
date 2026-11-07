//! Assembly, owner check and verifier on a SYNTHETIC Transactions set (ideal sharings written in MP-SPDZ's
//! byte format, Montgomery residues included), positive and negative. The real-MASCOT runs are checked by
//! `darkprep run --verify` and by research/dark_learning_2026_11_06/run_tape_step.py.
use darkprep::field::Fp;
use darkprep::mpspdz::Transactions;
use darkprep::owner;
use darkprep::schedule::{tags, Inputs, Phase, Plan, Release, StepParams, Tag, DEG, KAPPA};
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
    StepParams { d: 4, inputs: Inputs::Harness, trunc: [(5, 13), (5, 13), (4, 8), (8, 13)], proof_atoms: false, proof_triples: 0, phase: Phase::Step, rs: false }
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
    let sp = StepParams { d: 4, inputs: Inputs::Steady, trunc: [(5, 13), (5, 13), (4, 8), (8, 13)], proof_atoms: true, proof_triples: 7, phase: Phase::Step, rs: false };
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
    let base = StepParams { d, inputs: Inputs::Harness, trunc: pg.truncs(), proof_atoms: false, proof_triples: 0, phase: Phase::Step, rs: false };
    let chunk: Vec<StepParams> = (0..2).map(|j| StepParams { inputs: if j == 0 { Inputs::Harness } else { Inputs::Steady }, ..base }).collect();
    let (tapes, _) = darkstep::tape::deal_steps_prog(P, d, 5, 9, &vec![0u64; 2 * d * d + 2 * d], &[vec![0u64; 2 * d]], false, &pg);
    let ours: Vec<u8> = chunk.iter().flat_map(|sp| tags(sp)).map(|t| t as u8 + 1).collect();
    assert_eq!(ours, tapes[0].tags);
}

/// darkproof's deployed GEN6 program with RC + LB (the release's (s1, k1) = (11, 19)).
fn gen6_proof_params() -> darkproof::step::StepParams {
    gen6_proof_params_rs(false)
}

fn gen6_proof_params_rs(rs: bool) -> darkproof::step::StepParams {
    let g = darkstep::step::Program::GEN6;
    darkproof::step::StepParams { s1: g.s1, k1: g.k1, s2: g.s2, k2: g.k2, s3: g.s3, k3: g.k3, he: true, rc: true, r3: g.r3, t_lo: g.t_lo, lb: true, rs, pg: None }
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
        let base = StepParams { d, inputs: Inputs::Steady, trunc: g.truncs(), proof_atoms: false, proof_triples: 0, phase: Phase::Step, rs: false };
        let sp = base.release(Release { m, ncls, kc, lookup_triples: 0 }, nrt);
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
    let base = StepParams { d: 4, inputs: Inputs::Steady, trunc: g.truncs(), proof_atoms: false, proof_triples: 0, phase: Phase::Step, rs: false };
    let sp = base.release(Release { m: 2, ncls: 4, kc: 10, lookup_triples: 0 }, 11);
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

#[test]
fn handover_tape_is_auth_plain_only_and_verifies() {
    let d = 4;
    let n = 2 * d * d + 16;
    let sp = StepParams::at(d, Inputs::Steady).with_proof().handover(n);
    assert_eq!(tags(&sp), vec![Tag::Ar; n]);
    let plan = Plan::of(&sp);
    assert_eq!((plan.n_in, plan.n_ar, plan.n_tri, plan.n_lp, plan.trunc_classes.len()), (0, n, 0, 0, 0));
    let (files, _) = synth_plan(&plan, 8);
    let txs: Vec<Transactions> = files.iter().map(|f| Transactions::parse(f, P).unwrap()).collect();
    let tapes: Vec<Tape> = txs.iter().enumerate().map(|(i, t)| assemble(&sp, t, i as u32).unwrap()).collect();
    assert_eq!(darkprep::verify::verify_step(&sp, &tapes, &[]).unwrap().entries, n);
    assert!(verify(&tapes, &[]).is_err(), "a handover tape verified as a step");
    let mut bad = tapes.clone();
    bad[2].entries[n - 1].2 ^= 1;
    assert!(darkprep::verify::verify_step(&sp, &bad, &[]).is_err(), "a corrupted MAC verified");
}

#[test]
fn streamed_darkstep_tape_equals_darkstep_write_to() {
    let sp = StepParams::at(4, Inputs::Steady).with_proof();
    let (files, _) = synth(&sp, 9);
    let tx = Transactions::parse(&files[1], P).unwrap();
    let t = darkprep::tape::assemble(&sp, &tx, 1).unwrap();
    let ds = darkstep::tape::Tape {
        alpha_i: t.alpha_i,
        tags: t.entries.iter().map(|e| e.0 as u8 + 1).collect(),
        sh: t.entries.iter().map(|e| e.1).collect(),
        mac: t.entries.iter().map(|e| e.2).collect(),
    };
    let mut want = Vec::new();
    ds.write_to(&mut want).unwrap();
    let dir = std::env::temp_dir().join(format!("darkprep-stream-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("tape.bin");
    let mut w = darkprep::tape::DarkstepWriter::create(&path, tx.alpha_i, darkprep::schedule::n_entries(&sp)).unwrap();
    darkprep::tape::assemble_in_chunk_emit(&[sp], &tx, 1, 0, &mut |tg, sm| w.push(tg, sm).unwrap()).unwrap();
    w.finish().unwrap();
    let got = std::fs::read(&path).unwrap();
    std::fs::remove_dir_all(&dir).unwrap();
    assert_eq!(got, want);
    // negative control: a header count one short refuses the last entry
    let path2 = std::env::temp_dir().join(format!("darkprep-stream2-{}.bin", std::process::id()));
    let mut w = darkprep::tape::DarkstepWriter::create(&path2, tx.alpha_i, t.entries.len() - 1).unwrap();
    let mut refused = 0;
    darkprep::tape::assemble_in_chunk_emit(&[sp], &tx, 1, 0, &mut |tg, sm| if w.push(tg, sm).is_err() { refused += 1 }).unwrap();
    std::fs::remove_file(&path2).unwrap();
    assert_eq!(refused, 1);
    assert_eq!(darkprep::schedule::n_entries(&sp), tags(&sp).len());
}

#[test]
fn wipe_file_zeroes_every_hard_link_then_unlinks() {
    let dir = std::env::temp_dir().join(format!("darkprep-wipe-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (a, b) = (dir.join("a"), dir.join("b"));
    std::fs::write(&a, vec![0x5au8; 3 << 20 | 7]).unwrap();
    std::fs::hard_link(&a, &b).unwrap();
    darkprep::mpspdz::wipe_file(&a).unwrap();
    assert!(!a.exists());
    let rest = std::fs::read(&b).unwrap();
    assert_eq!(rest.len(), 3 << 20 | 7);
    assert!(rest.iter().all(|&x| x == 0), "a hard-linked name still holds data");
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn retiring_a_seat_erases_every_secret_of_that_party_and_only_those() {
    let root = std::env::temp_dir().join(format!("darkprep-retire-{}", std::process::id()));
    let pd = root.join("Player-Data");
    for d in ["3-p-61", "3-2-128", "3-p-319"] {
        std::fs::create_dir_all(pd.join(d)).unwrap();
    }
    std::fs::create_dir_all(root.join("Persistence")).unwrap();
    // (file, secret of party 0)
    let files = [
        ("Player-Data/Mascot-Secrets-p-61-abc-P0-3", true),
        ("Player-Data/Mascot-Secrets-p-61-abc-P0-3.retired-17", true),
        ("Player-Data/Mascot-Secrets-2-128-abc-P0-3", true),
        ("Player-Data/Mascot-Secrets-B-64-abc-P0-3", true),
        ("Player-Data/Mascot-Secrets-p-319-abc-P0-3", true),
        ("Player-Data/LowGear-Secrets-60-def-P0-3", true),
        ("Player-Data/Memory-p-P0", true),
        ("Player-Data/Memory-B-P0", true),
        ("Player-Data/3-p-61/Player-MAC-Keys-p-P0", true),
        ("Player-Data/3-p-61/Player-MAC-Keys-p-P0.retired-17", true),
        ("Player-Data/3-2-128/Player-MAC-Keys-2-P0", true),
        ("Player-Data/3-p-319/Player-MAC-Keys-p-P0", true),
        ("Persistence/Transactions-P0.data", true),
        ("Persistence/Transactions-gf2n-P0.data", true),
        // another party's material, in a loopback directory
        ("Player-Data/Mascot-Secrets-p-61-abc-P1-3", false),
        ("Player-Data/Memory-p-P1", false),
        ("Player-Data/3-p-61/Player-MAC-Keys-p-P1", false),
        ("Persistence/Transactions-P1.data", false),
        // public files of the seat
        ("Player-Data/P0.key", false),
        ("Player-Data/P0.pem", false),
        ("Player-Data/PairwiseParams-gfp-61-60-60-128-1-23-1-P0-3", false),
    ];
    for (f, _) in files {
        std::fs::write(root.join(f), b"alpha share").unwrap();
    }
    let keep = pd.join("keep-link");
    std::fs::hard_link(pd.join("Mascot-Secrets-2-128-abc-P0-3"), &keep).unwrap();
    let gone = darkprep::mpspdz::retire_mac_keys(&root, Some(0));
    assert_eq!(gone.len(), files.iter().filter(|f| f.1).count(), "{gone:?}");
    for (f, secret0) in files {
        assert_eq!(root.join(f).exists(), !secret0, "{f}");
    }
    // erased, not renamed: a second name for the same inode now reads zeros
    assert!(std::fs::read(&keep).unwrap().iter().all(|&b| b == 0));
    // loopback (None): every party's secrets, still no public file
    darkprep::mpspdz::retire_mac_keys(&root, None);
    for (f, _) in files {
        let public = f.ends_with(".key") || f.ends_with(".pem") || f.contains("PairwiseParams");
        assert_eq!(root.join(f).exists(), public, "{f}");
    }
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn has_mac_key_sees_only_the_partys_live_key() {
    let pd = std::env::temp_dir().join(format!("darkprep-haskey-{}", std::process::id()));
    std::fs::create_dir_all(&pd).unwrap();
    assert!(!darkprep::mpspdz::has_mac_key(&pd, "mascot", 0));
    std::fs::write(pd.join("Mascot-Secrets-p-61-abc-P1-3"), b"x").unwrap();
    std::fs::write(pd.join("Mascot-Secrets-p-61-abc-P0-3.retired-9"), b"x").unwrap();
    std::fs::write(pd.join("LowGear-Secrets-60-def-P0-3"), b"x").unwrap();
    assert!(!darkprep::mpspdz::has_mac_key(&pd, "mascot", 0));
    assert!(darkprep::mpspdz::has_mac_key(&pd, "mascot", 1));
    assert!(darkprep::mpspdz::has_mac_key(&pd, "lowgear", 0));
    std::fs::remove_dir_all(&pd).unwrap();
}

#[test]
fn rs_release_and_step_equal_their_dealers_tags() {
    // RS: K + 1 - s Trhb per truncation; L: each release lookup is lookup_bits_products Beaver triples
    let pr = darkproof::Profile::ledger();
    let p = darkproof::wire::he_field(&pr).unwrap();
    darkproof::field::set_p(p);
    let lp = pr.ligero();
    let prm = gen6_proof_params_rs(true);
    let tables = darkproof::step::tables_for(prm.t_lo);
    let lt = darkproof::step::lookup_bits_products(prm);
    let g = darkstep::step::Program::GEN6;
    for (d, m) in [(4usize, 2usize), (8, 3)] {
        let (ncls, kc) = (d.min(10), 10u32);
        let pol = darkproof::run::Policy { x: vec![0; d * m], labels: vec![0; m], ncls, kc, ignore_range: false };
        let mut dl = darkstep::tape::Dealer::new(p, 3, 5);
        dl.proof_rng = Some(PyRandom::from_u64(1));
        dl.rs = true;
        darkproof::run::deal_release(&mut dl, d, m, ncls, prm, kc, &lp, &tables, &pol);
        let nrt = darkproof::run::release_section(&lp, d, m, prm, &pol);
        let base = StepParams { d, inputs: Inputs::Steady, trunc: g.truncs(), proof_atoms: false, proof_triples: 0, phase: Phase::Step, rs: true };
        let sp = base.release(Release { m, ncls, kc, lookup_triples: lt }, nrt);
        let ours: Vec<u8> = tags(&sp).iter().map(|t| *t as u8 + 1).collect();
        assert_eq!(ours, dl.tapes[0].tags, "release d = {d}, M = {m}");
        assert_eq!(darkprep::schedule::n_entries(&sp), ours.len());
        // negative controls: without RS, or with the power chains, the tape differs
        assert_ne!(tags(&StepParams { rs: false, ..sp }).iter().map(|t| *t as u8 + 1).collect::<Vec<u8>>(), dl.tapes[0].tags);
        let pw = base.release(Release { m, ncls, kc, lookup_triples: 0 }, nrt);
        assert_ne!(tags(&pw).iter().map(|t| *t as u8 + 1).collect::<Vec<u8>>(), dl.tapes[0].tags);
        // the step under RS: darkstep's dealer with Dealer::rs, then the proof section
        let inputs = vec![0u64; 2 * d * d + 2 * d];
        let (_, mut ds) = darkstep::tape::deal_step_dealer_prog_rs(P, d, 5, 9, &inputs, true, &g, true);
        darkstep::tape::deal_proof_section(&mut ds, 13);
        let st = StepParams { d, inputs: Inputs::Harness, trunc: g.truncs(), proof_atoms: true, proof_triples: 13, phase: Phase::Step, rs: true };
        let ours: Vec<u8> = tags(&st).iter().map(|t| *t as u8 + 1).collect();
        assert_eq!(ours, ds.tapes[0].tags, "step d = {d}");
    }
}

#[test]
fn rs_synthetic_tapes_verify_and_a_wrong_low_bit_is_refused() {
    let g = darkstep::step::Program::GEN6;
    let sp = StepParams { d: 4, inputs: Inputs::Steady, trunc: g.truncs(), proof_atoms: true, proof_triples: 5, phase: Phase::Step, rs: true };
    let (files, _) = synth(&sp, 11);
    let txs: Vec<Transactions> = files.iter().map(|f| Transactions::parse(f, P).unwrap()).collect();
    let tapes: Vec<Tape> = txs.iter().enumerate().map(|(i, t)| assemble(&sp, t, i as u32).unwrap()).collect();
    let msgs: Vec<_> = txs.iter().map(|t| owner::custodian_message(&sp, t)).collect();
    let rs = owner::owner_masks(Fp::new(P), &msgs).unwrap();
    darkprep::verify::verify_step(&sp, &tapes, &rs).unwrap();
    // swap the first Trhb's entries with the second's on every tape (both bits stay 0/1 and MAC-valid): refused
    // unless the two bits are equal, so pick a truncation where they differ
    let n = tapes[0].entries.len();
    let mut done = false;
    for k in 0..n - 1 {
        if tapes[0].entries[k].0 == Tag::Trhb && tapes[0].entries[k + 1].0 == Tag::Trhb {
            let mut t = tapes.clone();
            for tp in t.iter_mut() {
                tp.entries.swap(k, k + 1);
            }
            if darkprep::verify::verify_step(&sp, &t, &rs).is_err() {
                done = true;
                break;
            }
        }
    }
    assert!(done, "no Trhb swap was refused");
}

/// A synthetic step tape sealed as party-chunk seals it, and its plain DLTAPE01 bytes.
fn sealed_fixture(v: &darkhand::vault::Vault, dir: &std::path::Path) -> (std::path::PathBuf, Vec<u8>) {
    let sp = StepParams::at(4, Inputs::Steady).with_proof();
    let (files, _) = synth(&sp, 12);
    let tx = Transactions::parse(&files[1], P).unwrap();
    let mut buf = darkprep::tape::DarkstepBuf::new(tx.alpha_i, darkprep::schedule::n_entries(&sp));
    darkprep::tape::assemble_in_chunk_emit(&[sp], &tx, 1, 0, &mut |t, sm| buf.push(t, sm).unwrap()).unwrap();
    let plain = buf.finish().unwrap();
    // the in-memory image equals the streamed file's bytes
    let pp = dir.join("plain.bin");
    let mut w = darkprep::tape::DarkstepWriter::create(&pp, tx.alpha_i, darkprep::schedule::n_entries(&sp)).unwrap();
    darkprep::tape::assemble_in_chunk_emit(&[sp], &tx, 1, 0, &mut |t, sm| w.push(t, sm).unwrap()).unwrap();
    w.finish().unwrap();
    assert_eq!(std::fs::read(&pp).unwrap(), plain);
    let path = dir.join("tape_1.bin");
    v.seal_to(&path, &darkprep::tape::tape_role("reh-c0-P1", 0), plain.clone()).unwrap();
    (path, plain)
}

#[test]
fn sealed_tape_opens_only_as_itself_and_never_after_its_key_is_destroyed() {
    let dir = std::env::temp_dir().join(format!("darkprep-vault-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let v = darkhand::vault::Vault::create("dl-vault:test:1:0:00", false).unwrap();
    let (path, plain) = sealed_fixture(&v, &dir);
    let on_disk = std::fs::read(&path).unwrap();
    assert!(on_disk.starts_with(b"DLVAULT1") && !on_disk.windows(16).any(|w| w == &plain[24..40]), "plaintext on disk");
    let t = darkprep::tape::open_sealed(&v, &path, "reh-c0-P1", 0).unwrap();
    let mut back = Vec::new();
    t.write_to(&mut back).unwrap();
    assert_eq!(back, plain);
    // another step, another chunk, another key: refused
    assert!(darkprep::tape::open_sealed(&v, &path, "reh-c0-P1", 1).is_err());
    assert!(darkprep::tape::open_sealed(&v, &path, "reh-c1-P1", 0).is_err());
    let other = darkhand::vault::Vault::create("dl-vault:test:1:0:00", false).unwrap();
    assert!(darkprep::tape::open_sealed(&other, &path, "reh-c0-P1", 0).is_err());
    // a plain DLTAPE01 tape is refused
    assert!(darkprep::tape::open_sealed(&v, &dir.join("plain.bin"), "reh-c0-P1", 0).err().unwrap().contains("unsealed"));
    // erasure: after destroy, neither the zero key (what a zeroed copy would give) nor a keyring load opens it
    let name = v.name.clone();
    v.destroy();
    assert!(darkprep::tape::open_sealed(&darkhand::vault::Vault::with_key(&name, [0; 32]), &path, "reh-c0-P1", 0).is_err());
    assert!(darkhand::vault::Vault::load(&name).is_err());
    std::fs::remove_dir_all(&dir).unwrap();
}

#[cfg(target_os = "linux")]
#[test]
fn sealed_tape_under_the_kernel_keyring_dies_with_its_invalidated_key() {
    // the deployment's path: the key in the uid's persistent keyring, loaded by name (as party-chunk does)
    let dir = std::env::temp_dir().join(format!("darkprep-vault-kr-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let name = format!("dl-vault:darkprep-test:1:0:{:016x}", std::process::id());
    let made = darkhand::vault::Vault::create(&name, true).unwrap();
    let v = darkhand::vault::Vault::load(&name).unwrap();
    let (path, _) = sealed_fixture(&v, &dir);
    assert!(darkprep::tape::open_sealed(&darkhand::vault::Vault::load(&name).unwrap(), &path, "reh-c0-P1", 0).is_ok());
    drop(v);
    let rep = made.destroy();
    assert_eq!(rep["key_in_keyring_after"], false, "{rep}");
    assert!(darkhand::vault::Vault::load(&name).is_err(), "the invalidated key still loads");
    std::fs::remove_dir_all(&dir).unwrap();
}

#[cfg(not(feature = "test-plain-tapes"))]
#[test]
fn a_production_build_refuses_to_write_an_unsealed_chunk() {
    // no --vault: refused before any MASCOT run, --plain-tapes or not
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_darkprep"))
        .args(["party-chunk", "--party", "0", "--d", "4", "--mode", "steady", "--plain-tapes", "--out", "/nonexistent/x-P0"])
        .output()
        .unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success() && err.contains("is required"), "{err}");
    // a vault name that no keyring holds: refused too (darkprep never makes a key)
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_darkprep"))
        .args(["party-chunk", "--party", "0", "--d", "4", "--mode", "steady", "--vault", "dl-vault:none:0:0:00", "--out", "/nonexistent/x-P0"])
        .output()
        .unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success() && (err.contains("vault") || err.contains("keyring")), "{err}");
}

#[test]
fn sealed_release_tape_streams_byte_equal_and_refuses_tampering() {
    use std::sync::Arc;
    let dir = std::env::temp_dir().join(format!("darkprep-v2-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let g = darkstep::step::Program::GEN6;
    let base = StepParams { d: 4, inputs: Inputs::Steady, trunc: g.truncs(), proof_atoms: false, proof_triples: 0, phase: Phase::Step, rs: true };
    let nrt = 40;
    let sp = base.release(Release { m: 2, ncls: 4, kc: 10, lookup_triples: 27 }, nrt);
    let (files, _) = synth_plan(&Plan::of(&sp), 13);
    let tx = Transactions::parse(&files[2], P).unwrap();
    let n = darkprep::schedule::n_entries(&sp);
    let v = darkhand::vault::Vault::create("dl-vault:test:2:1:00", false).unwrap();
    let key = dlvault::Key::new(&v.name, v.key_bytes());
    let role = darkprep::tape::tape_role("rel-P2", 0);
    let bs = 4096; // many blocks from a small tape
    let write = |path: &std::path::Path| {
        let mut w = darkprep::tape::SealedDarkstepWriter::create_bs(path, &key, &role, tx.alpha_i, n, bs).unwrap();
        darkprep::tape::assemble_in_chunk_emit(&[sp], &tx, 2, 0, &mut |t, sm| w.push(t, sm).unwrap()).unwrap();
        w.finish().unwrap();
    };
    let (pp, sa, sb) = (dir.join("plain.bin"), dir.join("a.bin"), dir.join("b.bin"));
    let mut w = darkprep::tape::DarkstepWriter::create(&pp, tx.alpha_i, n).unwrap();
    darkprep::tape::assemble_in_chunk_emit(&[sp], &tx, 2, 0, &mut |t, sm| w.push(t, sm).unwrap()).unwrap();
    w.finish().unwrap();
    write(&sa);
    write(&sb);
    let plain = std::fs::read(&pp).unwrap();
    assert!(std::fs::read(&sa).unwrap().starts_with(b"DLVAULT2"));
    // the streaming loader: the MPC part and every proof-section triple equal the plain tape's
    let k = Arc::new(dlvault::Key::new(&v.name, v.key_bytes()));
    let (tp, rp) = darkproof::run::load_release_tape(&pp, nrt).unwrap();
    let (ts, rs) = darkproof::run::load_release_tape_sealed(&sa, nrt, k.clone(), &role).unwrap();
    assert_eq!((tp.alpha_i, &tp.tags, &tp.sh, &tp.mac), (ts.alpha_i, &ts.tags, &ts.sh, &ts.mac));
    assert_eq!(rp.triples(0, nrt).unwrap().collect::<Vec<_>>(), rs.triples(0, nrt).unwrap().collect::<Vec<_>>());
    assert_eq!(rp.triples(17, 9).unwrap().collect::<Vec<_>>(), rs.triples(17, 9).unwrap().collect::<Vec<_>>());
    // and the whole plaintext byte-equal through dlvault's reader
    let mut back = Vec::new();
    std::io::Read::read_to_end(&mut dlvault::Reader::open(&sa, k.clone(), &role).unwrap(), &mut back).unwrap();
    assert_eq!(back, plain);
    // each loader refuses the other kind
    assert!(darkproof::run::load_release_tape(&sa, nrt).is_err());
    assert!(darkproof::run::load_release_tape_sealed(&pp, nrt, k.clone(), &role).is_err());
    // tampering: swapped blocks, a dropped final block, a block of another tape, another role
    let fa = std::fs::read(&sa).unwrap();
    let fb = std::fs::read(&sb).unwrap();
    let blk = |i: u64| (32 + i * (bs as u64 + 16)) as usize..(32 + (i + 1) * (bs as u64 + 16)) as usize;
    let load = |b: &[u8]| {
        let p = dir.join("t.bin");
        std::fs::write(&p, b).unwrap();
        darkproof::run::load_release_tape_sealed(&p, nrt, k.clone(), &role).map(|_| ())
    };
    let mut s = fa.clone();
    s[blk(0)].copy_from_slice(&fa[blk(1)]);
    s[blk(1)].copy_from_slice(&fa[blk(0)]);
    assert!(load(&s).is_err(), "swapped blocks loaded");
    let last = fa.len() - ((24 + 17 * n) % bs as usize + 16);
    assert!(load(&fa[..last]).is_err(), "a tape without its final block loaded");
    let mut s = fa.clone();
    s[blk(1)].copy_from_slice(&fb[blk(1)]);
    assert!(load(&s).is_err(), "a block of another tape loaded");
    assert!(darkproof::run::load_release_tape_sealed(&sa, nrt, k.clone(), &darkprep::tape::tape_role("rel-P2", 1)).is_err());
    assert!(load(&fa).is_ok(), "control: the untouched tape loads");
    // erasure: after destroy, the zero key opens nothing
    let name = v.name.clone();
    drop(key);
    v.destroy();
    let z = Arc::new(dlvault::Key::new(&name, &[0; 32]));
    assert!(darkproof::run::load_release_tape_sealed(&sa, nrt, z, &role).is_err());
    std::fs::remove_dir_all(&dir).unwrap();
}
