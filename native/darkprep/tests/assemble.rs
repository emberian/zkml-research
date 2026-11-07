//! Assembly, owner check and verifier on a SYNTHETIC Transactions set (ideal sharings written in MP-SPDZ's
//! byte format, Montgomery residues included), positive and negative. The real-MASCOT runs are checked by
//! `darkprep run --verify` and by research/dark_learning_2026_11_06/run_tape_step.py.
use darkprep::field::Fp;
use darkprep::mpspdz::Transactions;
use darkprep::owner;
use darkprep::schedule::{tags, Inputs, Plan, StepParams, Tag, DEG, KAPPA};
use darkprep::tape::{assemble, Tape};
use darkprep::verify::verify;
use pycompat::PyRandom;

const P: u64 = 2305843009210515457;

/// Ideal values for every section of the plan, then n additive (share, MAC) sharings, serialized like MP-SPDZ.
fn synth(sp: &StepParams, seed: u64) -> (Vec<Vec<u8>>, u64) {
    let fp = Fp::new(P);
    let mut rng = PyRandom::from_u64(seed);
    let mut r = |n: u64| rng.randbelow_u64(n);
    let plan = Plan::of(sp);
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
    StepParams { d: 4, inputs: Inputs::Harness, trunc: [(5, 13), (5, 13), (4, 8), (8, 13)] }
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
