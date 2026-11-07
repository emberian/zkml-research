//! The attack table of run_zkpopk_ligero.py (N = 16, three 61-bit primes, M = 3), executed natively: every forged
//! proof must be refused by the same check the harness names, and every honest one accepted.
//!
//!   cargo test --release -p dzkpopk --test attacks -- --nocapture

use dzkpopk::canon::Json;
use dzkpopk::field::Fe;
use dzkpopk::gen::{encrypt_pk, encrypt_sk, keygen, round_scale};
use dzkpopk::proof::values_to_digits;
use dzkpopk::rng::OsHiding;
use dzkpopk::statement::{layout, ntt_primes, BigPoly, Crt};
use dzkpopk::vectors::{ctx, params};
use dzkpopk::*;
use num_bigint::{BigInt, BigUint};
use pycompat::PyRandom;
use std::sync::Arc;

const T: usize = 309;

fn ctx_with(i: usize, v: Json) -> Json {
    match ctx() {
        Json::List(mut l) => {
            l[i] = v;
            Json::List(l)
        }
        _ => unreachable!(),
    }
}

struct Table {
    rows: Vec<(String, String, bool)>,
}

impl Table {
    fn row(&mut self, name: &str, r: Result<(), String>, expect_ok: bool, expect_why: &str) {
        let (ok, why) = match r {
            Ok(()) => (true, "accept".to_string()),
            Err(w) => (false, w),
        };
        let good = ok == expect_ok && why == expect_why;
        println!("{name:60} {} {why}{}", if ok { "ACCEPT " } else { "REFUSED" }, if good { "" } else { "   <-- UNEXPECTED" });
        self.rows.push((name.into(), why, good));
    }
}

fn flip(b: &[u8], at: usize) -> Vec<u8> {
    let mut v = b.to_vec();
    v[at] ^= 1;
    v
}

#[test]
fn attack_table_n16() {
    let (n, l, m) = (16usize, 3usize, 3usize);
    let (qp, t) = params(n, l);
    let q: BigUint = qp.iter().map(|&p| BigUint::from(p)).product();
    let mut rng = PyRandom::from_u64((n * 1000 + m) as u64);
    let mut tb = Table { rows: vec![] };
    const LIN: &str = "linear test: the folded limb equations do not hold";
    const QUAD: &str = "quadratic test: a committed digit is not binary";

    // --- the honest secret-key batch (run_zkpopk_ligero.sk_batch)
    let (reg0, s, epk) = keygen(n, &qp, t, "registry-seed-0", "custodian-1", &mut rng);
    let reg = Arc::new(reg0);
    let dc = 64.min(n / 2);
    let (mut cts, mut ws, mut slots, mut ms) = (vec![], vec![], vec![], vec![]);
    for j in 0..m {
        let sl: Vec<usize> = if j == m - 1 && m > 1 { (0..n).step_by((n / dc).max(1)).take(dc).collect() } else { (0..dc).collect() };
        let mut pm = vec![0u64; n];
        for &k in &sl {
            pm[k] = rng.randrange_u64(t);
        }
        let (ct, w) = encrypt_sk(&reg, &s, &pm, &sl, &mut rng, None);
        cts.push(ct);
        ws.push(w);
        slots.push(sl);
        ms.push(pm);
    }
    let wit = Witness::Sk { s: s.clone(), e_pk: epk.clone(), cts: ws.clone() };
    let st = Statement::new(reg.clone(), Kind::Sk, cts.clone(), slots.clone(), ctx()).unwrap();
    let blob = prove(&st, &wit, T).unwrap();
    let sh = shape(&st, T).unwrap();
    assert_eq!(blob.len(), proof_bytes(sh.k, sh.th, T, sh.m1, sh.m2));
    tb.row("honest secret-key batch", verify(&st, &blob, T), true, "accept");

    // --- stale context, other recipient, other call, other sender's key
    let others = [
        ("stale context: next step", ctx_with(2, Json::i(8))),
        ("stale context: other epoch", ctx_with(1, Json::i(1))),
        ("other recipient set", ctx_with(5, Json::list(vec![Json::s("custodian-0"), Json::s("custodian-3")]))),
        ("other call (replay into the transpose)", ctx_with(3, Json::s("matvec-T-0"))),
    ];
    for (name, c2) in others {
        let st2 = Statement::new(reg.clone(), Kind::Sk, cts.clone(), slots.clone(), c2).unwrap();
        tb.row(name, verify(&st2, &blob, T), false, LIN);
    }
    let (reg_other, _, _) = keygen(n, &qp, t, "registry-seed-9", "custodian-2", &mut rng);
    let st_o = Statement::new(Arc::new(reg_other), Kind::Sk, cts.clone(), slots.clone(), ctx()).unwrap();
    tb.row("verified against another custodian's registered key", verify(&st_o, &blob, T), false, LIN);

    // --- malformed keys
    let mut one = vec![BigUint::from(0u32); n];
    one[0] = BigUint::from(1u32);
    let bad = KeyRegistry::with_a(n, &qp, t, &reg.seed, &reg.key_id, reg.b.clone(), BigPoly::from_big(&one));
    let st_bad = Statement::new(Arc::new(bad), Kind::Sk, cts.clone(), slots.clone(), ctx()).unwrap();
    tb.row("malformed key: a = 1 instead of the pinned seed's a", verify(&st_bad, &blob, T), false, "key registry: a is not the pinned seed's");
    let rb_b: Vec<BigUint> = (0..n).map(|_| rng.randbelow_big(&q)).collect();
    let rb = Arc::new(KeyRegistry::new(n, &qp, t, "registry-seed-0", "custodian-1", BigPoly::from_big(&rb_b)));
    // e_pk = centered(-(b + a s)) over Z, a full-size integer, packed raw
    let crt = Crt::new(&qp);
    let e_big: Vec<BigInt> = (0..n)
        .map(|k| {
            let res: Vec<u64> = (0..l)
                .map(|i| {
                    let qi = qp[i];
                    let a_s = dzkpopk::statement::exact_nega(&dzkpopk::ntt::Nega::new(n), &rb.a_res()[i], &s).unwrap()[k];
                    ((-(rb.b_res()[i][k] as i128) - a_s).rem_euclid(qi as i128)) as u64
                })
                .collect();
            let x = BigInt::from(crt.combine(&res));
            if x > BigInt::from(&q / 2u32) {
                x - BigInt::from(q.clone())
            } else {
                x
            }
        })
        .collect();
    let st_rb = Statement::new(rb.clone(), Kind::Sk, cts.clone(), slots.clone(), ctx()).unwrap();
    let mut o = ProveOpts { cheat: Some(Cheat { raw: true, values1: vec![("e_pk".into(), Vals::Big(e_big))], ..Default::default() }), ..Default::default() };
    let b2 = prove_with(&st_rb, &wit, T, &mut o).unwrap();
    tb.row("malformed key: b random, prover forges e_pk = -(b + a s)", verify(&st_rb, &b2, T), false, QUAD);

    // --- mixed limbs: limb 0 encrypts m, limbs 1.. encrypt m'
    let mut m2 = vec![0u64; n];
    for &k in &slots[0] {
        m2[k] = rng.randrange_u64(t);
    }
    let (ct_b, _) = encrypt_sk(&reg, &s, &m2, &slots[0], &mut PyRandom::from_u64(5), None);
    let mix = |x: &BigPoly, y: &BigPoly| {
        let res: Vec<Vec<u64>> = qp.iter().enumerate().map(|(i, &p)| if i == 0 { x.residues(p) } else { y.residues(p) }).collect();
        BigPoly::from_rns(&res, &qp)
    };
    let mut cts_mix = cts.clone();
    cts_mix[0] = (mix(&cts[0].0, &ct_b.0), mix(&cts[0].1, &ct_b.1));
    let st_mix = Statement::new(reg.clone(), Kind::Sk, cts_mix, slots.clone(), ctx()).unwrap();
    let mut o = ProveOpts { cheat: Some(Cheat::default()), ..Default::default() };
    let b3 = prove_with(&st_mix, &wit, T, &mut o).unwrap();
    tb.row("mixed limbs: limb 0 encrypts m, limbs 1+ encrypt m'", verify(&st_mix, &b3, T), false, LIN);

    // --- oversized error 9 at one coefficient
    let mut e9 = ws[0].e.clone();
    e9[n / 2] = 9;
    let (ct9, w9) = encrypt_sk(&reg, &s, &ms[0], &slots[0], &mut PyRandom::from_u64(6), Some(e9.clone()));
    let mut cts9 = cts.clone();
    cts9[0] = ct9;
    let st9 = Statement::new(reg.clone(), Kind::Sk, cts9, slots.clone(), ctx()).unwrap();
    let mut ws9 = ws.clone();
    ws9[0] = w9.clone();
    let wit9 = Witness::Sk { s: s.clone(), e_pk: epk.clone(), cts: ws9.clone() };
    let (g1, _) = layout(Kind::Sk, n, &qp, t, &slots.iter().map(|x| x.len()).collect::<Vec<_>>(), 1).unwrap();
    let mut vals: Vec<(String, Vals)> = vec![("s".into(), Vals::Small(s.clone())), ("e_pk".into(), Vals::Small(epk.clone()))];
    for (j, w) in ws9.iter().enumerate() {
        let mut e = w.e.clone();
        if j == 0 {
            e[n / 2] = 8;
        }
        vals.push((format!("e{j}"), Vals::Small(e)));
        vals.push((format!("r{j}"), Vals::Small(w.r.clone())));
    }
    let mut d1 = values_to_digits(&g1, &vals, false).unwrap();
    let pos = 2 * n + 5 * n + 5 * (n / 2);
    d1[pos] = Fe::from_u64(2); // digits (2,1,1,1,1) = 17 = 9 + 8: one non-binary digit
    let mut o = ProveOpts { cheat: Some(Cheat { digits1: Some(d1), values1: vec![("e0".into(), Vals::Small(e9.clone()))], ..Default::default() }), ..Default::default() };
    let b4 = prove_with(&st9, &wit9, T, &mut o).unwrap();
    tb.row("oversized error 9, carried by a non-binary digit", verify(&st9, &b4, T), false, QUAD);
    let mut o = ProveOpts { cheat: Some(Cheat { values1: vals.clone(), ..Default::default() }), ..Default::default() };
    let b5 = prove_with(&st9, &wit9, T, &mut o).unwrap();
    tb.row("oversized error 9, prover claims 8 (binary digits)", verify(&st9, &b5, T), false, LIN);

    // --- plaintext nonzero off the layout
    let off = (0..n).find(|k| !slots[0].contains(k)).unwrap();
    let mut mo = ms[0].clone();
    mo[off] = 12345;
    let mut so: Vec<usize> = slots[0].clone();
    so.push(off);
    so.sort();
    let (cto, wo) = encrypt_sk(&reg, &s, &mo, &so, &mut PyRandom::from_u64(7), None);
    let wo2 = SkCt { e: wo.e.clone(), r: slots[0].iter().map(|&k| round_scale(&q, t, mo[k]).1).collect() };
    let mut cts_o = cts.clone();
    cts_o[0] = cto;
    let st_off = Statement::new(reg.clone(), Kind::Sk, cts_o, slots.clone(), ctx()).unwrap();
    let mut wso = ws.clone();
    wso[0] = wo2;
    let mut o = ProveOpts { cheat: Some(Cheat::default()), ..Default::default() };
    let b6 = prove_with(&st_off, &Witness::Sk { s: s.clone(), e_pk: epk.clone(), cts: wso }, T, &mut o).unwrap();
    tb.row("plaintext off the layout (padding coefficient nonzero)", verify(&st_off, &b6, T), false, LIN);

    // --- changed responses and codec
    let (k, th) = (sh.k, sh.th);
    let wstart = 64;
    let col0 = 64 + 32 * ((k + th) + (2 * k + th - 1) + (2 * k + 2 * th - 1));
    let mut nonc = blob.clone();
    nonc[64..96].copy_from_slice(&[0xff; 32]);
    let mut trail = blob.clone();
    trail.push(0);
    let cases: Vec<(&str, Vec<u8>, &str)> = vec![
        ("changed response: proximity message w", flip(&blob, wstart + 31), "Merkle path (root 1)"),
        ("changed response: linear message q", flip(&blob, wstart + 32 * (k + th) + 31), LIN),
        ("changed response: quadratic message p", flip(&blob, wstart + 32 * (3 * k + 2 * th - 1) + 31), QUAD),
        ("changed response: an opened column value", flip(&blob, col0 + 31), "Merkle path (root 1)"),
        ("changed response: a leaf salt", flip(&blob, col0 + 32 * (sh.m1 + 3) + 5), "Merkle path (root 1)"),
        ("changed commitment: root 1", flip(&blob, 3), LIN),
        ("changed commitment: root 2", flip(&blob, 40), LIN),
        ("truncated by one byte", blob[..blob.len() - 1].to_vec(), "proof length"),
        ("one trailing byte", trail, "proof length"),
        ("noncanonical element (w_0 replaced by 2^256 - 1 >= P)", nonc, "malformed: noncanonical field element"),
    ];
    for (name, bb, why) in cases {
        tb.row(name, verify(&st, &bb, T), false, why);
    }

    // --- Fiat-Shamir ordering: a junk ciphertext, the honest-verifier simulator on statement-only challenges
    let qd = &q / (2 * t as u128);
    let junk: Vec<BigUint> = (0..n).map(|kk| (&qd + 7u32 * kk as u32) % &q).collect();
    let zero = vec![BigUint::from(0u32); n];
    let mut cts_j = cts.clone();
    cts_j[0] = (BigPoly::from_big(&junk), BigPoly::from_big(&zero));
    let st_j = Statement::new(reg.clone(), Kind::Sk, cts_j, slots.clone(), ctx()).unwrap();
    let forged = simulate_legacy(&st_j, T, &mut OsHiding::new()).unwrap();
    tb.row("FS falsifier: simulated proof of a malformed ct, LEGACY verifier", verify_opts(&st_j, &forged, T, true), true, "accept");
    tb.row("FS falsifier: the same proof, real verifier", verify(&st_j, &forged, T), false, LIN);

    // --- public-key batch under the joint key
    let (regj0, _, _) = keygen(n, &qp, t, "joint-seed-0", "joint", &mut rng);
    let regj = Arc::new(regj0);
    let (mut pcts, mut pws, mut psl, mut pms) = (vec![], vec![], vec![], vec![]);
    for _ in 0..(m - 1).max(1) {
        let sx: Vec<usize> = (0..n.min(8)).collect();
        let mut pm = vec![0u64; n];
        for &kk in &sx {
            pm[kk] = rng.randrange_u64(t);
        }
        let (ct, w) = encrypt_pk(&regj, &pm, &sx, &mut rng, None);
        pcts.push(ct);
        pws.push(w);
        psl.push(sx);
        pms.push(pm);
    }
    let stp = Statement::new(regj.clone(), Kind::Pk, pcts.clone(), psl.clone(), ctx()).unwrap();
    let bp = prove(&stp, &Witness::Pk { cts: pws.clone() }, T).unwrap();
    let shp = shape(&stp, T).unwrap();
    assert_eq!(bp.len(), proof_bytes(shp.k, shp.th, T, shp.m1, shp.m2));
    tb.row("honest public-key batch (joint key)", verify(&stp, &bp, T), true, "accept");
    let mut e0 = pws[0].e0.clone();
    e0[1] = 9;
    let (ctb, mut wb) = encrypt_pk(&regj, &pms[0], &psl[0], &mut PyRandom::from_u64(8), Some(e0.clone()));
    wb.e0[1] = 8;
    let mut pc2 = pcts.clone();
    pc2[0] = ctb;
    let mut pw2 = pws.clone();
    pw2[0] = wb;
    let stb = Statement::new(regj.clone(), Kind::Pk, pc2, psl.clone(), ctx()).unwrap();
    let mut o = ProveOpts { cheat: Some(Cheat::default()), ..Default::default() };
    let bb = prove_with(&stb, &Witness::Pk { cts: pw2 }, T, &mut o).unwrap();
    tb.row("public key: oversized e0 = 9, prover claims 8", verify(&stb, &bb, T), false, LIN);

    // --- Codex review trace (gen 4): five 61-bit primes (Q 305 bits)
    let pw = ntt_primes(61, 6, 4);
    let (rw, _, _) = keygen(2, &pw[..5], pw[5], "audit-overflow", "custodian", &mut PyRandom::from_u64(0));
    let qw = rw.q.clone();
    let stw = Statement::new(Arc::new(rw), Kind::Sk, vec![(BigPoly::from_big(&[qw - 1u32, BigUint::from(0u32)]), BigPoly::from_big(&[BigUint::from(0u32), BigUint::from(0u32)]))], vec![vec![]], Json::s("audit")).unwrap();
    tb.row("regression: five 61-bit primes (Q 305 bits), zero bytes", verify(&stw, &[0u8; 100], T), false, "proof length");
    // a 256-bit "prime" is unrepresentable here (primes are u64); the nearest case: a prime just above the profile
    let qhi = {
        let mut p = (1u64 << 62) / 4 * 4 + 1;
        while !dzkpopk::statement::is_prime_u64(p) {
            p -= 4;
        }
        p
    };
    let rhi = Arc::new(KeyRegistry::new(2, &[qhi], t, "audit-optimized", "custodian", BigPoly::from_big(&[BigUint::from(0u32), BigUint::from(0u32)])));
    let sthi = Statement::new(rhi, Kind::Sk, vec![(BigPoly::from_big(&[BigUint::from(12345u32), BigUint::from(0u32)]), BigPoly::from_big(&[BigUint::from(0u32), BigUint::from(0u32)]))], vec![vec![]], Json::s("audit")).unwrap();
    let mut o = ProveOpts { cheat: Some(Cheat { raw: true, ..Default::default() }), ..Default::default() };
    let bz = prove_with(&sthi, &Witness::Sk { s: vec![0, 0], e_pk: vec![0, 0], cts: vec![SkCt { e: vec![0, 0], r: vec![] }] }, T, &mut o).unwrap();
    tb.row("regression: a 62-bit prime (out of profile), false statement", verify(&sthi, &bz, T), false, "key registry invalid");
    tb.row("regression: out-of-profile registry, verifier on arbitrary bytes", verify(&sthi, &[0u8; 4096], T), false, "key registry invalid");

    // --- independent review (gen 4): a 17-bit limb prime
    let small = ntt_primes(17, 1, 2 * n as u64)[0];
    let mut sp = vec![small];
    sp.extend_from_slice(&qp[1..]);
    let qs: BigUint = sp.iter().map(|&p| BigUint::from(p)).product();
    let red = |p: &BigPoly| BigPoly::from_big(&p.to_big().into_iter().map(|x| x % &qs).collect::<Vec<_>>());
    let rs = Arc::new(KeyRegistry::new(n, &sp, t, "registry-seed-0", "custodian-1", red(&reg.b)));
    let cts_s: Vec<(BigPoly, BigPoly)> = cts.iter().map(|(a, b)| (red(a), red(b))).collect();
    let st_s = Statement::new(rs, Kind::Sk, cts_s, slots.clone(), ctx()).unwrap();
    tb.row("regression: a 17-bit limb prime in the registry", verify(&st_s, &blob, T), false, "key registry invalid");

    // --- Codex review 2: one limb with Q < 17 t
    let q1 = ntt_primes(61, 1, 4)[0];
    let t1 = (0..).map(|i| q1 - 2 - 2 * i).find(|&x| dzkpopk::statement::is_prime_u64(x)).unwrap();
    let r1 = Arc::new(KeyRegistry::new(2, &[q1], t1, "audit-margin", "custodian", BigPoly::from_big(&[BigUint::from(0u32), BigUint::from(0u32)])));
    let st1 = Statement::new(r1, Kind::Sk, vec![(BigPoly::from_big(&[BigUint::from(8u32), BigUint::from(8u32)]), BigPoly::from_big(&[BigUint::from(0u32), BigUint::from(0u32)]))], vec![vec![]], Json::s("audit")).unwrap();
    tb.row("regression: one limb with Q < 17 t (no decryption margin)", verify(&st1, &[0u8; 64], T), false, "key registry invalid");

    // --- the recipient gate: products only after verify, none on refusal
    let mut calls = 0usize;
    let mut gate = |stt: &Statement, pf: &[u8]| -> Result<usize, String> {
        verify(stt, pf, T)?;
        calls += stt.cts().len();
        Ok(stt.cts().len())
    };
    let ok_n = gate(&st, &blob).unwrap();
    let before = ok_n;
    let refused = gate(&st_j, &forged).is_err();
    let gate_ok = refused && calls == before;
    println!("gate: products after accept {ok_n}, forged refused {refused}, products on refusal {}", calls - before);

    let bad_rows: Vec<_> = tb.rows.iter().filter(|r| !r.2).collect();
    println!("{} rows, {} unexpected", tb.rows.len(), bad_rows.len());
    assert!(bad_rows.is_empty(), "unexpected rows: {bad_rows:?}");
    assert!(gate_ok);
}

#[test]
fn review_regressions() {
    // independent review 2026-11-07: a BigPoly with nl = 0 or a ragged layout cannot be built (it panicked in len())
    assert!(BigPoly::from_limbs(0, vec![]).is_err());
    assert!(BigPoly::from_limbs(2, vec![1, 2, 3]).is_err());
    assert_eq!(BigPoly::from_limbs(2, vec![1, 0, 2, 0]).unwrap().len(), 2);
    // a Statement's fields are private (its context can no longer be changed under a cached digest): this file
    // only reaches them through getters, and N above 2^31 is outside the profile
    let (qp, t) = params(16, 3);
    let reg = KeyRegistry::with_a(1 << 32, &qp, t, "s", "k", BigPoly::from_limbs(1, vec![]).unwrap(), BigPoly::from_limbs(1, vec![]).unwrap());
    assert!(!reg.valid());
}
