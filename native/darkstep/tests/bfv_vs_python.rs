//! BFV keys, encryption, the returner's reply and decryption against bfv_ref/he_matvec (python3), small ring.
use darkstep::{arith, bfv, rns::Rns};
use pycompat::{PyRandom, ReprHasher};
use std::process::Command;
use std::sync::Arc;

const HARNESS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../research/dark_learning_2026_11_06");

fn py(code: &str) -> String {
    let out = Command::new("python3").current_dir(HARNESS).arg("-c").arg(code).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn h_big(v: &[num_bigint::BigUint]) -> String {
    let mut h = ReprHasher::new();
    h.raw(b"[");
    for (k, x) in v.iter().enumerate() {
        if k > 0 {
            h.sep();
        }
        h.raw(x.to_string().as_bytes());
    }
    h.raw(b"]");
    h.finish_hex()
}

fn h_u64(v: &[u64]) -> String {
    let mut h = ReprHasher::new();
    h.list_u64(v);
    h.finish_hex()
}

#[test]
fn keys_encrypt_return_decrypt_match() {
    let (n, l, fbits) = (256usize, 3usize, 100u32);
    let pr = arith::ntt_primes(61, l + 1, 2 * n as u64);
    let want = py(&format!(r#"
import hashlib, math, random
import bfv_ref as bfv, he_matvec as HM
N, L = {n}, {l}
pr = bfv.ntt_primes(61, L + 1, 2 * N); Qp, t = pr[:L], pr[L]; Q = math.prod(Qp)
H = lambda o: hashlib.sha256(repr(o).encode()).hexdigest()
k = HM.OwnKey(N, Q, t, seed=101)
m = [(i * 7919) % t for i in range(N)]
ct = k.sch.encrypt_exact(m)
rg = random.Random("ho|13|1|0|1|0|0|val")
P = [((i * 31337) % 2001) - 1000 for i in range(N)]
acc = HM.ptxct(P, ct, Q)
M = [rg.randrange(t) for _ in range(N)]
z0 = k.enc_zero_pk(rg)
F = 1 << {fbits}
c0 = [(x + y + (2 * Q * bfv.centered(mm, t) + t) // (2 * t) + rg.randint(-F, F)) % Q for x, y, mm in zip(acc[0], z0[0], M)]
c1 = [(x + y) % Q for x, y in zip(acc[1], z0[1])]
print(pr, H(k.pk[0]), H(k.pk[1]), H(ct[0]), H(ct[1]), H(k.sch.decrypt(ct)), H(M), H(c0), H(c1), H(k.sch.decrypt((c0, c1))))
"#));
    let rns = Arc::new(Rns::new(n, &pr[..l], pr[l]));
    let mut k = bfv::OwnKey::new(rns.clone(), 101);
    let t = rns.t;
    let m: Vec<u64> = (0..n as u64).map(|i| (i * 7919) % t).collect();
    let ct = k.encrypt_exact(&m);
    let mut pk0 = k.pk.pk0_ntt.clone();
    rns.inv(&mut pk0);
    let mut pk1 = k.pk.pk1_ntt.clone();
    rns.inv(&mut pk1);
    let mut rg = darkstep::coins::Coins::Py(PyRandom::from_str_seed("ho|13|1|0|1|0|0|val"));
    let p: Vec<i64> = (0..n as i64).map(|i| ((i * 31337) % 2001) - 1000).collect();
    let mut p_ntt = rns.from_signed(&p);
    rns.fwd(&mut p_ntt);
    let mut c0n = ct.c0.clone();
    rns.fwd(&mut c0n);
    let mut c1n = ct.c1.clone();
    rns.fwd(&mut c1n);
    let a0 = rns.mul_pw(&p_ntt, &c0n);
    let a1 = rns.mul_pw(&p_ntt, &c1n);
    let (ret, mm) = bfv::make_return(&rns, &k.pk, (&a0, &a1), &mut rg, fbits);
    let got = format!(
        "{:?} {} {} {} {} {} {} {} {} {}",
        pr,
        h_big(&rns.poly_big(&pk0)),
        h_big(&rns.poly_big(&pk1)),
        h_big(&rns.poly_big(&ct.c0)),
        h_big(&rns.poly_big(&ct.c1)),
        h_u64(&k.decrypt(&ct, None)),
        h_u64(&mm),
        h_big(&rns.poly_big(&ret.c0)),
        h_big(&rns.poly_big(&ret.c1)),
        h_u64(&k.decrypt(&ret, None))
    );
    assert_eq!(got, want);
    // negative control: a different returner stream must change the reply
    let mut rg2 = darkstep::coins::Coins::Py(PyRandom::from_str_seed("ho|13|1|0|1|0|0|mac"));
    let (ret2, _) = bfv::make_return(&rns, &k.pk, (&a0, &a1), &mut rg2, fbits);
    assert_ne!(h_big(&rns.poly_big(&ret2.c0)), h_big(&rns.poly_big(&ret.c0)));
}
