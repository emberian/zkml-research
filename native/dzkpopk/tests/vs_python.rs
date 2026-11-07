//! Bit-exact against the harness at N = 16, three 61-bit primes (3 sk cts, 2 pk cts, a key proof) and the
//! 3-custodian ceremony; cross-verification both ways; one-byte negative controls on both verifiers.
//!
//!   cargo test --release -p dzkpopk --features test-det --test vs_python -- --nocapture
//!
//! Runs python3 on tests/py/zkpopk_vectors.py (which imports the harness from research/dark_learning_2026_11_06).

use dzkpopk::vectors::instances;
use dzkpopk::*;
use std::path::PathBuf;
use std::process::Command;

const SEED: &str = "vs-python-1";
const T: usize = 309;

fn script() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/py/zkpopk_vectors.py")
}

fn py(args: &[&str], det: Option<&str>) -> String {
    let mut c = Command::new("python3");
    c.arg(script()).args(args);
    match det {
        Some(s) => c.env("DL_DETERMINISTIC", s),
        None => c.env_remove("DL_DETERMINISTIC"),
    };
    let out = c.output().expect("python3");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap()
}

fn tmpdir(tag: &str) -> PathBuf {
    let d = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("dzkpopk-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn first_diff(a: &[u8], b: &[u8]) -> Option<usize> {
    a.iter().zip(b).position(|(x, y)| x != y).or(if a.len() != b.len() { Some(a.len().min(b.len())) } else { None })
}

fn sha(b: &[u8]) -> String {
    pycompat::repr::sha256_hex(b)
}

#[test]
fn n16_bit_exact_and_cross_verified() {
    let dir = tmpdir("n16");
    let d = dir.to_str().unwrap();
    py(&["gen", "16", "3", "3", "309", d], Some(SEED));
    for (kind, st, wit) in instances(16, 3, 3) {
        let pyb = std::fs::read(dir.join(format!("py_{kind}.bin"))).unwrap();
        let mut opts = ProveOpts { det_seed: Some(SEED.into()), ..Default::default() };
        let nat = prove_with(&st, &wit, T, &mut opts).unwrap();
        println!("{kind}: python {} native {} bytes {} first-diff {:?}", sha(&pyb), sha(&nat), nat.len(), first_diff(&pyb, &nat));
        assert_eq!(first_diff(&pyb, &nat), None, "{kind}: native proof differs from the harness");
        assert_eq!(sha(&pyb), sha(&nat));
        // negative control on the comparison: another seed gives other bytes, found at offset 0 (root 1)
        let mut other = ProveOpts { det_seed: Some("another-seed".into()), ..Default::default() };
        let nat2 = prove_with(&st, &wit, T, &mut other).unwrap();
        assert_eq!(first_diff(&pyb, &nat2), Some(0), "{kind}: the comparison must be able to fail");
        // native verifies Python's proof; refuses it with one byte flipped
        assert_eq!(verify(&st, &pyb, T), Ok(()), "{kind}: native verify of the Python proof");
        let mut flipped = pyb.clone();
        let at = pyb.len() / 2;
        flipped[at] ^= 1;
        assert!(verify(&st, &flipped, T).is_err(), "{kind}: native verify must refuse a flipped byte");
        // Python verifies native's proof (a fresh OS-random one, so not a byte copy of its own); refuses a flip
        let fresh = prove(&st, &wit, T).unwrap();
        assert_ne!(fresh, pyb);
        let p = dir.join(format!("nat_{kind}.bin"));
        std::fs::write(&p, &fresh).unwrap();
        let r = py(&["verify", "16", "3", "3", "309", kind, p.to_str().unwrap()], None);
        assert!(r.contains("\"ok\": true"), "{kind}: Python verify of the native proof: {r}");
        let mut ff = fresh.clone();
        ff[at] ^= 1;
        std::fs::write(&p, &ff).unwrap();
        let r = py(&["verify", "16", "3", "3", "309", kind, p.to_str().unwrap()], None);
        assert!(r.contains("\"ok\": false"), "{kind}: Python verify must refuse a flipped byte: {r}");
        println!("{kind}: cross-verified; flipped byte at {at} refused by both ({})", r.trim());
    }
}

#[test]
fn ceremony_bit_exact() {
    let dir = tmpdir("cer");
    let out = py(&["ceremony", "16", "3", "309"], Some(SEED));
    let v: serde_json::Value = serde_json::from_str(&out).unwrap();
    let (primes, t) = dzkpopk::vectors::params(16, 3);
    let (cer, _) = ceremony::run_ceremony_det(1, 3, 16, &primes, t, T, SEED).unwrap();
    assert_eq!(v["seed"], cer.seed.clone().unwrap());
    assert_eq!(v["transcript"], cer.transcript());
    for i in 0..3 {
        assert_eq!(v["commits"][i], cer.commits[&i].clone());
        assert_eq!(v["proofs"][i], cer.keys[&i].proof_digest.clone(), "custodian {i}'s key proof digest");
        let b = Json::List(cer.registry(i).unwrap().b.to_big().into_iter().map(|x| Json::Int(x.into())).collect());
        assert_eq!(v["b_digest"][i], sha(&b.canonical()));
    }
    // negative control: another seed, other key proofs
    let (cer2, _) = ceremony::run_ceremony_det(1, 3, 16, &primes, t, T, "another-seed").unwrap();
    assert_ne!(v["proofs"][0], cer2.keys[&0].proof_digest.clone());
    let _ = dir;
}

#[test]
fn python_default_is_still_random() {
    // the hook is opt-in: without DL_DETERMINISTIC two harness proofs of the same key statement differ
    let d1 = tmpdir("rnd1");
    let d2 = tmpdir("rnd2");
    py(&["gen", "16", "3", "3", "309", d1.to_str().unwrap(), "key"], None);
    py(&["gen", "16", "3", "3", "309", d2.to_str().unwrap(), "key"], None);
    let a = std::fs::read(d1.join("py_key.bin")).unwrap();
    let b = std::fs::read(d2.join("py_key.bin")).unwrap();
    assert_eq!(a.len(), b.len());
    assert_ne!(a, b);
}
