//! Micro-benchmarks of the HE helpers' kernels at a profile: dsbench N L F_bits
use darkstep::arith::ntt_primes;
use darkstep::bfv::{make_return, OwnKey};
use darkstep::rns::Rns;
use pycompat::PyRandom;
use std::sync::Arc;
use std::time::Instant;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (n, l, f): (usize, usize, u32) = (a[1].parse().unwrap(), a[2].parse().unwrap(), a[3].parse().unwrap());
    let pr = ntt_primes(61, l + 1, 2 * n as u64);
    let rns = Arc::new(Rns::new(n, &pr[..l], pr[l]));
    let mut key = OwnKey::new(rns.clone(), 100);
    let m: Vec<u64> = (0..n as u64).map(|i| i % rns.t).collect();
    let it = 20;
    let t = Instant::now();
    let mut ct = key.encrypt_exact(&m);
    for _ in 1..it {
        ct = key.encrypt_exact(&m);
    }
    println!("encrypt_exact {:.2} ms", t.elapsed().as_secs_f64() * 1e3 / it as f64);
    let mut x = ct.c0.clone();
    let t = Instant::now();
    for _ in 0..it {
        rns.fwd(&mut x);
    }
    println!("ntt fwd (L limbs) {:.2} ms", t.elapsed().as_secs_f64() * 1e3 / it as f64);
    let t = Instant::now();
    for _ in 0..it {
        let _ = rns.mul_pw(&x, &ct.c1);
    }
    println!("mul_pw {:.2} ms", t.elapsed().as_secs_f64() * 1e3 / it as f64);
    let t = Instant::now();
    let mut r = darkstep::coins::Coins::Py(PyRandom::from_str_seed("x"));
    for _ in 0..it {
        let _ = make_return(&rns, &key.pk, (&x, &x), &mut r, f);
    }
    println!("make_return (reference coins) {:.2} ms", t.elapsed().as_secs_f64() * 1e3 / it as f64);
    let t = Instant::now();
    let mut r = darkstep::coins::Coins::Prf(darkstep::coins::Prf::new(&darkstep::coins::os_key(), "x"));
    for _ in 0..it {
        let _ = make_return(&rns, &key.pk, (&x, &x), &mut r, f);
    }
    println!("make_return (OS-keyed PRF coins) {:.2} ms", t.elapsed().as_secs_f64() * 1e3 / it as f64);
    let t = Instant::now();
    let mut r = PyRandom::from_str_seed("y");
    let mut s = 0u64;
    for _ in 0..it * n {
        let (_, mag) = r.randint_sym_pow2_arr::<5>(f);
        s ^= mag[0];
    }
    println!("flood draws {:.2} ms/poly ({s})", t.elapsed().as_secs_f64() * 1e3 / it as f64);
    let t = Instant::now();
    for _ in 0..it * n {
        s ^= r.randrange_u64(rns.t) ^ r.randint_i64(-8, 8) as u64 ^ r.ternary() as u64;
    }
    println!("small draws {:.2} ms/poly ({s})", t.elapsed().as_secs_f64() * 1e3 / it as f64);
    let t = Instant::now();
    for _ in 0..it {
        let _ = key.decrypt(&ct, None);
    }
    println!("decrypt (all coefs) {:.2} ms", t.elapsed().as_secs_f64() * 1e3 / it as f64);
    let t = Instant::now();
    for _ in 0..it {
        let _ = PyRandom::from_str_seed("ho|13|1|0|1|0|0|val");
    }
    println!("seed from str {:.3} ms", t.elapsed().as_secs_f64() * 1e3 / it as f64);
}
