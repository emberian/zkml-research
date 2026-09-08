//! One existing BabyBear contraction workload, original and optimized source.
#![allow(dead_code)]
#[path = "sumcheck_baseline.rs"]
mod baseline;
#[path = "sumcheck_optimized.rs"]
mod optimized;
use std::{hint::black_box, time::Instant};
const P: u64 = 2013265921;
fn values(n: usize, seed: u64) -> Vec<u64> {
    let mut s = seed;
    (0..n)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (s >> 17) % P
        })
        .collect()
}
fn timed<T>(f: &mut impl FnMut() -> T) -> f64 {
    let start = Instant::now();
    for _ in 0..8 {
        black_box(f());
    }
    start.elapsed().as_secs_f64() / 8.0
}
fn compare<A, B>(name: &str, mut old: impl FnMut() -> A, mut new: impl FnMut() -> B) {
    black_box(old());
    black_box(new());
    let mut a = Vec::new();
    let mut b = Vec::new();
    for round in 0..9 {
        if round % 2 == 0 {
            a.push(timed(&mut old));
            b.push(timed(&mut new));
        } else {
            b.push(timed(&mut new));
            a.push(timed(&mut old));
        }
    }
    let mut aa = a.clone();
    let mut bb = b.clone();
    aa.sort_by(f64::total_cmp);
    bb.sort_by(f64::total_cmp);
    println!("{{\"phase\":\"{name}\",\"old_seconds\":{a:?},\"new_seconds\":{b:?},\"old_median_seconds\":{},\"new_median_seconds\":{},\"speedup\":{}}}",aa[4],bb[4],aa[4]/bb[4]);
}
fn main() {
    let p = black_box(P);
    let (mu, kappa, nu) = (1, 10, 7);
    let a: Vec<_> = (0..1 << mu).map(|i| values(1 << kappa, 11 + i)).collect();
    let b: Vec<_> = (0..1 << kappa).map(|q| values(1 << nu, 97 + q)).collect();
    let old = baseline::MatmulClaim {
        mu,
        kappa,
        nu,
        a: a.clone(),
        b: b.clone(),
    };
    let new = optimized::MatmulClaim {
        mu,
        kappa,
        nu,
        a,
        b,
    };
    let x = values(mu, 41);
    let y = values(nu, 53);
    let r = values(kappa, 67);
    let output = old.output(p);
    assert_eq!(output, new.output(p));
    let old_tabs = old.tables(&x, &y, p);
    let new_tabs = new.tables(&x, &y, p);
    assert_eq!(old_tabs.a, new_tabs.a);
    assert_eq!(old_tabs.b, new_tabs.b);
    let before = baseline::prove_matmul(&old, &x, &y, &r, p);
    let after = optimized::prove_matmul(&new, &x, &y, &r, p);
    assert_eq!(before.claim, after.claim);
    assert_eq!(before.rounds, after.rounds);
    assert_eq!(before.challenges, after.challenges);
    let openings = |_: &[u64]| {
        (
            baseline::mle_eval(&old_tabs.a, &r, p),
            baseline::mle_eval(&old_tabs.b, &r, p),
        )
    };
    assert!(baseline::verify_matmul(
        &output, &x, &y, &before, openings, p
    ));
    assert!(optimized::verify_matmul(
        &output, &x, &y, &after, openings, p
    ));
    let mut forged = output.clone();
    forged[0][0] = (forged[0][0] + 1) % p;
    assert!(!baseline::verify_matmul(
        &forged, &x, &y, &before, openings, p
    ));
    assert!(!optimized::verify_matmul(
        &forged, &x, &y, &after, openings, p
    ));
    let mut tampered = after.clone();
    tampered.rounds[0][1] = (tampered.rounds[0][1] + 1) % p;
    assert!(!optimized::verify_matmul(
        &output, &x, &y, &tampered, openings, p
    ));
    println!("{{\"workload\":\"[2,1024]x[1024,128]\",\"field\":{p},\"transcript_equal\":true,\"honest_accepts\":true,\"forged_output_refused_both\":true,\"h1_mutation_refused\":true,\"iterations_per_sample\":8,\"samples\":9}}");
    compare(
        "bind_outer",
        || old.tables(black_box(&x), black_box(&y), p),
        || new.tables(black_box(&x), black_box(&y), p),
    );
    compare(
        "prove_matmul",
        || baseline::prove_matmul(&old, black_box(&x), black_box(&y), black_box(&r), p),
        || optimized::prove_matmul(&new, black_box(&x), black_box(&y), black_box(&r), p),
    );
    compare(
        "output_mle",
        || baseline::mle2_eval(black_box(&output), &x, &y, p),
        || optimized::mle2_eval(black_box(&output), &x, &y, p),
    );
    compare(
        "compute_output_unchanged",
        || old.output(p),
        || new.output(p),
    );
}
