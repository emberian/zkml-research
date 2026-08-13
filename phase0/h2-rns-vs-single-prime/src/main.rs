mod m128;
mod m64;

use m128::{Mod128, Ntt128};
use m64::{Mod64, Ntt64};
use std::hint::black_box;
use std::time::Instant;

// ---- the deployed RNS tower (fhe.rs default_parameters degree-4096) ----
const Q0: u64 = 0x000f_ffff_e001; // 36 bit
const Q1: u64 = 0x000f_ffff_c4001 >> 0; // placeholder, fixed below
const _: () = ();

const P61: u64 = (1u64 << 61) - (1u64 << 54) + 1; // 2^61 - 2^54 + 1
const P109_SOLINAS: u128 = (1u128 << 109) - (1u128 << 65) + 1;
const P109_GENERIC: u128 = 649037107316853453566312039784449; // 0x1fffffffffffffffffffffeb2001, 2-adicity 13

const N: usize = 4096;

fn bench<F: FnMut()>(label: &str, iters: usize, trials: usize, mut f: F) -> f64 {
    // warm up
    for _ in 0..(iters.max(1) / 4 + 1) {
        f();
    }
    let mut best = f64::MAX;
    for _ in 0..trials {
        let t = Instant::now();
        for _ in 0..iters {
            f();
        }
        let e = t.elapsed().as_secs_f64() / iters as f64;
        if e < best {
            best = e;
        }
    }
    println!("{:<48} {:>12.3} us", label, best * 1e6);
    best
}

fn main() {
    let q0: u64 = 0xffffee001;
    let q1: u64 = 0xffffc4001;
    let q2: u64 = 0x1ffffe0001;
    println!("== moduli ==");
    for (n, q) in [("q0", q0), ("q1", q1), ("q2", q2), ("p61", P61)] {
        println!("  {n:>4} = {q} ({} bits)", 64 - q.leading_zeros());
    }
    println!(
        "  p109_solinas = 2^109-2^65+1 = {} ({} bits)",
        P109_SOLINAS,
        128 - P109_SOLINAS.leading_zeros()
    );
    println!(
        "  p109_generic = {} ({} bits)",
        P109_GENERIC,
        128 - P109_GENERIC.leading_zeros()
    );
    let _ = Q0;
    let _ = Q1;

    // ---------------- correctness / baseline validation ----------------
    println!("\n== validation ==");
    // 1. my u64 NTT must implement the same negacyclic transform as fhe-math's
    //    NttOperator (up to the choice of primitive 2n-th root, which fhe-math
    //    picks at RANDOM from a fixed ChaCha8 seed): both must convolve
    //    negacyclically, i.e. forward/pointwise/backward == schoolbook.
    {
        use fhe_math::ntt::NttOperator;
        use fhe_math::zq::Modulus;
        let n = 8usize;
        let fm = Modulus::new(q0).unwrap();
        let op = NttOperator::new(&fm, n).unwrap();
        let mine = Ntt64::new(q0, n);
        let m = Mod64::new(q0);
        let a: Vec<u64> = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let b: Vec<u64> = vec![2, 7, 1, 8, 2, 8, 1, 8];
        let mut naive = vec![0u64; n];
        for i in 0..n {
            for j in 0..n {
                let k = (i + j) % n;
                let prod = m.mul(a[i], b[j]);
                if i + j < n {
                    naive[k] = (naive[k] + prod) % q0;
                } else {
                    naive[k] = (naive[k] + q0 - prod) % q0;
                }
            }
        }
        for tag in ["fhe-math NttOperator", "our Ntt64"] {
            let mut fa = a.clone();
            let mut fb = b.clone();
            if tag.starts_with("fhe") {
                op.forward(&mut fa);
                op.forward(&mut fb);
            } else {
                mine.forward(&mut fa);
                mine.forward(&mut fb);
            }
            let mut fc: Vec<u64> = fa
                .iter()
                .zip(fb.iter())
                .map(|(x, y)| m.mul(*x % q0, *y % q0))
                .collect();
            if tag.starts_with("fhe") {
                op.backward(&mut fc);
            } else {
                mine.backward(&mut fc);
            }
            let fc: Vec<u64> = fc.iter().map(|x| x % q0).collect();
            assert_eq!(fc, naive, "{tag} negacyclic convolution");
            println!("  {tag}: negacyclic convolution vs schoolbook (n=8): OK");
        }
    }
    // 2. round trip for all four
    {
        let check64 = |p: u64, name: &str| {
            let t = Ntt64::new(p, N);
            let orig: Vec<u64> = (0..N as u64).map(|i| (i * 104729 + 5) % p).collect();
            let mut a = orig.clone();
            t.forward(&mut a);
            t.backward(&mut a);
            let a: Vec<u64> = a.iter().map(|x| x % p).collect();
            assert_eq!(a, orig, "{name} round trip");
            println!("  {name} round trip: OK");
        };
        check64(q0, "u64@q0(36b)");
        check64(P61, "u64@p61(61b)");
        let check128 = |p: u128, name: &str| {
            let t = Ntt128::new(p, N);
            let orig: Vec<u128> = (0..N as u128).map(|i| (i * 104729 + 5) % p).collect();
            let mut a = orig.clone();
            t.forward(&mut a);
            t.backward(&mut a);
            let a: Vec<u128> = a.iter().map(|x| x % p).collect();
            assert_eq!(a, orig, "{name} round trip");
            println!("  {name} round trip: OK");
        };
        check128(P109_SOLINAS, "u128@p109_solinas");
        check128(P109_GENERIC, "u128@p109_generic");
    }
    // 3. negacyclic convolution correctness at small n for the u128 path
    {
        let n = 8usize;
        let p = P109_SOLINAS;
        let t = Ntt128::new(p, n);
        let m = Mod128::new(p);
        let a: Vec<u128> = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let b: Vec<u128> = vec![2, 7, 1, 8, 2, 8, 1, 8];
        let mut naive = vec![0u128; n];
        for i in 0..n {
            for j in 0..n {
                let k = (i + j) % n;
                let prod = m.mul(a[i], b[j]);
                if i + j < n {
                    naive[k] = (naive[k] + prod) % p;
                } else {
                    naive[k] = (naive[k] + p - prod) % p;
                }
            }
        }
        let mut fa = a.clone();
        let mut fb = b.clone();
        t.forward(&mut fa);
        t.forward(&mut fb);
        let mut fc: Vec<u128> = fa
            .iter()
            .zip(fb.iter())
            .map(|(x, y)| m.mul(*x % p, *y % p))
            .collect();
        t.backward(&mut fc);
        let fc: Vec<u128> = fc.iter().map(|x| x % p).collect();
        assert_eq!(fc, naive, "u128 negacyclic convolution");
        println!("  u128 negacyclic convolution vs schoolbook (n=8): OK");
    }

    // ---------------- (1) scalar modmul throughput ----------------
    println!("\n== scalar modmul throughput (vector of {N}, one pass) ==");
    let mut v64: Vec<u64> = (0..N as u64).map(|i| (i * 2654435761) % q0).collect();
    let m36 = Mod64::new(q0);
    let w36 = 1234567u64 % q0;
    let ws36 = m36.shoup(w36);
    let t_shoup36 = bench("u64 36-bit  Shoup mul  x4096", 400, 40, || {
        for x in v64.iter_mut() {
            *x = m36.mul_shoup(*x, w36, ws36);
        }
        black_box(&v64);
    });
    let t_barrett36 = bench("u64 36-bit  Barrett mul (2 var) x4096", 400, 40, || {
        for x in v64.iter_mut() {
            *x = m36.mul(*x, w36);
        }
        black_box(&v64);
    });

    let m61 = Mod64::new(P61);
    let mut v61: Vec<u64> = (0..N as u64).map(|i| (i * 2654435761) % P61).collect();
    let w61 = 1234567u64 % P61;
    let ws61 = m61.shoup(w61);
    let t_shoup61 = bench("u64 61-bit  Shoup mul  x4096", 400, 40, || {
        for x in v61.iter_mut() {
            *x = m61.mul_shoup(*x, w61, ws61);
        }
        black_box(&v61);
    });
    let t_barrett61 = bench("u64 61-bit  Barrett mul (2 var) x4096", 400, 40, || {
        for x in v61.iter_mut() {
            *x = m61.mul(*x, w61);
        }
        black_box(&v61);
    });

    let m109 = Mod128::new(P109_SOLINAS);
    let mut v109: Vec<u128> = (0..N as u128)
        .map(|i| (i * 2654435761) % P109_SOLINAS)
        .collect();
    let w109 = 1234567u128 % P109_SOLINAS;
    let ws109 = m109.shoup(w109);
    let t_shoup109 = bench("u128 109-bit Shoup mul x4096", 400, 40, || {
        for x in v109.iter_mut() {
            *x = m109.mul_shoup(*x, w109, ws109);
        }
        black_box(&v109);
    });
    let t_mont109 = bench("u128 109-bit Montgomery mul (2 var) x4096", 400, 40, || {
        for x in v109.iter_mut() {
            *x = m109.mmul(*x, w109);
        }
        black_box(&v109);
    });

    // ---------------- (2) NTT ----------------
    println!("\n== forward NTT, N={N} ==");
    let n36 = Ntt64::new(q0, N);
    let n61 = Ntt64::new(P61, N);
    let n109s = Ntt128::new(P109_SOLINAS, N);
    let n109g = Ntt128::new(P109_GENERIC, N);

    let mut a36: Vec<u64> = (0..N as u64).map(|i| (i * 7919 + 13) % q0).collect();
    let mut a61: Vec<u64> = (0..N as u64).map(|i| (i * 7919 + 13) % P61).collect();
    let mut a109: Vec<u128> = (0..N as u128)
        .map(|i| (i * 7919 + 13) % P109_SOLINAS)
        .collect();
    let mut a109g: Vec<u128> = (0..N as u128)
        .map(|i| (i * 7919 + 13) % P109_GENERIC)
        .collect();

    let t_ntt36 = bench("u64 36-bit  forward NTT", 60, 40, || {
        n36.forward(&mut a36);
        black_box(&a36);
    });
    let t_ntt61 = bench("u64 61-bit  forward NTT", 60, 40, || {
        n61.forward(&mut a61);
        black_box(&a61);
    });
    let t_ntt109s = bench("u128 109-bit forward NTT (Solinas prime)", 60, 40, || {
        n109s.forward(&mut a109);
        black_box(&a109);
    });
    let t_ntt109g = bench("u128 109-bit forward NTT (generic prime)", 60, 40, || {
        n109g.forward(&mut a109g);
        black_box(&a109g);
    });

    // reference: fhe-math's own operator, to prove the u64 baseline is not a strawman
    {
        use fhe_math::ntt::NttOperator;
        use fhe_math::zq::Modulus;
        let fm = Modulus::new(q0).unwrap();
        let op = NttOperator::new(&fm, N).unwrap();
        let mut a: Vec<u64> = (0..N as u64).map(|i| (i * 7919 + 13) % q0).collect();
        bench("  [ref] fhe-math NttOperator forward (36b)", 60, 40, || {
            op.forward(&mut a);
            black_box(&a);
        });
    }

    println!("\n== inverse NTT, N={N} ==");
    let t_intt36 = bench("u64 36-bit  backward NTT", 60, 40, || {
        n36.backward(&mut a36);
        black_box(&a36);
    });
    let t_intt109s = bench("u128 109-bit backward NTT (Solinas)", 60, 40, || {
        n109s.backward(&mut a109);
        black_box(&a109);
    });

    // ---------------- (3) derived: the whole-tower comparison ----------------
    println!("\n== DERIVED: RNS tower (3 x 36/36/37-bit) vs single 109-bit ==");
    let tower_ntt = 3.0 * t_ntt36;
    println!(
        "  forward NTT of one degree-4096 poly, full modulus:\n    RNS 3-limb : {:>10.3} us  (3 x {:.3})\n    single 109 : {:>10.3} us  (Solinas)\n    single 109 : {:>10.3} us  (generic)\n    ratio single/RNS = {:.2}x (Solinas), {:.2}x (generic)",
        tower_ntt * 1e6,
        t_ntt36 * 1e6,
        t_ntt109s * 1e6,
        t_ntt109g * 1e6,
        t_ntt109s / tower_ntt,
        t_ntt109g / tower_ntt
    );
    println!(
        "  per-coefficient modmul:\n    RNS 3-limb Shoup : {:>10.3} ns/coeff (3 x {:.3})\n    single 109 Shoup : {:>10.3} ns/coeff\n    ratio = {:.2}x",
        3.0 * t_shoup36 / N as f64 * 1e9,
        t_shoup36 / N as f64 * 1e9,
        t_shoup109 / N as f64 * 1e9,
        t_shoup109 / (3.0 * t_shoup36)
    );
    println!(
        "    RNS 3-limb general (Barrett): {:>8.3} ns/coeff | single 109 Montgomery: {:>8.3} ns/coeff | ratio {:.2}x",
        3.0 * t_barrett36 / N as f64 * 1e9,
        t_mont109 / N as f64 * 1e9,
        t_mont109 / (3.0 * t_barrett36)
    );
    println!(
        "  61-bit-vs-36-bit in the SAME u64 lane (H3 probe): shoup {:.2}x, barrett {:.2}x, ntt {:.2}x",
        t_shoup61 / t_shoup36,
        t_barrett61 / t_barrett36,
        t_ntt61 / t_ntt36
    );
    println!(
        "  inverse NTT ratio single/RNS = {:.2}x",
        t_intt109s / (3.0 * t_intt36)
    );

    // ---------------- (4) end-to-end BFV op models ----------------
    println!("\n== DERIVED: BFV operations at N=4096, log q = 109 ==");
    // Cost model in units of (forward NTT, pointwise modmul, adds).
    // fold_add / ct-ct add: no NTT, just modular add over all residues.
    let mut add64: Vec<u64> = (0..N as u64)
        .map(|i| (i.wrapping_mul(6364136223846793005) >> 20) % q0)
        .collect();
    let add64b: Vec<u64> = (0..N as u64)
        .map(|i| (i.wrapping_mul(1442695040888963407) >> 20) % q0)
        .collect();
    let t_add36 = bench("u64 36-bit  modular add x4096 (branchless)", 800, 40, || {
        for (x, y) in add64.iter_mut().zip(add64b.iter()) {
            let s = *x + *y;
            let d = s.wrapping_sub(q0);
            *x = if s >= q0 { d } else { s };
        }
        black_box(&add64);
    });
    let p109 = P109_SOLINAS;
    let mut add128: Vec<u128> = (0..N as u128)
        .map(|i| (i.wrapping_mul(6364136223846793005) << 40) % p109)
        .collect();
    let add128b: Vec<u128> = (0..N as u128)
        .map(|i| (i.wrapping_mul(1442695040888963407) << 40) % p109)
        .collect();
    let t_add109 = bench("u128 109-bit modular add x4096 (branchless)", 800, 40, || {
        for (x, y) in add128.iter_mut().zip(add128b.iter()) {
            let s = *x + *y;
            let d = s.wrapping_sub(p109);
            // branchless select
            let m = ((s >= p109) as u128).wrapping_neg();
            *x = (d & m) | (s & !m);
        }
        black_box(&add128);
    });
    // lazy variant: no reduction at all (values allowed to grow to <2p / <4p).
    // This is what a fold of <=512 adds could actually do if the modulus had spare bits.
    let t_add109_lazy = bench("u128 109-bit LAZY add x4096 (no reduce)", 800, 40, || {
        for (x, y) in add128.iter_mut().zip(add128b.iter()) {
            *x = x.wrapping_add(*y);
        }
        black_box(&add128);
    });
    let t_add36_lazy = bench("u64 36-bit  LAZY add x4096 (no reduce)", 800, 40, || {
        for (x, y) in add64.iter_mut().zip(add64b.iter()) {
            *x = x.wrapping_add(*y);
        }
        black_box(&add64);
    });
    println!(
        "  LAZY add ratio single/RNS = {:.2}x   (RNS 3x{:.3} us vs single {:.3} us)",
        t_add109_lazy / (3.0 * t_add36_lazy),
        t_add36_lazy * 1e6,
        t_add109_lazy * 1e6
    );
    println!(
        "  ct+ct add (2 polys x 1 modulus-worth): RNS {:.3} us vs single {:.3} us, ratio {:.2}x",
        2.0 * 3.0 * t_add36 * 1e6,
        2.0 * t_add109 * 1e6,
        (2.0 * t_add109) / (2.0 * 3.0 * t_add36)
    );

    println!(
        "  ct*pt (both already NTT, 2 polys pointwise): RNS {:.3} us vs single {:.3} us, ratio {:.2}x",
        2.0 * 3.0 * t_shoup36 * 1e6,
        2.0 * t_shoup109 * 1e6,
        (2.0 * t_shoup109) / (2.0 * 3.0 * t_shoup36)
    );

    // ---------------- (5) THE PROOF FIELD ITSELF ----------------
    // The 109-bit modmul cost is not only an FHE-side cost: if the 109-bit prime
    // IS the proof field, the prover pays it on every one of its own field
    // operations too. Baseline: BabyBear (2^31 - 2^27 + 1), scalar and packed.
    println!("\n== proof-field arithmetic: BabyBear vs 109-bit ==");
    {
        use p3_baby_bear::BabyBear;
        use p3_field::{PackedValue, PrimeCharacteristicRing};
        type BBPacked = <BabyBear as p3_field::Field>::Packing;

        let mut bb: Vec<BabyBear> = (0..N as u32)
            .map(|i| BabyBear::from_u32(i.wrapping_mul(2654435761) % 2013265921))
            .collect();
        let wbb = BabyBear::from_u32(1234567);
        let t_bb_scalar = bench("BabyBear scalar mul x4096", 800, 40, || {
            for x in bb.iter_mut() {
                *x *= wbb;
            }
            black_box(&bb);
        });
        let lanes = BBPacked::WIDTH;
        let mut bbp: Vec<BBPacked> = (0..N / lanes).map(|_| BBPacked::from(wbb)).collect();
        let wbbp = BBPacked::from(wbb);
        let t_bb_packed = bench(
            &format!("BabyBear PACKED mul x4096 ({} lanes/vec)", lanes),
            50000,
            5,
            || {
                for x in bbp.iter_mut() {
                    *x *= wbbp;
                }
                black_box(&bbp);
            },
        );
        println!(
            "  ns/mul: BabyBear scalar {:.4}, BabyBear packed {:.4}, u64-36b Shoup {:.4}, u128-109b Shoup {:.4}, u128-109b Montgomery {:.4}",
            t_bb_scalar / N as f64 * 1e9,
            t_bb_packed / N as f64 * 1e9,
            t_shoup36 / N as f64 * 1e9,
            t_shoup109 / N as f64 * 1e9,
            t_mont109 / N as f64 * 1e9
        );
        println!(
            "  PROOF-FIELD PENALTY of moving BabyBear -> 109-bit:  {:.2}x (vs scalar BabyBear)   {:.2}x (vs packed BabyBear)",
            t_shoup109 / t_bb_scalar,
            t_shoup109 / t_bb_packed
        );
        println!(
            "  (general 2-operand: Montgomery-109 vs scalar BabyBear = {:.2}x, vs packed = {:.2}x)",
            t_mont109 / t_bb_scalar,
            t_mont109 / t_bb_packed
        );
    }

    println!("\n== sizes ==");
    let rns_bytes_packed = (109f64 / 8.0).ceil() as usize; // if bit-packed
    println!(
        "  one degree-4096 poly, u64-per-residue storage: RNS 3x4096x8 = {} B; single 109-bit as 2xu64 = {} B",
        3 * N * 8,
        N * 16
    );
    println!(
        "  bit-packed: RNS 3 limbs (36+36+37=109 b) = {} B; single 109 b = {} B  (identical)",
        (N * 109 + 7) / 8,
        N * rns_bytes_packed
    );
}
