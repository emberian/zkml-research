//! `darkvfhe`: Native multithreaded (`rayon`) `HoistedB61` RNS-NTT `ct x ct` engine and verifier.
//!
//! Closes the #1 `[OPEN]` engineering boundary from `notes/vfhe-hoisted-certificate-breakthrough.md`:
//! 1. **Extended-Basis RNS-NTT Hoisted `ct x ct` Engine (`rns_hoist`)**:
//!    Precomputes NTT of unique input ciphertexts across `L = 3` ciphertext primes `Qp` and `k = 5`
//!    extension primes `Bp` (`8` 61-bit NTT primes total), accumulates unrescaled tensor products
//!    `(c0, c1, c2)` across `K` blocks (`K = 64` forward, `K = 32` transpose, `K = 2,374` dark `vPIR`,
//!    or `tau = 64` temporal outer-product steps) with 32-way lazy `u128` reduction in `rayon` parallel,
//!    runs 1 inverse NTT per output group `r`, and executes 1 exact BEHZ integer rescale + RNS-gadget
//!    relinearization (`P_ks = b_0`, four 60-bit limbs from `w = 20` digits).
//! 2. **Canonical Digit Lifts (`digits`)**:
//!    Supports both `Direct-20` (`10` `w = 20` digits for `Q`, `14` for `y`) and zero-slack
//!    `Exact-Garner-15` (`15` `w = 20` digits enforcing `u in [0, Q - 1]` via `delta_i = 2^61 - q_i < 2^20`,
//!    closing the `[Q, 2^183)` non-power-of-two boundary strip).
//! 3. **Fused `d`-Free Polynomial Rescale Certificate (`cert`)**:
//!    Witness-bound SHA-256 Fiat-Shamir transcript + `R_blk x K_blk` scalar matvec over `F_p` across all
//!    8 primes in parallel, proving exact Euclidean BEHZ division + negacyclic ring reduction without
//!    committing `d_k`.
//! 4. **Native 61-Bit `D1b` LogUp-GKR Fraction-Tree Prover & Verifier (`logup_gkr`)**:
//!    `ProveKit v2` subdomain-projected `[0, 2^20)` multiplicity commitment + multi-challenge (`c = 3`
//!    batched `2^18` trees @ `122.0` bits; `c = 4` monolithic trees @ `128.0+` bits) projective fraction
//!    tree + degree-3 GKR sumchecks (`Assurance/AirSumcheckCubic.lean`).

pub mod bigint;
pub mod cert;
pub mod dark_block;
pub mod dark_clearing;
pub mod dark_gdn;
pub mod dark_gdn_continual;
pub mod digits;
pub mod logup_gkr;
pub mod rns_hoist;
pub mod succinct_pcs;
pub mod threshold_custody;
pub mod whir_pcs;

use darkstep::arith::{invmod, mulmod, ntt_primes, submod, Modulus};
use num_bigint::BigUint;

const M61: u128 = (1u128 << 61) - 1;

/// Fast pseudo-Mersenne / Crandall modular reduction for 61-bit primes `p = 2^61 - delta`.
/// When `delta < 2^22` (true for all deployed `Qp`, `Bp`, and `t` primes), reduces any `x: u128`
/// in two 61-bit folds and one conditional subtraction with zero hardware divisions.
#[derive(Clone, Copy, Debug)]
pub struct FastPrime61 {
    pub p: u64,
    pub delta: u64,
    pub fast_fold: bool,
    pub barrett: Modulus,
}

impl FastPrime61 {
    pub fn new(p: u64) -> Self {
        assert!(p > (1u64 << 32) && p < (1u64 << 61));
        let delta = (1u64 << 61) - p;
        let fast_fold = delta < (1u64 << 22);
        FastPrime61 {
            p,
            delta,
            fast_fold,
            barrett: Modulus::new(p),
        }
    }

    #[inline(always)]
    pub fn red128(&self, x: u128) -> u64 {
        if self.fast_fold {
            let d = self.delta as u128;
            let t1 = (x & M61) + (x >> 61) * d;
            let t2 = ((t1 & M61) + (t1 >> 61) * d) as u64;
            if t2 >= self.p {
                t2 - self.p
            } else {
                t2
            }
        } else {
            (x % self.p as u128) as u64
        }
    }

    #[inline(always)]
    pub fn add(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= self.p {
            s - self.p
        } else {
            s
        }
    }

    #[inline(always)]
    pub fn sub(&self, a: u64, b: u64) -> u64 {
        if a >= b {
            a - b
        } else {
            a + self.p - b
        }
    }

    #[inline(always)]
    pub fn neg(&self, a: u64) -> u64 {
        if a == 0 {
            0
        } else {
            self.p - a
        }
    }

    #[inline(always)]
    pub fn mul(&self, a: u64, b: u64) -> u64 {
        self.red128(a as u128 * b as u128)
    }

    #[inline]
    pub fn pow(&self, mut base: u64, mut exp: u64) -> u64 {
        let mut res = 1u64;
        base %= self.p;
        while exp > 0 {
            if exp & 1 == 1 {
                res = self.mul(res, base);
            }
            base = self.mul(base, base);
            exp >>= 1;
        }
        res
    }

    #[inline]
    pub fn inv(&self, a: u64) -> u64 {
        let r = a % self.p;
        assert!(r != 0, "division by zero in F_p");
        self.pow(r, self.p - 2)
    }

    /// Dot product over `F_p` accumulating 32 `u64 * u64` products in `u128` per reduction.
    #[inline]
    pub fn dot(&self, a: &[u64], b: &[u64]) -> u64 {
        debug_assert_eq!(a.len(), b.len());
        let mut acc = 0u64;
        for (ca, cb) in a.chunks(32).zip(b.chunks(32)) {
            let mut s = 0u128;
            for (&x, &y) in ca.iter().zip(cb.iter()) {
                s += x as u128 * y as u128;
            }
            acc = self.add(acc, self.red128(s));
        }
        acc
    }

    /// Horner evaluation of polynomial `coeffs[0] + coeffs[1]*r + ...` modulo `p`.
    #[inline]
    pub fn eval_poly(&self, coeffs: &[u64], r: u64) -> u64 {
        let mut acc = 0u64;
        for &c in coeffs.iter().rev() {
            let v = if c >= self.p { c % self.p } else { c };
            acc = self.add(self.mul(acc, r), v);
        }
        acc
    }

    /// Evaluate `sum_{j=0}^{n-1} r^j mod p` in `O(log n)`.
    #[inline]
    pub fn ones_eval(&self, n: usize, r: u64) -> u64 {
        let rr = r % self.p;
        if rr == 1 {
            (n as u64) % self.p
        } else {
            let num = self.sub(self.pow(rr, n as u64), 1);
            let den = self.inv(self.sub(rr, 1));
            self.mul(num, den)
        }
    }
}

/// Public parameters for `HoistedB61` over `Z[X]/(X^N + 1)` with `L = 3` ciphertext primes `Qp`,
/// `k = 5` extension primes `Bp`, and plaintext modulus `t` (the SPDZ prime).
#[derive(Clone, Debug)]
pub struct HoistedParams {
    pub n: usize,
    pub qp: [u64; 3],
    pub bp: [u64; 5],
    pub all_primes: [u64; 8],
    pub fp: [FastPrime61; 8],
    pub fp_t: FastPrime61,
    pub t: u64,
    /// `Q = q0 * q1 * q2` (`~183` bits) as 3 little-endian `u64` limbs and `BigUint`.
    pub q_limbs: [u64; 3],
    pub half_q_limbs: [u64; 3],
    pub q_minus_half_q_limbs: [u64; 3],
    pub q_big: BigUint,
    pub half_q_big: BigUint,
    /// `M_QB = prod_{i=0..7} all_primes[i]` (`~488` bits) as 9 little-endian `u64` limbs and `BigUint`.
    pub mqb_limbs: [u64; 9],
    pub half_mqb_limbs: [u64; 9],
    pub mqb_big: BigUint,
    /// Prefix products `prod_{j < m} all_primes[j]` in 9-limb little-endian form (`m = 0..8`).
    pub prefix_prods: [[u64; 9]; 8],
    /// `prefix_prods[i] mod all_primes[m]` for `0 <= i < m < 8`.
    pub prefix_mod: [[u64; 8]; 8],
    /// `(prod_{j < m} all_primes[j])^{-1} mod all_primes[m]` for `m = 1..8`.
    pub inv_prefix_mod: [u64; 8],
    /// `Q mod p_l`, `floor(Q/2) mod p_l`, `t mod p_l`, and `2^100 mod p_l` for each of the 8 primes.
    pub q_mod_p: [u64; 8],
    pub half_q_mod_p: [u64; 8],
    pub t_mod_p: [u64; 8],
    pub pow2_100_mod_p: [u64; 8],
    /// RNS modulus-drop constants for `P_ks = bp[0]` -> `qp[0..3]`: `bp[0]^{-1} mod qp[k]`.
    pub inv_b0_mod_q: [u64; 3],
}

impl HoistedParams {
    /// Construct canonical `fhe_fork.setup(N)` parameters:
    /// `Qp = top 3 NTT primes < 2^61`, `t = 4th NTT prime`, `Bp = next 5 NTT primes`.
    pub fn for_ring(n: usize) -> Self {
        assert!(n.is_power_of_two() && n >= 16);
        let ps = ntt_primes(61, 9, 2 * n as u64);
        let qp = [ps[0], ps[1], ps[2]];
        let t = ps[3];
        let bp = [ps[4], ps[5], ps[6], ps[7], ps[8]];
        Self::new(n, qp, bp, t)
    }

    /// Deployed `N = 8192` parameters (`log2 Q = 183`, `L = 3`, `k = 5`).
    pub fn n8192() -> Self {
        Self::for_ring(8192)
    }

    pub fn new(n: usize, qp: [u64; 3], bp: [u64; 5], t: u64) -> Self {
        assert!(n.is_power_of_two() && n >= 2);
        let all_primes = [qp[0], qp[1], qp[2], bp[0], bp[1], bp[2], bp[3], bp[4]];
        for &p in &all_primes {
            assert_eq!((p - 1) % (2 * n as u64), 0, "prime {p} is not 1 mod 2N");
        }
        let fp = all_primes.map(FastPrime61::new);
        let fp_t = FastPrime61::new(t);

        let mut prefix_prods = [[0u64; 9]; 8];
        let mut cur = BigUint::from(1u32);
        let mut prefix_bigs = Vec::with_capacity(8);
        for m in 0..8 {
            prefix_prods[m] = bigint::biguint_to_limbs9(&cur);
            prefix_bigs.push(cur.clone());
            cur *= BigUint::from(all_primes[m]);
        }
        let mqb_big = cur;
        let half_mqb_big = &mqb_big >> 1usize;
        let mqb_limbs = bigint::biguint_to_limbs9(&mqb_big);
        let half_mqb_limbs = bigint::biguint_to_limbs9(&half_mqb_big);

        let q_big: BigUint = qp.iter().map(|&q| BigUint::from(q)).product();
        let half_q_big: BigUint = &q_big >> 1usize;
        let q_minus_half_q_big: BigUint = &q_big - &half_q_big;
        let q_limbs = bigint::biguint_to_limbs3(&q_big);
        let half_q_limbs = bigint::biguint_to_limbs3(&half_q_big);
        let q_minus_half_q_limbs = bigint::biguint_to_limbs3(&q_minus_half_q_big);

        let mut prefix_mod = [[0u64; 8]; 8];
        let mut inv_prefix_mod = [0u64; 8];
        for m in 1..8 {
            let pm = all_primes[m];
            for i in 0..m {
                prefix_mod[m][i] = bigint::biguint_mod_u64(&prefix_bigs[i], pm);
            }
            // Recompute directly from exact prefix_bigs[m] mod pm to avoid any overflow in u64 product:
            let p_mod = bigint::biguint_mod_u64(&prefix_bigs[m], pm);
            inv_prefix_mod[m] = invmod(p_mod, pm);
        }

        let two100 = BigUint::from(1u32) << 100usize;
        let mut q_mod_p = [0u64; 8];
        let mut half_q_mod_p = [0u64; 8];
        let mut t_mod_p = [0u64; 8];
        let mut pow2_100_mod_p = [0u64; 8];
        for l in 0..8 {
            let p = all_primes[l];
            q_mod_p[l] = bigint::biguint_mod_u64(&q_big, p);
            half_q_mod_p[l] = bigint::biguint_mod_u64(&half_q_big, p);
            t_mod_p[l] = t % p;
            pow2_100_mod_p[l] = bigint::biguint_mod_u64(&two100, p);
        }

        let b0 = bp[0];
        let inv_b0_mod_q = [
            invmod(b0 % qp[0], qp[0]),
            invmod(b0 % qp[1], qp[1]),
            invmod(b0 % qp[2], qp[2]),
        ];

        let _ = (mulmod, submod);
        HoistedParams {
            n,
            qp,
            bp,
            all_primes,
            fp,
            fp_t,
            t,
            q_limbs,
            half_q_limbs,
            q_minus_half_q_limbs,
            q_big,
            half_q_big,
            mqb_limbs,
            half_mqb_limbs,
            mqb_big,
            prefix_prods,
            prefix_mod,
            inv_prefix_mod,
            q_mod_p,
            half_q_mod_p,
            t_mod_p,
            pow2_100_mod_p,
            inv_b0_mod_q,
        }
    }

    /// Public worst-case CRT no-wrap check (`Astra E6`):
    /// Ensures `max |t * D_{k,j} + floor(Q/2)| + max |Q * y_{k,j} + s_{k,j}| < Q * B`
    /// even when lifted inputs only satisfy power-of-two `< 2^183` bounds (`max_y_bits` quotient bound).
    pub fn check_crt_nowrap(&self, k_blk: usize, max_y_bits: u32) -> bool {
        let q_bits = self.q_big.bits() as usize;
        let max_lhs = BigUint::from(self.t)
            * BigUint::from(k_blk as u64)
            * BigUint::from(2u64 * self.n as u64)
            * (BigUint::from(1u32) << (2 * q_bits - 2))
            + &self.half_q_big;
        let max_rhs = (&self.q_big << (max_y_bits as usize)) + (BigUint::from(1u32) << q_bits);
        max_lhs + max_rhs < self.mqb_big
    }

    /// Recommended signed quotient shift bit-width `max_y_bits` (`262` for `K <= 64`, `268` for `K <= 4096`).
    pub fn default_max_y_bits(&self, k_blk: usize) -> u32 {
        if k_blk <= 64 {
            262
        } else {
            let extra = (usize::BITS - (k_blk - 1).leading_zeros()).saturating_sub(6);
            262 + extra
        }
    }
}

/// Read current resident set size (RSS) and peak resident set size in MiB on macOS (`mach_task_basic_info` / `getrusage`)
/// or Linux (`/proc/self/status`).
pub fn process_memory_mib() -> (f64, f64) {
    #[cfg(target_os = "macos")]
    unsafe {
        let mut usage: libc::rusage = std::mem::zeroed();
        if libc::getrusage(libc::RUSAGE_SELF, &mut usage) == 0 {
            // On macOS/Darwin, ru_maxrss is in bytes!
            let peak_mib = (usage.ru_maxrss as f64) / (1024.0 * 1024.0);
            return (peak_mib, peak_mib);
        }
        (0.0, 0.0)
    }
    #[cfg(not(target_os = "macos"))]
    {
        let cur = darkproof::rss_gb("VmRSS") * (1e9 / (1024.0 * 1024.0));
        let peak = darkproof::rss_gb("VmHWM") * (1e9 / (1024.0 * 1024.0));
        (cur, peak)
    }
}
