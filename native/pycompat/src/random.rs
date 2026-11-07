//! CPython's `random.Random`, bit-exact: MT19937, `init_by_array` seeding from an int, str seeding
//! (version 2: the str's UTF-8 bytes followed by their SHA-512, read big-endian), `getrandbits`,
//! `_randbelow_with_getrandbits`, `randrange`, `randint` and `choice`.
//! Reference: CPython Modules/_randommodule.c and Lib/random.py (3.10 to 3.15 agree on all of these).
use num_bigint::{BigInt, BigUint, Sign};
use sha2::{Digest, Sha512};

const NN: usize = 624;
const MM: usize = 397;

#[derive(Clone)]
pub struct PyRandom {
    mt: Box<[u32; NN]>,
    idx: usize,
}

impl PyRandom {
    fn init_genrand(s: u32) -> Self {
        let mut mt = Box::new([0u32; NN]);
        mt[0] = s;
        for i in 1..NN {
            mt[i] = 1812433253u32.wrapping_mul(mt[i - 1] ^ (mt[i - 1] >> 30)).wrapping_add(i as u32);
        }
        PyRandom { mt, idx: NN }
    }

    /// `init_by_array` with 32-bit key words, least significant first.
    pub fn from_key(key: &[u32]) -> Self {
        let mut r = Self::init_genrand(19650218);
        let mt = &mut r.mt;
        let (mut i, mut j) = (1usize, 0usize);
        let klen = key.len().max(1);
        let mut k = NN.max(klen);
        while k > 0 {
            let kj = if key.is_empty() { 0 } else { key[j] };
            mt[i] = (mt[i] ^ (mt[i - 1] ^ (mt[i - 1] >> 30)).wrapping_mul(1664525))
                .wrapping_add(kj)
                .wrapping_add(j as u32);
            i += 1;
            j += 1;
            if i >= NN {
                mt[0] = mt[NN - 1];
                i = 1;
            }
            if j >= klen {
                j = 0;
            }
            k -= 1;
        }
        k = NN - 1;
        while k > 0 {
            mt[i] = (mt[i] ^ (mt[i - 1] ^ (mt[i - 1] >> 30)).wrapping_mul(1566083941)).wrapping_sub(i as u32);
            i += 1;
            if i >= NN {
                mt[0] = mt[NN - 1];
                i = 1;
            }
            k -= 1;
        }
        mt[0] = 0x8000_0000;
        r
    }

    /// `random.Random(n)` for a nonnegative int given as a BigUint (CPython uses abs(n)).
    pub fn from_biguint(n: &BigUint) -> Self {
        let words = n.to_u32_digits();
        if words.is_empty() {
            Self::from_key(&[0])
        } else {
            Self::from_key(&words)
        }
    }

    pub fn from_u64(n: u64) -> Self {
        Self::from_biguint(&BigUint::from(n))
    }

    pub fn from_i64(n: i64) -> Self {
        Self::from_u64(n.unsigned_abs())
    }

    /// `random.Random(int(hexdigest, 16))`.
    pub fn from_hex_int(hex: &str) -> Self {
        Self::from_biguint(&BigUint::parse_bytes(hex.as_bytes(), 16).expect("hex"))
    }

    /// `random.Random(s)` for a str (version 2 seeding).
    pub fn from_str_seed(s: &str) -> Self {
        let mut buf = s.as_bytes().to_vec();
        buf.extend_from_slice(&Sha512::digest(s.as_bytes()));
        Self::from_biguint(&BigUint::from_bytes_be(&buf))
    }

    /// `random.Random().setstate((3, words + (idx,), None))`: the 624 MT words and the position, as
    /// `getstate()[1]` lists them (625 entries).
    pub fn from_state(state: &[u64]) -> Self {
        assert_eq!(state.len(), NN + 1, "getstate()[1] has 625 entries");
        let mut mt = Box::new([0u32; NN]);
        for (m, &w) in mt.iter_mut().zip(state) {
            *m = u32::try_from(w).expect("MT word");
        }
        let idx = state[NN] as usize;
        assert!(idx <= NN, "MT position");
        PyRandom { mt, idx }
    }

    /// The inverse of `from_state` (625 entries).
    pub fn state(&self) -> Vec<u64> {
        let mut out: Vec<u64> = self.mt.iter().map(|&w| w as u64).collect();
        out.push(self.idx as u64);
        out
    }

    fn twist(&mut self) {
        let mt = &mut self.mt;
        const UPPER: u32 = 0x8000_0000;
        const LOWER: u32 = 0x7fff_ffff;
        const MATRIX_A: u32 = 0x9908_b0df;
        for kk in 0..NN {
            let y = (mt[kk] & UPPER) | (mt[(kk + 1) % NN] & LOWER);
            mt[kk] = mt[(kk + MM) % NN] ^ (y >> 1) ^ if y & 1 != 0 { MATRIX_A } else { 0 };
        }
        self.idx = 0;
    }

    #[inline]
    pub fn genrand_u32(&mut self) -> u32 {
        if self.idx >= NN {
            self.twist();
        }
        let mut y = self.mt[self.idx];
        self.idx += 1;
        y ^= y >> 11;
        y ^= (y << 7) & 0x9d2c_5680;
        y ^= (y << 15) & 0xefc6_0000;
        y ^= y >> 18;
        y
    }

    /// getrandbits(k) for k <= 64.
    #[inline]
    pub fn getrandbits_u64(&mut self, k: u32) -> u64 {
        debug_assert!(k <= 64);
        if k == 0 {
            return 0;
        }
        if k <= 32 {
            return (self.genrand_u32() >> (32 - k)) as u64;
        }
        let lo = self.genrand_u32() as u64;
        let rem = k - 32;
        let hi = (self.genrand_u32() >> (32 - rem)) as u64;
        lo | (hi << 32)
    }

    /// getrandbits(k) for any k, as little-endian u64 limbs (ceil(k/64) of them, at least one).
    pub fn getrandbits_limbs(&mut self, k: u32) -> Vec<u64> {
        let nl = ((k as usize) + 63) / 64;
        let mut out = vec![0u64; nl.max(1)];
        if k <= 32 {
            out[0] = self.getrandbits_u64(k);
            return out;
        }
        let mut rem = k as i64;
        let mut w = 0usize;
        while rem > 0 {
            let mut r = self.genrand_u32();
            if rem < 32 {
                r >>= 32 - rem;
            }
            out[w / 2] |= (r as u64) << (32 * (w % 2));
            w += 1;
            rem -= 32;
        }
        out
    }

    /// `_randbelow(n)` for 0 < n < 2^64.
    #[inline]
    pub fn randbelow_u64(&mut self, n: u64) -> u64 {
        if n == 0 {
            return 0;
        }
        let k = 64 - n.leading_zeros();
        loop {
            let r = self.getrandbits_u64(k);
            if r < n {
                return r;
            }
        }
    }

    /// `_randbelow(n)` for n given as little-endian u64 limbs (no trailing zero limbs needed).
    pub fn randbelow_limbs(&mut self, n: &[u64]) -> Vec<u64> {
        let k = bitlen(n);
        if k == 0 {
            return vec![0];
        }
        loop {
            let r = self.getrandbits_limbs(k);
            if lt(&r, n) {
                return r;
            }
        }
    }

    pub fn randbelow_big(&mut self, n: &BigUint) -> BigUint {
        let limbs = n.to_u64_digits();
        let r = self.randbelow_limbs(&limbs);
        BigUint::from_slice(&to_u32s(&r))
    }

    #[inline]
    pub fn randrange_u64(&mut self, n: u64) -> u64 {
        self.randbelow_u64(n)
    }

    /// randint(a, b) with b - a + 1 < 2^64.
    #[inline]
    pub fn randint_i64(&mut self, a: i64, b: i64) -> i64 {
        let width = (b as i128 - a as i128 + 1) as u64;
        (a as i128 + self.randbelow_u64(width) as i128) as i64
    }

    pub fn randint_big(&mut self, a: &BigInt, b: &BigInt) -> BigInt {
        let width = (b - a + 1u32).to_biguint().expect("empty range");
        a + BigInt::from_biguint(Sign::Plus, self.randbelow_big(&width))
    }

    /// randint(-f, f) for f = 2^fbits, returned as (negative?, magnitude limbs).
    pub fn randint_sym_pow2(&mut self, fbits: u32) -> (bool, Vec<u64>) {
        // width = 2^(fbits+1) + 1
        let nl = (fbits as usize + 1) / 64 + 1;
        let mut width = vec![0u64; nl];
        width[(fbits as usize + 1) / 64] |= 1u64 << ((fbits + 1) % 64);
        width[0] += 1;
        let r = self.randbelow_limbs(&width);
        // value = r - 2^fbits
        let mut f = vec![0u64; nl];
        f[fbits as usize / 64] |= 1u64 << (fbits % 64);
        let mut rr = r.clone();
        rr.resize(nl, 0);
        if lt(&rr, &f) {
            (true, sub_limbs(&f, &rr))
        } else {
            (false, sub_limbs(&rr, &f))
        }
    }

    /// getrandbits(k) into a fixed array of W little-endian limbs (k <= 64 W), no allocation.
    #[inline]
    pub fn getrandbits_arr<const W: usize>(&mut self, k: u32) -> [u64; W] {
        let mut out = [0u64; W];
        if k <= 32 {
            out[0] = self.getrandbits_u64(k);
            return out;
        }
        debug_assert!(k as usize <= 64 * W);
        let mut rem = k as i64;
        let mut w = 0usize;
        while rem > 0 {
            let mut r = self.genrand_u32();
            if rem < 32 {
                r >>= 32 - rem;
            }
            out[w / 2] |= (r as u64) << (32 * (w % 2));
            w += 1;
            rem -= 32;
        }
        out
    }

    /// _randbelow(n) for n given as W limbs, no allocation.
    #[inline]
    pub fn randbelow_arr<const W: usize>(&mut self, n: &[u64; W]) -> [u64; W] {
        let k = bitlen(n);
        if k == 0 {
            return [0; W];
        }
        loop {
            let r = self.getrandbits_arr::<W>(k);
            if lt(&r, n) {
                return r;
            }
        }
    }

    /// randint(-2^f, 2^f) as (negative?, magnitude) in W limbs, no allocation (f + 2 <= 64 W).
    #[inline]
    pub fn randint_sym_pow2_arr<const W: usize>(&mut self, fbits: u32) -> (bool, [u64; W]) {
        let mut width = [0u64; W];
        width[(fbits as usize + 1) / 64] |= 1u64 << ((fbits + 1) % 64);
        width[0] += 1;
        let r = self.randbelow_arr(&width);
        let mut f = [0u64; W];
        f[fbits as usize / 64] |= 1u64 << (fbits % 64);
        if lt(&r, &f) {
            (true, sub_arr(&f, &r))
        } else {
            (false, sub_arr(&r, &f))
        }
    }

    /// choice(seq) index for len(seq) = n.
    #[inline]
    pub fn choice_idx(&mut self, n: usize) -> usize {
        self.randbelow_u64(n as u64) as usize
    }

    /// choice((-1, 0, 1)).
    #[inline]
    pub fn ternary(&mut self) -> i64 {
        self.choice_idx(3) as i64 - 1
    }
}

pub fn bitlen(n: &[u64]) -> u32 {
    for i in (0..n.len()).rev() {
        if n[i] != 0 {
            return 64 * i as u32 + (64 - n[i].leading_zeros());
        }
    }
    0
}

/// a < b on little-endian limbs of possibly different lengths.
pub fn lt(a: &[u64], b: &[u64]) -> bool {
    let l = a.len().max(b.len());
    for i in (0..l).rev() {
        let x = *a.get(i).unwrap_or(&0);
        let y = *b.get(i).unwrap_or(&0);
        if x != y {
            return x < y;
        }
    }
    false
}

/// a - b for a >= b, equal lengths.
pub fn sub_limbs(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut out = vec![0u64; a.len()];
    let mut borrow = 0u64;
    for i in 0..a.len() {
        let y = *b.get(i).unwrap_or(&0);
        let (d1, b1) = a[i].overflowing_sub(y);
        let (d2, b2) = d1.overflowing_sub(borrow);
        out[i] = d2;
        borrow = (b1 || b2) as u64;
    }
    out
}

fn sub_arr<const W: usize>(a: &[u64; W], b: &[u64; W]) -> [u64; W] {
    let mut out = [0u64; W];
    let mut borrow = 0u64;
    for i in 0..W {
        let (d1, b1) = a[i].overflowing_sub(b[i]);
        let (d2, b2) = d1.overflowing_sub(borrow);
        out[i] = d2;
        borrow = (b1 || b2) as u64;
    }
    out
}

pub fn to_u32s(l: &[u64]) -> Vec<u32> {
    l.iter().flat_map(|&x| [x as u32, (x >> 32) as u32]).collect()
}
