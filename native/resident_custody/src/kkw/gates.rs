//! One circuit description, five evaluations.
//!
//! A circuit sees only [`Builder`]. [`Trace`] computes the extended witness in the clear.
//! [`Eval`] turns the same calls into degree-two constraint words for a [`Gates`] mode:
//! [`Count`] measures the shape, [`Check`] evaluates the residual of a clear or masked
//! witness, [`Quadratic`] the homogeneous quadratic part on the aggregate mask, and
//! [`Online`] the masked residual together with every party's linear share.
//!
//! For a constraint `f`, masked witness `m` and mask `r = ⊕ r_i`,
//! `f(m ⊕ r) = Check(m) ⊕ Quadratic(r) ⊕ ⊕_i Online_i(r_i)`. Each online bit plane holds one bit from each of the 64 party tapes.
use super::keccak;
use super::tape::{Aggregate, Tapes};
use super::{Fingerprint, PARTIES};
use std::ops::BitXor;

/// A 64-bit circuit word in one evaluation. Every operation here is GF(2)-linear.
pub(crate) trait Lane: Copy + BitXor<Output = Self> {
    fn zero() -> Self;
    fn rotl(self, k: u32) -> Self;
    fn shl(self, k: u32) -> Self;
    fn shr(self, k: u32) -> Self;
    /// Bitwise AND with a public constant.
    fn mask(self, m: u64) -> Self;
    /// Copy bit `bit` to all 64 positions.
    fn splat(self, bit: u32) -> Self;
    /// Reverse the bit order within each byte.
    fn rev8(self) -> Self;
}

impl Lane for u64 {
    #[inline(always)]
    fn zero() -> Self {
        0
    }
    #[inline(always)]
    fn rotl(self, k: u32) -> Self {
        self.rotate_left(k)
    }
    #[inline(always)]
    fn shl(self, k: u32) -> Self {
        debug_assert!(k < 64);
        self << k
    }
    #[inline(always)]
    fn shr(self, k: u32) -> Self {
        debug_assert!(k < 64);
        self >> k
    }
    #[inline(always)]
    fn mask(self, m: u64) -> Self {
        self & m
    }
    #[inline(always)]
    fn splat(self, bit: u32) -> Self {
        0u64.wrapping_sub((self >> bit) & 1)
    }
    #[inline(always)]
    fn rev8(self) -> Self {
        self.reverse_bits().swap_bytes()
    }
}

// Six butterfly exchanges transpose a 64-by-64 matrix, LSB first in both axes.
#[inline]
fn transpose(m: &mut [u64; 64]) {
    #[inline(always)]
    fn swap<const S: usize>(m: &mut [u64; 64], mask: u64) {
        for rows in m.chunks_exact_mut(2 * S) {
            let (a, b) = rows.split_at_mut(S);
            for (x, y) in a.iter_mut().zip(b) {
                let t = ((*x >> S) ^ *y) & mask;
                *x ^= t << S;
                *y ^= t;
            }
        }
    }
    swap::<1>(m, 0x5555_5555_5555_5555);
    swap::<2>(m, 0x3333_3333_3333_3333);
    swap::<4>(m, 0x0f0f_0f0f_0f0f_0f0f);
    swap::<8>(m, 0x00ff_00ff_00ff_00ff);
    swap::<16>(m, 0x0000_ffff_0000_ffff);
    swap::<32>(m, 0x0000_0000_ffff_ffff);
}

/// In plane z, bit p is party p's share of bit z of the circuit word.
#[derive(Copy, Clone)]
struct Planes([u64; 64]);

impl Planes {
    #[inline]
    fn from_parties(mut words: [u64; PARTIES]) -> Self {
        transpose(&mut words);
        Self(words)
    }
    #[inline]
    fn into_parties(mut self) -> [u64; PARTIES] {
        transpose(&mut self.0);
        self.0
    }
}

impl BitXor for Planes {
    type Output = Self;
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] ^ rhs.0[i]))
    }
}

impl Lane for Planes {
    fn zero() -> Self {
        Self([0; 64])
    }
    fn rotl(mut self, k: u32) -> Self {
        self.0.rotate_right(k as usize);
        self
    }
    fn shl(self, k: u32) -> Self {
        let mut result = Self::zero();
        result.0[k as usize..].copy_from_slice(&self.0[..64 - k as usize]);
        result
    }
    fn shr(self, k: u32) -> Self {
        let mut result = Self::zero();
        result.0[..64 - k as usize].copy_from_slice(&self.0[k as usize..]);
        result
    }
    #[inline(always)]
    fn mask(self, m: u64) -> Self {
        Self(std::array::from_fn(|i| {
            self.0[i] & 0u64.wrapping_sub((m >> i) & 1)
        }))
    }
    fn splat(self, bit: u32) -> Self {
        Self([self.0[bit as usize]; 64])
    }
    fn rev8(self) -> Self {
        Self(std::array::from_fn(|i| self.0[i ^ 7]))
    }
}

/// A masked word and its party shares.
#[derive(Copy, Clone)]
pub(crate) struct Pair {
    public: u64,
    shares: Planes,
}

impl BitXor for Pair {
    type Output = Self;
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self {
        Self {
            public: self.public ^ rhs.public,
            shares: self.shares ^ rhs.shares,
        }
    }
}

impl Lane for Pair {
    #[inline(always)]
    fn zero() -> Self {
        Self {
            public: 0,
            shares: Planes::zero(),
        }
    }
    #[inline(always)]
    fn rotl(self, k: u32) -> Self {
        Self {
            public: self.public.rotl(k),
            shares: self.shares.rotl(k),
        }
    }
    #[inline(always)]
    fn shl(self, k: u32) -> Self {
        Self {
            public: self.public.shl(k),
            shares: self.shares.shl(k),
        }
    }
    #[inline(always)]
    fn shr(self, k: u32) -> Self {
        Self {
            public: self.public.shr(k),
            shares: self.shares.shr(k),
        }
    }
    #[inline(always)]
    fn mask(self, m: u64) -> Self {
        Self {
            public: self.public & m,
            shares: self.shares.mask(m),
        }
    }
    #[inline(always)]
    fn splat(self, bit: u32) -> Self {
        Self {
            public: self.public.splat(bit),
            shares: self.shares.splat(bit),
        }
    }
    #[inline(always)]
    fn rev8(self) -> Self {
        Self {
            public: self.public.rev8(),
            shares: self.shares.rev8(),
        }
    }
}

/// The circuit-writer interface. Product and Keccak outputs are committed, hence affine.
/// A product of two affine words is the only nonlinear operation.
pub(crate) trait Builder {
    type W: Lane;
    /// Little-endian word `word` of the private input, zero past its end.
    fn input(&mut self, word: usize) -> Self::W;
    fn constant(&self, c: u64) -> Self::W;
    /// The committed product `x & y`.
    fn and(&mut self, x: Self::W, y: Self::W) -> Self::W;
    fn assert_zero(&mut self, x: Self::W);
    /// Require `x & y == 0`.
    fn assert_disjoint(&mut self, x: Self::W, y: Self::W);
    /// Keccak-f[1600] with every output lane committed.
    fn permute(&mut self, s: [Self::W; 25]) -> [Self::W; 25];
    /// Keccak-f[1600] committing only the four lanes of a 256-bit squeeze.
    fn squeeze(&mut self, s: [Self::W; 25]) -> [Self::W; 4];
    /// Keccak-f[1600] whose 256-bit squeeze is the public `root`.
    fn squeeze_is(&mut self, s: [Self::W; 25], root: [u64; 4]);
}

/// Primitive operations of one constraint evaluation.
pub(super) trait Gates {
    type W: Lane;
    fn input(&mut self, word: usize) -> Self::W;
    /// The next committed word of the extended witness.
    fn alloc(&mut self) -> Self::W;
    fn constant(&self, c: u64) -> Self::W;
    /// A product of two affine words, as it enters a constraint.
    fn and(&mut self, x: Self::W, y: Self::W) -> Self::W;
    /// A linear term of a constraint.
    fn affine(&self, x: Self::W) -> Self::W;
    /// One constraint word, which must be zero.
    fn emit(&mut self, v: Self::W);
}

pub(super) struct Eval<G>(pub(super) G);

impl<G: Gates> Builder for Eval<G> {
    type W = G::W;
    #[inline(always)]
    fn input(&mut self, word: usize) -> G::W {
        self.0.input(word)
    }
    #[inline(always)]
    fn constant(&self, c: u64) -> G::W {
        self.0.constant(c)
    }
    fn and(&mut self, x: G::W, y: G::W) -> G::W {
        let z = self.0.alloc();
        let product = self.0.and(x, y);
        let linear = self.0.affine(z);
        self.0.emit(product ^ linear);
        z
    }
    fn assert_zero(&mut self, x: G::W) {
        let linear = self.0.affine(x);
        self.0.emit(linear);
    }
    fn assert_disjoint(&mut self, x: G::W, y: G::W) {
        let product = self.0.and(x, y);
        self.0.emit(product);
    }
    fn permute(&mut self, s: [G::W; 25]) -> [G::W; 25] {
        keccak::permute(&mut self.0, s)
    }
    fn squeeze(&mut self, s: [G::W; 25]) -> [G::W; 4] {
        keccak::squeeze(&mut self.0, s, None)
    }
    fn squeeze_is(&mut self, s: [G::W; 25], root: [u64; 4]) {
        keccak::squeeze(&mut self.0, s, Some(root));
    }
}

/// Little-endian word `word` of `bytes`, zero-extended.
pub(super) fn word(bytes: &[u8], word: usize) -> u64 {
    let mut w = [0; 8];
    if let Some(rest) = bytes.get(8 * word..) {
        let n = rest.len().min(8);
        w[..n].copy_from_slice(&rest[..n]);
    }
    u64::from_le_bytes(w)
}

/// The clear evaluation that computes every committed word.
pub(super) struct Trace<'a> {
    input: &'a [u8],
    pub(super) words: Vec<u64>,
}

impl<'a> Trace<'a> {
    pub(super) fn new(input: &'a [u8]) -> Self {
        Self {
            input,
            words: vec![],
        }
    }
}

impl Builder for Trace<'_> {
    type W = u64;
    fn input(&mut self, w: usize) -> u64 {
        word(self.input, w)
    }
    fn constant(&self, c: u64) -> u64 {
        c
    }
    fn and(&mut self, x: u64, y: u64) -> u64 {
        self.words.push(x & y);
        x & y
    }
    fn assert_zero(&mut self, _: u64) {}
    fn assert_disjoint(&mut self, _: u64, _: u64) {}
    fn permute(&mut self, s: [u64; 25]) -> [u64; 25] {
        keccak::trace_permute(s, &mut self.words)
    }
    fn squeeze(&mut self, s: [u64; 25]) -> [u64; 4] {
        keccak::trace_squeeze(s, false, &mut self.words)
    }
    fn squeeze_is(&mut self, s: [u64; 25], _: [u64; 4]) {
        keccak::trace_squeeze(s, true, &mut self.words);
    }
}

/// Counts committed words and constraint words.
#[derive(Default)]
pub(super) struct Count {
    pub(super) words: usize,
    pub(super) checks: usize,
}

impl Gates for Count {
    type W = u64;
    fn input(&mut self, _: usize) -> u64 {
        0
    }
    fn alloc(&mut self) -> u64 {
        self.words += 1;
        0
    }
    fn constant(&self, _: u64) -> u64 {
        0
    }
    fn and(&mut self, _: u64, _: u64) -> u64 {
        0
    }
    fn affine(&self, _: u64) -> u64 {
        0
    }
    fn emit(&mut self, _: u64) {
        self.checks += 1;
    }
}

/// The full residual of an extended witness, clear or masked.
pub(super) struct Check<'a, F> {
    data: &'a [u8],
    input_len: usize,
    next: usize,
    sink: F,
}

impl<'a, F: FnMut(u64)> Check<'a, F> {
    pub(super) fn new(data: &'a [u8], input_len: usize, sink: F) -> Self {
        Self {
            data,
            input_len,
            next: 0,
            sink,
        }
    }
}

impl<F: FnMut(u64)> Gates for Check<'_, F> {
    type W = u64;
    fn input(&mut self, w: usize) -> u64 {
        word(&self.data[..self.input_len], w)
    }
    fn alloc(&mut self) -> u64 {
        let at = self.input_len + 8 * self.next;
        self.next += 1;
        u64::from_le_bytes(self.data[at..at + 8].try_into().unwrap())
    }
    fn constant(&self, c: u64) -> u64 {
        c
    }
    fn and(&mut self, x: u64, y: u64) -> u64 {
        x & y
    }
    fn affine(&self, x: u64) -> u64 {
        x
    }
    fn emit(&mut self, v: u64) {
        (self.sink)(v)
    }
}

/// The homogeneous quadratic part of every constraint, on the aggregate mask.
pub(super) struct Quadratic {
    mask: Aggregate,
    input: Vec<u64>,
    chunk: Vec<u64>,
    at: usize,
    remaining: usize,
    pub(super) hash: Fingerprint,
}

impl Quadratic {
    pub(super) fn new(mask: Aggregate, input_len: usize, words: usize, hash: Fingerprint) -> Self {
        // The input region and the first chunk come from one keystream call per party.
        let mut mask = mask;
        let first = words.min(super::tape::MASK_CHUNK);
        let mut bytes = vec![0; input_len + 8 * first];
        mask.fill(&mut bytes);
        let (input, chunk) = bytes.split_at(input_len);
        Self {
            input: (0..input_len.div_ceil(8)).map(|w| word(input, w)).collect(),
            mask,
            chunk: chunk
                .chunks_exact(8)
                .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
                .collect(),
            at: 0,
            remaining: words - first,
            hash,
        }
    }
}

impl Gates for Quadratic {
    type W = u64;
    fn input(&mut self, w: usize) -> u64 {
        self.input.get(w).copied().unwrap_or(0)
    }
    fn alloc(&mut self) -> u64 {
        if self.at == self.chunk.len() {
            let n = self.remaining.min(super::tape::MASK_CHUNK);
            assert!(n > 0, "read past the extended witness");
            self.remaining -= n;
            let mut buf = [0; 8 * super::tape::MASK_CHUNK];
            let bytes = &mut buf[..8 * n];
            self.mask.fill(bytes);
            self.chunk.clear();
            self.chunk.extend(
                bytes
                    .chunks_exact(8)
                    .map(|b| u64::from_le_bytes(b.try_into().unwrap())),
            );
            self.at = 0;
        }
        self.at += 1;
        self.chunk[self.at - 1]
    }
    fn constant(&self, _: u64) -> u64 {
        0
    }
    fn and(&mut self, x: u64, y: u64) -> u64 {
        x & y
    }
    fn affine(&self, _: u64) -> u64 {
        0
    }
    fn emit(&mut self, v: u64) {
        self.hash.push(v);
    }
}

/// The masked residual and each party's online share of every constraint.
/// The prover reads the clear witness and derives the masked word from all 64 tapes.
/// The verifier reads the masked witness and holds no tape for the hidden party.
pub(super) struct Online<'a> {
    tapes: Tapes,
    data: &'a [u8],
    clear: bool,
    input_len: usize,
    next: usize,
    pub(super) public: Fingerprint,
    pub(super) parties: Vec<Fingerprint>,
}

impl<'a> Online<'a> {
    pub(super) fn new(
        tapes: Tapes,
        data: &'a [u8],
        clear: bool,
        input_len: usize,
        hash: &Fingerprint,
    ) -> Self {
        Self {
            tapes,
            data,
            clear,
            input_len,
            next: 0,
            public: hash.clone(),
            parties: vec![hash.clone(); PARTIES],
        }
    }
    #[inline(always)]
    fn pair(&self, value: u64, words: [u64; PARTIES]) -> Pair {
        Pair {
            public: if self.clear {
                value ^ words.iter().fold(0, |a, b| a ^ b)
            } else {
                value
            },
            shares: Planes::from_parties(words),
        }
    }
}

impl Gates for Online<'_> {
    type W = Pair;
    fn input(&mut self, w: usize) -> Pair {
        let value = word(&self.data[..self.input_len], w);
        self.pair(value, self.tapes.input(w))
    }
    fn alloc(&mut self) -> Pair {
        let at = self.input_len + 8 * self.next;
        self.next += 1;
        let value = u64::from_le_bytes(self.data[at..at + 8].try_into().unwrap());
        let shares = self.tapes.next();
        self.pair(value, shares)
    }
    #[inline(always)]
    fn constant(&self, c: u64) -> Pair {
        Pair {
            public: c,
            shares: Planes::zero(),
        }
    }
    #[inline(always)]
    fn and(&mut self, x: Pair, y: Pair) -> Pair {
        // At public masked operands a, b the party term is a·y_i + b·x_i.
        let (a, b) = (x.public, y.public);
        Pair {
            public: a & b,
            shares: x.shares.mask(b) ^ y.shares.mask(a),
        }
    }
    #[inline(always)]
    fn affine(&self, x: Pair) -> Pair {
        x
    }
    fn emit(&mut self, v: Pair) {
        self.public.push(v.public);
        for (hash, share) in self.parties.iter_mut().zip(v.shares.into_parties()) {
            hash.push(share);
        }
    }
}

/// One party's online share with scalar words, for differential tests against [`Online`].
#[cfg(test)]
pub(super) struct Party<'a> {
    pub(super) operands: std::slice::Iter<'a, (u64, u64)>,
    pub(super) tape: &'a [u8],
    pub(super) input_len: usize,
    pub(super) next: usize,
    pub(super) hash: Fingerprint,
}

#[cfg(test)]
impl Gates for Party<'_> {
    type W = u64;
    fn input(&mut self, w: usize) -> u64 {
        word(&self.tape[..self.input_len], w)
    }
    fn alloc(&mut self) -> u64 {
        let at = self.input_len + 8 * self.next;
        self.next += 1;
        u64::from_le_bytes(self.tape[at..at + 8].try_into().unwrap())
    }
    fn constant(&self, _: u64) -> u64 {
        0
    }
    fn and(&mut self, x: u64, y: u64) -> u64 {
        let &(a, b) = self.operands.next().unwrap();
        (x & b) ^ (y & a)
    }
    fn affine(&self, x: u64) -> u64 {
        x
    }
    fn emit(&mut self, v: u64) {
        self.hash.push(v);
    }
}

/// Records the public operands of every product, for [`Party`].
#[cfg(test)]
pub(super) struct Operands<'a> {
    pub(super) check: Check<'a, fn(u64)>,
    pub(super) seen: Vec<(u64, u64)>,
}

#[cfg(test)]
impl Gates for Operands<'_> {
    type W = u64;
    fn input(&mut self, w: usize) -> u64 {
        self.check.input(w)
    }
    fn alloc(&mut self) -> u64 {
        self.check.alloc()
    }
    fn constant(&self, c: u64) -> u64 {
        c
    }
    fn and(&mut self, x: u64, y: u64) -> u64 {
        self.seen.push((x, y));
        x & y
    }
    fn affine(&self, x: u64) -> u64 {
        x
    }
    fn emit(&mut self, _: u64) {}
}
