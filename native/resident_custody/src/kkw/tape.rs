//! Party tapes, generated in order. Each tape is the AES-128-CTR keystream under its party's
//! key, as long as the extended witness. Nothing here holds a whole tape: the input region is
//! materialized once and committed words arrive in chunks.
use super::gates::word;
use super::PARTIES;
use aes::cipher::{KeyIvInit, StreamCipher};

pub(super) type Cipher = ctr::Ctr64BE<aes::Aes128Enc>;
/// Words per refill of the party shares: 32 KiB.
pub(super) const CHUNK: usize = 64;
/// Words per refill of the aggregate mask.
pub(super) const MASK_CHUNK: usize = 512;

pub(super) fn cipher(key: &[u8; 16]) -> Cipher {
    Cipher::new(key.into(), &[0; 16].into())
}

fn keystream(c: &mut Cipher, out: &mut [u8]) {
    out.fill(0);
    c.apply_keystream(out);
}

/// The XOR of every party's tape.
pub(super) struct Aggregate(Vec<Cipher>);

impl Aggregate {
    pub(super) fn new(ciphers: Vec<Cipher>) -> Self {
        Self(ciphers)
    }
    /// Overwrite `out` with the next `out.len()` bytes of the aggregate mask. CTR mode XORs
    /// each party's keystream in place.
    pub(super) fn fill(&mut self, out: &mut [u8]) {
        out.fill(0);
        for c in &mut self.0 {
            c.apply_keystream(out);
        }
    }
}

/// Every party's tape as one word per party. A missing party contributes zero.
pub(super) struct Tapes {
    ciphers: Vec<Option<Cipher>>,
    input: Vec<[u64; PARTIES]>,
    chunk: Vec<[u64; PARTIES]>,
    at: usize,
    /// Committed words not yet generated.
    remaining: usize,
}

impl Tapes {
    pub(super) fn new(mut ciphers: Vec<Option<Cipher>>, input_len: usize, words: usize) -> Self {
        assert_eq!(ciphers.len(), PARTIES);
        let mut input = vec![[0; PARTIES]; input_len.div_ceil(8)];
        let mut bytes = vec![0; input_len];
        for (p, c) in ciphers.iter_mut().enumerate() {
            if let Some(c) = c {
                keystream(c, &mut bytes);
                for (w, slot) in input.iter_mut().enumerate() {
                    slot[p] = word(&bytes, w);
                }
            }
        }
        Self {
            ciphers,
            input,
            chunk: vec![],
            at: 0,
            remaining: words,
        }
    }
    pub(super) fn input(&self, w: usize) -> [u64; PARTIES] {
        self.input.get(w).copied().unwrap_or([0; PARTIES])
    }
    pub(super) fn next(&mut self) -> [u64; PARTIES] {
        if self.at == self.chunk.len() {
            self.refill();
        }
        self.at += 1;
        self.chunk[self.at - 1]
    }
    fn refill(&mut self) {
        let n = self.remaining.min(CHUNK);
        assert!(n > 0, "read past the extended witness");
        self.remaining -= n;
        let mut buf = [0; 8 * CHUNK];
        let bytes = &mut buf[..8 * n];
        self.chunk.clear();
        self.chunk.resize(n, [0; PARTIES]);
        for (p, c) in self.ciphers.iter_mut().enumerate() {
            if let Some(c) = c {
                keystream(c, bytes);
                for (slot, w) in self.chunk.iter_mut().zip(bytes.chunks_exact(8)) {
                    slot[p] = u64::from_le_bytes(w.try_into().unwrap());
                }
            }
        }
        self.at = 0;
    }
}
