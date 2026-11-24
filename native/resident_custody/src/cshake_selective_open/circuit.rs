//! cSHAKE256 of public and private byte strings, as constraints, and the resident cell opening.
//!
//! [`absorb`] pads the concatenation of its pieces under SP 800-185 and returns the state the
//! final permutation reads. Blocks that hold only public bytes are absorbed in the clear.
//! Private pieces are word sequences with a byte length; each rate lane gathers its bytes by
//! public shifts and masks, so a piece may start at any byte offset.
use super::framed::{absorb as absorb_clear, check_ranges, prefix, Circuit, Statement};
use crate::kkw::{self, Builder, Lane};
use anyhow::{ensure, Result};
use std::collections::BTreeMap;

const RATE: usize = 136;

pub(crate) enum Piece<'a, W> {
    Public(&'a [u8]),
    /// Little-endian words; bytes at or past the length are ignored.
    Words(&'a [W], usize),
}

impl<W> Piece<'_, W> {
    fn len(&self) -> usize {
        match self {
            Piece::Public(b) => b.len(),
            Piece::Words(_, n) => *n,
        }
    }
}

/// Bytes `[lo, hi)` of a 64-bit word.
fn bytes_mask(lo: usize, hi: usize) -> u64 {
    (lo..hi).fold(0, |m, j| m | 0xff << (8 * j))
}

/// The private bytes of message lane `k`.
fn private_lane<W: Lane>(pieces: &[Piece<'_, W>], k: usize) -> W {
    let mut lane = W::zero();
    let mut at = 0;
    for p in pieces {
        if let Piece::Words(words, len) = p {
            let lo = (8 * k).max(at);
            let hi = (8 * k + 8).min(at + len);
            if lo < hi {
                let word = |q: usize| words.get(q).copied().unwrap_or(W::zero());
                // Piece byte `t` sits at lane byte 0.
                let part = match (8 * k).checked_sub(at) {
                    Some(t) => {
                        let (q, r) = (t / 8, (t % 8) as u32);
                        if r == 0 {
                            word(q)
                        } else {
                            word(q).shr(8 * r) ^ word(q + 1).shl(64 - 8 * r)
                        }
                    }
                    None => word(0).shl(8 * (at - 8 * k) as u32),
                };
                lane = lane ^ part.mask(bytes_mask(lo - 8 * k, hi - 8 * k));
            }
        }
        at += p.len();
    }
    lane
}

/// Pad `pieces` under cSHAKE256 with customization `domain` and absorb every block, permuting
/// between blocks. The caller squeezes the returned state.
pub(crate) fn absorb<B: Builder>(
    b: &mut B,
    domain: &[u8],
    pieces: &[Piece<'_, B::W>],
) -> [B::W; 25] {
    let total: usize = pieces.iter().map(Piece::len).sum();
    let blocks = total / RATE + 1;
    let mut public = vec![0; blocks * RATE];
    let mut first_private = total;
    let mut at = 0;
    for p in pieces {
        match p {
            Piece::Public(bytes) => public[at..at + bytes.len()].copy_from_slice(bytes),
            Piece::Words(..) => first_private = first_private.min(at),
        }
        at += p.len();
    }
    public[total] ^= 0x04;
    *public.last_mut().unwrap() ^= 0x80;
    let start = (first_private / RATE).min(blocks - 1);
    let mut clear = prefix(domain);
    for block in public.chunks_exact(RATE).take(start) {
        absorb_clear(&mut clear, block);
        keccak::f1600(&mut clear);
    }
    let mut s = clear.map(|x| b.constant(x));
    for block in start..blocks {
        for (i, lane) in s.iter_mut().take(RATE / 8).enumerate() {
            let k = block * (RATE / 8) + i;
            let c = u64::from_le_bytes(public[8 * k..8 * k + 8].try_into().unwrap());
            *lane = *lane ^ b.constant(c) ^ private_lane(pieces, k);
        }
        if block + 1 < blocks {
            s = b.permute(s);
        }
    }
    s
}

/// The little-endian lanes of a digest.
pub(crate) fn lanes(d: &[u8; 32]) -> [u64; 4] {
    std::array::from_fn(|i| u64::from_le_bytes(d[8 * i..8 * i + 8].try_into().unwrap()))
}

/// A framed cell under its statement: cSHAKE256(domain, frame ‖ blind ‖ cell) is the cell
/// root, and the authorized ranges of the cell are the projected bytes.
pub(crate) struct Cell<'a> {
    framed: &'a Circuit,
    st: &'a Statement,
    /// Input word to (mask, expected value) for every word a range touches.
    projection: BTreeMap<usize, (u64, u64)>,
}

impl<'a> Cell<'a> {
    pub(crate) fn new(framed: &'a Circuit, st: &'a Statement) -> Result<Self> {
        ensure!(
            check_ranges(framed.width, &st.ranges)? == st.projected_bytes.len(),
            "answer length"
        );
        let mut projection = BTreeMap::<usize, (u64, u64)>::new();
        let positions = st
            .ranges
            .iter()
            .flat_map(|&(a, b)| usize::from(a)..usize::from(b));
        for (i, &byte) in positions.zip(&st.projected_bytes) {
            let at = 32 + i;
            let e = projection.entry(at / 8).or_default();
            e.0 |= 0xff << (8 * (at % 8));
            e.1 |= u64::from(byte) << (8 * (at % 8));
        }
        Ok(Self {
            framed,
            st,
            projection,
        })
    }
}

impl kkw::Circuit for Cell<'_> {
    const LABEL: &'static [u8] = b"framed cSHAKE256 cell opening";
    fn input_len(&self) -> usize {
        32 + self.framed.width
    }
    fn statement(&self) -> Result<Vec<u8>> {
        Ok(bincode::serialize(&(
            self.framed.domain,
            &self.framed.frame,
            self.framed.width as u64,
            self.st,
        ))?)
    }
    fn run<B: Builder>(&self, b: &mut B) {
        let n = self.input_len();
        let words: Vec<B::W> = (0..n.div_ceil(8)).map(|w| b.input(w)).collect();
        let s = absorb(
            b,
            self.framed.domain,
            &[Piece::Public(&self.framed.frame), Piece::Words(&words, n)],
        );
        b.squeeze_is(s, lanes(&self.st.cell_root));
        for (&w, &(mask, expected)) in &self.projection {
            let e = b.constant(expected);
            b.assert_zero(words[w].mask(mask) ^ e);
        }
    }
}
