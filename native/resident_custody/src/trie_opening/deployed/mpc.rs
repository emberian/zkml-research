//! The private OpeningRel circuit. The public plan fixes every hash call, so the witness
//! layout and the proof length depend only on public shape.
//!
//! Private input, in 64-bit words: the custody secret and the inner digest (four words
//! each), then per reader prefix of `n` bits, in order: for an empty answer a terminal flag
//! word, the private singleton's 65-byte path in nine words and its content digest; for at
//! most one member, the walk bits packed little-endian (bit i is depth i); and `n` sibling
//! digests, root first.
use super::Plan;
use crate::cshake_selective_open::circuit::{absorb, lanes, Piece};
use crate::kkw::{Builder, Circuit, Lane};
use crate::trie_opening::{NODE_HASH_DOMAIN, OUTER_HASH_DOMAIN};
use anyhow::Result;

pub(super) const PATH_WORDS: usize = 9;

/// Input words of one reader prefix.
pub(super) fn job_words(prefix: usize, count: usize) -> usize {
    let mut w = 4 * prefix;
    if count == 0 {
        w += 1 + PATH_WORDS + 4;
    }
    if count <= 1 {
        w += prefix.div_ceil(64);
    }
    w
}

/// The bits of word `k` that are below `n`.
fn valid(n: usize, k: usize) -> u64 {
    match n.saturating_sub(64 * k) {
        0 => 0,
        r if r >= 64 => u64::MAX,
        r => (1 << r) - 1,
    }
}

fn bits(prefix: &[bool], k: usize) -> u64 {
    prefix
        .iter()
        .skip(64 * k)
        .take(64)
        .enumerate()
        .fold(0, |w, (i, &b)| w | u64::from(b) << i)
}

struct Reader(usize);
impl Reader {
    fn take<B: Builder>(&mut self, b: &mut B, n: usize) -> Vec<B::W> {
        let v = (self.0..self.0 + n).map(|w| b.input(w)).collect();
        self.0 += n;
        v
    }
    fn digest<B: Builder>(&mut self, b: &mut B) -> [B::W; 4] {
        self.take(b, 4).try_into().ok().unwrap()
    }
}

/// `flag` selects `yes` over `no` in every bit position where it is set.
fn select<B: Builder>(b: &mut B, flag: B::W, yes: [B::W; 4], no: [B::W; 4]) -> [B::W; 4] {
    let mut out = no;
    for (o, (y, n)) in out.iter_mut().zip(yes.into_iter().zip(no)) {
        *o = n ^ b.and(flag, y ^ n);
    }
    out
}

fn node<B: Builder>(
    b: &mut B,
    tag: u8,
    left: &[B::W],
    left_len: usize,
    right: &[B::W],
) -> [B::W; 4] {
    let s = absorb(
        b,
        NODE_HASH_DOMAIN,
        &[
            Piece::Public(&[tag]),
            Piece::Words(left, left_len),
            Piece::Words(right, 32),
        ],
    );
    b.squeeze(s)
}

impl Circuit for Plan {
    const LABEL: &'static [u8] = b"private framed OpeningRel";
    fn input_len(&self) -> usize {
        self.len
    }
    fn statement(&self) -> Result<Vec<u8>> {
        Ok(self.statement.clone())
    }
    fn run<B: Builder>(&self, b: &mut B) {
        let mut r = Reader(0);
        let secret = r.digest(b);
        let inner = r.digest(b);
        let outer = absorb(
            b,
            OUTER_HASH_DOMAIN,
            &[
                Piece::Public(&self.frame),
                Piece::Words(&secret, 32),
                Piece::Words(&inner, 32),
            ],
        );
        b.squeeze_is(outer, lanes(&self.root));
        for job in &self.jobs {
            let n = job.prefix.len();
            let m = n.div_ceil(64);
            let mut h = lanes(&job.below).map(|x| b.constant(x));
            let terminal = (job.count == 0).then(|| {
                let t = r.take(b, 1)[0].mask(1);
                let path = r.take(b, PATH_WORDS);
                let content = r.digest(b);
                // The leaf hash reads the canonical path: its last nibble is zero.
                let mut canonical = path.clone();
                canonical[8] = canonical[8].mask(0xf0);
                let leaf = node(b, 0, &canonical, 65, &content);
                h = select(b, t.splat(0), leaf, h);
                (t, path)
            });
            let walk: Vec<B::W> = if job.count <= 1 {
                let w = r.take(b, m);
                w.into_iter()
                    .enumerate()
                    .map(|(k, x)| x.mask(valid(n, k)))
                    .collect()
            } else {
                vec![]
            };
            if job.count <= 1 {
                // The walk is an initial run of ones. Its length stays private.
                for k in 0..m {
                    let carry = if k == 0 {
                        b.constant(1)
                    } else {
                        walk[k - 1].shr(63)
                    };
                    let not_prev = walk[k].shl(1) ^ carry ^ b.constant(u64::MAX);
                    b.assert_disjoint(walk[k], not_prev);
                }
            }
            if let Some((t, path)) = terminal {
                // A private singleton may stop above an empty requested prefix only if its
                // path matches every walked bit and leaves the prefix somewhere.
                let spread = t.splat(0);
                let mut same_all: Option<B::W> = None;
                for k in 0..m {
                    let prefix_bits = b.constant(bits(&job.prefix, k));
                    let diff = (path[k].rev8() ^ prefix_bits).mask(valid(n, k));
                    let live = b.and(walk[k], spread);
                    b.assert_disjoint(live, diff);
                    // Positions past the prefix count as matching.
                    let same = diff ^ b.constant(u64::MAX);
                    same_all = Some(match same_all {
                        None => same,
                        Some(acc) => b.and(acc, same),
                    });
                }
                let matches = match same_all {
                    None => b.constant(1),
                    Some(mut acc) => {
                        for s in [32, 16, 8, 4, 2, 1] {
                            let shifted = acc.shr(s);
                            acc = b.and(acc, shifted);
                        }
                        acc.mask(1)
                    }
                };
                b.assert_disjoint(t, matches);
            }
            let siblings: Vec<[B::W; 4]> = (0..n).map(|_| r.digest(b)).collect();
            for i in (0..n).rev() {
                let s = siblings[i];
                let (left, right) = if job.prefix[i] { (s, h) } else { (h, s) };
                let parent = node(b, 1, &left, 32, &right);
                h = if job.count <= 1 {
                    let active = walk[i / 64].splat((i % 64) as u32);
                    select(b, active, parent, h)
                } else {
                    parent
                };
            }
            for (x, y) in h.into_iter().zip(inner) {
                b.assert_zero(x ^ y);
            }
        }
        debug_assert_eq!(8 * r.0, self.len);
    }
}
