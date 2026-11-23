//! Paired Keccak rounds with quadratic constraints on alternate states.
//! For a row z after chi, two hints z0*z2 and z0*z3 + z1*z4
//! suffice to express all five inverse coordinates quadratically.
use super::*;
use std::ops::BitXor;
mod planes;
use polyval::{universal_hash::UniversalHash, Polyval};

const PAIRS: usize = 11;
const CHECKS: usize = PAIRS * 35 + 25 + 4;
pub(super) const CHECK_BYTES: usize = CHECKS * 8;
pub(super) const TRACE_BYTES: usize = (PAIRS * 35 + 25) * 8;

pub(super) struct TraceCircuit<'a> {
    pub(super) st: &'a Statement,
    pub(super) input_len: usize,
    initial: [u64; 25],
}

type State = [u64; 25];
fn chi(b: State) -> State {
    std::array::from_fn(|i| b[i] ^ (!b[i / 5 * 5 + (i + 1) % 5] & b[i / 5 * 5 + (i + 2) % 5]))
}

impl<'a> TraceCircuit<'a> {
    pub(super) fn new(width: usize, st: &'a Statement) -> Result<Self> {
        ensure!((1..=103).contains(&width), "single-block cell width");
        ensure!(
            check_ranges(width, &st.ranges)? == st.projected_bytes.len(),
            "answer length"
        );
        let input_len = width + 32;
        let mut initial = prefix(DOMAIN);
        let mut block = [0; 136];
        block[input_len] ^= 4;
        block[135] ^= 128;
        absorb(&mut initial, &block);
        Ok(Self {
            st,
            input_len,
            initial,
        })
    }
    pub(super) fn len(&self) -> usize {
        self.input_len + TRACE_BYTES
    }

    fn initial(&self, input: &[u8], public: bool) -> State {
        let mut state = if public { self.initial } else { [0; 25] };
        let mut block = [0; 136];
        block[..self.input_len].copy_from_slice(&input[..self.input_len]);
        absorb(&mut state, &block);
        state
    }

    pub(super) fn witness(&self, blind: &Digest, cell: &[u8]) -> Vec<u8> {
        let mut bytes = [blind.as_slice(), cell].concat();
        let mut state = self.initial(&bytes, true);
        for (r, rc) in RC.iter().copied().enumerate().take(23) {
            let z = chi(linear(state));
            state = z;
            state[0] ^= rc;
            if r % 2 == 1 || r == 22 {
                for lane in state {
                    bytes.extend(lane.to_le_bytes());
                }
            }
            if r % 2 == 1 {
                for row in z.chunks_exact(5) {
                    bytes.extend((row[0] & row[2]).to_le_bytes());
                    bytes.extend(((row[0] & row[3]) ^ (row[1] & row[4])).to_le_bytes());
                }
            }
        }
        bytes
    }
}

// The same quadratic equations drive the clear residual F, its homogeneous
// quadratic part Q, and the linear online term F(a+x) + F(a) + Q(x).
// AND operands depend only on the supplied input and alternate round states.
trait Lane: Copy + BitXor<Output = Self> {
    fn constant(x: u64) -> Self;
    fn linear_state(s: [Self; 25]) -> [Self; 25];
}

impl Lane for u64 {
    fn constant(x: u64) -> Self {
        x
    }
    fn linear_state(s: State) -> State {
        linear(s)
    }
}

trait Gates {
    type Word: Lane;
    const PUBLIC: bool = false;
    fn affine(&self, value: Self::Word) -> Self::Word {
        value
    }
    fn and(&mut self, x: Self::Word, y: Self::Word) -> Self::Word;
}
struct Public(Vec<(u64, u64)>);
impl Gates for Public {
    type Word = u64;
    const PUBLIC: bool = true;
    fn and(&mut self, x: u64, y: u64) -> u64 {
        self.0.push((x, y));
        x & y
    }
}
struct Quadratic;
impl Gates for Quadratic {
    type Word = u64;
    fn affine(&self, _: u64) -> u64 {
        0
    }
    fn and(&mut self, x: u64, y: u64) -> u64 {
        x & y
    }
}
#[cfg(test)]
struct Online<'a>(std::slice::Iter<'a, (u64, u64)>);
#[cfg(test)]
impl Gates for Online<'_> {
    type Word = u64;
    fn and(&mut self, x: u64, y: u64) -> u64 {
        let &(a, b) = self.0.next().unwrap();
        (x & b) ^ (y & a)
    }
}

fn forward<G: Gates>(b: &[G::Word; 25], g: &mut G) -> [G::Word; 25] {
    std::array::from_fn(|i| {
        let x = b[i / 5 * 5 + (i + 1) % 5];
        let y = b[i / 5 * 5 + (i + 2) % 5];
        g.affine(b[i])
            ^ g.and(
                if G::PUBLIC {
                    x ^ G::Word::constant(u64::MAX)
                } else {
                    x
                },
                y,
            )
    })
}

// Each pair product is reused in all inverse coordinates that need it.
fn inverse<G: Gates>(
    [a, b, c, d, e]: [G::Word; 5],
    [p, q]: [G::Word; 2],
    g: &mut G,
) -> ([G::Word; 5], [G::Word; 2]) {
    let ab = g.and(a, b);
    let ac = g.and(a, c);
    let ad = g.and(a, d);
    let ae = g.and(a, e);
    let bc = g.and(b, c);
    let bd = g.and(b, d);
    let be = g.and(b, e);
    let cd = g.and(c, d);
    let ce = g.and(c, e);
    let de = g.and(d, e);
    let pd = g.and(p, d);
    (
        [
            g.affine(a ^ c ^ e) ^ bc ^ ad ^ be ^ de ^ g.and(q, d),
            g.affine(a ^ b ^ d) ^ ac ^ cd ^ ae ^ g.and(p, e),
            g.affine(b ^ c ^ e) ^ ab ^ bd ^ be ^ de ^ g.and(q, b),
            g.affine(a ^ c ^ d) ^ bc ^ ae ^ ce ^ pd ^ g.and(q, c),
            g.affine(b ^ d ^ e) ^ ab ^ ad ^ cd ^ pd,
        ],
        [g.affine(p) ^ ac, g.affine(q) ^ ad ^ be],
    )
}

impl TraceCircuit<'_> {
    fn equations<G: Gates>(
        &self,
        mut state: [G::Word; 25],
        mut words: impl Iterator<Item = G::Word>,
        g: &mut G,
        mut emit: impl FnMut(G::Word),
    ) {
        for r in 0..PAIRS {
            let mut first = forward(&G::Word::linear_state(state), g);
            if G::PUBLIC {
                first[0] = first[0] ^ G::Word::constant(RC[2 * r]);
            }
            let before = G::Word::linear_state(first);
            state = std::array::from_fn(|_| words.next().unwrap());
            for row in 0..5 {
                let mut z = std::array::from_fn(|col| state[row * 5 + col]);
                if G::PUBLIC && row == 0 {
                    z[0] = z[0] ^ G::Word::constant(RC[2 * r + 1]);
                }
                let hints = std::array::from_fn(|_| words.next().unwrap());
                let (inv, aux) = inverse(z, hints, g);
                for (col, v) in inv.into_iter().enumerate() {
                    emit(v ^ before[row * 5 + col]);
                }
                for v in aux {
                    emit(v);
                }
            }
        }
        for r in [22, 23] {
            let b = G::Word::linear_state(state);
            // Only the first four coordinates of the final chi row are public.
            let mut out = forward(&b, g);
            if G::PUBLIC {
                out[0] = out[0] ^ G::Word::constant(RC[r]);
            }
            if r == 22 {
                state = std::array::from_fn(|_| words.next().unwrap());
                for (a, b) in out.into_iter().zip(state) {
                    emit(a ^ g.affine(b));
                }
            } else {
                for (v, chunk) in out.into_iter().zip(self.st.cell_root.chunks_exact(8)) {
                    let root = if G::PUBLIC {
                        u64::from_le_bytes(chunk.try_into().unwrap())
                    } else {
                        0
                    };
                    emit(v ^ G::Word::constant(root));
                }
            }
        }
    }
    fn residual<G: Gates<Word = u64>>(&self, data: &[u8], g: &mut G) -> Vec<u8> {
        let words = data[self.input_len..]
            .chunks_exact(8)
            .map(|w| u64::from_le_bytes(w.try_into().unwrap()));
        let mut checks = Vec::with_capacity(CHECK_BYTES + self.st.projected_bytes.len());
        self.equations(self.initial(data, G::PUBLIC), words, g, |v| {
            checks.extend(v.to_le_bytes())
        });
        for (&expected, byte) in self
            .st
            .projected_bytes
            .iter()
            .zip(project(&data[32..self.input_len], &self.st.ranges))
        {
            checks.push(g.affine(byte as u64) as u8 ^ if G::PUBLIC { expected } else { 0 });
        }
        checks
    }
    pub(super) fn masked(&self, data: &[u8]) -> Masked {
        let mut g = Public(Vec::with_capacity(1200));
        let residual = self.residual(data, &mut g);
        Masked {
            wires: g.0,
            residual,
        }
    }
    pub(super) fn products(&self, data: &[u8], batch: &Batch) -> Digest {
        batch.hash(&self.residual(data, &mut Quadratic))
    }
    #[cfg(test)]
    pub(super) fn message(
        &self,
        data: &[u8],
        masked: &Masked,
        batch: &Batch,
        pad: &Digest,
    ) -> Digest {
        let mut d = batch.hash(&self.residual(data, &mut Online(masked.wires.iter())));
        xor(&mut d, pad);
        d
    }
}
pub(super) struct Masked {
    wires: Vec<(u64, u64)>,
    pub(super) residual: Vec<u8>,
}

#[cfg(test)]
#[test]
fn every_party_matches_scalar_polarization() -> Result<()> {
    let blind = [17; 32];
    let batch = Batch::new(&[33; 32], &[42; 32]);
    for width in [1, 64, 103] {
        let cell = vec![0xa3; width];
        let st = statement(&blind, &cell, vec![(0, width as u16)])?;
        let circuit = TraceCircuit::new(width, &st)?;
        let mut tapes = vec![0; PARTIES * circuit.len()];
        stream(b"party transpose test", &[&blind]).read(&mut tapes);
        let masked = circuit.masked(&tapes[..circuit.len()]);
        let pads = [[0x5c; 32]; PARTIES];
        let msgs = circuit.party_messages(&tapes, &masked, &batch, &pads);
        for (p, tape) in tapes.chunks_exact(circuit.len()).enumerate() {
            assert_eq!(
                msgs[p],
                circuit.message(tape, &masked, &batch, &pads[p]),
                "party {p}"
            );
        }
    }
    Ok(())
}

#[cfg(test)]
#[test]
fn all_inverse_rows_and_hints() {
    for x in 0..32 {
        let row: [u64; 5] = std::array::from_fn(|i| ((x >> i) & 1) as u64);
        let z = std::array::from_fn(|i| row[i] ^ (!row[(i + 1) % 5] & row[(i + 2) % 5]));
        let p = z[0] & z[2];
        let q = (z[0] & z[3]) ^ (z[1] & z[4]);
        for h in 0..4 {
            let (decoded, flags) = inverse(z, [h & 1, h >> 1], &mut Public(vec![]));
            assert_eq!(flags == [0, 0], h == p + 2 * q);
            if flags == [0, 0] {
                assert_eq!(decoded, row);
            }
        }
    }
}
/// Two independent POLYVAL evaluations. The checked byte length is fixed by
/// the verifier. Each component has collision probability at most L / 2^128
/// for L blocks, even if a root is zero.
pub(super) struct Batch([Polyval; 2]);
impl Batch {
    pub fn new(ctx: &Digest, root: &Digest) -> Self {
        let keys = digest(b"selective opening quadratic batch", &[ctx, root]);
        Self(std::array::from_fn(|i| {
            Polyval::new(keys[i * 16..][..16].try_into().unwrap())
        }))
    }
    pub fn hash(&self, bytes: &[u8]) -> Digest {
        let mut d = [0; 32];
        for (out, mut hash) in d.chunks_exact_mut(16).zip(self.0.clone()) {
            hash.update_padded(bytes);
            out.copy_from_slice(&hash.finalize());
        }
        d
    }
}
