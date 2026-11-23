//! Extended witness: one packed χ result per lane of the first 23 rounds.
//! The final four χ results are determined by the public digest and linear wires.
use super::*;
use crate::cshake_selective_open::{absorb, linear, prefix, project, DOMAIN, RC};
use polyval::{universal_hash::UniversalHash, Polyval};

const PRIVATE_LANES: usize = 23 * 25;
const CHECKS: usize = PRIVATE_LANES + 4;
pub(super) const TRACE_BYTES: usize = PRIVATE_LANES * 8;

pub(super) struct Circuit<'a> {
    pub st: &'a Statement,
    pub input_len: usize,
    initial: [u64; 25],
}

impl<'a> Circuit<'a> {
    pub fn new(width: usize, st: &'a Statement) -> Result<Self> {
        ensure!((1..=103).contains(&width), "single-block cell width");
        ensure!(
            check_ranges(width, &st.ranges)? == st.projected_bytes.len(),
            "answer length"
        );
        Ok(Self {
            st,
            input_len: 32 + width,
            initial: prefix(DOMAIN),
        })
    }

    pub fn len(&self) -> usize {
        self.input_len + TRACE_BYTES
    }

    fn walk<const PUBLIC: bool>(
        &self,
        input: &[u8],
        mut gate: impl FnMut(usize, u64, u64, Option<u64>) -> u64,
    ) {
        let mut block = [0u8; 136];
        block[..self.input_len].copy_from_slice(input);
        let mut state = if PUBLIC {
            block[self.input_len] ^= 4;
            block[135] ^= 128;
            self.initial
        } else {
            [0; 25]
        };
        absorb(&mut state, &block);
        for (r, &rc) in RC.iter().enumerate() {
            let b = linear(state);
            let last = r == 23;
            for i in 0..if last { 4 } else { 25 } {
                let j = i / 5 * 5 + (i + 1) % 5;
                let k = i / 5 * 5 + (i + 2) % 5;
                let x = if PUBLIC { !b[j] } else { b[j] };
                let fixed = last.then(|| {
                    let output = if PUBLIC {
                        word(&self.st.cell_root, i) ^ if i == 0 { rc } else { 0 }
                    } else {
                        0
                    };
                    b[i] ^ output
                });
                state[i] = b[i] ^ gate(r * 25 + i, x, b[k], fixed);
            }
            if PUBLIC {
                state[0] ^= rc;
            }
        }
    }

    pub fn witness(&self, blind: &Digest, cell: &[u8]) -> Vec<u8> {
        let input = [blind.as_slice(), cell].concat();
        let mut bytes = input.clone();
        self.walk::<true>(&input, |_, x, y, fixed| {
            let z = x & y;
            if fixed.is_none() {
                bytes.extend(z.to_le_bytes());
            }
            z
        });
        bytes
    }

    fn wires<const PUBLIC: bool>(&self, data: &[u8], mut visit: impl FnMut(usize, u64, u64, u64)) {
        let (input, trace) = data.split_at(self.input_len);
        self.walk::<PUBLIC>(input, |i, x, y, fixed| {
            let z = fixed.unwrap_or_else(|| word(trace, i));
            visit(i, x, y, z);
            z
        });
    }

    pub fn masked(&self, data: &[u8]) -> Masked {
        let mut wires = Vec::with_capacity(CHECKS);
        let mut residual = Vec::with_capacity(CHECKS * 8 + self.st.projected_bytes.len());
        self.wires::<true>(data, |_, x, y, z| {
            wires.push((x, y));
            residual.extend(((x & y) ^ z).to_le_bytes());
        });
        let mut answer = project(&data[32..self.input_len], &self.st.ranges);
        xor(&mut answer, &self.st.projected_bytes);
        residual.extend(answer);
        Masked { wires, residual }
    }

    pub fn products(&self, mask: &[u8], batch: &Batch) -> Digest {
        let mut bytes = Vec::with_capacity(CHECKS * 8 + self.st.projected_bytes.len());
        self.wires::<false>(mask, |_, x, y, _| bytes.extend((x & y).to_le_bytes()));
        bytes.resize(CHECKS * 8 + self.st.projected_bytes.len(), 0);
        batch.hash(&bytes)
    }

    pub fn message(&self, mask: &[u8], masked: &Masked, batch: &Batch, pad: &Digest) -> Digest {
        let mut bytes = Vec::with_capacity(CHECKS * 8 + self.st.projected_bytes.len());
        self.wires::<false>(mask, |i, x, y, z| {
            let (a, b) = masked.wires[i];
            bytes.extend(((a & y) ^ (b & x) ^ z).to_le_bytes());
        });
        bytes.extend(project(&mask[32..self.input_len], &self.st.ranges));
        let mut d = batch.hash(&bytes);
        xor(&mut d, pad);
        d
    }
}

pub(super) struct Masked {
    wires: Vec<(u64, u64)>,
    pub residual: Vec<u8>,
}

fn word(bytes: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap())
}

/// Two independent POLYVAL evaluations. The checked byte length is fixed by
/// the verifier. Each component has collision probability at most L / 2^128
/// for L blocks, even if a root is zero.
pub(super) struct Batch([Polyval; 2]);
impl Batch {
    pub fn new(ctx: &Digest, root: &Digest) -> Self {
        let keys = digest(b"W13 quadratic batch", &[ctx, root]);
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
