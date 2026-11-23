//! A three-view ZKBoo Boolean circuit. The fixed public cell width is a circuit
//! parameter. Coordinates are half-open byte intervals. Only χ consumes tape.
use crate::{digest, random_seed, stream, transcript, Digest};
use anyhow::{ensure, Context, Result};
use serde::{Deserialize, Serialize};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{CShake256, CShake256Core, Shake256};

pub const REPETITIONS: usize = 219;
pub const DOMAIN: &[u8] = b"resident-custody/blinded-cell/v1";
const RATE: usize = 136;
const GATES: usize = 24 * 25;
const LEAVES: usize = 3 * REPETITIONS;
const TREE: usize = LEAVES.next_power_of_two();

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Statement {
    pub cell_root: Digest,
    pub ranges: Vec<(u16, u16)>,
    pub projected_bytes: Vec<u8>,
}

pub fn root(blind: &Digest, cell: &[u8]) -> Digest {
    Circuit::resident(cell.len()).root(blind, cell)
}

fn encode_nat(mut n: u64) -> Vec<u8> {
    let mut bytes = vec![];
    while n > 0 {
        bytes.push((n % 255) as u8);
        n /= 255;
    }
    bytes.push(255);
    bytes
}

/// The outer circuit constructs PrivateCellOpening.outerFrame from the
/// caller-selected layout digest, cell identity and version. Its private
/// suffix is the 32-byte custody secret and the 32-byte index digest.
pub struct Circuit {
    domain: &'static [u8],
    frame: Vec<u8>,
    width: usize,
}
impl Circuit {
    pub fn resident(width: usize) -> Self {
        Self {
            domain: DOMAIN,
            frame: Vec::new(),
            width,
        }
    }
    pub fn private_cell_outer(layout: &Digest, cell_id: &[u8], version: u64) -> Result<Self> {
        ensure!(cell_id.len() <= 4000, "cell identity too large");
        let mut wire = b"DREGG/STORE".to_vec();
        wire.push(3);
        wire.extend(layout);
        let mut ctx = encode_nat(1);
        ctx.extend(encode_nat(wire.len() as u64));
        ctx.extend(wire);
        let mut custody = encode_nat(cell_id.len() as u64);
        custody.extend(cell_id);
        custody.extend(encode_nat(version));
        let mut frame = encode_nat(ctx.len() as u64);
        frame.extend(ctx);
        frame.extend(encode_nat((custody.len() + 32) as u64));
        frame.extend(custody);
        Ok(Self {
            domain: b"DREGG/PRIVATE-CELL/OUTER/v2",
            frame,
            width: 32,
        })
    }
    pub fn root(&self, blind: &Digest, cell: &[u8]) -> Digest {
        let mut h = CShake256::from_core(CShake256Core::new(self.domain));
        h.update(&self.frame);
        h.update(blind);
        h.update(cell);
        let mut out = [0; 32];
        h.finalize_xof().read(&mut out);
        out
    }
}

pub fn check_ranges(width: usize, ranges: &[(u16, u16)]) -> Result<usize> {
    ensure!((1..=4096).contains(&width), "cell width");
    let mut end = 0;
    let mut size = 0;
    for &(a, b) in ranges {
        ensure!(
            end <= a && a < b && usize::from(b) <= width,
            "invalid slice"
        );
        end = b;
        size += usize::from(b - a);
    }
    Ok(size)
}

fn project(cell: &[u8], ranges: &[(u16, u16)]) -> Vec<u8> {
    ranges
        .iter()
        .flat_map(|&(a, b)| cell[usize::from(a)..usize::from(b)].iter().copied())
        .collect()
}

pub fn statement(blind: &Digest, cell: &[u8], ranges: Vec<(u16, u16)>) -> Result<Statement> {
    check_ranges(cell.len(), &ranges)?;
    Ok(Statement {
        cell_root: root(blind, cell),
        projected_bytes: project(cell, &ranges),
        ranges,
    })
}

// SP 800-185 bytepad(encode_string("") || encode_string(DOMAIN), 136).
// This whole first absorb is public and can be evaluated once in the clear.
fn prefix(domain: &[u8]) -> [u64; 25] {
    let mut block = [0u8; RATE];
    let bits = u16::try_from(domain.len() * 8).unwrap();
    let mut encoded = vec![1, 136, 1, 0];
    if bits <= 255 {
        encoded.extend([1, bits as u8]);
    } else {
        encoded.push(2);
        encoded.extend(bits.to_be_bytes());
    }
    encoded.extend(domain);
    block[..encoded.len()].copy_from_slice(&encoded);
    let mut s = [0; 25];
    absorb(&mut s, &block);
    keccak::f1600(&mut s);
    s
}

fn absorb(s: &mut [u64; 25], block: &[u8]) {
    for (w, b) in s.iter_mut().zip(block.chunks_exact(8)) {
        *w ^= u64::from_le_bytes(b.try_into().unwrap());
    }
}

// FIPS 202, lane x+5y, bit z stored in bit z of the u64.
const ROT: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];
const RC: [u64; 24] = [
    0x1,
    0x8082,
    0x800000000000808a,
    0x8000000080008000,
    0x808b,
    0x80000001,
    0x8000000080008081,
    0x8000000000008009,
    0x8a,
    0x88,
    0x80008009,
    0x8000000a,
    0x8000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x80000001,
    0x8000000080008008,
];

fn linear(s: [u64; 25]) -> [u64; 25] {
    let parity: [u64; 5] =
        std::array::from_fn(|x| s[x] ^ s[x + 5] ^ s[x + 10] ^ s[x + 15] ^ s[x + 20]);
    let mut b = [0; 25];
    for y in 0..5 {
        for x in 0..5 {
            let d = parity[(x + 4) % 5] ^ parity[(x + 1) % 5].rotate_left(1);
            b[y + 5 * ((2 * x + 3 * y) % 5)] = (s[x + 5 * y] ^ d).rotate_left(ROT[x + 5 * y]);
        }
    }
    b
}

struct View {
    seed: Digest,
    input: Vec<u8>,
    masks: Vec<u64>,
    gates: Vec<u8>,
    output: Vec<u8>,
}
impl View {
    fn new(seed: Digest, len: usize, frame_len: usize) -> Self {
        let mut input = vec![0; len];
        let mut tape = stream(b"private tape", &[&seed]);
        tape.read(&mut input);
        let mut bytes = vec![0; ((len + frame_len) / RATE + 1) * GATES * 8];
        tape.read(&mut bytes);
        let masks = bytes
            .chunks_exact(8)
            .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
            .collect();
        Self {
            seed,
            input,
            masks,
            gates: Vec::with_capacity(bytes.len()),
            output: vec![],
        }
    }
    fn commit(&self) -> Digest {
        digest(
            b"party view",
            &[&self.seed, &self.input, &self.gates, &self.output],
        )
    }
}

fn xor(dst: &mut [u8], src: &[u8]) {
    debug_assert_eq!(dst.len(), src.len());
    for (d, s) in dst.iter_mut().zip(src) {
        *d ^= s;
    }
}

// For an opened adjacent pair, the neighbor's AND messages come from
// the proof. Every gate of the first view is independently recomputed.
fn evaluate<const N: usize>(
    views: &mut [View; N],
    ranges: &[(u16, u16)],
    circuit: &Circuit,
    neighbor: Option<&[u8]>,
) {
    let mut states = [prefix(circuit.domain); N];
    let inputs = views.each_ref().map(|v| {
        let mut raw = v.input.clone();
        crate::trace_pack::decode(&mut raw);
        [circuit.frame.as_slice(), raw.as_slice()].concat()
    });
    let len = inputs[0].len();
    let mut gate = 0;
    for block in 0..=len / RATE {
        for (state, input) in states.iter_mut().zip(&inputs) {
            let mut bytes = [0; RATE];
            let rem = &input[block * RATE..];
            let n = rem.len().min(RATE);
            bytes[..n].copy_from_slice(&rem[..n]);
            if n < RATE {
                bytes[n] ^= 0x04;
                bytes[RATE - 1] ^= 0x80;
            }
            absorb(state, &bytes);
        }
        for rc in RC {
            let b = states.map(linear);
            for i in 0..25 {
                let row = i / 5 * 5;
                let j = row + (i + 1) % 5;
                let k = row + (i + 2) % 5;
                for p in 0..N {
                    let q = (p + 1) % N;
                    let z = if let Some(trace) = neighbor.filter(|_| p + 1 == N) {
                        u64::from_le_bytes(trace[gate * 8..gate * 8 + 8].try_into().unwrap())
                    } else {
                        // For XOR shares x, y: z_p = x_p y_p + x_p y_q
                        // + x_q y_p + r_p + r_q, where q=p+1 modulo 3.
                        (!b[p][j] & b[p][k])
                            ^ (!b[p][j] & b[q][k])
                            ^ (!b[q][j] & b[p][k])
                            ^ views[p].masks[gate]
                            ^ views[q].masks[gate]
                    };
                    states[p][i] = b[p][i] ^ z;
                    views[p].gates.extend(z.to_le_bytes());
                }
                gate += 1;
            }
            for state in &mut states {
                state[0] ^= rc;
            }
        }
    }
    for ((state, v), input) in states.iter().zip(views.iter_mut()).zip(&inputs) {
        for lane in &state[..4] {
            v.output.extend(lane.to_le_bytes());
        }
        v.output
            .extend(project(&input[circuit.frame.len() + 32..], ranges));
    }
}

fn seed_children(seed: &Digest) -> [Digest; 2] {
    let mut children = [[0; 32]; 2];
    let mut r = stream(b"GGM children", &[seed]);
    for child in &mut children {
        r.read(child);
    }
    children
}

fn expand(tree: &mut [Digest], i: usize) {
    if i < TREE {
        let [a, b] = seed_children(&tree[i]);
        tree[2 * i] = a;
        tree[2 * i + 1] = b;
        expand(tree, 2 * i);
        expand(tree, 2 * i + 1);
    }
}

// Return maximal subtrees containing opened views only. Omit padding.
fn frontier(challenges: &[usize]) -> Vec<usize> {
    let mut hidden = vec![false; 2 * TREE];
    for (r, &p) in challenges.iter().enumerate() {
        hidden[TREE + (p + 2) % 3 * REPETITIONS + r] = true;
    }
    for i in (1..TREE).rev() {
        hidden[i] = hidden[2 * i] || hidden[2 * i + 1];
    }
    fn collect(out: &mut Vec<usize>, hidden: &[bool], i: usize, start: usize, width: usize) {
        if start >= LEAVES {
            return;
        }
        if !hidden[i] {
            out.push(i);
        } else if width > 1 {
            collect(out, hidden, 2 * i, start, width / 2);
            collect(out, hidden, 2 * i + 1, start + width / 2, width / 2);
        }
    }
    let mut nodes = vec![];
    collect(&mut nodes, &hidden, 1, 0, TREE);
    nodes
}

fn trits(h: &Digest) -> Vec<usize> {
    let mut r = stream(b"uniform challenges", &[h]);
    let mut out = Vec::with_capacity(REPETITIONS);
    while out.len() < REPETITIONS {
        let mut byte = [0];
        r.read(&mut byte);
        if byte[0] < 255 {
            out.push(usize::from(byte[0] % 3));
        }
    }
    out
}

fn fs(circuit: &Circuit, st: &Statement) -> Result<Shake256> {
    ensure!(
        check_ranges(circuit.width, &st.ranges)? == st.projected_bytes.len(),
        "projection width"
    );
    Ok(transcript(
        b"FS 219 Keccak ZKBoo",
        &[
            circuit.domain,
            &circuit.frame,
            &(circuit.width as u64).to_le_bytes(),
            &bincode::serialize(st)?,
        ],
    ))
}

fn finish(h: Shake256) -> Digest {
    let mut d = [0; 32];
    h.finalize_xof().read(&mut d);
    d
}

struct Round {
    correction: Vec<u8>,
    gates: [Vec<u8>; 3],
    commitments: [Digest; 3],
}

pub fn prove(blind: &Digest, cell: &[u8], st: &Statement) -> Result<Vec<u8>> {
    Circuit::resident(cell.len()).prove(blind, cell, st)
}
impl Circuit {
    pub fn prove(&self, blind: &Digest, cell: &[u8], st: &Statement) -> Result<Vec<u8>> {
        ensure!(cell.len() == self.width, "wrong circuit width");
        let h = fs(self, st)?;
        ensure!(
            self.root(blind, cell) == st.cell_root
                && project(cell, &st.ranges) == st.projected_bytes,
            "witness mismatch"
        );
        self.prove_views(blind, cell, st, h)
    }

    fn prove_views(
        &self,
        blind: &Digest,
        cell: &[u8],
        st: &Statement,
        mut h: Shake256,
    ) -> Result<Vec<u8>> {
        let mut tree = vec![[0; 32]; 2 * TREE];
        tree[1] = random_seed()?;
        expand(&mut tree, 1);
        let mut witness = [blind.as_slice(), cell].concat();
        crate::trace_pack::encode(&mut witness);
        let mut rounds = Vec::with_capacity(REPETITIONS);
        for r in 0..REPETITIONS {
            let mut views = std::array::from_fn(|p| {
                View::new(
                    tree[TREE + p * REPETITIONS + r],
                    witness.len(),
                    self.frame.len(),
                )
            });
            let mut correction = witness.clone();
            for v in &views {
                xor(&mut correction, &v.input);
            }
            xor(&mut views[2].input, &correction);
            evaluate(&mut views, &st.ranges, self, None);
            let commitments = views.each_ref().map(View::commit);
            h.update(&correction);
            for (c, v) in commitments.iter().zip(&views) {
                h.update(c);
                h.update(&v.output);
            }
            rounds.push(Round {
                correction,
                gates: views.map(|v| v.gates),
                commitments,
            });
        }
        let d = finish(h);
        let challenges = trits(&d);
        let mut proof = d.to_vec();
        for i in frontier(&challenges) {
            proof.extend(tree[i]);
        }
        for (r, p) in rounds.iter().zip(challenges) {
            proof.extend(&r.correction);
            proof.extend(r.commitments[(p + 2) % 3]);
            proof.extend(&r.gates[(p + 1) % 3]);
        }
        Ok(proof)
    }
}

fn take<'a>(proof: &mut &'a [u8], n: usize) -> Result<&'a [u8]> {
    let (a, b) = proof.split_at_checked(n).context("truncated proof")?;
    *proof = b;
    Ok(a)
}

/// The verifier supplies the trusted circuit width and permitted slices.
pub fn verify(width: usize, permitted: &[(u16, u16)], st: &Statement, proof: &[u8]) -> Result<()> {
    Circuit::resident(width).verify(permitted, st, proof)
}
impl Circuit {
    pub fn verify(&self, permitted: &[(u16, u16)], st: &Statement, mut proof: &[u8]) -> Result<()> {
        ensure!(permitted == st.ranges, "slice permission");
        let mut h = fs(self, st)?;
        let d: Digest = take(&mut proof, 32)?.try_into()?;
        let challenges = trits(&d);
        let nodes = frontier(&challenges);
        let len = self.width + 32;
        let trace_len = ((len + self.frame.len()) / RATE + 1) * GATES * 8;
        ensure!(
            proof.len() == nodes.len() * 32 + REPETITIONS * (len + 32 + trace_len),
            "proof length"
        );
        let mut tree = vec![[0; 32]; 2 * TREE];
        for i in nodes {
            tree[i] = take(&mut proof, 32)?.try_into()?;
            expand(&mut tree, i);
        }
        for (r, p) in challenges.into_iter().enumerate() {
            let q = (p + 1) % 3;
            let hidden = (p + 2) % 3;
            let correction = take(&mut proof, len)?;
            let hidden_commit = take(&mut proof, 32)?;
            let trace = take(&mut proof, trace_len)?;
            let mut views = [p, q].map(|party| {
                let mut v = View::new(tree[TREE + party * REPETITIONS + r], len, self.frame.len());
                if party == 2 {
                    xor(&mut v.input, correction);
                }
                v
            });
            evaluate(&mut views, &st.ranges, self, Some(trace));
            let mut hidden_output = [st.cell_root.as_slice(), &st.projected_bytes].concat();
            for v in &views {
                xor(&mut hidden_output, &v.output);
            }
            h.update(correction);
            for party in 0..3 {
                if party == hidden {
                    h.update(hidden_commit);
                    h.update(&hidden_output);
                } else {
                    let v = &views[usize::from(party == q)];
                    h.update(&v.commit());
                    h.update(&v.output);
                }
            }
        }
        ensure!(finish(h) == d, "Fiat-Shamir transcript");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn verifier_checks_hidden_witness_without_prover_preflight() -> Result<()> {
        let blind = random_seed()?;
        let mut cell = [7u8; 64];
        let st = statement(&blind, &cell, vec![(0, 2)])?;
        cell[63] ^= 1;
        let c = Circuit::resident(64);
        let malformed = c.prove_views(&blind, &cell, &st, fs(&c, &st)?)?;
        assert!(c.verify(&st.ranges, &st, &malformed).is_err());
        Ok(())
    }
}
