//! Salted cut-and-choose MPC-in-the-head over a committed extended witness.
//!
//! A [`Circuit`] is a straight-line program over 64-bit words with a public shape. Its
//! extended witness is the private input followed by every committed word: products and
//! Keccak checkpoints. Every constraint has degree two in it. Each of [`INSTANCES`]
//! preprocessing instances masks that witness with the XOR of [`PARTIES`] seeded tapes.
//! The prover commits every masked witness and seed vector, then derives two POLYVAL keys
//! that fingerprint all constraints of an instance at once (Katz, Kolesnikov and Wang with
//! one batched check per instance). [`ONLINE_INSTANCES`] instances open all but one party;
//! the verifier regenerates the preprocessing of the rest.
mod gates;
mod keccak;
mod tape;
mod tree;

pub(crate) use gates::{Builder, Lane};

use crate::{digest, random_seed, stream, transcript, Digest};
use anyhow::{ensure, Context, Result};
use gates::{Check, Count, Eval, Online, Quadratic, Trace};
use polyval::{universal_hash::UniversalHash, Polyval};
use rayon::prelude::*;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use tape::{cipher, Aggregate, Tapes, CHUNK};
use tree::{fill_merkle, frontier, merkle, recover, tree, Seed};

pub const PARTIES: usize = 64;
pub const INSTANCES: usize = 640;
pub const ONLINE_INSTANCES: usize = 23;
/// Largest constraint residual, in 16-byte POLYVAL blocks. The batch error bound in the
/// soundness test is taken at this length.
pub const MAX_BLOCKS: usize = 1 << 20;
const TOP: u32 = u32::MAX;
const FIRST: &[u8] = b"masked extended witness commitment tree";
const ONLINE: &[u8] = b"online broadcast commitment tree";
/// Party frontier seeds, hidden seed commitment, nonce and aggregate correction.
const OPENING_OVERHEAD: usize = PARTIES.ilog2() as usize * 16 + 96;

/// A straight-line circuit. Its shape and constants are fixed by its public statement.
pub(crate) trait Circuit: Sync {
    const LABEL: &'static [u8];
    /// Private input bytes, the first part of the extended witness.
    fn input_len(&self) -> usize;
    /// Every public value the circuit reads, in a canonical encoding.
    fn statement(&self) -> Result<Vec<u8>>;
    fn run<B: Builder>(&self, b: &mut B);
}

/// Sizes fixed by a circuit's public statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Shape {
    pub input_len: usize,
    /// Committed words after the input.
    pub words: usize,
    /// Constraint words.
    pub checks: usize,
}

impl Shape {
    pub(crate) fn of<C: Circuit>(c: &C) -> Result<Self> {
        let mut count = Eval(Count::default());
        c.run(&mut count);
        let shape = Self {
            input_len: c.input_len(),
            words: count.0.words,
            checks: count.0.checks,
        };
        ensure!(
            shape.blocks() <= MAX_BLOCKS,
            "circuit exceeds the batched check bound"
        );
        Ok(shape)
    }
    pub(crate) fn witness_len(&self) -> usize {
        self.input_len + 8 * self.words
    }
    pub(crate) fn blocks(&self) -> usize {
        (8 * self.checks).div_ceil(16)
    }
    /// Proof bytes for a challenge whose instance tree frontier has `frontier` nodes.
    pub(crate) fn proof_len(&self, frontier: usize) -> usize {
        96 + 80 * frontier + ONLINE_INSTANCES * (OPENING_OVERHEAD + self.witness_len())
    }
}

/// The clear extended witness: `input` and every committed word.
fn extend<C: Circuit>(c: &C, shape: &Shape, input: &[u8]) -> Result<Vec<u8>> {
    ensure!(input.len() == shape.input_len, "private input length");
    let mut t = Trace::new(input);
    c.run(&mut t);
    ensure!(t.words.len() == shape.words, "trace shape");
    let mut w = input.to_vec();
    w.extend(t.words.iter().flat_map(|x| x.to_le_bytes()));
    Ok(w)
}

/// Whether `input` satisfies every constraint of `c`.
#[cfg(test)]
pub(crate) fn satisfied<C: Circuit>(c: &C, input: &[u8]) -> Result<bool> {
    let shape = Shape::of(c)?;
    let w = extend(c, &shape, input)?;
    let mut bad = 0;
    c.run(&mut Eval(Check::new(&w, shape.input_len, |v| bad |= v)));
    Ok(bad == 0)
}

/// Two independent POLYVAL evaluations. Each has collision probability at most L / 2^128
/// for a nonzero residual of L fixed-length blocks, even if a key is zero.
struct Batch([Polyval; 2]);

impl Batch {
    fn new(ctx: &Digest, root: &Digest) -> Self {
        let keys = digest(b"extended witness quadratic batch", &[ctx, root]);
        Self(std::array::from_fn(|i| {
            Polyval::new(keys[i * 16..][..16].try_into().unwrap())
        }))
    }
    fn stream(&self) -> Fingerprint {
        Fingerprint {
            hash: self.0.clone(),
            buf: [0; 8 * CHUNK],
            fill: 0,
        }
    }
}

/// A streaming batch fingerprint of a word sequence.
#[derive(Clone)]
struct Fingerprint {
    hash: [Polyval; 2],
    buf: [u8; 8 * CHUNK],
    fill: usize,
}

impl Fingerprint {
    #[inline(always)]
    fn push(&mut self, v: u64) {
        self.buf[8 * self.fill..8 * self.fill + 8].copy_from_slice(&v.to_le_bytes());
        self.fill += 1;
        if self.fill == CHUNK {
            self.flush();
        }
    }
    fn flush(&mut self) {
        // Full chunks are whole blocks, so only the final call pads.
        for h in &mut self.hash {
            h.update_padded(&self.buf[..8 * self.fill]);
        }
        self.fill = 0;
    }
    fn finish(mut self) -> Digest {
        self.flush();
        let mut d = [0; 32];
        for (out, h) in d.chunks_exact_mut(16).zip(self.hash) {
            out.copy_from_slice(&h.finalize());
        }
        d
    }
}

fn xor(a: &mut [u8], b: &[u8]) {
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter_mut().zip(b) {
        *x ^= y;
    }
}

fn xor32(a: &mut Digest, b: &Digest) {
    xor(a, b)
}

fn context<C: Circuit>(c: &C, shape: &Shape, salt: &Digest, binding: &[u8]) -> Result<Digest> {
    Ok(digest(
        b"extended witness KKW proof",
        &[
            salt,
            C::LABEL,
            &c.statement()?,
            binding,
            &(PARTIES as u32).to_le_bytes(),
            &(INSTANCES as u32).to_le_bytes(),
            &(ONLINE_INSTANCES as u32).to_le_bytes(),
            &(shape.input_len as u64).to_le_bytes(),
            &(shape.words as u64).to_le_bytes(),
            &(shape.checks as u64).to_le_bytes(),
        ],
    ))
}

fn challenges(d: &Digest) -> Vec<(usize, usize)> {
    let mut r = stream(b"online subset and hidden parties", &[d]);
    let mut selected = vec![];
    while selected.len() < ONLINE_INSTANCES {
        let mut bytes = [0; 4];
        r.read(&mut bytes);
        let v = u32::from_le_bytes(bytes);
        let limit = (1u64 << 32) / INSTANCES as u64 * INSTANCES as u64;
        if u64::from(v) >= limit {
            continue;
        }
        let j = v as usize % INSTANCES;
        if selected.iter().any(|&(i, _)| i == j) {
            continue;
        }
        r.read(&mut bytes);
        selected.push((j, u32::from_le_bytes(bytes) as usize % PARTIES));
    }
    selected.sort_unstable();
    selected
}

// Fixed-width fields follow a one-byte purpose under the seed-expansion domain.
fn prg(
    purpose: u8,
    salt: &Digest,
    instance: u32,
    position: u32,
    seed: &Seed,
) -> sha3::Shake128Reader {
    let mut h = sha3::Shake128::default();
    h.update(b"resident-custody/selective-opening/prg");
    h.update(&[purpose]);
    h.update(salt);
    h.update(&instance.to_le_bytes());
    h.update(&position.to_le_bytes());
    h.update(seed);
    h.finalize_xof()
}

/// Separate segments of a position-bound XOF output: the seed commitment, which a puncture
/// discloses, then the private pad and AES key.
struct Material {
    commit: Digest,
    pad: Digest,
    key: [u8; 16],
}
fn material(salt: &Digest, j: usize, p: usize, seed: &Seed) -> Material {
    let mut m = [0; 80];
    prg(1, salt, j as u32, p as u32, seed).read(&mut m);
    Material {
        commit: m[..32].try_into().unwrap(),
        pad: m[32..64].try_into().unwrap(),
        key: m[64..].try_into().unwrap(),
    }
}

/// One instance's parties, with the hidden one's material unknown.
struct Parties {
    base: Digest,
    pads: Vec<Option<Digest>>,
    keys: Vec<Option<[u8; 16]>>,
}
impl Parties {
    fn new(salt: &Digest, j: usize, seeds: &[Seed], hidden: Option<(usize, &Digest)>) -> Self {
        let mut h = transcript(b"selective opening seed vector", &[]);
        let mut pads = vec![];
        let mut keys = vec![];
        for (p, seed) in seeds.iter().enumerate() {
            match hidden {
                Some((q, commit)) if q == p => {
                    h.update(commit);
                    pads.push(None);
                    keys.push(None);
                }
                _ => {
                    let m = material(salt, j, p, seed);
                    h.update(&m.commit);
                    pads.push(Some(m.pad));
                    keys.push(Some(m.key));
                }
            }
        }
        Self {
            base: finish(h),
            pads,
            keys,
        }
    }
    fn aggregate(&self) -> Aggregate {
        Aggregate::new(self.keys.iter().flatten().map(cipher).collect())
    }
    fn tapes(&self, shape: &Shape) -> Tapes {
        Tapes::new(
            self.keys.iter().map(|k| k.as_ref().map(cipher)).collect(),
            shape.input_len,
            shape.words,
        )
    }
    fn pad_sum(&self) -> Digest {
        let mut s = [0; 32];
        for p in self.pads.iter().flatten() {
            xor32(&mut s, p);
        }
        s
    }
}

fn finish(h: sha3::Shake256) -> Digest {
    let mut d = [0; 32];
    h.finalize_xof().read(&mut d);
    d
}
fn masked_leaf(base: &Digest, nonce: &Digest, len: usize) -> sha3::Shake256 {
    let mut h = transcript(b"committed masked extended witness", &[base, nonce]);
    h.update(&(len as u64).to_le_bytes());
    h
}
fn pre_leaf(base: &Digest, aux: &Digest) -> Digest {
    digest(b"preprocessed instance", &[base, aux])
}
fn messages(nonce: &Digest, msgs: &[Digest]) -> Digest {
    let mut h = transcript(b"online broadcast vector", &[nonce]);
    for msg in msgs {
        h.update(msg);
    }
    finish(h)
}
fn fs(ctx: &Digest, a: &Digest, prep: &[Digest], b: &Digest) -> Digest {
    let mut h = transcript(b"cut and choose", &[ctx, a, b]);
    for p in prep {
        h.update(p);
    }
    finish(h)
}

/// Online evaluation of one instance: party fingerprints and the masked residual's.
fn online<C: Circuit>(
    c: &C,
    shape: &Shape,
    tapes: Tapes,
    data: &[u8],
    clear: bool,
    batch: &Batch,
) -> (Digest, Vec<Digest>) {
    let mut e = Eval(Online::new(
        tapes,
        data,
        clear,
        shape.input_len,
        &batch.stream(),
    ));
    c.run(&mut e);
    let Eval(o) = e;
    (
        o.public.finish(),
        o.parties.into_iter().map(Fingerprint::finish).collect(),
    )
}

/// Prove that `input` satisfies `c`, binding the caller's public `binding`.
pub(crate) fn prove<C: Circuit>(c: &C, input: &[u8], binding: &[u8]) -> Result<Vec<u8>> {
    let shape = Shape::of(c)?;
    let witness = extend(c, &shape, input)?;
    let mut bad = 0;
    c.run(&mut Eval(Check::new(&witness, shape.input_len, |v| {
        bad |= v
    })));
    ensure!(bad == 0, "witness does not satisfy the circuit");
    prove_witness(
        c,
        &shape,
        &witness,
        binding,
        #[cfg(test)]
        None,
    )
}

/// A cheating prover for tests, with no preflight. Instances below `forged` commit the
/// preprocessing correction that cancels the false residual online. Every other instance
/// keeps correct preprocessing and falsifies exactly one party's message, so it opens online
/// only if that party stays hidden.
#[cfg(test)]
pub(crate) fn prove_cheating<C: Circuit>(
    c: &C,
    input: &[u8],
    binding: &[u8],
    forged: usize,
) -> Result<Vec<u8>> {
    let shape = Shape::of(c)?;
    let witness = extend(c, &shape, input)?;
    prove_witness(c, &shape, &witness, binding, Some(forged))
}

fn prove_witness<C: Circuit>(
    c: &C,
    shape: &Shape,
    witness: &[u8],
    binding: &[u8],
    #[cfg(test)] cheat: Option<usize>,
) -> Result<Vec<u8>> {
    let salt = random_seed()?;
    let ctx = context(c, shape, &salt, binding)?;
    let roots = tree(&salt, TOP, INSTANCES, random_seed()?[..16].try_into()?);
    let masters = &roots[INSTANCES.next_power_of_two()..][..INSTANCES];
    // The hiding nonce of a masked witness never derives from the seeds the offline
    // check discloses.
    let nonce_key = random_seed()?;
    let nonce = |j: usize| {
        digest(
            b"private transcript nonce",
            &[&nonce_key, &salt, &(j as u32).to_le_bytes()],
        )
    };
    let seeds = |j: usize| tree(&salt, j as u32, PARTIES, masters[j]);

    // Pass 1: commit every masked witness and seed vector.
    let committed: Vec<(Digest, Digest)> = (0..INSTANCES)
        .into_par_iter()
        .map(|j| {
            let parties = Parties::new(&salt, j, &seeds(j)[PARTIES..], None);
            let mut mask = parties.aggregate();
            let mut h = masked_leaf(&parties.base, &nonce(j), witness.len());
            let mut buf = vec![0; 8 * CHUNK * 8];
            for chunk in witness.chunks(buf.len()) {
                let b = &mut buf[..chunk.len()];
                mask.fill(b);
                xor(b, chunk);
                h.update(b);
            }
            (parties.base, finish(h))
        })
        .collect();
    let a = merkle(&committed.iter().map(|c| c.1).collect::<Vec<_>>(), FIRST);
    let batch = Batch::new(&ctx, &a[1]);
    // For a false witness, the fingerprint of its clear residual.
    #[cfg(test)]
    let delta = cheat.map(|_| {
        let mut h = batch.stream();
        c.run(&mut Eval(Check::new(witness, shape.input_len, |v| {
            h.push(v)
        })));
        h.finish()
    });

    // Pass 2: every party's online message. With f(w) = 0, the aggregate correction
    // H(Q(r)) ⊕ Σ pads equals H(masked residual) ⊕ Σ messages.
    let second: Vec<(Digest, Digest, Digest)> = (0..INSTANCES)
        .into_par_iter()
        .map(|j| {
            let parties = Parties::new(&salt, j, &seeds(j)[PARTIES..], None);
            let (public, hashes) = online(c, shape, parties.tapes(shape), witness, true, &batch);
            let msgs: Vec<Digest> = hashes
                .into_iter()
                .zip(&parties.pads)
                .map(|(mut h, pad)| {
                    xor32(&mut h, pad.as_ref().unwrap());
                    h
                })
                .collect();
            let mut aux = public;
            for m in &msgs {
                xor32(&mut aux, m);
            }
            #[cfg(test)]
            let mut msgs = msgs;
            #[cfg(test)]
            if let (Some(forged), Some(delta)) = (cheat, delta) {
                if j >= forged {
                    xor32(&mut aux, &delta);
                    xor32(&mut msgs[j % PARTIES], &delta);
                }
            }
            (
                aux,
                pre_leaf(&parties.base, &aux),
                messages(&nonce(j), &msgs),
            )
        })
        .collect();
    let b = merkle(&second.iter().map(|s| s.2).collect::<Vec<_>>(), ONLINE);
    let d = fs(
        &ctx,
        &a[1],
        &second.iter().map(|s| s.1).collect::<Vec<_>>(),
        &b[1],
    );
    let selected = challenges(&d);
    let nodes = frontier(
        INSTANCES,
        &selected.iter().map(|&(j, _)| j).collect::<Vec<_>>(),
    );
    let mut proof = [salt, a[1], d].concat();
    for &i in &nodes {
        proof.extend(roots[i]);
        proof.extend(a[i]);
        proof.extend(b[i]);
    }
    let header = proof.len();
    let opening = OPENING_OVERHEAD + witness.len();
    proof.resize(header + ONLINE_INSTANCES * opening, 0);
    proof[header..]
        .par_chunks_exact_mut(opening)
        .zip(&selected)
        .for_each(|(out, &(j, hidden))| {
            let seeds = seeds(j);
            let mut at = 0;
            let mut put = |bytes: &[u8]| {
                out[at..at + bytes.len()].copy_from_slice(bytes);
                at += bytes.len();
            };
            for i in frontier(PARTIES, &[hidden]) {
                put(&seeds[i]);
            }
            put(&material(&salt, j, hidden, &seeds[PARTIES + hidden]).commit);
            put(&nonce(j));
            // Recompute the masked witness rather than keep 640 of them.
            let parties = Parties::new(&salt, j, &seeds[PARTIES..], None);
            let masked = &mut out[at..at + witness.len()];
            parties.aggregate().fill(masked);
            xor(masked, witness);
            at += witness.len();
            out[at..].copy_from_slice(&second[j].0);
        });
    debug_assert_eq!(proof.len(), shape.proof_len(nodes.len()));
    Ok(proof)
}

fn take<'a>(proof: &mut &'a [u8], n: usize) -> Result<&'a [u8]> {
    let (a, b) = proof.split_at_checked(n).context("truncated proof")?;
    *proof = b;
    Ok(a)
}
fn read<const L: usize>(proof: &mut &[u8]) -> Result<[u8; L]> {
    Ok(take(proof, L)?.try_into()?)
}

/// Verify a proof that some private input satisfies `c`, under the caller's `binding`.
pub(crate) fn verify<C: Circuit>(c: &C, binding: &[u8], mut proof: &[u8]) -> Result<()> {
    let shape = Shape::of(c)?;
    let salt = read(&mut proof)?;
    let ctx = context(c, &shape, &salt, binding)?;
    let first = read(&mut proof)?;
    let d = read(&mut proof)?;
    let selected = challenges(&d);
    let nodes = frontier(
        INSTANCES,
        &selected.iter().map(|&(j, _)| j).collect::<Vec<_>>(),
    );
    let size = INSTANCES.next_power_of_two();
    let opening = OPENING_OVERHEAD + shape.witness_len();
    ensure!(
        proof.len() == nodes.len() * 80 + ONLINE_INSTANCES * opening,
        "proof length"
    );
    let mut roots = vec![[0; 16]; 2 * size];
    let mut a = vec![[0; 32]; 2 * size];
    let mut b = a.clone();
    for &i in &nodes {
        recover(&mut roots, &salt, TOP, i, read(&mut proof)?);
        a[i] = read(&mut proof)?;
        b[i] = read(&mut proof)?;
    }
    let batch = Batch::new(&ctx, &first);
    let opened: Result<Vec<_>> = selected
        .par_iter()
        .zip(proof.par_chunks_exact(opening))
        .map(|(&(j, hidden), mut proof)| {
            let mut seeds = vec![[0; 16]; 2 * PARTIES];
            for i in frontier(PARTIES, &[hidden]) {
                recover(&mut seeds, &salt, j as u32, i, read(&mut proof)?);
            }
            let hidden_commit: Digest = read(&mut proof)?;
            let nonce = read(&mut proof)?;
            let masked = take(&mut proof, shape.witness_len())?;
            let aux = read(&mut proof)?;
            let parties = Parties::new(&salt, j, &seeds[PARTIES..], Some((hidden, &hidden_commit)));
            let (public, hashes) = online(c, &shape, parties.tapes(&shape), masked, false, &batch);
            // The public residual fixes the hidden party's message.
            let mut msgs = vec![[0; 32]; PARTIES];
            let mut hidden_msg = public;
            xor32(&mut hidden_msg, &aux);
            for (p, (mut h, pad)) in hashes.into_iter().zip(&parties.pads).enumerate() {
                if let Some(pad) = pad {
                    xor32(&mut h, pad);
                    xor32(&mut hidden_msg, &h);
                    msgs[p] = h;
                }
            }
            msgs[hidden] = hidden_msg;
            let mut leaf = masked_leaf(&parties.base, &nonce, masked.len());
            leaf.update(masked);
            Ok((
                j,
                finish(leaf),
                messages(&nonce, &msgs),
                pre_leaf(&parties.base, &aux),
            ))
        })
        .collect();
    let mut online_pre = vec![None; INSTANCES];
    for (j, first_leaf, online_leaf, pre) in opened? {
        a[size + j] = first_leaf;
        b[size + j] = online_leaf;
        online_pre[j] = Some(pre);
    }
    fill_merkle(&mut a, FIRST, &nodes);
    ensure!(a[1] == first, "masked wire commitment");
    fill_merkle(&mut b, ONLINE, &nodes);
    let pre: Vec<_> = online_pre
        .into_par_iter()
        .enumerate()
        .map(|(j, p)| {
            p.unwrap_or_else(|| {
                let seeds = tree(&salt, j as u32, PARTIES, roots[size + j]);
                let parties = Parties::new(&salt, j, &seeds[PARTIES..], None);
                let mut q = Eval(Quadratic::new(
                    parties.aggregate(),
                    shape.input_len,
                    shape.words,
                    batch.stream(),
                ));
                c.run(&mut q);
                let mut aux = q.0.hash.finish();
                xor32(&mut aux, &parties.pad_sum());
                pre_leaf(&parties.base, &aux)
            })
        })
        .collect();
    ensure!(
        fs(&ctx, &first, &pre, &b[1]) == d,
        "cut-and-choose transcript"
    );
    Ok(())
}

#[cfg(test)]
pub(crate) mod tests {
    use super::gates::{Operands, Party};
    use super::*;
    use num_bigint::BigUint;

    /// Test an inconsistent extended witness through the ordinary transcript encoder.
    pub(crate) fn with_flipped_last_word<C: Circuit>(c: &C, input: &[u8]) -> Result<Vec<u8>> {
        let shape = Shape::of(c)?;
        let mut witness = extend(c, &shape, input)?;
        let last = witness.len() - 8;
        witness[last] ^= 1;
        let mut residual = 0;
        c.run(&mut Eval(Check::new(&witness, shape.input_len, |v| {
            residual |= v
        })));
        assert_ne!(residual, 0);
        prove_witness(c, &shape, &witness, &[], None)
    }

    fn choose(n: usize, k: usize) -> BigUint {
        (0..k).fold(BigUint::from(1u8), |a, i| a * (n - i) / (i + 1))
    }
    pub(crate) fn frontier_len(hidden: &[usize]) -> usize {
        frontier(INSTANCES, hidden).len()
    }
    /// Frontier nodes of the instance tree under final challenge `d`.
    pub(crate) fn challenge_frontier(d: &Digest) -> usize {
        frontier_len(&challenges(d).iter().map(|&(j, _)| j).collect::<Vec<_>>())
    }
    /// The worst split and its exact escape probability, numerator over denominator.
    pub(crate) fn worst_split(n: usize, m: usize, t: usize) -> (usize, BigUint, BigUint) {
        let mut worst = (0, BigUint::from(0u8), BigUint::from(1u8));
        for k in 0..=t {
            let num = choose(t, k);
            let den = choose(m, k) * BigUint::from(n).pow((t - k) as u32);
            if &num * &worst.2 > &den * &worst.1 {
                worst = (k, num, den);
            }
        }
        worst
    }
    /// Whether M (L / 2^128)^2 + max_k p_k < 2^-128, by integer cross multiplication.
    pub(crate) fn sound_at(blocks: usize) -> bool {
        let (_, num, den) = worst_split(PARTIES, INSTANCES, ONLINE_INSTANCES);
        let scale = BigUint::from(1u8) << 256;
        let batch = BigUint::from(INSTANCES) * BigUint::from(blocks) * BigUint::from(blocks);
        (num * &scale + &den * batch) << 128 < den * scale
    }

    #[test]
    fn exact_soundness_ledger_at_the_largest_circuit() {
        let (k, num, den) = worst_split(PARTIES, INSTANCES, ONLINE_INSTANCES);
        assert_eq!(k, 14);
        assert!((&num << 128) < den);
        assert!(sound_at(MAX_BLOCKS));
        // The bound has room: even 2^40 blocks stay below 2^-128 in total.
        assert!(sound_at(1 << 40));
        println!("N={PARTIES} M={INSTANCES} tau={ONLINE_INSTANCES} worst_k={k} escape={num}/{den} max_blocks={MAX_BLOCKS}");
    }

    /// For every circuit in `cases` with a satisfying input: the scalar per-party evaluation
    /// matches the online shares, and the three evaluations sum to the clear residual.
    pub(crate) fn differential<C: Circuit>(c: &C, input: &[u8]) -> Result<()> {
        let shape = Shape::of(c)?;
        let w = extend(c, &shape, input)?;
        let batch = Batch::new(&[7; 32], &[9; 32]);
        let keys: Vec<[u8; 16]> = (0..PARTIES)
            .map(|p| {
                digest(b"differential tape", &[&[p as u8]])[..16]
                    .try_into()
                    .unwrap()
            })
            .collect();
        let mut tapes = vec![vec![0; w.len()]; PARTIES];
        let mut mask = vec![0; w.len()];
        for (t, k) in tapes.iter_mut().zip(&keys) {
            Aggregate::new(vec![cipher(k)]).fill(t);
            xor(&mut mask, t);
        }
        let mut masked = w.clone();
        xor(&mut masked, &mask);
        let (public, hashes) = online(
            c,
            &shape,
            Tapes::new(
                keys.iter().map(|k| Some(cipher(k))).collect(),
                shape.input_len,
                shape.words,
            ),
            &w,
            true,
            &batch,
        );
        let mut recorded = Eval(Operands {
            check: Check::new(&masked, shape.input_len, (|_| {}) as fn(u64)),
            seen: vec![],
        });
        c.run(&mut recorded);
        let operands = recorded.0.seen;
        // H(masked residual) = H(f(w)) + H(Q(r)) + Σ_i H(online_i(r_i)), by linearity of H.
        let mut sum = [0; 32];
        for (p, tape) in tapes.iter().enumerate() {
            let mut party = Eval(Party {
                operands: operands.iter(),
                tape,
                input_len: shape.input_len,
                next: 0,
                hash: batch.stream(),
            });
            c.run(&mut party);
            assert!(party.0.operands.next().is_none());
            let h = party.0.hash.finish();
            ensure!(h == hashes[p], "party {p} differs from scalar polarization");
            xor32(&mut sum, &h);
        }
        let mut q = Eval(Quadratic::new(
            Aggregate::new(keys.iter().map(cipher).collect()),
            shape.input_len,
            shape.words,
            batch.stream(),
        ));
        c.run(&mut q);
        let mut clear = batch.stream();
        c.run(&mut Eval(Check::new(&w, shape.input_len, |v| {
            clear.push(v)
        })));
        xor32(&mut sum, &clear.finish());
        xor32(&mut sum, &q.0.hash.finish());
        ensure!(sum == public, "polarization identity");
        Ok(())
    }
}
