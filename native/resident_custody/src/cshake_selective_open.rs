//! Salted cut-and-choose MPCitH for one secret Keccak rate block.
//! The offline multiplication triples and online broadcasts are checked with
//! two verifier-derived polynomial fingerprints after binding the extended
//! witness. Two-round constraints and seed openings are described in the research note.
mod circuit;
mod framed;
pub(crate) use framed::{
    absorb, encode_nat, linear, prefix, project, prove_mpc, take, verify_mpc, View, RC,
};
pub use framed::{check_ranges, root, statement, Circuit, Statement, DOMAIN, REPETITIONS};
mod tree;

use crate::{digest, random_seed, stream, transcript, Digest};
use anyhow::{ensure, Result};
use circuit::{Batch, TraceCircuit};
use rayon::prelude::*;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use tree::{fill_merkle, frontier, merkle, recover, tree, Seed};

pub const PARTIES: usize = 64;
pub const INSTANCES: usize = 640;
pub const ONLINE_INSTANCES: usize = 23;
const TOP: u32 = u32::MAX;
const FIRST: &[u8] = b"selective opening masked wire commitment tree";
const ONLINE: &[u8] = b"selective opening online commitment tree";

fn xor(a: &mut [u8], b: &[u8]) {
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter_mut().zip(b) {
        *x ^= y;
    }
}
fn ctx(width: usize, st: &Statement, salt: &Digest, binding: &[u8]) -> Result<Digest> {
    Ok(digest(
        b"selective opening batched KKW resident cSHAKE256 paired rounds",
        &[
            salt,
            binding,
            &(width as u64).to_le_bytes(),
            &(PARTIES as u32).to_le_bytes(),
            &(INSTANCES as u32).to_le_bytes(),
            &(ONLINE_INSTANCES as u32).to_le_bytes(),
            &bincode::serialize(st)?,
        ],
    ))
}

fn challenges(d: &Digest) -> Vec<(usize, usize)> {
    let mut r = stream(b"selective opening subset and hidden parties", &[d]);
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
fn party_commit(salt: &Digest, j: usize, p: usize, seed: &Seed) -> Digest {
    let mut commitment = [0; 32];
    prg(1, salt, j as u32, p as u32, seed).read(&mut commitment);
    commitment
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
fn tape(salt: &Digest, j: usize, p: usize, seed: &Seed, mask: &mut [u8]) -> (Digest, Digest) {
    use aes::cipher::{KeyIvInit, StreamCipher};
    // Separate segments of a position-bound XOF output. Only the commitment
    // segment is disclosed at the puncture. The CTR key and pad stay private.
    let mut material = [0; 80];
    prg(1, salt, j as u32, p as u32, seed).read(&mut material);
    let mut cipher =
        ctr::Ctr64BE::<aes::Aes128Enc>::new(material[64..].try_into().unwrap(), &[0; 16].into());
    mask.fill(0);
    cipher.apply_keystream(mask);
    (
        material[..32].try_into().unwrap(),
        material[32..64].try_into().unwrap(),
    )
}

struct Prep {
    base: Digest,
    mask: Vec<u8>,
    pad: Digest,
}
fn preprocess(c: &TraceCircuit, salt: &Digest, j: usize, parties: &[Seed]) -> Prep {
    let mut h = transcript(b"selective opening seed vector", &[]);
    let mut mask = vec![0; c.len()];
    let mut sum = vec![0; c.len()];
    let mut pads = [0; 32];
    for (p, seed) in parties.iter().enumerate() {
        let (commit, pad) = tape(salt, j, p, seed, &mut mask);
        h.update(&commit);
        xor(&mut pads, &pad);
        xor(&mut sum, &mask);
    }
    Prep {
        base: finish(h),
        mask: sum,
        pad: pads,
    }
}
fn finish(h: sha3::Shake256) -> Digest {
    let mut d = [0; 32];
    h.finalize_xof().read(&mut d);
    d
}
fn first_leaf(base: &Digest, nonce: &Digest, masked: &[u8]) -> Digest {
    digest(
        b"selective opening committed masked extended witness",
        &[base, nonce, masked],
    )
}
fn pre_leaf(base: &Digest, aux: &Digest) -> Digest {
    digest(b"selective opening preprocessed instance", &[base, aux])
}
fn messages(nonce: &Digest, msgs: &[Digest]) -> Digest {
    let mut h = transcript(b"selective opening online broadcast vector", &[nonce]);
    for msg in msgs {
        h.update(msg);
    }
    finish(h)
}
fn fs(ctx: &Digest, a: &Digest, prep: &[Digest], b: &Digest) -> Digest {
    let mut h = transcript(b"selective opening cut and choose", &[ctx, a, b]);
    for p in prep {
        h.update(p);
    }
    finish(h)
}

struct Saved {
    prep: Prep,
    nonce: Digest,
    masked: Vec<u8>,
}
impl Saved {
    fn aux(&self, c: &TraceCircuit, batch: &Batch) -> Digest {
        let mut d = c.products(&self.prep.mask, batch);
        xor(&mut d, &self.prep.pad);
        d
    }
}
/// Prove the authorized projection of a resident cell.
pub fn prove(blind: &Digest, cell: &[u8], st: &Statement) -> Result<Vec<u8>> {
    Circuit::resident(cell.len()).prove(blind, cell, st)
}

pub fn verify(width: usize, permitted: &[(u16, u16)], st: &Statement, proof: &[u8]) -> Result<()> {
    Circuit::resident(width).verify(permitted, st, proof)
}

/// Bind a single-block opening to an additional public statement.
pub fn prove_with_context(
    blind: &Digest,
    cell: &[u8],
    st: &Statement,
    binding: &[u8],
) -> Result<Vec<u8>> {
    let c = TraceCircuit::new(cell.len(), st)?;
    ensure!(
        root(blind, cell) == st.cell_root
            && crate::cshake_selective_open::project(cell, &st.ranges) == st.projected_bytes,
        "witness mismatch"
    );
    prove_views(
        &c,
        blind,
        cell,
        binding,
        #[cfg(test)]
        0,
    )
}
fn prove_views(
    c: &TraceCircuit,
    blind: &Digest,
    cell: &[u8],
    binding: &[u8],
    #[cfg(test)] corrupt_instances: usize,
) -> Result<Vec<u8>> {
    let salt = random_seed()?;
    let ctx = ctx(cell.len(), c.st, &salt, binding)?;
    let roots = tree(&salt, TOP, INSTANCES, random_seed()?[..16].try_into()?);
    let masters = &roots[INSTANCES.next_power_of_two()..][..INSTANCES];
    // Offline seed disclosure must never open the hiding nonce on a masked
    // witness or its broadcast transcript.
    let nonce_key = random_seed()?;
    let witness = c.witness(blind, cell);
    let saved: Vec<_> = masters
        .par_iter()
        .enumerate()
        .map(|(j, &master)| {
            let parties = tree(&salt, j as u32, PARTIES, master);
            let prep = preprocess(c, &salt, j, &parties[PARTIES..]);
            let mut masked = witness.clone();
            xor(&mut masked, &prep.mask);
            let nonce = digest(
                b"selective opening private transcript nonce",
                &[&nonce_key, &salt, &(j as u32).to_le_bytes()],
            );
            Saved {
                prep,
                nonce,
                masked,
            }
        })
        .collect();
    let a = merkle(
        &saved
            .iter()
            .map(|s| first_leaf(&s.prep.base, &s.nonce, &s.masked))
            .collect::<Vec<_>>(),
        FIRST,
    );
    let batch = Batch::new(&ctx, &a[1]);
    #[cfg(test)]
    let forged_residual =
        (corrupt_instances != 0).then(|| batch.hash(&c.masked(&witness).residual));
    let aux_for = |j: usize| {
        let aux = saved[j].aux(c, &batch);
        #[cfg(test)]
        if j < corrupt_instances {
            // Make an invalid extended witness pass the online aggregate by
            // falsifying its offline product. Seed regeneration must catch it.
            let mut forged = aux;
            xor(&mut forged, forged_residual.as_ref().unwrap());
            return forged;
        }
        aux
    };
    let commitments: Vec<_> = saved
        .par_iter()
        .enumerate()
        .map(|(j, s)| {
            let parties = tree(&salt, j as u32, PARTIES, masters[j]);
            let masked = c.masked(&s.masked);
            let mut tapes = vec![0; PARTIES * c.len()];
            let pads: Vec<_> = parties[PARTIES..]
                .iter()
                .zip(tapes.chunks_exact_mut(c.len()))
                .enumerate()
                .map(|(p, (seed, buf))| tape(&salt, j, p, seed, buf).1)
                .collect();
            let msgs = c.party_messages(&tapes, &masked, &batch, &pads);
            #[cfg(test)]
            let msgs = {
                let mut msgs = msgs;
                if let Some(delta) = forged_residual.filter(|_| j >= corrupt_instances) {
                    // Correct preprocessing: falsify exactly one party's message.
                    // This instance can open online iff that party stays hidden.
                    xor(&mut msgs[j % PARTIES], &delta);
                }
                msgs
            };
            (
                pre_leaf(&s.prep.base, &aux_for(j)),
                messages(&s.nonce, &msgs),
            )
        })
        .collect();
    let (pre, online): (Vec<_>, Vec<_>) = commitments.into_iter().unzip();
    let b = merkle(&online, ONLINE);
    let d = fs(&ctx, &a[1], &pre, &b[1]);
    let selected = challenges(&d);
    let mut proof = [salt, a[1], d].concat();
    for i in frontier(
        INSTANCES,
        &selected.iter().map(|&(j, _)| j).collect::<Vec<_>>(),
    ) {
        proof.extend(roots[i]);
        proof.extend(a[i]);
        proof.extend(b[i]);
    }
    for (j, hidden) in selected {
        let parties = tree(&salt, j as u32, PARTIES, masters[j]);
        for i in frontier(PARTIES, &[hidden]) {
            proof.extend(parties[i]);
        }
        proof.extend(party_commit(&salt, j, hidden, &parties[PARTIES + hidden]));
        let s = &saved[j];
        proof.extend(s.nonce);
        proof.extend(&s.masked);
        proof.extend(aux_for(j));
        // The public zero residual fixes the hidden party's aggregate online
        // message. The verifier reconstructs it and checks the committed vector.
    }
    Ok(proof)
}

fn read<const L: usize>(proof: &mut &[u8]) -> Result<[u8; L]> {
    Ok(take(proof, L)?.try_into()?)
}

/// Verify a single-block opening and its caller-supplied public context.
pub fn verify_with_context(
    width: usize,
    permitted: &[(u16, u16)],
    st: &Statement,
    binding: &[u8],
    mut proof: &[u8],
) -> Result<()> {
    ensure!(permitted == st.ranges, "slice permission");
    let c = TraceCircuit::new(width, st)?;
    let salt = read(&mut proof)?;
    let ctx = ctx(width, st, &salt, binding)?;
    let first = read(&mut proof)?;
    let d = read(&mut proof)?;
    let selected = challenges(&d);
    let nodes = frontier(
        INSTANCES,
        &selected.iter().map(|&(j, _)| j).collect::<Vec<_>>(),
    );
    let size = INSTANCES.next_power_of_two();
    ensure!(
        proof.len()
            == nodes.len() * 80 + ONLINE_INSTANCES * (PARTIES.ilog2() as usize * 16 + 96 + c.len()),
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
    let mut online_pre = vec![None; INSTANCES];
    let opening_len = PARTIES.ilog2() as usize * 16 + 96 + c.len();
    let opened: Result<Vec<_>> = selected
        .into_par_iter()
        .zip(proof.par_chunks_exact(opening_len))
        .map(|((j, hidden), mut proof)| {
            let mut parties = vec![[0; 16]; 2 * PARTIES];
            for i in frontier(PARTIES, &[hidden]) {
                recover(&mut parties, &salt, j as u32, i, read(&mut proof)?);
            }
            let hidden_commit: Digest = read(&mut proof)?;
            let nonce = read(&mut proof)?;
            let data = take(&mut proof, c.len())?;
            let aux = read(&mut proof)?;
            let masked = c.masked(data);
            let mut hidden_msg = batch.hash(&masked.residual);
            xor(&mut hidden_msg, &aux);
            let mut commit = transcript(b"selective opening seed vector", &[]);
            let mut tapes = vec![0; PARTIES * c.len()];
            let mut pads = [[0; 32]; PARTIES];
            for (p, (seed, buf)) in parties[PARTIES..]
                .iter()
                .zip(tapes.chunks_exact_mut(c.len()))
                .enumerate()
            {
                if p == hidden {
                    commit.update(&hidden_commit);
                } else {
                    let (seed_commit, pad) = tape(&salt, j, p, seed, buf);
                    commit.update(&seed_commit);
                    pads[p] = pad;
                }
            }
            let mut msgs = c.party_messages(&tapes, &masked, &batch, &pads);
            for (p, msg) in msgs.iter().enumerate() {
                if p != hidden {
                    xor(&mut hidden_msg, msg);
                }
            }
            msgs[hidden] = hidden_msg;
            let base = finish(commit);
            Ok((
                j,
                first_leaf(&base, &nonce, data),
                messages(&nonce, &msgs),
                pre_leaf(&base, &aux),
            ))
        })
        .collect();
    for (j, first, online, pre) in opened? {
        a[size + j] = first;
        b[size + j] = online;
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
                let parties = tree(&salt, j as u32, PARTIES, roots[size + j]);
                let s = preprocess(&c, &salt, j, &parties[PARTIES..]);
                let mut aux = c.products(&s.mask, &batch);
                xor(&mut aux, &s.pad);
                pre_leaf(&s.base, &aux)
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
mod tests {
    use super::*;
    use crate::trie_opening::Branch;
    use num_bigint::BigUint;
    use std::time::Instant;

    fn choose(n: usize, k: usize) -> BigUint {
        (0..k).fold(BigUint::from(1u8), |a, i| a * (n - i) / (i + 1))
    }
    /// Return the worst split and its exact escape numerator and denominator.
    /// Only the display logarithm is rounded.
    fn soundness_bits_exact(n: usize, m: usize, t: usize) -> (usize, BigUint, BigUint, f64) {
        let mut worst = (0, BigUint::from(0u8), BigUint::from(1u8));
        for k in 0..=t {
            let num = choose(t, k);
            let den = choose(m, k) * BigUint::from(n).pow((t - k) as u32);
            if &num * &worst.2 > &den * &worst.1 {
                worst = (k, num, den);
            }
        }
        let bits = worst.2.to_string().parse::<f64>().unwrap().log2()
            - worst.1.to_string().parse::<f64>().unwrap().log2();
        (worst.0, worst.1, worst.2, bits)
    }

    #[test]
    fn exact_cheating_splits() {
        for (n, m, t, secure) in [
            (PARTIES, INSTANCES, ONLINE_INSTANCES, true),
            (64, 343, 27, true),
            (128, 352, 24, false),
            (128, 384, 24, false),
            (16, 242, 36, false),
            (32, 285, 30, false),
        ] {
            let (k, num, den, bits) = soundness_bits_exact(n, m, t);
            assert_eq!((&num << 128) <= den, secure);
            if secure {
                for bad in 0..=t {
                    assert!(
                        choose(t, bad) << 128
                            <= choose(m, bad) * BigUint::from(n).pow((t - bad) as u32)
                    );
                }
            }
            println!("N={n} M={m} tau={t} worst_k={k} escape={num}/{den} bits={bits:.9}");
        }
        // Count actual challenges in a toy game independently of the binomial
        // formula. This is a counting test only. The proof API fixes PARTIES,INSTANCES,ONLINE_INSTANCES.
        for k in 0..=2 {
            let mut pass = 0;
            for a in 0..4 {
                for b in a + 1..4 {
                    for pa in 0..2 {
                        for pb in 0..2 {
                            if (0..k).all(|j| j == a || j == b)
                                && (a < k || pa == 0)
                                && (b < k || pb == 0)
                            {
                                pass += 1u32;
                            }
                        }
                    }
                }
            }
            assert_eq!(
                BigUint::from(pass) * choose(4, k) * 2u32.pow((2 - k) as u32),
                choose(2, k) * 24u32
            );
        }
        // Even allowing the two POLYVAL tests and a union over instances, the
        // combined ideal challenge probability at one try is below 2^-128.
        let (worst, num, den, _) = soundness_bits_exact(PARTIES, INSTANCES, ONLINE_INSTANCES);
        assert_eq!(worst, 14);
        let blocks = (circuit::CHECK_BYTES + 103).div_ceil(16);
        let scale = BigUint::from(1u8) << 256;
        assert!((num * &scale + &den * (INSTANCES * blocks * blocks)) << 128 <= den * scale);
    }

    #[test]
    fn worst_case_wire_budget() {
        // The top tree has two occupied perfect subtrees (512 and 128
        // leaves). For h punctures in a depth-d perfect tree, each level has
        // at most min(2^level,h) occupied ancestors. Bit reversal attains it.
        fn perfect_frontier(depth: u32, h: usize) -> usize {
            1 + (0..depth).map(|d| (1usize << d).min(h)).sum::<usize>() - h
        }
        assert_eq!(INSTANCES, 512 + 128);
        let mut max = 0;
        for left in 0..=ONLINE_INSTANCES {
            let right = ONLINE_INSTANCES - left;
            let mut hidden: Vec<_> = (0..left)
                .map(|i| (i as u32).reverse_bits() as usize >> 23)
                .chain((0..right).map(|i| 512 + ((i as u32).reverse_bits() as usize >> 25)))
                .collect();
            hidden.sort_unstable();
            let bound = perfect_frontier(9, left) + perfect_frontier(7, right);
            assert_eq!(frontier(INSTANCES, &hidden).len(), bound);
            max = max.max(bound);
        }
        assert_eq!(max, 109);
        let bytes = 96
            + 80 * max
            + ONLINE_INSTANCES
                * (PARTIES.ilog2() as usize * 16 + 96 + 32 + 64 + circuit::TRACE_BYTES);
        assert_eq!(bytes, 90_880);
        let header = crate::custody_mesh::HeaderOpening {
            w0_leaf: [0; 32], cell_root: [0; 32],
            journal: Default::default(), proof: vec![0; bytes],
        };
        assert_eq!(bincode::serialized_size(&header).unwrap(), crate::custody_mesh::MAX_HEADER_WIRE);
        assert!(crate::custody_mesh::MAX_HEADER_WIRE <= 91_000);
        assert!(bytes + 65 + 3 * 32 <= 92_000);
    }

    #[test]
    fn native_trace_and_batched_beaver_identity() -> Result<()> {
        let batch = Batch::new(&[7; 32], &[9; 32]);
        for width in [1usize, 64, 103] {
            let blind = random_seed()?;
            let cell = vec![0xab; width];
            let st = statement(&blind, &cell, vec![(0, 1)])?;
            let c = TraceCircuit::new(width, &st)?;
            let w = c.witness(&blind, &cell);
            assert!(c.masked(&w).residual.iter().all(|&b| b == 0));
            let mut mask = vec![0; c.len()];
            stream(b"identity test", &[&blind]).read(&mut mask);
            let mut public = w.clone();
            xor(&mut public, &mask);
            let masked = c.masked(&public);
            let mut check = c.message(&mask, &masked, &batch, &[0; 32]);
            xor(&mut check, &c.products(&mask, &batch));
            assert_eq!(check, batch.hash(&masked.residual));
        }
        Ok(())
    }

    #[test]
    fn authenticated_projection_and_adversarial_openings() -> Result<()> {
        let blind = random_seed()?;
        let mut cell = [0x61; 64];
        let canary = random_seed()?;
        cell[32..].copy_from_slice(&canary);
        let st = statement(&blind, &cell, vec![(1, 5), (18, 22)])?;
        let mut path = [0x54; 65];
        path[64] = 0x40;
        let siblings = [[1; 32], [2; 32], [3; 32]];
        let branch = Branch {
            path: &path,
            siblings: &siblings,
        };
        let world = branch.root(&st.cell_root)?;
        let binding = branch.binding(&world, &st.cell_root)?;
        let mut proof = branch.prove(&world, &blind, &cell, &st)?;
        branch.verify(&world, 64, &st.ranges, &st, &proof)?;
        assert!(proof.len() <= 90_880);
        assert!(proof.windows(32).all(|w| w != canary && w != blind));
        println!(
            "authenticated leaf proof {} bytes; neither private 32-byte string appeared",
            proof.len()
        );

        let d: Digest = proof[64..96].try_into()?;
        let js: Vec<_> = challenges(&d).iter().map(|&(j, _)| j).collect();
        let start = 96 + 80 * frontier(INSTANCES, &js).len();
        let c = TraceCircuit::new(64, &st)?;
        let opening = start + PARTIES.ilog2() as usize * 16;
        for (name, offset) in [
            ("GGM puncture", start),
            ("hidden party commitment", opening),
            ("masked round state", opening + 64 + c.input_len),
            ("inverse chi hint", opening + 64 + c.input_len + 25 * 8),
            ("committed online broadcasts", 96 + 16 + 32),
            ("nonce", opening + 32),
            ("preprocessing correction", opening + 64 + c.len()),
            ("offline seed", 96),
        ] {
            proof[offset] ^= 1;
            assert!(
                branch.verify(&world, 64, &st.ranges, &st, &proof).is_err(),
                "{name}"
            );
            proof[offset] ^= 1;
            println!("rejected {name}");
        }
        let other = [[1; 32], [4; 32], [3; 32]];
        let wrong = Branch {
            path: &path,
            siblings: &other,
        };
        assert!(wrong.verify(&world, 64, &st.ranges, &st, &proof).is_err());
        assert!(branch
            .verify(&world, 64, &[(0, 4), (18, 22)], &st, &proof)
            .is_err());
        let wrong_world = wrong.root(&st.cell_root)?;
        assert!(wrong
            .verify(&wrong_world, 64, &st.ranges, &st, &proof)
            .is_err());
        let mut answer = st.clone();
        answer.projected_bytes[0] ^= 1;
        assert!(branch
            .verify(&world, 64, &st.ranges, &answer, &proof)
            .is_err());
        assert!(branch
            .verify(&world, 64, &st.ranges, &st, &proof[..proof.len() - 1])
            .is_err());
        cell[63] ^= 1;
        for k in [0, 14] {
            let forged = prove_views(&c, &blind, &cell, &binding, k)?;
            assert!(branch.verify(&world, 64, &st.ranges, &st, &forged).is_err());
            println!("rejected changed hidden witness with {k} corrupted preprocessing instances");
        }
        println!("rejected sibling, policy, authenticated context transplant, answer, truncation, bypassed hidden-byte mutation");
        Ok(())
    }

    #[test]
    #[ignore = "serial wall-clock benchmark"]
    fn authenticated_release_gate() -> Result<()> {
        let blind = random_seed()?;
        let cell = [0x61; 64];
        let st = statement(&blind, &cell, vec![(1, 5), (18, 22)])?;
        let path = [0; 65];
        let siblings = [[1; 32], [2; 32], [3; 32]];
        let branch = Branch {
            path: &path,
            siblings: &siblings,
        };
        let world = branch.root(&st.cell_root)?;
        let branch_bytes = path.len() + std::mem::size_of_val(&siblings);
        println!(
            "workers={} public_branch_bytes={branch_bytes}",
            rayon::current_num_threads()
        );
        let mut samples = [vec![], vec![], vec![]];
        for _ in 0..9 {
            let t = Instant::now();
            let p = branch.prove(&world, &blind, &cell, &st)?;
            let prove_ms = t.elapsed().as_secs_f64() * 1000.;
            let t = Instant::now();
            branch.verify(&world, 64, &st.ranges, &st, &p)?;
            let verify_ms = t.elapsed().as_secs_f64() * 1000.;
            println!(
                "bytes={} prove_ms={prove_ms:.3} verify_ms={verify_ms:.3}",
                p.len()
            );
            assert!(p.len() + branch_bytes <= 92_000);
            for (v, x) in samples
                .iter_mut()
                .zip([p.len() as f64, prove_ms, verify_ms])
            {
                v.push(x);
            }
        }
        for v in &mut samples {
            v.sort_by(f64::total_cmp);
        }
        println!(
            "medians bytes={} prove_ms={:.3} verify_ms={:.3}",
            samples[0][4], samples[1][4], samples[2][4]
        );
        assert!(samples[1][4] <= 120., "prove median exceeded 120 ms");
        assert!(samples[2][4] <= 40., "verify median exceeded 40 ms");
        Ok(())
    }
}
