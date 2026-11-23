//! OpeningRel for framed custody, at the canonical wire-image boundary.
//! The caller supplies its trusted kind/layout, fieldOf and StoreCodec
//! encodings of the public view. Every reveal byte stays in the MPC witness.
use super::{node, Path};
use crate::cshake_selective_open::{self as zk, View};
use crate::{transcript, Digest};
use anyhow::{ensure, Result};
use serde::Serialize;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core, Shake256,
};
use std::collections::BTreeSet;

mod mpc;
const ADDRESS: &[u8] = b"DREGG/PRIVATE-CELL/ADDRESS/v1";
const CONTENT: &[u8] = b"DREGG/PRIVATE-CELL/CONTENT/v1";

#[derive(Clone, Serialize)]
pub enum Field {
    Slot(Digest),
    Balance(Digest),
    Code,
    Body,
    AtomsOf(Digest),
    Annotations,
}
fn tag(field: Option<&Field>) -> Vec<bool> {
    let (family, atom, n) = match field {
        Some(Field::Slot(n)) => (0, false, n),
        Some(Field::Balance(n)) => (1, false, n),
        Some(Field::Code) => (2, false, &[0; 32]),
        Some(Field::Body) => (3, false, &[0; 32]),
        Some(Field::AtomsOf(n)) => (3, true, n),
        Some(Field::Annotations) => (4, false, &[0; 32]),
        None => (5, false, &[0; 32]),
    };
    let mut bits = vec![family & 4 != 0, family & 2 != 0, family & 1 != 0, atom];
    // PrivateCellScope.bitsW enumerates Nat.testBit from zero upwards.
    bits.extend((0..256).map(|i| n[i / 8] & (1 << (i % 8)) != 0));
    bits
}

#[derive(Clone, Serialize)]
pub struct Entry {
    /// From the selected kind's fieldOf; integer field parameters are little endian.
    pub field: Option<Field>,
    /// Exact addressStream and valueBytes outputs of the caller's canonical codec.
    pub address: Vec<u8>,
    pub value: Vec<u8>,
}
#[derive(Clone, Serialize)]
pub struct Statement {
    pub root: Digest,
    pub layout: Digest,
    pub cell: Vec<u8>,
    pub version: u64,
    /// None is the full view. Some([]) has no reader prefixes.
    pub fields: Option<Vec<Field>>,
    pub view: Vec<Entry>,
}
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Leaf {
    pub path: Path,
    pub content: Digest,
}
fn hash(domain: &[u8], parts: &[&[u8]]) -> Digest {
    let mut h = CShake256::from_core(CShake256Core::new(domain));
    for p in parts {
        h.update(p);
    }
    let mut d = [0; 32];
    h.finalize_xof().read(&mut d);
    d
}
impl Entry {
    pub fn image(&self) -> Leaf {
        let mut bits = tag(self.field.as_ref());
        let address = hash(ADDRESS, &[&self.address]);
        bits.extend((0..256).map(|i| address[i / 8] & (128 >> (i % 8)) != 0));
        let mut path = [0; 65];
        for (i, b) in bits.into_iter().enumerate() {
            if b {
                path[i / 8] |= 128 >> (i % 8);
            }
        }
        Leaf {
            path,
            content: hash(
                CONTENT,
                &[
                    &zk::encode_nat(self.address.len() as u64),
                    &self.address,
                    &self.value,
                ],
            ),
        }
    }
}
fn bit(path: &Path, d: usize) -> bool {
    path[d / 8] & (128 >> (d % 8)) != 0
}
fn under(path: &Path, p: &[bool]) -> bool {
    p.iter().enumerate().all(|(i, &b)| bit(path, i) == b)
}
fn subtree(leaves: &[Leaf], depth: usize) -> Digest {
    match leaves {
        [] => node(&[&[2]]),
        [leaf] => node(&[&[0], &leaf.path, &leaf.content]),
        _ => {
            // All callers establish unique, sorted canonical 516-bit paths.
            let mid = leaves.partition_point(|l| !bit(&l.path, depth));
            node(&[
                &[1],
                &subtree(&leaves[..mid], depth + 1),
                &subtree(&leaves[mid..], depth + 1),
            ])
        }
    }
}
fn sorted_image(entries: &[Entry]) -> Result<Vec<Leaf>> {
    let mut addresses = BTreeSet::new();
    ensure!(
        entries.iter().all(|e| addresses.insert(&e.address)),
        "duplicate address"
    );
    let mut leaves: Vec<_> = entries.iter().map(Entry::image).collect();
    leaves.sort_unstable();
    ensure!(
        leaves.windows(2).all(|w| w[0].path != w[1].path),
        "duplicate path"
    );
    Ok(leaves)
}
struct Job {
    prefix: Vec<bool>,
    count: usize,
    below: Digest,
}
struct Plan {
    frame: Vec<u8>,
    jobs: Vec<Job>,
    len: usize,
}
impl Plan {
    fn new(st: &Statement) -> Result<Self> {
        let frame = zk::Circuit::private_cell_outer(&st.layout, &st.cell, st.version)?.frame;
        let prefixes: BTreeSet<_> = match &st.fields {
            None => [vec![]].into_iter().collect(),
            Some(fields) => fields
                .iter()
                .map(|f| {
                    let mut p = tag(Some(f));
                    if matches!(f, Field::Body) {
                        p.truncate(3);
                    }
                    p
                })
                .collect(),
        };
        let leaves = sorted_image(&st.view)?;
        ensure!(
            leaves
                .iter()
                .all(|l| prefixes.iter().any(|p| under(&l.path, p))),
            "answer outside scope"
        );
        let mut jobs = vec![];
        let mut len = 64usize;
        for prefix in prefixes {
            let members: Vec<_> = leaves
                .iter()
                .copied()
                .filter(|l| under(&l.path, &prefix))
                .collect();
            let count = members.len();
            let below = subtree(&members, prefix.len());
            len += prefix.len() * (32 + usize::from(count <= 1)) + if count == 0 { 98 } else { 0 };
            jobs.push(Job {
                prefix,
                count,
                below,
            });
        }
        Ok(Self { frame, jobs, len })
    }
}
pub struct Reveal {
    /// From root to actual stopping depth.
    pub siblings: Vec<Digest>,
    /// Only an early terminal outside an empty answer needs a private member.
    pub other: Option<Leaf>,
}
pub struct Witness {
    pub secret: Digest,
    pub inner: Digest,
    pub reveals: Vec<Reveal>,
}
impl Witness {
    /// Build the private index and actual reveals from a canonical live store.
    /// The entries supplied here exclude the custody/blinding address.
    pub fn from_index(st: &Statement, secret: Digest, entries: &[Entry]) -> Result<Self> {
        let plan = Plan::new(st)?;
        let leaves = sorted_image(entries)?;
        let inner = subtree(&leaves, 0);
        let reveals = plan
            .jobs
            .iter()
            .map(|job| {
                let mut sub = leaves.as_slice();
                let mut siblings = vec![];
                for (depth, &b) in job.prefix.iter().enumerate() {
                    if sub.len() <= 1 {
                        break;
                    }
                    let mid = sub.partition_point(|l| !bit(&l.path, depth));
                    let (left, right) = sub.split_at(mid);
                    let (next, other) = if b { (right, left) } else { (left, right) };
                    siblings.push(subtree(other, depth + 1));
                    sub = next;
                }
                let other = sub
                    .first()
                    .copied()
                    .filter(|l| sub.len() == 1 && !under(&l.path, &job.prefix));
                Reveal { siblings, other }
            })
            .collect();
        Ok(Self {
            secret,
            inner,
            reveals,
        })
    }
    fn pack(&self, plan: &Plan) -> Result<Vec<u8>> {
        ensure!(self.reveals.len() == plan.jobs.len(), "missing prefix");
        let mut bytes = [self.secret, self.inner].concat();
        for (job, r) in plan.jobs.iter().zip(&self.reveals) {
            ensure!(
                r.siblings.len() <= job.prefix.len()
                    && (job.count < 2 || r.siblings.len() == job.prefix.len()),
                "reveal shape"
            );
            if job.count == 0 {
                bytes.push(u8::from(r.other.is_some()));
                let leaf = r.other.unwrap_or(Leaf {
                    path: [0; 65],
                    content: [0; 32],
                });
                ensure!(leaf.path[64] & 15 == 0, "noncanonical path");
                bytes.extend(leaf.path);
                bytes.extend(leaf.content);
            } else {
                ensure!(r.other.is_none(), "unexpected early member");
            }
            for i in 0..job.prefix.len() {
                if job.count <= 1 {
                    bytes.push(u8::from(i < r.siblings.len()));
                }
                bytes.extend(r.siblings.get(i).copied().unwrap_or([0; 32]));
            }
        }
        Ok(bytes)
    }
}

fn fs(st: &Statement) -> Result<Shake256> {
    Ok(transcript(
        b"private framed OpeningRel 219 ZKBoo",
        &[&bincode::serialize(st)?],
    ))
}
pub fn prove(st: &Statement, w: &Witness) -> Result<Vec<u8>> {
    let plan = Plan::new(st)?;
    let witness = w.pack(&plan)?;
    let (output, gates) = mpc::clear(&plan, &witness);
    ensure!(
        output[..32] == st.root && output[32..].iter().all(|&v| v == 0),
        "private opening relation"
    );
    zk::prove_mpc(witness, gates, fs(st)?, |views| {
        mpc::evaluate(&plan, views, None)
    })
}
pub fn verify(st: &Statement, proof: &[u8]) -> Result<()> {
    let plan = Plan::new(st)?;
    let (mut expected, gates) = mpc::clear(&plan, &vec![0; plan.len]);
    expected.fill(0);
    expected[..32].copy_from_slice(&st.root);
    zk::verify_mpc(
        plan.len,
        gates,
        &expected,
        fs(st)?,
        proof,
        |views, trace| mpc::evaluate(&plan, views, Some(trace)),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    fn entry(field: Field, address: u8) -> Entry {
        Entry {
            field: Some(field),
            address: vec![address, 255],
            value: vec![address + 10, 255],
        }
    }
    fn fixture() -> (Statement, Vec<Entry>) {
        let entries = vec![
            entry(Field::Body, 1),
            entry(Field::AtomsOf([7; 32]), 2),
            entry(Field::Code, 3),
        ];
        (
            Statement {
                root: [0; 32],
                layout: [9; 32],
                cell: b"seat".to_vec(),
                version: 300,
                fields: Some(vec![Field::Body]),
                view: entries[..2].to_vec(),
            },
            entries,
        )
    }
    fn prepare(st: &mut Statement, index: &[Entry]) -> Result<Witness> {
        let w = Witness::from_index(st, [17; 32], index)?;
        st.root = zk::Circuit::private_cell_outer(&st.layout, &st.cell, st.version)?
            .root(&w.secret, &w.inner);
        Ok(w)
    }
    fn unchecked(st: &Statement, private: Vec<u8>) -> Result<Vec<u8>> {
        let plan = Plan::new(st)?;
        let (_, gates) = mpc::clear(&plan, &private);
        zk::prove_mpc(private, gates, fs(st)?, |v| mpc::evaluate(&plan, v, None))
    }
    #[test]
    fn private_prefix_answers_bind_every_member_and_version() -> Result<()> {
        let (mut st, index) = fixture();
        let w = prepare(&mut st, &index)?;
        // Independently generated by research/w13_compact_opening/vectors.go.
        assert_eq!(
            w.inner,
            [
                0xb3, 0xd9, 0x82, 0x88, 0xb9, 0xd6, 0x23, 0x14, 0x70, 0x07, 0x07, 0xd8, 0xe1, 0x3e,
                0xfe, 0x06, 0x48, 0xd2, 0x71, 0xff, 0xc2, 0xfd, 0x05, 0xe4, 0xea, 0xe3, 0xd3, 0xb9,
                0xb7, 0xc4, 0x81, 0x8b
            ]
        );
        assert_eq!(
            st.root,
            [
                0xae, 0x61, 0x0f, 0x27, 0xf3, 0x86, 0xcb, 0x56, 0xf0, 0xcb, 0x2d, 0xda, 0x38, 0x63,
                0xbe, 0x8c, 0x62, 0x4e, 0xee, 0x44, 0x2f, 0x69, 0xc9, 0xa6, 0x37, 0x6e, 0x0a, 0xf0,
                0xe4, 0x2c, 0xf4, 0xde
            ]
        );
        let p = prove(&st, &w)?;
        verify(&st, &p)?;
        println!("private body prefix two members, one hidden entry: {} proof bytes; inner={:02x?} outer={:02x?}",p.len(),w.inner,st.root);
        assert!(!p.windows(32).any(|b| b == w.secret || b == w.inner));
        let mut relabeled = st.clone();
        relabeled.version += 1;
        assert!(verify(&relabeled, &p).is_err());
        let mut omitted = st.clone();
        omitted.view.pop();
        let plan = Plan::new(&omitted)?;
        let proof = unchecked(&omitted, w.pack(&plan)?)?;
        assert!(verify(&omitted, &proof).is_err());
        let mut changed = st.clone();
        changed.view[1].value.push(42);
        assert!(prove(&changed, &w).is_err());
        let mut substituted = st.clone();
        substituted.view[0] = index[2].clone();
        assert!(Plan::new(&substituted).is_err());
        Ok(())
    }
    #[test]
    #[ignore = "measures a depth-260 private field proof"]
    fn full_field_prefix_proof() -> Result<()> {
        let (mut st, index) = fixture();
        st.fields = Some(vec![Field::Code]);
        st.view = index[2..].to_vec();
        let w = prepare(&mut st, &index)?;
        let start = std::time::Instant::now();
        let p = prove(&st, &w)?;
        let pt = start.elapsed();
        let start = std::time::Instant::now();
        verify(&st, &p)?;
        println!(
            "260-bit private prefix proof bytes={} prove_ms={:.3} verify_ms={:.3}",
            p.len(),
            pt.as_secs_f64() * 1000.,
            start.elapsed().as_secs_f64() * 1000.
        );
        Ok(())
    }

    #[test]
    fn private_early_stop_empty_and_singleton() -> Result<()> {
        let (mut st, index) = fixture();
        st.view.clear();
        let mut w = prepare(&mut st, &index[2..])?;
        assert!(w.reveals[0].siblings.is_empty() && w.reveals[0].other.is_some());
        let p = prove(&st, &w)?;
        verify(&st, &p)?;
        println!(
            "private body prefix empty answer with hidden singleton: {} proof bytes",
            p.len()
        );
        // Keep a genuine root for a selected leaf and try to present it as a
        // private early terminal with empty answer. Bypass prover preflight.
        let selected = index[0].image();
        w.reveals[0].other = Some(selected);
        w.inner = subtree(&[selected], 0);
        st.root = zk::Circuit::private_cell_outer(&st.layout, &st.cell, st.version)?
            .root(&w.secret, &w.inner);
        let plan = Plan::new(&st)?;
        assert!(verify(&st, &unchecked(&st, w.pack(&plan)?)?).is_err());
        for (scope, visible, index) in [
            (Some(vec![Field::Body]), &index[..1], &index[..1]),
            (None, &index[..], &index[..]),
            (Some(vec![]), &index[..0], &index[..]),
            (Some(vec![Field::Body]), &index[..0], &index[..0]),
            (
                Some(vec![Field::Body, Field::AtomsOf([7; 32])]),
                &index[..2],
                &index[..],
            ),
        ] {
            st.fields = scope;
            st.view = visible.to_vec();
            let w = prepare(&mut st, index)?;
            let plan = Plan::new(&st)?;
            let (out, _) = mpc::clear(&plan, &w.pack(&plan)?);
            assert_eq!(&out[..32], &st.root);
            assert!(out[32..].iter().all(|&v| v == 0));
        }
        Ok(())
    }
}
