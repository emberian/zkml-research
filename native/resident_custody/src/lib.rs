//! Resident custody and selective disclosure protocols.
#![forbid(unsafe_code)]

pub mod belt_latch_kernel;
pub mod cshake_selective_open;
pub mod custody_mesh;
mod tower;
mod trace_pack;
pub mod trie_opening;

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake256, Shake256Reader};

pub type Digest = [u8; 32];

fn transcript(label: &[u8], fields: &[&[u8]]) -> Shake256 {
    let mut hash = Shake256::default();
    for field in [b"resident-custody/v1".as_slice(), label]
        .into_iter()
        .chain(fields.iter().copied())
    {
        hash.update(&(field.len() as u64).to_le_bytes());
        hash.update(field);
    }
    hash
}

fn stream(label: &[u8], fields: &[&[u8]]) -> Shake256Reader {
    transcript(label, fields).finalize_xof()
}

fn digest(label: &[u8], fields: &[&[u8]]) -> Digest {
    let mut out = [0; 32];
    stream(label, fields).read(&mut out);
    out
}

pub fn random_seed() -> anyhow::Result<Digest> {
    let mut seed = [0; 32];
    getrandom::getrandom(&mut seed).map_err(|e| anyhow::anyhow!("OS randomness: {e}"))?;
    Ok(seed)
}
