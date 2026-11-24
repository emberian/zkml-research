//! The cSHAKE256 framing of resident cells: SP 800-185 prefix and padding, the custody
//! frame of a private store cell, statements and byte ranges. Coordinates are half-open byte
//! intervals. Proofs run on the extended-witness engine for every width and frame.
use super::circuit::Cell;
use crate::{kkw, Digest};
use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{CShake256, CShake256Core};

pub const DOMAIN: &[u8] = b"resident-custody/blinded-cell/v1";
const RATE: usize = 136;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Statement {
    pub cell_root: Digest,
    pub ranges: Vec<(u16, u16)>,
    pub projected_bytes: Vec<u8>,
}

pub fn root(blind: &Digest, cell: &[u8]) -> Digest {
    Circuit::resident(cell.len()).root(blind, cell)
}

pub(crate) fn encode_nat(mut n: u64) -> Vec<u8> {
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
    pub(crate) domain: &'static [u8],
    pub(crate) frame: Vec<u8>,
    pub(crate) width: usize,
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
            domain: crate::trie_opening::OUTER_HASH_DOMAIN,
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

pub(crate) fn project(cell: &[u8], ranges: &[(u16, u16)]) -> Vec<u8> {
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
pub(crate) fn prefix(domain: &[u8]) -> [u64; 25] {
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

pub(crate) fn absorb(s: &mut [u64; 25], block: &[u8]) {
    for (w, b) in s.iter_mut().zip(block.chunks_exact(8)) {
        *w ^= u64::from_le_bytes(b.try_into().unwrap());
    }
}

impl Circuit {
    pub fn prove(&self, blind: &Digest, cell: &[u8], st: &Statement) -> Result<Vec<u8>> {
        self.prove_with(blind, cell, st, &[])
    }
    /// Prove an opening bound to the caller's additional public `binding`.
    pub(crate) fn prove_with(
        &self,
        blind: &Digest,
        cell: &[u8],
        st: &Statement,
        binding: &[u8],
    ) -> Result<Vec<u8>> {
        ensure!(cell.len() == self.width, "wrong circuit width");
        let c = Cell::new(self, st)?;
        ensure!(
            self.root(blind, cell) == st.cell_root
                && project(cell, &st.ranges) == st.projected_bytes,
            "witness mismatch"
        );
        kkw::prove(&c, &[blind.as_slice(), cell].concat(), binding)
    }
    pub fn verify(&self, permitted: &[(u16, u16)], st: &Statement, proof: &[u8]) -> Result<()> {
        self.verify_with(permitted, st, &[], proof)
    }
    pub(crate) fn verify_with(
        &self,
        permitted: &[(u16, u16)],
        st: &Statement,
        binding: &[u8],
        proof: &[u8],
    ) -> Result<()> {
        ensure!(permitted == st.ranges, "slice permission");
        kkw::verify(&Cell::new(self, st)?, binding, proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn verifier_checks_hidden_witness_without_prover_preflight() -> Result<()> {
        let blind = crate::random_seed()?;
        let mut cell = [7u8; 104];
        let st = statement(&blind, &cell, vec![(0, 2)])?;
        cell[63] ^= 1;
        let c = Circuit::resident(104);
        let input = [blind.as_slice(), &cell].concat();
        let circuit = Cell::new(&c, &st)?;
        assert!(!kkw::satisfied(&circuit, &input)?);
        for forged in [0, kkw::INSTANCES] {
            let malformed = kkw::prove_cheating(&circuit, &input, &[], forged)?;
            assert!(c.verify(&st.ranges, &st, &malformed).is_err());
        }
        Ok(())
    }
}
