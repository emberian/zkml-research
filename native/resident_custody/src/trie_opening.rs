//! A resident byte-cell membership proof with public branch metadata.
//! The caller pins the world root, path, width and release policy. The caller
//! may use an early-stop leaf, since its digest commits to all 516 path bits.
use crate::{
    cshake_selective_open::{self as opening, Statement},
    Digest,
};
use anyhow::{ensure, Result};
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core,
};

// Persisted store hash customizations, shared by the clear and MPC readers.
// Compiler/PrivateCellRoot.lean defines these bytes in the companion tree.
pub(crate) const NODE_HASH_DOMAIN: &[u8] = b"DREGG/PRIVATE-CELL/NODE/v2";
pub(crate) const OUTER_HASH_DOMAIN: &[u8] = b"DREGG/PRIVATE-CELL/OUTER/v2";

pub type Path = [u8; 65];
pub struct Branch<'a> {
    pub path: &'a Path,
    /// Root-to-leaf order. Direction bits are MSB first.
    pub siblings: &'a [Digest],
}
fn node(parts: &[&[u8]]) -> Digest {
    let mut h = CShake256::from_core(CShake256Core::new(NODE_HASH_DOMAIN));
    for p in parts {
        h.update(p);
    }
    let mut out = [0; 32];
    h.finalize_xof().read(&mut out);
    out
}
impl Branch<'_> {
    pub fn root(&self, leaf: &Digest) -> Result<Digest> {
        ensure!(
            self.path[64] & 15 == 0 && self.siblings.len() <= 516,
            "noncanonical trie path"
        );
        let mut h = node(&[&[0], self.path, leaf]);
        for (depth, sibling) in self.siblings.iter().enumerate().rev() {
            h = if self.path[depth / 8] & (128 >> (depth % 8)) == 0 {
                node(&[&[1], &h, sibling])
            } else {
                node(&[&[1], sibling, &h])
            };
        }
        Ok(h)
    }
    pub(crate) fn binding(&self, world: &Digest, leaf: &Digest) -> Result<Digest> {
        ensure!(self.root(leaf)? == *world, "world membership");
        let mut h = crate::transcript(
            b"authenticated resident byte projection",
            &[
                world,
                self.path,
                leaf,
                &(self.siblings.len() as u16).to_le_bytes(),
            ],
        );
        for s in self.siblings {
            h.update(s);
        }
        let mut out = [0; 32];
        h.finalize_xof().read(&mut out);
        Ok(out)
    }
    pub fn prove(
        &self,
        world: &Digest,
        blind: &Digest,
        cell: &[u8],
        st: &Statement,
    ) -> Result<Vec<u8>> {
        opening::prove_with_context(blind, cell, st, &self.binding(world, &st.cell_root)?)
    }
    pub fn verify(
        &self,
        world: &Digest,
        width: usize,
        permitted: &[(u16, u16)],
        st: &Statement,
        proof: &[u8],
    ) -> Result<()> {
        opening::verify_with_context(
            width,
            permitted,
            st,
            &self.binding(world, &st.cell_root)?,
            proof,
        )
    }
}
pub use opening::statement;

/// Private prefix witnesses and framed custody proofs for canonical wire views.
pub mod deployed;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn full_depth_pinned_wire_vector() -> Result<()> {
        let mut path = [0x54; 65];
        path[64] = 0x40;
        let mut siblings: Vec<_> = (0..516).map(|i| [i as u8; 32]).collect();
        let world = Branch {
            path: &path,
            siblings: &siblings,
        }
        .root(&[42; 32])?;
        assert_eq!(
            world,
            [
                0x7f, 0xe3, 0xf1, 0xc7, 0x0f, 0xe5, 0x94, 0x9e, 0x5f, 0xcd, 0xcf, 0xbf, 0x28, 0xec,
                0x86, 0xdc, 0xb9, 0x89, 0xc8, 0x79, 0xb6, 0x1c, 0x65, 0x67, 0xe9, 0xef, 0xf3, 0x7d,
                0xa7, 0x2f, 0xd8, 0xdc
            ]
        );
        path[2] ^= 4;
        assert_ne!(
            world,
            Branch {
                path: &path,
                siblings: &siblings
            }
            .root(&[42; 32])?
        );
        siblings.push([0; 32]);
        assert!(Branch {
            path: &path,
            siblings: &siblings
        }
        .root(&[42; 32])
        .is_err());
        path[64] |= 1;
        assert!(Branch {
            path: &path,
            siblings: &[]
        }
        .root(&[42; 32])
        .is_err());
        Ok(())
    }
}
