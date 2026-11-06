//! Registry v2 hashing (ROOTS-V2.md): cSHAKE256 with N = "" and S = "mir13/v2/<kind>", 32-byte output.

use tiny_keccak::{CShake, Hasher};

pub type D = [u8; 32];

pub fn h(kind: &str, parts: &[&[u8]]) -> D {
    let s = format!("mir13/v2/{kind}");
    let mut c = CShake::v256(b"", s.as_bytes());
    for p in parts {
        c.update(p);
    }
    let mut out = [0u8; 32];
    c.finalize(&mut out);
    out
}

pub fn leaf(row: &[u8]) -> D {
    h("leaf", &[row])
}

/// Binary Merkle root; the list is padded to a power of two with H("pad", ""), an empty list is H("empty", "").
pub fn merkle(items: &[D]) -> D {
    if items.is_empty() {
        return h("empty", &[]);
    }
    let pad = h("pad", &[]);
    let mut level: Vec<D> = items.to_vec();
    let n = level.len().next_power_of_two();
    level.resize(n, pad);
    while level.len() > 1 {
        level = level.chunks(2).map(|p| h("node", &[&p[0], &p[1]])).collect();
    }
    level[0]
}

pub fn merkle_par(items: &[D]) -> D {
    use rayon::prelude::*;
    if items.len() < 1 << 14 {
        return merkle(items);
    }
    let pad = h("pad", &[]);
    let mut level: Vec<D> = items.to_vec();
    let n = level.len().next_power_of_two();
    level.resize(n, pad);
    while level.len() > 1 {
        level = level.par_chunks(2).map(|p| h("node", &[&p[0], &p[1]])).collect();
    }
    level[0]
}

pub fn slice_root(nrows: u64, row_elems: u64, leaves: &[D]) -> D {
    let m = merkle_par(leaves);
    h("slice", &[&nrows.to_le_bytes(), &row_elems.to_le_bytes(), &m])
}

pub fn tensor_root(name: &str, dims: &[u64], e: i32, int_bytes: u8, slice_roots: &[D]) -> D {
    let mut pre = vec![];
    pre.extend_from_slice(&(name.len() as u32).to_le_bytes());
    pre.extend_from_slice(name.as_bytes());
    pre.extend_from_slice(&(dims.len() as u32).to_le_bytes());
    for d in dims {
        pre.extend_from_slice(&d.to_le_bytes());
    }
    pre.extend_from_slice(&e.to_le_bytes());
    pre.push(int_bytes);
    pre.extend_from_slice(&(slice_roots.len() as u64).to_le_bytes());
    let m = merkle(slice_roots);
    h("tensor", &[&pre, &m])
}

/// R_{l,e}: the three matrices of routed expert e of layer l, each with its tensor exponent.
pub fn expert_root(layer: u32, expert: u32, parts: &[(i32, D); 3]) -> D {
    let mut pre = vec![];
    pre.extend_from_slice(&layer.to_le_bytes());
    pre.extend_from_slice(&expert.to_le_bytes());
    for (e, r) in parts {
        pre.extend_from_slice(&e.to_le_bytes());
        pre.extend_from_slice(r);
    }
    h("expert", &[&pre])
}

pub fn hex(d: &[u8]) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}
