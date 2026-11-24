//! Canonical, position-bound GGM and Merkle trees. Padded leaves have
//! no instances and are never serialized.
use super::prg;
use crate::{digest, Digest};
use sha3::digest::XofReader;
pub(super) type Seed = [u8; 16];

pub(super) fn tree(salt: &Digest, id: u32, n: usize, root: Seed) -> Vec<Seed> {
    let mut t = vec![[0; 16]; 2 * n.next_power_of_two()];
    t[1] = root;
    expand(&mut t, salt, id, 1);
    t
}
fn expand(t: &mut [Seed], salt: &Digest, id: u32, i: usize) {
    if i >= t.len() / 2 {
        return;
    }
    let mut d = [0; 32];
    prg(0, salt, id, i as u32, &t[i]).read(&mut d);
    t[2 * i].copy_from_slice(&d[..16]);
    t[2 * i + 1].copy_from_slice(&d[16..]);
    expand(t, salt, id, 2 * i);
    expand(t, salt, id, 2 * i + 1);
}

pub(super) fn frontier(n: usize, hidden: &[usize]) -> Vec<usize> {
    fn walk(
        nodes: &mut Vec<usize>,
        n: usize,
        hidden: &[usize],
        i: usize,
        start: usize,
        size: usize,
    ) {
        if start >= n {
            return;
        }
        if hidden.is_empty() {
            nodes.push(i);
            return;
        }
        if size > 1 {
            let mid = start + size / 2;
            let cut = hidden.partition_point(|&x| x < mid);
            walk(nodes, n, &hidden[..cut], 2 * i, start, size / 2);
            walk(nodes, n, &hidden[cut..], 2 * i + 1, mid, size / 2);
        }
    }
    let mut nodes = vec![];
    walk(&mut nodes, n, hidden, 1, 0, n.next_power_of_two());
    nodes
}

pub(super) fn recover(t: &mut [Seed], salt: &Digest, id: u32, i: usize, seed: Seed) {
    t[i] = seed;
    expand(t, salt, id, i);
}

pub(super) fn merkle(leaves: &[Digest], label: &[u8]) -> Vec<Digest> {
    let size = leaves.len().next_power_of_two();
    let mut t = vec![[0; 32]; 2 * size];
    t[size..size + leaves.len()].copy_from_slice(leaves);
    fill_merkle(&mut t, label, &[]);
    t
}

pub(super) fn fill_merkle(t: &mut [Digest], label: &[u8], frontier: &[usize]) {
    let mut supplied = vec![false; t.len() / 2];
    for &i in frontier {
        if i < supplied.len() {
            supplied[i] = true;
        }
    }
    for i in (1..t.len() / 2).rev() {
        if !supplied[i] {
            t[i] = digest(
                label,
                &[&(i as u32).to_le_bytes(), &t[2 * i], &t[2 * i + 1]],
            );
        }
    }
}
