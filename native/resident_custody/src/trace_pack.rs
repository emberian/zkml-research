//! Represent a full 32-byte input block by the 256 bits Tr(x β_i).
//! β_i are the little-endian recursive monomials of the Fan–Paar tower.
//! The inverse Gram matrix maps traces to the byte coordinates fed to Keccak.
use std::sync::OnceLock;
type Word = [u64; 4];
type Matrix = [Word; 256];

fn pack(bits: &[u8]) -> Word {
    let mut out = [0; 4];
    for (i, &bit) in bits.iter().enumerate() {
        out[i / 64] |= u64::from(bit) << (i % 64);
    }
    out
}

// Transpose of multiplication by y in T[y]/(y² + g*y + 1):
// (l,h) -> (h,l + mul_g^T(h)). At the bottom g=1.
fn transpose_generator(row: &mut [u8]) {
    let (lo, hi) = row.split_at_mut(row.len() / 2);
    let mut reduced = hi.to_vec();
    if reduced.len() > 1 {
        transpose_generator(&mut reduced);
    }
    for ((l, h), r) in lo.iter_mut().zip(hi).zip(reduced) {
        (*l, *h) = (*h, *l ^ r);
    }
}

fn gram() -> Matrix {
    // Relative trace(a+b*y)=b*g. Compose the eight relative traces.
    let mut tr = vec![1];
    while tr.len() < 256 {
        let mut top = tr.clone();
        if top.len() > 1 {
            transpose_generator(&mut top);
        }
        tr.fill(0);
        tr.extend(top);
    }
    std::array::from_fn(|i| {
        let mut row = tr.clone();
        for level in 0..8 {
            if (i >> level) & 1 != 0 {
                for block in row.chunks_exact_mut(2 << level) {
                    transpose_generator(block);
                }
            }
        }
        pack(&row)
    })
}

fn inverse(mut m: Matrix) -> Matrix {
    let mut inv = std::array::from_fn(|i| {
        let mut row = [0; 4];
        row[i / 64] = 1 << (i % 64);
        row
    });
    for i in 0..256 {
        let bit = 1 << (i % 64);
        let pivot = (i..256)
            .find(|&r| m[r][i / 64] & bit != 0)
            .expect("nondegenerate trace pairing");
        m.swap(i, pivot);
        inv.swap(i, pivot);
        for r in 0..256 {
            if r != i && m[r][i / 64] & bit != 0 {
                for j in 0..4 {
                    m[r][j] ^= m[i][j];
                    inv[r][j] ^= inv[i][j];
                }
            }
        }
    }
    inv
}

fn maps() -> &'static (Matrix, Matrix) {
    static MAPS: OnceLock<(Matrix, Matrix)> = OnceLock::new();
    MAPS.get_or_init(|| {
        let g = gram();
        (g, inverse(g))
    })
}

fn apply(m: &Matrix, bytes: &mut [u8]) {
    // A partial final block uses the identity representation.
    for block in bytes.chunks_exact_mut(32) {
        let x: Word = std::array::from_fn(|j| {
            u64::from_le_bytes(block[j * 8..j * 8 + 8].try_into().unwrap())
        });
        for (byte, rows) in block.iter_mut().zip(m.chunks_exact(8)) {
            *byte = 0;
            for (j, row) in rows.iter().enumerate() {
                let folded = (row[0] & x[0]) ^ (row[1] & x[1]) ^ (row[2] & x[2]) ^ (row[3] & x[3]);
                *byte |= ((folded.count_ones() & 1) as u8) << j;
            }
        }
    }
}
pub(crate) fn encode(bytes: &mut [u8]) {
    apply(&maps().0, bytes)
}
pub(crate) fn decode(bytes: &mut [u8]) {
    apply(&maps().1, bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn deployed_trace_and_every_basis_coordinate() {
        assert_eq!(maps().0[0], [0, 0, 0xc63a6da56da5a557, 0x26c6636dc63a6da5]);
        for i in 0..256 {
            let mut bytes = [0; 32];
            bytes[i / 8] = 1 << (i % 8);
            let original = bytes;
            encode(&mut bytes);
            decode(&mut bytes);
            assert_eq!(bytes, original);
        }
    }
}
