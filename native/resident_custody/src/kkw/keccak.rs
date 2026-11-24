//! Keccak-f[1600] as degree-two constraints with a checkpoint every two rounds.
//!
//! For a row z of the second round's χ output, before ι, the hints p = z0·z2 and
//! q = z0·z3 + z1·z4 make every coordinate of χ⁻¹ quadratic. A pair of rounds commits the
//! 25 lanes after its second round and 10 hints, and checks χ⁻¹ of that state against the
//! forward χ of its first round. A 256-bit squeeze reads lanes 0 to 3 only, so the last pair
//! commits row 0 alone: five lanes and two hints.
use super::gates::{Gates, Lane};

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

#[inline(always)]
fn parity<W: Lane>(s: &[W; 25]) -> [W; 5] {
    let c: [W; 5] = std::array::from_fn(|x| s[x] ^ s[x + 5] ^ s[x + 10] ^ s[x + 15] ^ s[x + 20]);
    std::array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotl(1))
}

/// θ, ρ and π.
fn linear<W: Lane>(s: [W; 25]) -> [W; 25] {
    let d = parity(&s);
    let mut b = [W::zero(); 25];
    for y in 0..5 {
        for x in 0..5 {
            b[y + 5 * ((2 * x + 3 * y) % 5)] = (s[x + 5 * y] ^ d[x]).rotl(ROT[x + 5 * y]);
        }
    }
    b
}

/// Row 0 of θ, ρ and π: π moves the diagonal lanes 0, 6, 12, 18 and 24 there.
fn linear_row0<W: Lane>(s: &[W; 25]) -> [W; 5] {
    let d = parity(s);
    std::array::from_fn(|y| (s[6 * y] ^ d[y]).rotl(ROT[6 * y]))
}

fn chi_clear(b: [u64; 25]) -> [u64; 25] {
    std::array::from_fn(|i| b[i] ^ (!b[i / 5 * 5 + (i + 1) % 5] & b[i / 5 * 5 + (i + 2) % 5]))
}

fn chi<G: Gates>(g: &mut G, b: [G::W; 25]) -> [G::W; 25] {
    let mut out = [G::W::zero(); 25];
    let not = g.constant(u64::MAX);
    for (i, o) in out.iter_mut().enumerate() {
        let x = b[i / 5 * 5 + (i + 1) % 5];
        let y = b[i / 5 * 5 + (i + 2) % 5];
        *o = g.affine(b[i]) ^ g.and(x ^ not, y);
    }
    out
}

/// χ⁻¹ on one row with its two hints, and the two hint equations. Each pair product is
/// reused in every inverse coordinate that needs it.
pub(super) fn inverse<G: Gates>(
    g: &mut G,
    [a, b, c, d, e]: [G::W; 5],
    [p, q]: [G::W; 2],
) -> ([G::W; 5], [G::W; 2]) {
    let ab = g.and(a, b);
    let ac = g.and(a, c);
    let ad = g.and(a, d);
    let ae = g.and(a, e);
    let bc = g.and(b, c);
    let bd = g.and(b, d);
    let be = g.and(b, e);
    let cd = g.and(c, d);
    let ce = g.and(c, e);
    let de = g.and(d, e);
    let pd = g.and(p, d);
    let qd = g.and(q, d);
    let pe = g.and(p, e);
    let qb = g.and(q, b);
    let qc = g.and(q, c);
    (
        [
            g.affine(a ^ c ^ e) ^ bc ^ ad ^ be ^ de ^ qd,
            g.affine(a ^ b ^ d) ^ ac ^ cd ^ ae ^ pe,
            g.affine(b ^ c ^ e) ^ ab ^ bd ^ be ^ de ^ qb,
            g.affine(a ^ c ^ d) ^ bc ^ ae ^ ce ^ pd ^ qc,
            g.affine(b ^ d ^ e) ^ ab ^ ad ^ cd ^ pd,
        ],
        [g.affine(p) ^ ac, g.affine(q) ^ ad ^ be],
    )
}

fn check_row<G: Gates>(g: &mut G, z: [G::W; 5], before: &[G::W]) {
    let hints = [g.alloc(), g.alloc()];
    let (inv, aux) = inverse(g, z, hints);
    for (v, &b) in inv.into_iter().zip(before) {
        g.emit(v ^ b);
    }
    for v in aux {
        g.emit(v);
    }
}

/// Rounds `r` and `r + 1`. Returns the committed state after round `r + 1`.
fn pair<G: Gates>(g: &mut G, s: [G::W; 25], r: usize) -> [G::W; 25] {
    let mut first = chi(g, linear(s));
    first[0] = first[0] ^ g.constant(RC[r]);
    let before = linear(first);
    let next: [G::W; 25] = std::array::from_fn(|_| g.alloc());
    for row in 0..5 {
        let mut z: [G::W; 5] = std::array::from_fn(|c| next[5 * row + c]);
        if row == 0 {
            z[0] = z[0] ^ g.constant(RC[r + 1]);
        }
        check_row(g, z, &before[5 * row..5 * row + 5]);
    }
    next
}

pub(super) fn permute<G: Gates>(g: &mut G, mut s: [G::W; 25]) -> [G::W; 25] {
    for r in (0..24).step_by(2) {
        s = pair(g, s, r);
    }
    s
}

/// The four lanes of a 256-bit squeeze. With a public root they are constants, and only the
/// fifth lane of row 0 and the two hints are committed.
pub(super) fn squeeze<G: Gates>(g: &mut G, mut s: [G::W; 25], root: Option<[u64; 4]>) -> [G::W; 4] {
    for r in (0..22).step_by(2) {
        s = pair(g, s, r);
    }
    let mut first = chi(g, linear(s));
    first[0] = first[0] ^ g.constant(RC[22]);
    let before = linear_row0(&first);
    let lanes: [G::W; 5] = match root {
        None => std::array::from_fn(|_| g.alloc()),
        Some(root) => {
            let last = g.alloc();
            [
                g.constant(root[0]),
                g.constant(root[1]),
                g.constant(root[2]),
                g.constant(root[3]),
                last,
            ]
        }
    };
    let mut z = lanes;
    z[0] = z[0] ^ g.constant(RC[23]);
    check_row(g, z, &before);
    [lanes[0], lanes[1], lanes[2], lanes[3]]
}

fn round(s: [u64; 25], r: usize) -> ([u64; 25], [u64; 25]) {
    let z = chi_clear(linear(s));
    let mut next = z;
    next[0] ^= RC[r];
    (next, z)
}

fn hints(z: &[u64]) -> [u64; 2] {
    [z[0] & z[2], (z[0] & z[3]) ^ (z[1] & z[4])]
}

fn trace_pair(s: [u64; 25], r: usize, out: &mut Vec<u64>) -> [u64; 25] {
    let (s1, _) = round(s, r);
    let (s2, z) = round(s1, r + 1);
    out.extend(s2);
    for row in z.chunks_exact(5) {
        out.extend(hints(row));
    }
    s2
}

pub(super) fn trace_permute(mut s: [u64; 25], out: &mut Vec<u64>) -> [u64; 25] {
    for r in (0..24).step_by(2) {
        s = trace_pair(s, r, out);
    }
    s
}

pub(super) fn trace_squeeze(mut s: [u64; 25], public: bool, out: &mut Vec<u64>) -> [u64; 4] {
    for r in (0..22).step_by(2) {
        s = trace_pair(s, r, out);
    }
    let (s23, _) = round(s, 22);
    let (s24, z) = round(s23, 23);
    if public {
        out.push(s24[4]);
    } else {
        out.extend(&s24[..5]);
    }
    out.extend(hints(&z[..5]));
    [s24[0], s24[1], s24[2], s24[3]]
}

#[cfg(test)]
mod tests {
    use super::super::gates::{Builder, Check, Eval, Trace};
    use super::*;

    /// Words a full permutation commits.
    const PERMUTE_WORDS: usize = 12 * 35;
    /// Words a 256-bit squeeze commits.
    const SQUEEZE_WORDS: usize = 11 * 35 + 7;

    struct Clear;
    impl Gates for Clear {
        type W = u64;
        fn input(&mut self, _: usize) -> u64 {
            0
        }
        fn alloc(&mut self) -> u64 {
            0
        }
        fn constant(&self, c: u64) -> u64 {
            c
        }
        fn and(&mut self, x: u64, y: u64) -> u64 {
            x & y
        }
        fn affine(&self, x: u64) -> u64 {
            x
        }
        fn emit(&mut self, _: u64) {}
    }

    #[test]
    fn all_inverse_rows_and_hints() {
        for x in 0..32 {
            let row: [u64; 5] = std::array::from_fn(|i| ((x >> i) & 1) as u64);
            let z = std::array::from_fn(|i| row[i] ^ (!row[(i + 1) % 5] & row[(i + 2) % 5] & 1));
            let p = z[0] & z[2];
            let q = (z[0] & z[3]) ^ (z[1] & z[4]);
            for h in 0..4 {
                let (decoded, flags) = inverse(&mut Clear, z, [h & 1, h >> 1]);
                assert_eq!(flags == [0, 0], h == p + 2 * q);
                if flags == [0, 0] {
                    assert_eq!(decoded, row);
                }
            }
        }
    }

    #[test]
    fn checkpoints_reproduce_keccak_and_satisfy_their_equations() {
        let mut s = [0u64; 25];
        for (i, lane) in s.iter_mut().enumerate() {
            *lane = 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i as u64 + 1);
        }
        let mut expected = s;
        keccak::f1600(&mut expected);
        let mut words = vec![];
        assert_eq!(trace_permute(s, &mut words), expected);
        assert_eq!(words.len(), PERMUTE_WORDS);
        let mut squeezed = vec![];
        assert_eq!(trace_squeeze(s, false, &mut squeezed), expected[..4]);
        assert_eq!(squeezed.len(), SQUEEZE_WORDS);
        let mut public = vec![];
        trace_squeeze(s, true, &mut public);
        assert_eq!(public.len(), SQUEEZE_WORDS - 4);

        // The input lanes are the private input; every equation of the clear witness is zero,
        // and flipping any committed bit breaks one.
        struct Lanes([u64; 25]);
        impl Lanes {
            fn run<B: Builder>(&self, b: &mut B) {
                let s = std::array::from_fn(|i| b.input(i));
                let out = b.permute(s);
                for (i, w) in out.into_iter().enumerate() {
                    let c = b.constant(self.0[i]);
                    b.assert_zero(w ^ c);
                }
            }
        }
        let input: Vec<u8> = s.iter().flat_map(|w| w.to_le_bytes()).collect();
        let circuit = Lanes(expected);
        let mut t = Trace::new(&input);
        circuit.run(&mut t);
        let witness = [
            input.clone(),
            t.words.iter().flat_map(|w| w.to_le_bytes()).collect(),
        ]
        .concat();
        let mut bad = 0;
        circuit.run(&mut Eval(Check::new(&witness, 200, |v| bad |= v)));
        assert_eq!(bad, 0);
        for bit in [200 * 8, 200 * 8 + 25 * 64 + 3, witness.len() * 8 - 1] {
            let mut flipped = witness.clone();
            flipped[bit / 8] ^= 1 << (bit % 8);
            let mut bad = 0;
            circuit.run(&mut Eval(Check::new(&flipped, 200, |v| bad |= v)));
            assert_ne!(bad, 0, "bit {bit}");
        }
        let mut root_expected = [0; 4];
        root_expected.copy_from_slice(&expected[..4]);
        struct Root([u64; 4]);
        impl Root {
            fn run<B: Builder>(&self, b: &mut B) {
                let s = std::array::from_fn(|i| b.input(i));
                b.squeeze_is(s, self.0);
            }
        }
        let mut t = Trace::new(&input);
        Root(root_expected).run(&mut t);
        let witness = [
            input.clone(),
            t.words.iter().flat_map(|w| w.to_le_bytes()).collect(),
        ]
        .concat();
        for (claimed, ok) in [(root_expected, true), ([1, 2, 3, 4], false)] {
            let mut bad = 0;
            Root(claimed).run(&mut Eval(Check::new(&witness, 200, |v| bad |= v)));
            assert_eq!(bad == 0, ok);
        }
    }
}
