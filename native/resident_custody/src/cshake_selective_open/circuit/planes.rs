//! A bit plane contains the same Keccak bit from each of 64 party tapes.
//! Only affine shares and the polarization of AND are evaluated online.
//! A local AND of two party shares would omit the Beaver cross terms.
use super::*;
use crate::cshake_selective_open::framed::ROT;

#[derive(Copy, Clone)]
pub(super) struct Plane([u64; 64]);
impl BitXor for Plane {
    type Output = Self;
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] ^ rhs.0[i]))
    }
}

impl Lane for Plane {
    fn constant(x: u64) -> Self {
        Self(std::array::from_fn(|i| 0u64.wrapping_sub((x >> i) & 1)))
    }
    fn linear_state(s: [Self; 25]) -> [Self; 25] {
        let c: [Self; 5] =
            std::array::from_fn(|i| s[i] ^ s[i + 5] ^ s[i + 10] ^ s[i + 15] ^ s[i + 20]);
        let d: [Self; 5] = std::array::from_fn(|i| {
            Self(std::array::from_fn(|z| {
                c[(i + 4) % 5].0[z] ^ c[(i + 1) % 5].0[(z + 63) % 64]
            }))
        });
        let mut out = [Self([0; 64]); 25];
        for y in 0..5 {
            for x in 0..5 {
                let i = x + 5 * y;
                let lane = s[i] ^ d[x];
                let offset = 64 - ROT[i] as usize;
                out[y + 5 * ((2 * x + 3 * y) % 5)] =
                    Self(std::array::from_fn(|z| lane.0[(z + offset) % 64]));
            }
        }
        out
    }
}

struct Polarized<'a>(std::slice::Iter<'a, (u64, u64)>);
impl Gates for Polarized<'_> {
    type Word = Plane;
    #[inline(always)]
    fn and(&mut self, x: Plane, y: Plane) -> Plane {
        let &(a, b) = self.0.next().unwrap();
        let a = Plane::constant(a);
        let b = Plane::constant(b);
        Plane(std::array::from_fn(|z| {
            (x.0[z] & b.0[z]) ^ (y.0[z] & a.0[z])
        }))
    }
}

// Six butterfly exchanges transpose a 64-by-64 matrix, LSB first in both axes.
#[inline]
fn transpose(m: &mut [u64; 64]) {
    #[inline(always)]
    fn swap<const S: usize>(m: &mut [u64; 64], mask: u64) {
        for rows in m.chunks_exact_mut(2 * S) {
            let (a, b) = rows.split_at_mut(S);
            for (x, y) in a.iter_mut().zip(b) {
                let t = ((*x >> S) ^ *y) & mask;
                *x ^= t << S;
                *y ^= t;
            }
        }
    }
    swap::<1>(m, 0x5555_5555_5555_5555);
    swap::<2>(m, 0x3333_3333_3333_3333);
    swap::<4>(m, 0x0f0f_0f0f_0f0f_0f0f);
    swap::<8>(m, 0x00ff_00ff_00ff_00ff);
    swap::<16>(m, 0x0000_ffff_0000_ffff);
    swap::<32>(m, 0x0000_0000_ffff_ffff);
}

fn slice(tapes: &[u8], stride: usize, start: usize, end: usize) -> Plane {
    let keep = u64::MAX >> (8 * (8 - (end - start).min(8)));
    let load = |p: usize| {
        let at = p * stride + start;
        u64::from_le_bytes(tapes[at..at + 8].try_into().unwrap()) & keep
    };
    let mut plane = std::array::from_fn(load);
    transpose(&mut plane);
    Plane(plane)
}

impl TraceCircuit<'_> {
    pub(in crate::cshake_selective_open) fn party_messages(
        &self,
        tapes: &[u8],
        masked: &Masked,
        batch: &Batch,
        pads: &[Digest],
    ) -> Vec<Digest> {
        const {
            assert!(PARTIES == 64);
        }
        let stride = self.len();
        let state = std::array::from_fn(|i| {
            if i * 8 < self.input_len {
                slice(tapes, stride, i * 8, self.input_len)
            } else {
                Plane([0; 64])
            }
        });
        let words = (self.input_len..stride)
            .step_by(8)
            .map(|i| slice(tapes, stride, i, stride));
        let len = 8 * CHECKS + self.st.projected_bytes.len();
        let mut residuals = vec![0; len * PARTIES];
        let mut index = 0;
        self.equations(state, words, &mut Polarized(masked.wires.iter()), |lane| {
            let mut words = lane.0;
            transpose(&mut words);
            for (p, word) in words.into_iter().enumerate() {
                residuals[p * len + index..p * len + index + 8]
                    .copy_from_slice(&word.to_le_bytes());
            }
            index += 8;
        });
        residuals
            .chunks_exact_mut(len)
            .zip(tapes.chunks_exact(stride))
            .zip(pads)
            .map(|((residual, tape), pad)| {
                let mut tail = &mut residual[8 * CHECKS..];
                for &(a, b) in &self.st.ranges {
                    let bytes = &tape[32 + usize::from(a)..32 + usize::from(b)];
                    let (dst, next) = tail.split_at_mut(bytes.len());
                    dst.copy_from_slice(bytes);
                    tail = next;
                }
                let mut d = batch.hash(residual);
                xor(&mut d, pad);
                d
            })
            .collect()
    }
}
