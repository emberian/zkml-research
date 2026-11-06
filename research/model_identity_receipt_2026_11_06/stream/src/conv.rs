//! FlashProve docs/model.md section 11: stored blocks -> decoded values v -> products p -> integers w.
//! Every f32 operation below is one IEEE binary32 operation; Rust never contracts a*b+c into an FMA.

use crate::gguf::*;
use half::f16;

pub const WIDTH: u64 = 5120;
pub const HEAD_DIMENSION: u64 = 128;
pub const NORM_CONSTANT: f32 = unsafe { std::mem::transmute::<u32, f32>(0x3F8F1BBD) };
pub const QUERY_CONSTANT: f32 = unsafe { std::mem::transmute::<u32, f32>(0x3DCA62C2) };
pub const LARGEST_MATRIX_INTEGER: i64 = 4095;
pub const EMBEDDING_BOUND: i64 = 1 << 30;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Role {
    Embedding,
    /// a matrix, with the norm it reads and the constant
    Matrix,
    Norm,
}

#[derive(Clone, Debug)]
pub struct Use {
    pub role: Role,
    pub norm: Option<(String, f32)>,
}

const LAYER_KINDS: &[(&str, Option<(&str, bool)>)] = &[
    ("attn_q", Some(("attn_norm", true))),
    ("attn_k", Some(("attn_norm", false))),
    ("attn_v", Some(("attn_norm", false))),
    ("attn_output", None),
    ("ffn_gate", Some(("ffn_norm", false))),
    ("ffn_up", Some(("ffn_norm", false))),
    ("ffn_down", None),
    ("ffn_gate_inp", Some(("ffn_norm", false))),
    ("ffn_gate_shexp", Some(("ffn_norm", false))),
    ("ffn_up_shexp", Some(("ffn_norm", false))),
    ("ffn_down_shexp", None),
    ("ffn_gate_exps", Some(("ffn_norm", false))),
    ("ffn_up_exps", Some(("ffn_norm", false))),
    ("ffn_down_exps", None),
];

/// (layer, kind) of a name blk.<l>.<kind>.weight with l decimal and no leading zero.
pub fn layer_kind(name: &str) -> Option<(u64, &str)> {
    let rest = name.strip_prefix("blk.")?;
    let dot = rest.find('.')?;
    let digits = &rest[..dot];
    if digits.is_empty() || digits.len() > 9 || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if digits.len() > 1 && digits.starts_with('0') {
        return None;
    }
    let kind = rest[dot + 1..].strip_suffix(".weight")?;
    Some((digits.parse().ok()?, kind))
}

/// The rule's classification (weight_sums.cpp classify / weight_sums.py select).
pub fn classify(name: &str) -> Option<Use> {
    if name == "token_embd.weight" {
        return Some(Use { role: Role::Embedding, norm: None });
    }
    if name == "output.weight" {
        return Some(Use { role: Role::Matrix, norm: Some(("output_norm.weight".into(), NORM_CONSTANT)) });
    }
    if name == "output_norm.weight" {
        return Some(Use { role: Role::Norm, norm: None });
    }
    let (l, kind) = layer_kind(name)?;
    if kind == "attn_norm" || kind == "ffn_norm" {
        return Some(Use { role: Role::Norm, norm: None });
    }
    for (k, n) in LAYER_KINDS {
        if *k == kind {
            let norm = n.map(|(nk, q)| (format!("blk.{l}.{nk}.weight"), if q { QUERY_CONSTANT } else { NORM_CONSTANT }));
            return Some(Use { role: Role::Matrix, norm });
        }
    }
    None
}

#[inline]
fn le16(b: &[u8]) -> u16 {
    u16::from_le_bytes([b[0], b[1]])
}
#[inline]
fn h2f(b: &[u8]) -> f32 {
    f16::from_bits(le16(b)).to_f32()
}

#[inline]
fn scale_and_minimum(s: &[u8], j: usize) -> (u8, u8) {
    if j < 4 {
        (s[j] & 63, s[j + 4] & 63)
    } else {
        ((s[j + 4] & 15) | ((s[j - 4] >> 6) << 4), (s[j + 4] >> 4) | ((s[j] >> 6) << 4))
    }
}

fn decode_q4_or_q5(block: &[u8], fifth: Option<&[u8]>, codes: &[u8], out: &mut [f32]) {
    let d = h2f(&block[0..2]);
    let dmin = h2f(&block[2..4]);
    for j in 0..8 {
        let (sc, mn) = scale_and_minimum(&block[4..16], j);
        let step = d * (sc as f32);
        let lowest = dmin * (mn as f32);
        let bytes = &codes[32 * (j / 2)..32 * (j / 2) + 32];
        let shift = 4 * (j % 2);
        for i in 0..32 {
            let mut q = ((bytes[i] >> shift) & 15) as i32;
            if let Some(f) = fifth {
                q += (((f[i] >> j) & 1) as i32) << 4;
            }
            let product = step * (q as f32);
            out[32 * j + i] = product - lowest;
        }
    }
}

fn decode_q6(block: &[u8], out: &mut [f32]) {
    let ql = &block[0..128];
    let qh = &block[128..192];
    let scales = &block[192..208];
    let d = h2f(&block[208..210]);
    let mut steps = [0f32; 16];
    for k in 0..16 {
        steps[k] = d * ((scales[k] as i8) as f32);
    }
    for a in 0..2 {
        for t in 0..4 {
            for c in 0..32 {
                let low = ((ql[64 * a + 32 * (t % 2) + c] >> (4 * (t / 2))) & 15) as i32;
                let high = ((qh[32 * a + c] >> (2 * t)) & 3) as i32;
                let n = 128 * a + 32 * t + c;
                out[n] = steps[n / 16] * (((low | (high << 4)) - 32) as f32);
            }
        }
    }
}

/// Decode `out.len()` elements from `bytes` (whole blocks).
pub fn decode(t: u32, bytes: &[u8], out: &mut [f32]) {
    let n = out.len();
    match t {
        Q4_K => {
            for b in 0..n / 256 {
                let blk = &bytes[b * 144..b * 144 + 144];
                decode_q4_or_q5(blk, None, &blk[16..], &mut out[b * 256..b * 256 + 256]);
            }
        }
        Q5_K => {
            for b in 0..n / 256 {
                let blk = &bytes[b * 176..b * 176 + 176];
                decode_q4_or_q5(blk, Some(&blk[16..48]), &blk[48..], &mut out[b * 256..b * 256 + 256]);
            }
        }
        Q6_K => {
            for b in 0..n / 256 {
                decode_q6(&bytes[b * 210..b * 210 + 210], &mut out[b * 256..b * 256 + 256]);
            }
        }
        Q8_0 => {
            for b in 0..n / 32 {
                let blk = &bytes[b * 34..b * 34 + 34];
                let d = h2f(&blk[0..2]);
                for i in 0..32 {
                    out[b * 32 + i] = d * ((blk[2 + i] as i8) as f32);
                }
            }
        }
        F16 => {
            for i in 0..n {
                out[i] = h2f(&bytes[2 * i..2 * i + 2]);
            }
        }
        BF16 => {
            for i in 0..n {
                out[i] = f32::from_bits((le16(&bytes[2 * i..2 * i + 2]) as u32) << 16);
            }
        }
        _ => {
            for i in 0..n {
                out[i] = f32::from_le_bytes([bytes[4 * i], bytes[4 * i + 1], bytes[4 * i + 2], bytes[4 * i + 3]]);
            }
        }
    }
}

/// Products of one row: p = RN32(gamma_k * v) or v.
#[inline]
pub fn products(v: &mut [f32], gamma: Option<&[f32]>) {
    if let Some(g) = gamma {
        for (x, gk) in v.iter_mut().zip(g.iter()) {
            *x = *gk * *x;
        }
    }
}

/// The largest e with RNE(2^e * largest) <= 4095, for finite largest > 0 (weight_sums.py exponent_of).
pub fn exponent_of(largest: f32) -> i32 {
    let x = largest as f64;
    // frexp: x = m * 2^ex with m in [0.5, 1)
    let bits = x.to_bits();
    let raw = ((bits >> 52) & 0x7ff) as i32;
    assert!(raw != 0 && raw != 0x7ff, "exponent_of needs a normal binary64");
    let ex = raw - 1022;
    let mut e = 12 - ex;
    if x * pow2(e) >= LARGEST_MATRIX_INTEGER as f64 + 0.5 {
        e -= 1;
    }
    e
}

/// w = RNE(2^e * p), exact in binary64 for |e| <= 100.
#[inline]
pub fn integer(p: f32, scale: f64) -> i64 {
    ((p as f64) * scale).round_ties_even() as i64
}

/// 2^e as an exact binary64, for -1022 <= e <= 1023.
pub fn pow2(e: i32) -> f64 {
    assert!((-1022..=1023).contains(&e));
    f64::from_bits(((e + 1023) as u64) << 52)
}
