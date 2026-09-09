//! Caller-selected signed class sums for one eight-class SIMD bank.
//! This command possesses the full reader key; proof acceptance belongs to its caller.
use fhe::bfv::{BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, SecretKey};
use fhe_math::rq::Representation;
use fhe_traits::{DeserializeParametrized, FheDecoder, FheDecrypter, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{error::Error, fs, io::Read, path::Path, sync::Arc};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
const N: usize = 8192;
const LANES: usize = 8;
const CAPACITY: u8 = 8;
const DOT_BOUND: i64 = 20000;
const T: u64 = 4294475777;
const Q: [u64; 4] = [
    1125899906826241,
    1125899906629633,
    1125899905744897,
    1125899905351681,
];

fn hash(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}

fn read(p: &Path, max: usize) -> Result<Vec<u8>> {
    let f = fs::File::open(p)?;
    if f.metadata()?.len() > max as u64 {
        return Err(format!("file exceeds {max}-byte limit: {}", p.display()).into());
    }
    let mut b = Vec::new();
    f.take(max as u64 + 1).read_to_end(&mut b)?;
    if b.len() > max {
        return Err(format!("file exceeds {max}-byte limit: {}", p.display()).into());
    }
    Ok(b)
}

fn params() -> Result<Arc<BfvParameters>> {
    Ok(BfvParametersBuilder::new()
        .set_degree(N)
        .set_plaintext_modulus(T)
        .set_moduli(&Q)
        .set_variance(10)
        .build_arc()?)
}

fn digest_argument(value: &str, name: &str) -> Result<()> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|x| x.is_ascii_digit() || (b'a'..=b'f').contains(&x))
    {
        return Err(format!("{name} must be exactly 64 lowercase hexadecimal characters").into());
    }
    Ok(())
}

fn counts_argument(encoded: &str) -> Result<[u8; LANES]> {
    let counts: [u8; LANES] = serde_json::from_str(encoded)
        .map_err(|e| format!("COUNTS_JSON must be a literal JSON array of eight integers: {e}"))?;
    if counts.iter().any(|&count| count > CAPACITY) {
        return Err("each class count must be in 0..8".into());
    }
    Ok(counts)
}

fn read_class_sums(
    issuer: &Path,
    dot_path: &Path,
    expected_dot: &str,
    expected_key: &str,
    counts: [u8; LANES],
) -> Result<()> {
    // Public identities and canonical ciphertext shape precede any private-key read.
    let public_key_bytes = read(&issuer.join("evaluation.key"), 16 << 20)?;
    if hash(&public_key_bytes) != expected_key {
        return Err("evaluation-key SHA-256 mismatch".into());
    }
    let encoded = read(dot_path, 2 << 20)?;
    if hash(&encoded) != expected_dot {
        return Err("dot-ciphertext SHA-256 mismatch".into());
    }
    let p = params()?;
    let ciphertext = Ciphertext::from_bytes(&encoded, &p)?;
    if ciphertext.len() != 2 || ciphertext.to_bytes() != encoded {
        return Err("ciphertext must have two components and canonical serialization".into());
    }
    for poly in ciphertext.iter() {
        if p.level_of_context(poly.ctx())? != 0
            || *poly.representation() != Representation::Ntt
            || poly.coefficients().nrows() != Q.len()
            || poly.coefficients().ncols() != N
            || poly
                .coefficients()
                .outer_iter()
                .zip(Q)
                .any(|(row, prime)| row.iter().any(|&x| x >= prime))
        {
            return Err("ciphertext must have canonical level-zero NTT residues".into());
        }
    }

    let secret = SecretKey::from_bytes(&read(&issuer.join(".private/reader.key"), 2 << 20)?, &p)?;
    let values = Vec::<u64>::try_decode(&secret.try_decrypt(&ciphertext)?, Encoding::simd())?;
    if values.len() != N || values.iter().any(|&x| x >= T) {
        return Err("decryption must contain 8192 canonical plaintext residues".into());
    }
    if values
        .iter()
        .enumerate()
        .any(|(index, &value)| value != values[index % LANES])
    {
        return Err("all 8192 slots must repeat the same eight class sums".into());
    }
    let class_sums: Vec<i64> = values[..LANES]
        .iter()
        .map(|&x| {
            if x > T / 2 {
                x as i64 - T as i64
            } else {
                x as i64
            }
        })
        .collect();
    let bounds = counts.map(|count| DOT_BOUND * i64::from(count));
    for (lane, (&sum, &bound)) in class_sums.iter().zip(&bounds).enumerate() {
        if !(-bound..=bound).contains(&sum) {
            return Err(format!(
                "class lane {lane} exceeds its count-dependent signed bound {bound}"
            )
            .into());
        }
    }
    let signed_sum: i64 = class_sums.iter().sum();
    println!(
        "{}",
        json!({
            "schema": "packed-class-sum-reader-v1",
            "dot_ciphertext_sha256": expected_dot,
            "evaluation_key_sha256": expected_key,
            "class_sums": class_sums,
            "sum_values": class_sums,
            "signed_sum": signed_sum,
            "counts": counts,
            "per_class_signed_bounds": bounds,
            "signed_bound": DOT_BOUND * i64::from(CAPACITY),
            "all8192_slots_repeat8": true,
            "zero_empty_lanes": true,
            "full_reader_key": true,
            "scope": "Signed BFV class sums with caller-supplied accepted counts. Full reader capability remains. Proof/controller acceptance is the caller's responsibility."
        })
    );
    Ok(())
}

fn main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 7 || a[1] != "read" {
        return Err("usage: read ISSUER DOT_CT DOT_SHA256 EVALKEY_SHA256 COUNTS_JSON".into());
    }
    digest_argument(&a[4], "DOT_SHA256")?;
    digest_argument(&a[5], "EVALKEY_SHA256")?;
    let counts = counts_argument(&a[6])?;
    read_class_sums(Path::new(&a[2]), Path::new(&a[3]), &a[4], &a[5], counts)
}
