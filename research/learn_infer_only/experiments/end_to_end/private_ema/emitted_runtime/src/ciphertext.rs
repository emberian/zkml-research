//! PEMA0001 envelope compatibility and generic TFHE Boolean gates.
use crate::Backend;
use bincode::Options;
use serde::{de::DeserializeOwned, Serialize};
use std::{
    fs::{self, OpenOptions},
    io::{Read, Write},
    path::Path,
};
use tfhe::boolean::prelude::*;

pub const STATE: u8 = 1;
pub const INPUT: u8 = 2;
pub const QUERY: u8 = 3;
pub const OUTPUT: u8 = 4;
const MAGIC: &[u8; 8] = b"PEMA0001";
const MAX_BITS_BYTES: usize = 64 * 1024 * 1024;
const MAX_KEY_BYTES: usize = 1024 * 1024 * 1024;

#[derive(Default, Debug, Serialize)]
pub struct Calls {
    pub xor: usize,
    pub and: usize,
    pub trivial_encrypt: usize,
}

pub struct TfheBoolean<'a> {
    pub key: &'a ServerKey,
    pub calls: Calls,
}
impl Backend for TfheBoolean<'_> {
    type Bit = Ciphertext;
    fn constant(&mut self, value: bool) -> Ciphertext {
        self.calls.trivial_encrypt += 1;
        self.key.trivial_encrypt(value)
    }
    fn xor(&mut self, a: &Ciphertext, b: &Ciphertext) -> Ciphertext {
        self.calls.xor += 1;
        self.key.xor(a, b)
    }
    fn and(&mut self, a: &Ciphertext, b: &Ciphertext) -> Ciphertext {
        self.calls.and += 1;
        self.key.and(a, b)
    }
}

pub fn read_limited(path: &Path, maximum: usize) -> Result<Vec<u8>, String> {
    let file = fs::File::open(path).map_err(|e| format!("open input: {e}"))?;
    let mut bytes = Vec::new();
    file.take((maximum + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("read input: {e}"))?;
    if bytes.len() > maximum {
        return Err("input exceeds byte limit".into());
    }
    Ok(bytes)
}

fn decode_canonical<T: DeserializeOwned + Serialize>(bytes: &[u8]) -> Result<T, String> {
    // Default free bincode functions use fixed-width integers. Reject trailing data
    // explicitly and retain the preceding probe's reserialization equality check.
    let decoded: T = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(bytes.len() as u64)
        .reject_trailing_bytes()
        .deserialize(bytes)
        .map_err(|e| format!("decode bincode: {e}"))?;
    let encoded = bincode::serialize(&decoded).map_err(|e| format!("reencode bincode: {e}"))?;
    if encoded != bytes {
        return Err("noncanonical bincode bytes".into());
    }
    Ok(decoded)
}

pub fn read_server_key(path: &Path) -> Result<ServerKey, String> {
    decode_canonical(&read_limited(path, MAX_KEY_BYTES)?)
}

pub fn require_encrypted(bits: &[Ciphertext]) -> Result<(), String> {
    if bits.iter().any(|b| !matches!(b, Ciphertext::Encrypted(_))) {
        return Err("artifact bits must all be Encrypted variants".into());
    }
    Ok(())
}

pub fn read_bits(path: &Path, kind: u8, count: usize) -> Result<Vec<Ciphertext>, String> {
    let bytes = read_limited(path, MAX_BITS_BYTES)?;
    if bytes.len() < 17 || &bytes[..8] != MAGIC {
        return Err("invalid PEMA0001 envelope".into());
    }
    if bytes[8] != kind {
        return Err("ciphertext envelope kind mismatch".into());
    }
    let length = u64::from_le_bytes(
        bytes[9..17]
            .try_into()
            .map_err(|_| "invalid envelope length")?,
    );
    if length != (bytes.len() - 17) as u64 {
        return Err("ciphertext envelope length mismatch".into());
    }
    let bits: Vec<Ciphertext> = decode_canonical(&bytes[17..])?;
    if bits.len() != count {
        return Err("ciphertext bit count mismatch".into());
    }
    require_encrypted(&bits)?;
    Ok(bits)
}

pub fn write_bits_new(path: &Path, kind: u8, bits: &[Ciphertext]) -> Result<usize, String> {
    require_encrypted(bits)?;
    let payload = bincode::serialize(bits).map_err(|e| format!("serialize bits: {e}"))?;
    let mut bytes = Vec::with_capacity(17 + payload.len());
    bytes.extend_from_slice(MAGIC);
    bytes.push(kind);
    bytes.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    bytes.extend(payload);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|e| format!("create new output: {e}"))?;
    file.write_all(&bytes)
        .map_err(|e| format!("write output: {e}"))?;
    file.sync_all().map_err(|e| format!("sync output: {e}"))?;
    Ok(bytes.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generic_bincode_compatibility_and_trailing_rejection() {
        let original = vec![1u32, 2, 3];
        let bytes = bincode::serialize(&original).unwrap();
        assert_eq!(decode_canonical::<Vec<u32>>(&bytes).unwrap(), original);
        let mut trailing = bytes;
        trailing.push(0);
        assert!(decode_canonical::<Vec<u32>>(&trailing).is_err());
    }

    #[test]
    fn public_constants_cannot_be_artifact_outputs() {
        assert!(require_encrypted(&[Ciphertext::Trivial(false)]).is_err());
        assert!(require_encrypted(&[Ciphertext::Trivial(true)]).is_err());
    }
}
