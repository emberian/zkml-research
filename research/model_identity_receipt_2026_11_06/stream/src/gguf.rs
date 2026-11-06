//! GGUF v3 container: the header, the metadata we need and the tensor table.
//! Spec: ggml docs/gguf.md; FlashProve docs/model.md section 11.1.

use std::io::Read;

pub const F32: u32 = 0;
pub const F16: u32 = 1;
pub const Q8_0: u32 = 8;
pub const Q4_K: u32 = 12;
pub const Q5_K: u32 = 13;
pub const Q6_K: u32 = 14;
pub const BF16: u32 = 30;

/// (elements per block, bytes per block) for the seven storage types section 11.2 reads.
pub fn block_shape(t: u32) -> Option<(u64, u64)> {
    Some(match t {
        F32 => (1, 4),
        F16 => (1, 2),
        BF16 => (1, 2),
        Q8_0 => (32, 34),
        Q4_K => (256, 144),
        Q5_K => (256, 176),
        Q6_K => (256, 210),
        _ => return None,
    })
}

pub fn type_name(t: u32) -> String {
    match t {
        F32 => "F32".into(),
        F16 => "F16".into(),
        BF16 => "BF16".into(),
        Q8_0 => "Q8_0".into(),
        Q4_K => "Q4_K".into(),
        Q5_K => "Q5_K".into(),
        Q6_K => "Q6_K".into(),
        other => format!("type{other}"),
    }
}

#[derive(Clone, Debug)]
pub struct TensorInfo {
    pub name: String,
    pub dims: Vec<u64>,
    pub ggml_type: u32,
    /// offset relative to the start of the data section
    pub rel_offset: u64,
    pub elements: u64,
    /// byte length, None for a storage type outside the seven
    pub n_bytes: Option<u64>,
}

#[derive(Clone, Debug)]
pub struct Header {
    pub architecture: Option<String>,
    pub embedding_length: Option<u64>,
    pub block_count: Option<u64>,
    pub key_length: Option<u64>,
    pub alignment: u64,
    pub tensors: Vec<TensorInfo>,
    /// absolute offset of the data section in the file
    pub data_start: u64,
}

pub struct Counting<R: Read> {
    pub inner: R,
    pub pos: u64,
}
impl<R: Read> Read for Counting<R> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = self.inner.read(buf)?;
        self.pos += n as u64;
        Ok(n)
    }
}

fn rd<const N: usize, R: Read>(r: &mut R) -> std::io::Result<[u8; N]> {
    let mut b = [0u8; N];
    r.read_exact(&mut b)?;
    Ok(b)
}
fn u32le<R: Read>(r: &mut R) -> std::io::Result<u32> {
    Ok(u32::from_le_bytes(rd::<4, _>(r)?))
}
fn u64le<R: Read>(r: &mut R) -> std::io::Result<u64> {
    Ok(u64::from_le_bytes(rd::<8, _>(r)?))
}
fn string<R: Read>(r: &mut R) -> std::io::Result<Vec<u8>> {
    let n = u64le(r)?;
    if n > (1 << 30) {
        return Err(bad("string longer than 1 GiB"));
    }
    let mut v = vec![0u8; n as usize];
    r.read_exact(&mut v)?;
    Ok(v)
}
fn bad(m: &str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, m.to_string())
}

enum Val {
    U(u64),
    S(Vec<u8>),
    Other,
}

fn skip_value<R: Read>(r: &mut R, t: u32) -> std::io::Result<Val> {
    Ok(match t {
        0 | 1 | 7 => Val::U(rd::<1, _>(r)?[0] as u64),
        2 | 3 => Val::U(u16::from_le_bytes(rd::<2, _>(r)?) as u64),
        4 | 5 => Val::U(u32le(r)? as u64),
        6 => {
            rd::<4, _>(r)?;
            Val::Other
        }
        8 => Val::S(string(r)?),
        9 => {
            let et = u32le(r)?;
            let n = u64le(r)?;
            for _ in 0..n {
                skip_value(r, et)?;
            }
            Val::Other
        }
        10 | 11 => Val::U(u64le(r)?),
        12 => {
            rd::<8, _>(r)?;
            Val::Other
        }
        _ => return Err(bad("unknown metadata value type")),
    })
}

/// Parse a GGUF header from the start of a stream. On return the reader is positioned at the
/// first byte after the tensor table (`pos`); the data section starts at `data_start`.
pub fn parse<R: Read>(r: &mut Counting<R>) -> std::io::Result<Header> {
    if &rd::<4, _>(r)? != b"GGUF" {
        return Err(bad("not a GGUF file"));
    }
    if u32le(r)? != 3 {
        return Err(bad("not GGUF version 3"));
    }
    let n_tensors = u64le(r)?;
    let n_kv = u64le(r)?;
    let mut h = Header {
        architecture: None,
        embedding_length: None,
        block_count: None,
        key_length: None,
        alignment: 32,
        tensors: vec![],
        data_start: 0,
    };
    let mut kv: Vec<(String, Val)> = vec![];
    for _ in 0..n_kv {
        let key = String::from_utf8_lossy(&string(r)?).into_owned();
        let t = u32le(r)?;
        let v = skip_value(r, t)?;
        kv.push((key, v));
    }
    for (k, v) in &kv {
        if k == "general.architecture" {
            if let Val::S(s) = v {
                h.architecture = Some(String::from_utf8_lossy(s).into_owned());
            }
        }
        if k == "general.alignment" {
            if let Val::U(a) = v {
                h.alignment = *a;
            }
        }
    }
    if let Some(a) = &h.architecture {
        for (k, v) in &kv {
            if let Val::U(x) = v {
                if *k == format!("{a}.embedding_length") {
                    h.embedding_length = Some(*x)
                }
                if *k == format!("{a}.block_count") {
                    h.block_count = Some(*x)
                }
                if *k == format!("{a}.attention.key_length") {
                    h.key_length = Some(*x)
                }
            }
        }
    }
    for _ in 0..n_tensors {
        let name = String::from_utf8(string(r)?).map_err(|_| bad("tensor name not UTF-8"))?;
        let nd = u32le(r)?;
        if nd == 0 || nd > 4 {
            return Err(bad("tensor with 0 or more than 4 dimensions"));
        }
        let mut dims = vec![];
        for _ in 0..nd {
            dims.push(u64le(r)?);
        }
        let t = u32le(r)?;
        let off = u64le(r)?;
        let elements: u64 = dims.iter().product();
        let n_bytes = block_shape(t).map(|(e, b)| elements / e * b);
        h.tensors.push(TensorInfo { name, dims, ggml_type: t, rel_offset: off, elements, n_bytes });
    }
    let a = h.alignment.max(1);
    h.data_start = r.pos.div_ceil(a) * a;
    Ok(h)
}
