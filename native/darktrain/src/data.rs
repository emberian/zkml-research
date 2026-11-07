//! MNIST from the official IDX files, checked against pinned digests before parsing (downloads are untrusted).
//! Sources: https://ossci-datasets.s3.amazonaws.com/mnist/ (torchvision's mirror), cross-checked against
//! https://storage.googleapis.com/cvdf-datasets/mnist/; the gzip md5s equal torchvision's published ones.
use sha2::{Digest, Sha256};
use std::path::Path;

/// (file, sha256 of the decompressed IDX file, sha256 of the .gz as downloaded)
pub const MNIST: [(&str, &str, &str); 4] = [
    ("train-images-idx3-ubyte", "ba891046e6505d7aadcbbe25680a0738ad16aec93bde7f9b65e87a2fc25776db", "440fcabf73cc546fa21475e81ea370265605f56be210a4024d2ca8f203523609"),
    ("train-labels-idx1-ubyte", "65a50cbbf4e906d70832878ad85ccda5333a97f0f4c3dd2ef09a8a9eef7101c5", "3552534a0a558bbed6aed32b30c495cca23d567ec52cac8be1a0730e8010255c"),
    ("t10k-images-idx3-ubyte", "0fa7898d509279e482958e8ce81c8e77db3f2f8254e26661ceb7762c4d494ce7", "8d422c7b0a1c1c79245a5bcf07fe86e33eeafee792b84584aec276f5a2dbc4e6"),
    ("t10k-labels-idx1-ubyte", "ff7bcfd416de33731a308c3f266cc351222c34898ecbeaf847f06e48f7ec33f2", "f7ae60f92e00ec6debd23a6088c31dbd2371eca3ffa0defaefb259924204aec6"),
];

pub struct Split {
    /// n images of 784 bytes, row-major 28 x 28
    pub img: Vec<u8>,
    pub lab: Vec<u8>,
    pub n: usize,
}

pub struct Mnist {
    pub train: Split,
    pub test: Split,
}

fn read_checked(dir: &Path, name: &str, want: &str) -> Result<Vec<u8>, String> {
    let b = std::fs::read(dir.join(name)).map_err(|e| format!("{name}: {e}"))?;
    let got = pycompat::repr::hex(&Sha256::digest(&b));
    if got != want {
        return Err(format!("{name}: sha256 {got} != pinned {want}"));
    }
    Ok(b)
}

fn be32(b: &[u8], o: usize) -> usize {
    u32::from_be_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]]) as usize
}

fn split(dir: &Path, im: (&str, &str), lb: (&str, &str)) -> Result<Split, String> {
    let i = read_checked(dir, im.0, im.1)?;
    let l = read_checked(dir, lb.0, lb.1)?;
    if be32(&i, 0) != 0x0803 || be32(&l, 0) != 0x0801 {
        return Err("bad IDX magic".into());
    }
    let n = be32(&i, 4);
    if be32(&l, 4) != n || be32(&i, 8) != 28 || be32(&i, 12) != 28 || i.len() != 16 + n * 784 || l.len() != 8 + n {
        return Err("bad IDX dims".into());
    }
    let lab = l[8..].to_vec();
    if lab.iter().any(|&c| c > 9) {
        return Err("label out of range".into());
    }
    Ok(Split { img: i[16..].to_vec(), lab, n })
}

pub fn load(dir: &Path) -> Result<Mnist, String> {
    let f = |k: usize| (MNIST[k].0, MNIST[k].1);
    Ok(Mnist { train: split(dir, f(0), f(1))?, test: split(dir, f(2), f(3))? })
}

impl Split {
    pub fn image(&self, k: usize) -> &[u8] {
        &self.img[k * 784..(k + 1) * 784]
    }
}
