use dlvault::{Key, Reader, Writer, HEADER, TAG};
use std::sync::Arc;
use std::io::{Read, Seek, SeekFrom};

const BS: u32 = 64;

fn dir(tag: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("dlvault-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn plain(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(31).wrapping_add(seed)).collect()
}

/// Seal `p` writing three "columns" back to front, as a column-major tape's writer does in its own order.
fn seal(path: &std::path::Path, key: &Key, role: &str, p: &[u8]) {
    let mut w = Writer::create_bs(path, key, role, p.len() as u64, BS).unwrap();
    let (a, b) = (p.len() / 3, 2 * p.len() / 3);
    for (lo, hi) in [(b, p.len()), (0, a), (a, b)] {
        for c in p[lo..hi].chunks(7).enumerate() {
            w.write_at((lo + 7 * c.0) as u64, c.1).unwrap();
        }
    }
    w.finish().unwrap();
}

fn read_all(path: &std::path::Path, key: &Arc<Key>, role: &str) -> std::io::Result<Vec<u8>> {
    let mut r = Reader::open(path, key.clone(), role)?;
    let mut v = Vec::new();
    r.read_to_end(&mut v)?;
    Ok(v)
}

#[test]
fn roundtrip_and_seek() {
    let d = dir("rt");
    let key = Arc::new(Key::new("dl-vault:t:0:0:00", &[7; 32]));
    let p = plain(1000, 3);
    let f = d.join("a");
    seal(&f, &key, "release|c|0", &p);
    assert_eq!(std::fs::metadata(&f).unwrap().len(), HEADER + 1000 + 16 * TAG);
    assert_eq!(read_all(&f, &key, "release|c|0").unwrap(), p);
    let mut r = Reader::open(&f, key.clone(), "release|c|0").unwrap();
    for off in [999u64, 0, 63, 64, 500, 127] {
        r.seek(SeekFrom::Start(off)).unwrap();
        let mut b = [0u8; 1];
        r.read_exact(&mut b).unwrap();
        assert_eq!(b[0], p[off as usize]);
    }
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn swapped_dropped_spliced_or_foreign_blocks_are_refused() {
    let d = dir("neg");
    let key = Arc::new(Key::new("dl-vault:t:0:0:00", &[7; 32]));
    let p = plain(1000, 3);
    let (a, b) = (d.join("a"), d.join("b"));
    seal(&a, &key, "release|c|0", &p);
    seal(&b, &key, "release|c|0", &p); // the same plaintext, key, role and length: another file id
    let blk = |i: u64| (HEADER + i * (BS as u64 + TAG)) as usize..(HEADER + (i + 1) * (BS as u64 + TAG)) as usize;
    let fa = std::fs::read(&a).unwrap();
    let fb = std::fs::read(&b).unwrap();
    // swapped blocks 2 and 3
    let mut s = fa.clone();
    s[blk(2)].copy_from_slice(&fa[blk(3)]);
    s[blk(3)].copy_from_slice(&fa[blk(2)]);
    std::fs::write(d.join("swap"), &s).unwrap();
    assert!(read_all(&d.join("swap"), &key, "release|c|0").is_err(), "swapped blocks read");
    // the final block dropped (and the file shortened accordingly)
    let last = fa.len() - (1000 % BS as usize + TAG as usize);
    std::fs::write(d.join("drop"), &fa[..last]).unwrap();
    assert!(Reader::open(&d.join("drop"), key.clone(), "release|c|0").is_err(), "a truncated file opened");
    // ... and with the header's length and count rewritten to match (the AAD binds them): block 0 refuses
    let mut t = fa[..last].to_vec();
    t[16..24].copy_from_slice(&(1000u64 - (1000 % BS as u64)).to_le_bytes());
    t[28..32].copy_from_slice(&15u32.to_le_bytes());
    std::fs::write(d.join("drop2"), &t).unwrap();
    assert!(Reader::open(&d.join("drop2"), key.clone(), "release|c|0").is_err(), "a re-headed truncated file opened");
    // a block from another tape spliced in
    let mut s = fa.clone();
    s[blk(5)].copy_from_slice(&fb[blk(5)]);
    std::fs::write(d.join("splice"), &s).unwrap();
    assert!(read_all(&d.join("splice"), &key, "release|c|0").is_err(), "a spliced block read");
    // another role, another key, the zero key (a destroyed key's copy)
    assert!(Reader::open(&a, key.clone(), "release|c|1").is_err());
    assert!(Reader::open(&a, Arc::new(Key::new("dl-vault:t:0:0:00", &[8; 32])), "release|c|0").is_err());
    assert!(Reader::open(&a, Arc::new(Key::new("dl-vault:t:0:0:00", &[0; 32])), "release|c|0").is_err());
    // control: the untouched file still reads
    assert_eq!(read_all(&a, &key, "release|c|0").unwrap(), p);
    std::fs::remove_dir_all(&d).unwrap();
}

#[test]
fn a_writer_refuses_double_writes_and_unfinished_files() {
    let d = dir("w");
    let key = Arc::new(Key::new("dl-vault:t:0:0:00", &[7; 32]));
    let mut w = Writer::create_bs(&d.join("a"), &key, "r", 200, BS).unwrap();
    w.write_at(0, &[1; 64]).unwrap();
    assert!(w.write_at(10, &[1; 4]).is_err(), "a sealed block written again");
    w.write_at(64, &[2; 100]).unwrap();
    assert!(w.finish().is_err(), "an unfinished file was finished");
    assert!(!d.join("a").exists(), "an unfinished file took the final name");
    std::fs::remove_dir_all(&d).unwrap();
}
