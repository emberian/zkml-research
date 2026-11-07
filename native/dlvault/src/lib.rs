//! DLVAULT2: a sealed file too large to seal or open whole (the release tape, gigabytes), in fixed blocks.
//!
//! Layout: `DLVAULT2 | file id (8) | plaintext length (8, LE) | block size (4, LE) | block count (4, LE)` (32 bytes),
//! then block b (b = 0 .. count-1) at 32 + b (BS + 16): ChaCha20-Poly1305 of plaintext bytes [b BS, min((b+1) BS, len))
//! and its 16-byte tag. Nonce: file id | b (u32 BE). AAD: `dl-vault2|<key name>|<role>|<file id hex>|<b>|<count>|<len>|<BS>`.
//! So a block opens only under its own key, role and file, in its own place, in a file of its own length:
//! reordered, dropped, truncated or spliced blocks (or a changed header) are refused. The key is the seat's epoch
//! file key (darkhand::vault, which DLVAULT1 files share); destroying it erases the file wherever its blocks are.
//!
//! The writer takes bytes at any offset, each byte exactly once (a column-major tape is written column by column):
//! a block is sealed and written as soon as it is full, so only partly written blocks are held in memory.
//! The reader implements Read + Seek over the plaintext, opening one block at a time.
use ring::aead::{Aad, LessSafeKey, Nonce, UnboundKey, CHACHA20_POLY1305};
use std::collections::BTreeMap;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

pub const MAGIC: &[u8; 8] = b"DLVAULT2";
pub const HEADER: u64 = 32;
pub const TAG: u64 = 16;
pub const BLOCK: u32 = 1 << 20;

/// A file key and its keyring name (the name is in every block's AAD). Zeroed on drop.
pub struct Key {
    name: String,
    key: Box<[u8; 32]>,
}

impl Key {
    pub fn new(name: &str, key: &[u8; 32]) -> Key {
        Key { name: name.to_string(), key: Box::new(*key) }
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    fn aead(&self) -> LessSafeKey {
        LessSafeKey::new(UnboundKey::new(&CHACHA20_POLY1305, &self.key[..]).expect("32-byte key"))
    }
}

impl std::fmt::Debug for Key {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Key({})", self.name)
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        for b in self.key.iter_mut() {
            unsafe { std::ptr::write_volatile(b, 0) };
        }
    }
}

struct Geom {
    id: [u8; 8],
    len: u64,
    bs: u32,
    count: u32,
}

impl Geom {
    fn aad(&self, key: &Key, role: &str, b: u32) -> Vec<u8> {
        let id: String = self.id.iter().map(|x| format!("{x:02x}")).collect();
        format!("dl-vault2|{}|{role}|{id}|{b}|{}|{}|{}", key.name, self.count, self.len, self.bs).into_bytes()
    }
    fn nonce(&self, b: u32) -> Nonce {
        let mut n = [0u8; 12];
        n[..8].copy_from_slice(&self.id);
        n[8..].copy_from_slice(&b.to_be_bytes());
        Nonce::assume_unique_for_key(n)
    }
    fn plain_len(&self, b: u32) -> usize {
        (self.len - b as u64 * self.bs as u64).min(self.bs as u64) as usize
    }
    fn at(&self, b: u32) -> u64 {
        HEADER + b as u64 * (self.bs as u64 + TAG)
    }
    fn file_len(&self) -> u64 {
        HEADER + self.len + self.count as u64 * TAG
    }
    fn header(&self) -> [u8; 32] {
        let mut h = [0u8; 32];
        h[..8].copy_from_slice(MAGIC);
        h[8..16].copy_from_slice(&self.id);
        h[16..24].copy_from_slice(&self.len.to_le_bytes());
        h[24..28].copy_from_slice(&self.bs.to_le_bytes());
        h[28..32].copy_from_slice(&self.count.to_le_bytes());
        h
    }
}

/// Writes a DLVAULT2 file of a known plaintext length: `write_at` in any order, each byte once; `finish` checks that
/// every block was sealed, syncs, and renames the temporary file over `path`.
pub struct Writer<'k> {
    key: &'k Key,
    role: String,
    g: Geom,
    f: std::fs::File,
    tmp: PathBuf,
    path: PathBuf,
    /// partly written blocks: (buffer, bytes written)
    open: BTreeMap<u32, (Vec<u8>, usize)>,
    sealed: Vec<bool>,
}

impl<'k> Writer<'k> {
    pub fn create(path: &Path, key: &'k Key, role: &str, len: u64) -> std::io::Result<Writer<'k>> {
        Self::create_bs(path, key, role, len, BLOCK)
    }
    /// With another block size (tests: many blocks from a small file).
    pub fn create_bs(path: &Path, key: &'k Key, role: &str, len: u64, bs: u32) -> std::io::Result<Writer<'k>> {
        let count = len.div_ceil(bs as u64);
        let count = u32::try_from(count).map_err(|_| std::io::Error::other("too many blocks"))?;
        let mut id = [0u8; 8];
        getrandom::getrandom(&mut id).map_err(|e| std::io::Error::other(e.to_string()))?;
        let g = Geom { id, len, bs, count };
        let tmp = path.with_extension("sealing");
        let mut o = std::fs::OpenOptions::new();
        o.write(true).create(true).truncate(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            o.mode(0o600);
        }
        let mut f = o.open(&tmp)?;
        f.write_all(&g.header())?;
        f.set_len(g.file_len())?;
        Ok(Writer { key, role: role.to_string(), g, f, tmp, path: path.to_path_buf(), open: BTreeMap::new(), sealed: vec![false; count as usize] })
    }

    pub fn write_at(&mut self, mut off: u64, mut data: &[u8]) -> std::io::Result<()> {
        if off + data.len() as u64 > self.g.len {
            return Err(std::io::Error::other("write past the declared length"));
        }
        while !data.is_empty() {
            let b = (off / self.g.bs as u64) as u32;
            let pl = self.g.plain_len(b);
            let o = (off - b as u64 * self.g.bs as u64) as usize;
            let k = data.len().min(pl - o);
            if self.sealed[b as usize] {
                return Err(std::io::Error::other(format!("block {b} written twice")));
            }
            let e = self.open.entry(b).or_insert_with(|| (vec![0u8; pl], 0));
            e.0[o..o + k].copy_from_slice(&data[..k]);
            e.1 += k;
            if e.1 > pl {
                return Err(std::io::Error::other(format!("block {b}: a byte written twice")));
            }
            if e.1 == pl {
                let (buf, _) = self.open.remove(&b).unwrap();
                self.seal_block(b, buf)?;
            }
            off += k as u64;
            data = &data[k..];
        }
        Ok(())
    }

    fn seal_block(&mut self, b: u32, mut buf: Vec<u8>) -> std::io::Result<()> {
        let tag = self.key.aead().seal_in_place_separate_tag(self.g.nonce(b), Aad::from(self.g.aad(self.key, &self.role, b)), &mut buf).map_err(|_| std::io::Error::other("seal"))?;
        buf.extend_from_slice(tag.as_ref());
        self.f.seek(SeekFrom::Start(self.g.at(b)))?;
        self.f.write_all(&buf)?;
        self.sealed[b as usize] = true;
        Ok(())
    }

    pub fn finish(mut self) -> std::io::Result<()> {
        if !self.open.is_empty() || self.sealed.iter().any(|s| !s) {
            let missing = self.sealed.iter().filter(|s| !**s).count();
            for (_, (buf, _)) in self.open.iter_mut() {
                buf.iter_mut().for_each(|x| *x = 0);
            }
            return Err(std::io::Error::other(format!("{missing} blocks not fully written")));
        }
        self.f.sync_all()?;
        std::fs::rename(&self.tmp, &self.path)
    }
}

/// Is this file DLVAULT2?
pub fn is_sealed(path: &Path) -> bool {
    let mut h = [0u8; 8];
    std::fs::File::open(path).and_then(|mut f| f.read_exact(&mut h)).is_ok() && &h == MAGIC
}

/// Reads a DLVAULT2 file's plaintext with Read + Seek, opening one block at a time.
pub struct Reader {
    key: std::sync::Arc<Key>,
    role: String,
    g: Geom,
    f: std::fs::File,
    pos: u64,
    cur: Option<(u32, Vec<u8>)>,
}

impl Reader {
    pub fn open(path: &Path, key: std::sync::Arc<Key>, role: &str) -> std::io::Result<Reader> {
        let mut f = std::fs::File::open(path)?;
        let mut h = [0u8; 32];
        f.read_exact(&mut h)?;
        if &h[..8] != MAGIC {
            return Err(std::io::Error::other(format!("{}: not a DLVAULT2 file", path.display())));
        }
        let g = Geom {
            id: h[8..16].try_into().unwrap(),
            len: u64::from_le_bytes(h[16..24].try_into().unwrap()),
            bs: u32::from_le_bytes(h[24..28].try_into().unwrap()),
            count: u32::from_le_bytes(h[28..32].try_into().unwrap()),
        };
        if g.bs == 0 || g.len.div_ceil(g.bs as u64) != g.count as u64 {
            return Err(std::io::Error::other(format!("{}: inconsistent header", path.display())));
        }
        let fl = f.metadata()?.len();
        if fl != g.file_len() {
            return Err(std::io::Error::other(format!("{}: {fl} bytes, a sealed file of this header has {} (truncated or extended)", path.display(), g.file_len())));
        }
        let mut r = Reader { key, role: role.to_string(), g, f, pos: 0, cur: None };
        // the header's fields are authenticated by every block's AAD: open the first block now, so a file under
        // another key / role / header fails at open
        if r.g.count > 0 {
            r.block(0)?;
        }
        Ok(r)
    }

    pub fn len(&self) -> u64 {
        self.g.len
    }
    pub fn is_empty(&self) -> bool {
        self.g.len == 0
    }

    fn block(&mut self, b: u32) -> std::io::Result<()> {
        if self.cur.as_ref().map(|c| c.0) == Some(b) {
            return Ok(());
        }
        let pl = self.g.plain_len(b);
        let mut buf = vec![0u8; pl + TAG as usize];
        self.f.seek(SeekFrom::Start(self.g.at(b)))?;
        self.f.read_exact(&mut buf)?;
        let n = self
            .key
            .aead()
            .open_in_place(self.g.nonce(b), Aad::from(self.g.aad(&self.key, &self.role, b)), &mut buf)
            .map_err(|_| std::io::Error::other(format!("block {b} does not open under this key, role and place")))?
            .len();
        buf.truncate(n);
        if let Some((_, old)) = self.cur.as_mut() {
            old.iter_mut().for_each(|x| *x = 0);
        }
        self.cur = Some((b, buf));
        Ok(())
    }
}

impl Read for Reader {
    fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
        if self.pos >= self.g.len || out.is_empty() {
            return Ok(0);
        }
        let b = (self.pos / self.g.bs as u64) as u32;
        self.block(b)?;
        let o = (self.pos - b as u64 * self.g.bs as u64) as usize;
        let cur = &self.cur.as_ref().unwrap().1;
        let k = out.len().min(cur.len() - o);
        out[..k].copy_from_slice(&cur[o..o + k]);
        self.pos += k as u64;
        Ok(k)
    }
}

impl Seek for Reader {
    fn seek(&mut self, p: SeekFrom) -> std::io::Result<u64> {
        let np = match p {
            SeekFrom::Start(x) => x as i128,
            SeekFrom::End(x) => self.g.len as i128 + x as i128,
            SeekFrom::Current(x) => self.pos as i128 + x as i128,
        };
        if np < 0 {
            return Err(std::io::Error::other("seek before the start"));
        }
        self.pos = np as u64;
        Ok(self.pos)
    }
}

impl Drop for Reader {
    fn drop(&mut self) {
        if let Some((_, b)) = self.cur.as_mut() {
            b.iter_mut().for_each(|x| *x = 0);
        }
    }
}
