//! A custodian's scan of its own address space for its secret material, just before it exits.
//!
//! Canaries are one-way: the scanner keeps SipHash-2-4 tags (random 128-bit key) of sampled secret words, never the
//! words, so the canary set itself leaks nothing usable. The scan reads every readable, writable mapping of
//! /proc/self/maps (heap, anonymous mappings, every thread's stack) through /proc/self/mem and tags every aligned
//! 8-byte word; a hit is a word whose tag is a canary's. Linux only (elsewhere it reports `available: false`).
use std::hash::Hasher;

pub struct Canaries {
    k0: u64,
    k1: u64,
    tags: std::collections::HashMap<u64, usize>,
    pub kinds: Vec<(String, usize)>,
    /// words at or above this are never canaries (`bounded`): the disk scan then tags only words below it
    below: Option<u64>,
    /// tags of 16-byte strings (`add_text16`, e.g. a key share as decimal text), looked for at every offset of files
    /// up to TEXT_MAX bytes (key files are small)
    text16: std::collections::HashMap<u64, usize>,
}

const TEXT_MAX: u64 = 1 << 20;

#[allow(deprecated)]
fn tag16(k0: u64, k1: u64, b: &[u8]) -> u64 {
    let mut h = std::hash::SipHasher::new_with_keys(k0, k1);
    h.write(&b[..16]);
    h.finish()
}

/// A scan of files on disk (`Canaries::scan_paths`).
#[derive(Debug, Clone, Default)]
pub struct DiskReport {
    pub files: usize,
    pub bytes: u64,
    pub hits: u64,
    pub by_kind: Vec<u64>,
    /// (path, hits) of every file with a hit
    pub hit_files: Vec<(String, u64)>,
    /// paths that could not be read (a missing path is not listed: erasure unlinks them)
    pub unreadable: Vec<String>,
    pub seconds: f64,
}

#[derive(Debug, Clone)]
pub struct ScanReport {
    pub available: bool,
    pub regions: usize,
    pub bytes: u64,
    pub hits: u64,
    /// mapping name of the first hits (heap, stack, anon, ...)
    pub where_: Vec<String>,
    /// hits per canary kind (index into Canaries::kinds)
    pub by_kind: Vec<u64>,
    /// the first hits in detail: (kind index, mapping name, mapping start, mapping length, offset of the word in it)
    pub detail: Vec<(usize, String, u64, u64, u64)>,
    /// an address in the scanning frame (the stack pointer's neighbourhood): a [stack] hit above it is in a live caller
    /// frame, one below it in dead stack
    pub sp: u64,
    pub seconds: f64,
}

#[allow(deprecated)]
fn tag(k0: u64, k1: u64, w: u64) -> u64 {
    let mut h = std::hash::SipHasher::new_with_keys(k0, k1);
    h.write_u64(w);
    h.finish()
}

impl Canaries {
    pub fn new() -> Self {
        let mut b = [0u8; 16];
        getrandom::getrandom(&mut b).expect("os rng");
        Canaries {
            k0: u64::from_le_bytes(b[..8].try_into().unwrap()),
            k1: u64::from_le_bytes(b[8..].try_into().unwrap()),
            tags: std::collections::HashMap::new(),
            kinds: Vec::new(),
            below: None,
            text16: std::collections::HashMap::new(),
        }
    }

    /// Canaries of words below `bound` only (field elements and NTT residues: below 2^61). A file scan tags a word
    /// only when it is below the bound, so it can look at every byte offset (files are not word-aligned) at about
    /// twice the aligned cost instead of eight times.
    pub fn bounded(bound: u64) -> Self {
        Canaries { below: Some(bound), ..Canaries::new() }
    }

    /// Add up to `max` words of `xs`, evenly spaced (all when fewer). Words 0 and 1 are skipped (not secret).
    pub fn add_words(&mut self, kind: &str, xs: &[u64], max: usize) {
        let step = xs.len().div_ceil(max.max(1)).max(1);
        let mut k = 0;
        for &w in xs.iter().step_by(step) {
            if w > 1 && self.below.map_or(true, |b| w < b) {
                self.tags.insert(tag(self.k0, self.k1, w), self.kinds.len());
                k += 1;
            }
        }
        self.kinds.push((kind.to_string(), k));
    }

    /// Add a byte string as its aligned 8-byte words (a String's or Vec's heap buffer starts aligned).
    pub fn add_bytes(&mut self, kind: &str, b: &[u8]) {
        let ws: Vec<u64> = b.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
        self.add_words(kind, &ws, ws.len());
    }

    /// Add the first 16 bytes of a string (shorter strings are not added: the kind then counts 0).
    pub fn add_text16(&mut self, kind: &str, b: &[u8]) {
        let k = if b.len() >= 16 {
            self.text16.insert(tag16(self.k0, self.k1, b), self.kinds.len());
            1
        } else {
            0
        };
        self.kinds.push((kind.to_string(), k));
    }

    pub fn len(&self) -> usize {
        self.tags.len() + self.text16.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tags.is_empty()
    }

    #[cfg(target_os = "linux")]
    pub fn scan(&self) -> ScanReport {
        use std::io::{Read, Seek, SeekFrom};
        let t = std::time::Instant::now();
        let maps = std::fs::read_to_string("/proc/self/maps").unwrap_or_default();
        let mut mem = match std::fs::File::open("/proc/self/mem") {
            Ok(f) => f,
            Err(_) => {
                return ScanReport { available: false, regions: 0, bytes: 0, hits: 0, where_: vec![], by_kind: vec![], detail: vec![], sp: 0, seconds: 0.0 }
            }
        };
        let here = 0u8;
        let sp = std::hint::black_box(&here) as *const u8 as u64;
        let mut rep = ScanReport { available: true, regions: 0, bytes: 0, hits: 0, where_: vec![], by_kind: vec![0; self.kinds.len()], detail: vec![], sp, seconds: 0.0 };
        let mut buf = vec![0u8; 1 << 22];
        for line in maps.lines() {
            let mut it = line.split_whitespace();
            let (range, perms) = match (it.next(), it.next()) {
                (Some(r), Some(p)) => (r, p),
                _ => continue,
            };
            let name = line.split_whitespace().nth(5).unwrap_or("[anon]").to_string();
            if !perms.starts_with("rw") || name == "[vvar]" || name == "[vsyscall]" {
                continue;
            }
            let (a, b) = range.split_once('-').unwrap();
            let (a, b) = (u64::from_str_radix(a, 16).unwrap(), u64::from_str_radix(b, 16).unwrap());
            rep.regions += 1;
            let mut off = a;
            while off < b {
                let k = ((b - off) as usize).min(buf.len());
                if mem.seek(SeekFrom::Start(off)).is_err() || mem.read_exact(&mut buf[..k]).is_err() {
                    off += k as u64;
                    continue;
                }
                rep.bytes += k as u64;
                for (ci, c) in buf[..k].chunks_exact(8).enumerate() {
                    let w = u64::from_le_bytes(c.try_into().unwrap());
                    if w > 1 {
                        let Some(&kd) = self.tags.get(&tag(self.k0, self.k1, w)) else { continue };
                        rep.hits += 1;
                        rep.by_kind[kd] += 1;
                        if rep.where_.len() < 8 {
                            rep.where_.push(name.clone());
                        }
                        if rep.detail.len() < 64 {
                            rep.detail.push((kd, name.clone(), a, b - a, off - a + 8 * ci as u64));
                        }
                    }
                }
                off += k as u64;
            }
        }
        unsafe { crate::erase::zero_raw(buf.as_mut_ptr(), buf.len()) };
        rep.seconds = t.elapsed().as_secs_f64();
        rep
    }

    #[cfg(not(target_os = "linux"))]
    pub fn scan(&self) -> ScanReport {
        ScanReport { available: false, regions: 0, bytes: 0, hits: 0, where_: vec![], by_kind: vec![], detail: vec![], sp: 0, seconds: 0.0 }
    }
}

impl Canaries {
    /// Scan every regular file under `paths` (directories recursively; symlinks are not followed) at every byte
    /// offset, on all cores (`DLH_SCAN_THREADS` caps them). Read buffers are zeroed after use.
    pub fn scan_paths(&self, paths: &[std::path::PathBuf]) -> DiskReport {
        use std::os::unix::fs::FileExt;
        use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
        let t = std::time::Instant::now();
        let mut rep = DiskReport { by_kind: vec![0; self.kinds.len()], ..Default::default() };
        let mut files: Vec<(std::path::PathBuf, u64)> = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        let mut stack: Vec<std::path::PathBuf> = paths.to_vec();
        while let Some(p) = stack.pop() {
            let md = match std::fs::symlink_metadata(&p) {
                Ok(m) => m,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                Err(_) => {
                    rep.unreadable.push(p.display().to_string());
                    continue;
                }
            };
            if md.is_dir() {
                match std::fs::read_dir(&p) {
                    Ok(rd) => stack.extend(rd.flatten().map(|e| e.path())),
                    Err(_) => rep.unreadable.push(p.display().to_string()),
                }
            } else if md.is_file() {
                let key = std::fs::canonicalize(&p).unwrap_or(p.clone());
                if seen.insert(key) {
                    files.push((p, md.len()));
                }
            }
        }
        files.sort();
        rep.files = files.len();
        // work units of 64 MiB; a unit reads 7 bytes past its end so that a word starting in it is seen whole
        const UNIT: u64 = 64 << 20;
        let units: Vec<(usize, u64, u64)> = files
            .iter()
            .enumerate()
            .flat_map(|(f, (_, len))| (0..len.div_ceil(UNIT)).map(move |u| (f, u * UNIT, (len - u * UNIT).min(UNIT))))
            .collect();
        let per_file: Vec<AtomicU64> = files.iter().map(|_| AtomicU64::new(0)).collect();
        let by_kind: Vec<AtomicU64> = self.kinds.iter().map(|_| AtomicU64::new(0)).collect();
        let bad: Vec<std::sync::atomic::AtomicBool> = files.iter().map(|_| Default::default()).collect();
        let bytes = AtomicU64::new(0);
        let next = AtomicUsize::new(0);
        let nt = std::env::var("DLH_SCAN_THREADS").ok().and_then(|x| x.parse().ok())
            .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4)).max(1);
        let below = self.below.unwrap_or(u64::MAX);
        std::thread::scope(|s| {
            for _ in 0..nt {
                s.spawn(|| {
                    let mut buf = vec![0u8; UNIT as usize + 8];
                    let mut open: Option<(usize, std::fs::File)> = None;
                    loop {
                        let u = next.fetch_add(1, Ordering::Relaxed);
                        let Some(&(f, off, len)) = units.get(u) else { break };
                        if open.as_ref().map(|o| o.0) != Some(f) {
                            open = std::fs::File::open(&files[f].0).ok().map(|h| (f, h));
                        }
                        let Some((_, h)) = open.as_ref() else {
                            bad[f].store(true, Ordering::Relaxed);
                            continue;
                        };
                        let want = (len + 7).min(files[f].1 - off) as usize;
                        let mut got = 0;
                        while got < want {
                            match h.read_at(&mut buf[got..want], off + got as u64) {
                                Ok(0) => break,
                                Ok(k) => got += k,
                                Err(_) => break,
                            }
                        }
                        bytes.fetch_add(got.min(len as usize) as u64, Ordering::Relaxed);
                        let starts = (len as usize).min(got.saturating_sub(7));
                        let mut hits = 0u64;
                        for p in 0..starts {
                            let w = u64::from_le_bytes(buf[p..p + 8].try_into().unwrap());
                            if w > 1 && w < below {
                                if let Some(&kd) = self.tags.get(&tag(self.k0, self.k1, w)) {
                                    hits += 1;
                                    by_kind[kd].fetch_add(1, Ordering::Relaxed);
                                }
                            }
                        }
                        if !self.text16.is_empty() && files[f].1 <= TEXT_MAX && got >= 16 {
                            for p in 0..=got - 16 {
                                if let Some(&kd) = self.text16.get(&tag16(self.k0, self.k1, &buf[p..p + 16])) {
                                    hits += 1;
                                    by_kind[kd].fetch_add(1, Ordering::Relaxed);
                                }
                            }
                        }
                        if hits > 0 {
                            per_file[f].fetch_add(hits, Ordering::Relaxed);
                        }
                    }
                    unsafe { crate::erase::zero_raw(buf.as_mut_ptr(), buf.len()) };
                });
            }
        });
        rep.bytes = bytes.into_inner();
        rep.by_kind = by_kind.into_iter().map(|x| x.into_inner()).collect();
        rep.hits = rep.by_kind.iter().sum();
        for (k, (p, _)) in files.iter().enumerate() {
            let h = per_file[k].load(Ordering::Relaxed);
            if h > 0 {
                rep.hit_files.push((p.display().to_string(), h));
            }
            if bad[k].load(Ordering::Relaxed) {
                rep.unreadable.push(p.display().to_string());
            }
        }
        rep.seconds = t.elapsed().as_secs_f64();
        rep
    }
}

impl Default for Canaries {
    fn default() -> Self {
        Self::new()
    }
}
