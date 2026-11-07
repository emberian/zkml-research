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
        }
    }

    /// Add up to `max` words of `xs`, evenly spaced (all when fewer). Words 0 and 1 are skipped (not secret).
    pub fn add_words(&mut self, kind: &str, xs: &[u64], max: usize) {
        let step = xs.len().div_ceil(max.max(1)).max(1);
        let mut k = 0;
        for &w in xs.iter().step_by(step) {
            if w > 1 {
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

    pub fn len(&self) -> usize {
        self.tags.len()
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
                return ScanReport { available: false, regions: 0, bytes: 0, hits: 0, where_: vec![], by_kind: vec![], seconds: 0.0 }
            }
        };
        let mut rep = ScanReport { available: true, regions: 0, bytes: 0, hits: 0, where_: vec![], by_kind: vec![0; self.kinds.len()], seconds: 0.0 };
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
                for c in buf[..k].chunks_exact(8) {
                    let w = u64::from_le_bytes(c.try_into().unwrap());
                    if w > 1 {
                        let Some(&kd) = self.tags.get(&tag(self.k0, self.k1, w)) else { continue };
                        rep.hits += 1;
                        rep.by_kind[kd] += 1;
                        if rep.where_.len() < 8 {
                            rep.where_.push(name.clone());
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
        ScanReport { available: false, regions: 0, bytes: 0, hits: 0, where_: vec![], by_kind: vec![], seconds: 0.0 }
    }
}

impl Default for Canaries {
    fn default() -> Self {
        Self::new()
    }
}
