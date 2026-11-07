//! Streaming CPython `repr()` into SHA-256, for the harness's Fiat-Shamir and commitment hashes, which hash
//! `repr(obj).encode()` of tuples, lists, dicts, ints, bools and plain ASCII strs. Nothing is materialized: the
//! writer pushes bytes straight into the hasher through a small buffer.
use sha2::{Digest, Sha256};

pub struct ReprHasher {
    h: Sha256,
    buf: Vec<u8>,
}

impl Default for ReprHasher {
    fn default() -> Self {
        Self::new()
    }
}

impl ReprHasher {
    pub fn new() -> Self {
        ReprHasher { h: Sha256::new(), buf: Vec::with_capacity(1 << 16) }
    }

    #[inline]
    pub fn raw(&mut self, b: &[u8]) {
        if self.buf.len() + b.len() > self.buf.capacity() {
            self.h.update(&self.buf);
            self.buf.clear();
            if b.len() > self.buf.capacity() {
                self.h.update(b);
                return;
            }
        }
        self.buf.extend_from_slice(b);
    }

    #[inline]
    pub fn u64(&mut self, mut v: u64) {
        let mut tmp = [0u8; 20];
        let mut i = 20;
        if v == 0 {
            self.raw(b"0");
            return;
        }
        while v > 0 {
            i -= 1;
            tmp[i] = b'0' + (v % 10) as u8;
            v /= 10;
        }
        self.raw(&tmp[i..]);
    }

    #[inline]
    pub fn i64(&mut self, v: i64) {
        if v < 0 {
            self.raw(b"-");
        }
        self.u64(v.unsigned_abs());
    }

    pub fn i128(&mut self, v: i128) {
        if v < 0 {
            self.raw(b"-");
        }
        let s = v.unsigned_abs().to_string();
        self.raw(s.as_bytes());
    }

    pub fn bool(&mut self, b: bool) {
        self.raw(if b { b"True" } else { b"False" });
    }

    /// repr of a str with no quote, backslash or non-printable character: single-quoted.
    pub fn s(&mut self, s: &str) {
        debug_assert!(s.bytes().all(|c| (0x20..0x7f).contains(&c) && c != b'\'' && c != b'\\'));
        self.raw(b"'");
        self.raw(s.as_bytes());
        self.raw(b"'");
    }

    pub fn sep(&mut self) {
        self.raw(b", ");
    }

    /// repr of a list of u64.
    pub fn list_u64(&mut self, xs: &[u64]) {
        self.raw(b"[");
        for (k, &x) in xs.iter().enumerate() {
            if k > 0 {
                self.raw(b", ");
            }
            self.u64(x);
        }
        self.raw(b"]");
    }

    pub fn finish(mut self) -> [u8; 32] {
        self.h.update(&self.buf);
        self.h.finalize().into()
    }

    pub fn finish_hex(self) -> String {
        hex(&self.finish())
    }
}

pub fn hex(b: &[u8]) -> String {
    const D: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(b.len() * 2);
    for &x in b {
        s.push(D[(x >> 4) as usize] as char);
        s.push(D[(x & 15) as usize] as char);
    }
    s
}

pub fn sha256_hex(b: &[u8]) -> String {
    hex(&Sha256::digest(b))
}
