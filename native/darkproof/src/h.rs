//! The harness's hashes: H(*parts) = sha256 over repr(part).encode() for each part, concatenated. Digests are kept
//! as 32 raw bytes; wherever the harness hashes a digest it hashes its hex string's repr, which `Py::hx` writes.
use crate::Ctx;
use pycompat::ReprHasher;

pub type Hash = [u8; 32];

pub struct Py(ReprHasher);

impl Default for Py {
    fn default() -> Self {
        Py::new()
    }
}

const HEX: &[u8; 16] = b"0123456789abcdef";

pub fn hex(h: &[u8]) -> String {
    pycompat::repr::hex(h)
}

pub fn unhex32(s: &str) -> Option<Hash> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

/// Python's repr() of a str (quote choice, escapes). ASCII is exact; non-ASCII characters are written as themselves
/// except the C1 controls, NBSP and soft hyphen ([OPEN] full str.isprintable() table not ported).
pub fn py_str_repr(s: &str) -> String {
    let q = if s.contains('\'') && !s.contains('"') { '"' } else { '\'' };
    let mut out = String::with_capacity(s.len() + 2);
    out.push(q);
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c == q => {
                out.push('\\');
                out.push(c);
            }
            c if (c as u32) < 0x20 || c as u32 == 0x7f || (0x80..=0xa0).contains(&(c as u32)) || c as u32 == 0xad => {
                out.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => out.push(c),
        }
    }
    out.push(q);
    out
}

impl Py {
    pub fn new() -> Self {
        Py(ReprHasher::new())
    }
    /// A hasher with a 256-byte write buffer: for the many hashers of a streamed level (same digest as `new`).
    pub fn lean() -> Self {
        Py(ReprHasher::with_capacity(256))
    }
    #[inline]
    pub fn raw(&mut self, b: &[u8]) -> &mut Self {
        self.0.raw(b);
        self
    }
    /// repr of a plain ASCII str literal with no quotes or backslashes.
    #[inline]
    pub fn s(&mut self, s: &str) -> &mut Self {
        self.0.s(s);
        self
    }
    /// repr of any str.
    pub fn str_any(&mut self, s: &str) -> &mut Self {
        let r = py_str_repr(s);
        self.0.raw(r.as_bytes());
        self
    }
    /// repr of a digest's hex string.
    #[inline]
    pub fn hx(&mut self, h: &Hash) -> &mut Self {
        let mut buf = [0u8; 66];
        buf[0] = b'\'';
        for (i, &b) in h.iter().enumerate() {
            buf[1 + 2 * i] = HEX[(b >> 4) as usize];
            buf[2 + 2 * i] = HEX[(b & 15) as usize];
        }
        buf[65] = b'\'';
        self.0.raw(&buf);
        self
    }
    #[inline]
    pub fn int(&mut self, v: u64) -> &mut Self {
        self.0.u64(v);
        self
    }
    #[inline]
    pub fn list(&mut self, xs: &[u64]) -> &mut Self {
        self.0.list_u64(xs);
        self
    }
    /// repr of a tuple of ints.
    pub fn tuple(&mut self, xs: &[u64]) -> &mut Self {
        self.0.raw(b"(");
        for (k, &x) in xs.iter().enumerate() {
            if k > 0 {
                self.0.raw(b", ");
            }
            self.0.u64(x);
        }
        if xs.len() == 1 {
            self.0.raw(b",");
        }
        self.0.raw(b")");
        self
    }
    /// repr of a list of digests' hex strings.
    pub fn list_hx(&mut self, xs: &[Hash]) -> &mut Self {
        self.0.raw(b"[");
        for (k, x) in xs.iter().enumerate() {
            if k > 0 {
                self.0.raw(b", ");
            }
            self.hx(x);
        }
        self.0.raw(b"]");
        self
    }
    /// repr of a tuple of digests' hex strings.
    pub fn tuple_hx(&mut self, xs: &[Hash]) -> &mut Self {
        self.0.raw(b"(");
        for (k, x) in xs.iter().enumerate() {
            if k > 0 {
                self.0.raw(b", ");
            }
            self.hx(x);
        }
        if xs.len() == 1 {
            self.0.raw(b",");
        }
        self.0.raw(b")");
        self
    }
    /// repr of a list of lists of ints.
    pub fn list2(&mut self, xs: &[Vec<u64>]) -> &mut Self {
        self.0.raw(b"[");
        for (k, x) in xs.iter().enumerate() {
            if k > 0 {
                self.0.raw(b", ");
            }
            self.0.list_u64(x);
        }
        self.0.raw(b"]");
        self
    }
    /// repr of the binding context tuple (model, epoch, step).
    pub fn ctx(&mut self, c: &Ctx) -> &mut Self {
        self.0.raw(b"(");
        self.str_any(&c.model);
        self.0.raw(b", ");
        self.0.u64(c.epoch);
        self.0.raw(b", ");
        self.0.u64(c.step);
        self.0.raw(b")");
        self
    }
    pub fn done(self) -> Hash {
        self.0.finish()
    }
}

/// H("leaf", salt, col).
#[inline]
pub fn h_leaf(salt: &Hash, col: &[u64]) -> Hash {
    let mut h = Py::new();
    h.s("leaf").hx(salt).list(col);
    h.done()
}

#[inline]
pub fn h_pad(j: u64) -> Hash {
    let mut h = Py::new();
    h.s("pad").int(j);
    h.done()
}

#[inline]
pub fn h_node(a: &Hash, b: &Hash) -> Hash {
    let mut h = Py::new();
    h.hx(a).hx(b);
    h.done()
}

/// H(x) for a list of ints (the repr digest the deterministic hook labels shares with), as hex.
pub fn h_list_hex(xs: &[u64]) -> String {
    let mut h = Py::new();
    h.list(xs);
    hex(&h.done())
}
