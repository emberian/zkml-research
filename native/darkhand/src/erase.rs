//! Enforced erasure. Three layers:
//! 1. `ZeroOnFree`: a global allocator that overwrites every block with zeros (volatile word stores) before handing
//!    it back, and implements realloc as allocate-copy-wipe, so a buffer that ever held a share (queue messages,
//!    BufWriter buffers, the old block of a grown Vec) is zero once it is freed. A custodian binary declares it with
//!    `#[global_allocator] static A: darkhand::erase::ZeroOnFree = darkhand::erase::ZeroOnFree;`.
//! 2. `Wipe`: explicit in-place zeroing of the live structures (shares, MAC shares, key, commitment tails and salts)
//!    before they are dropped.
//! 3. `wipe_file`: overwrite a state file with zeros, fsync, unlink, fsync the directory.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{compiler_fence, AtomicU64, Ordering};

pub static WIPED_BYTES: AtomicU64 = AtomicU64::new(0);

/// Volatile zeroing (the stores cannot be elided as dead before a free).
///
/// # Safety
/// `p..p + n` must be writable.
pub unsafe fn zero_raw(p: *mut u8, n: usize) {
    let mut i = 0;
    let al = p.align_offset(8).min(n);
    while i < al {
        std::ptr::write_volatile(p.add(i), 0);
        i += 1;
    }
    while i + 8 <= n {
        std::ptr::write_volatile(p.add(i) as *mut u64, 0);
        i += 8;
    }
    while i < n {
        std::ptr::write_volatile(p.add(i), 0);
        i += 1;
    }
    compiler_fence(Ordering::SeqCst);
}

pub struct ZeroOnFree;

unsafe impl GlobalAlloc for ZeroOnFree {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        System.alloc(l)
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        System.alloc_zeroed(l)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        zero_raw(p, l.size());
        WIPED_BYTES.fetch_add(l.size() as u64, Ordering::Relaxed);
        System.dealloc(p, l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        let nl = Layout::from_size_align_unchecked(new, l.align());
        let np = System.alloc(nl);
        if !np.is_null() {
            std::ptr::copy_nonoverlapping(p, np, l.size().min(new));
            self.dealloc(p, l);
        }
        np
    }
}

pub trait Wipe {
    fn wipe(&mut self);
}

macro_rules! wipe_slice {
    ($t:ty) => {
        impl Wipe for [$t] {
            fn wipe(&mut self) {
                unsafe { zero_raw(self.as_mut_ptr() as *mut u8, std::mem::size_of_val(self)) }
            }
        }
        impl Wipe for Vec<$t> {
            fn wipe(&mut self) {
                // the whole capacity, not only the length
                let cap = self.capacity();
                unsafe { zero_raw(self.as_mut_ptr() as *mut u8, cap * std::mem::size_of::<$t>()) }
                self.clear();
            }
        }
    };
}
wipe_slice!(u64);
wipe_slice!(i64);
wipe_slice!(u8);
wipe_slice!([u8; 32]);
wipe_slice!(darkstep::party::Sh);

impl Wipe for String {
    fn wipe(&mut self) {
        unsafe { self.as_mut_vec().wipe() }
    }
}

macro_rules! wipe_nested {
    ($t:ty) => {
        impl Wipe for Vec<Vec<$t>> {
            fn wipe(&mut self) {
                for v in self.iter_mut() {
                    v.wipe();
                }
                self.clear();
            }
        }
    };
}
wipe_nested!(u64);
wipe_nested!(darkstep::party::Sh);

impl Wipe for darkproof::pcs::PcsParty {
    fn wipe(&mut self) {
        self.ext.wipe();
        self.salts.wipe();
        for l in self.tree.iter_mut() {
            l.wipe();
        }
        self.tree.clear();
    }
}

impl Wipe for darkstep::tape::Tape {
    fn wipe(&mut self) {
        self.alpha_i = 0;
        unsafe { std::ptr::write_volatile(&mut self.alpha_i, 0) };
        self.sh.wipe();
        self.mac.wipe();
        self.tags.wipe();
    }
}

impl Wipe for dzkpopk::ceremony::Custodian {
    fn wipe(&mut self) {
        self.s.wipe();
        self.e.wipe();
        self.r.wipe();
        self.salt.wipe();
    }
}

/// Overwrite a file with zeros, fsync, unlink, fsync its directory. Missing files are fine (already gone).
pub fn wipe_file(path: &std::path::Path) -> std::io::Result<()> {
    use std::io::Write;
    let len = match std::fs::metadata(path) {
        Ok(m) => m.len(),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(e) => return Err(e),
    };
    {
        let mut f = std::fs::OpenOptions::new().write(true).open(path)?;
        let z = vec![0u8; 1 << 20];
        let mut left = len;
        while left > 0 {
            let k = left.min(z.len() as u64) as usize;
            f.write_all(&z[..k])?;
            left -= k as u64;
        }
        f.sync_all()?;
    }
    std::fs::remove_file(path)?;
    if let Some(dir) = path.parent() {
        std::fs::File::open(dir)?.sync_all()?;
    }
    Ok(())
}
