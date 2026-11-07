//! Cryptographic erasure of a custodian's state files. Overwriting a file in place does not erase it on ZFS (copy on
//! write, snapshots) or on an SSD (the FTL keeps old pages), so the claim cannot rest on wipes. Every secret state file
//! (checkpoint, carry, TLS key) is sealed instead under a per-epoch FILE KEY K that never reaches a disk:
//!   - K (32 bytes from the OS RNG) lives in the process's memory and in the Linux kernel's per-uid PERSISTENT keyring
//!     (KEYCTL_GET_PERSISTENT), under the name `dl-vault:<model>:<seat>:<epoch>:<cert fingerprint, 16 hex>`.
//!     The keyring keeps it across a planned process restart (forge's nightly pause, `serve --resume`), never writes
//!     it to storage, and loses it at reboot: a reboot erases the files too (the stated bound; neither forge nor bb2
//!     has swap, and a box that does would need encrypted swap). The keyring also expires an unused persistent
//!     keyring after kernel.keys.persistent_keyring_expiry seconds (3 days by default).
//!   - A sealed file is `DLVAULT1 | nonce (12) | ChaCha20-Poly1305(plain) | tag (16)`, with the AAD
//!     `dl-vault|<name>|<role>`: a file opens only under its own seat's, epoch's key and in its own role.
//!   - `destroy` invalidates the kernel key (KEYCTL_INVALIDATE, which removes it at once whatever else links it) and
//!     zeroes the in-memory copy; after it, no key the seat or its uid holds opens the files, wherever their blocks are.
//! Two seats on one box under one uid (the development layouts on bb2) can read each other's K; one custodian per
//! machine (or per uid) is the deployment.
use ring::aead::{Aad, LessSafeKey, Nonce, UnboundKey, CHACHA20_POLY1305};
use std::io::Write;
use std::path::Path;

pub const MAGIC: &[u8; 8] = b"DLVAULT1";
const NONCE: usize = 12;
const TAG: usize = 16;

pub struct Vault {
    pub name: String,
    key: Box<[u8; 32]>,
    /// the kernel key's serial, when it is in the persistent keyring
    serial: Option<i64>,
}

impl Drop for Vault {
    fn drop(&mut self) {
        unsafe { crate::erase::zero_raw(self.key.as_mut_ptr(), 32) };
    }
}

/// The keyring name of seat `seat`'s file key at `epoch` (fpr: its TLS certificate's sha256 hex; 16 hex are used).
pub fn key_name(model: &str, seat: usize, epoch: u64, fpr: &str) -> String {
    format!("dl-vault:{model}:{seat}:{epoch}:{}", &fpr[..fpr.len().min(16)])
}

#[cfg(target_os = "linux")]
mod kr {
    use std::ffi::CString;
    const KEYCTL_GET_PERSISTENT: libc::c_long = 22;
    const KEYCTL_SEARCH: libc::c_long = 10;
    const KEYCTL_READ: libc::c_long = 11;
    const KEYCTL_INVALIDATE: libc::c_long = 21;
    const KEY_SPEC_PROCESS_KEYRING: libc::c_long = -2;

    fn err(what: &str) -> String {
        format!("{what}: {}", std::io::Error::last_os_error())
    }

    /// The uid's persistent keyring, linked into this process's keyring (so its keys are possessed).
    pub fn persistent() -> Result<i64, String> {
        let r = unsafe { libc::syscall(libc::SYS_keyctl, KEYCTL_GET_PERSISTENT, -1 as libc::c_long, KEY_SPEC_PROCESS_KEYRING) };
        if r < 0 { Err(err("keyctl get_persistent")) } else { Ok(r) }
    }

    pub fn add(name: &str, payload: &[u8], ring: i64) -> Result<i64, String> {
        let (t, d) = (CString::new("user").unwrap(), CString::new(name).map_err(|e| e.to_string())?);
        let r = unsafe { libc::syscall(libc::SYS_add_key, t.as_ptr(), d.as_ptr(), payload.as_ptr(), payload.len(), ring as libc::c_long) };
        if r < 0 { Err(err("add_key")) } else { Ok(r) }
    }

    pub fn search(name: &str, ring: i64) -> Option<i64> {
        let (t, d) = (CString::new("user").unwrap(), CString::new(name).ok()?);
        let r = unsafe { libc::syscall(libc::SYS_keyctl, KEYCTL_SEARCH, ring as libc::c_long, t.as_ptr(), d.as_ptr(), 0 as libc::c_long) };
        (r >= 0).then_some(r)
    }

    pub fn read(serial: i64, out: &mut [u8; 32]) -> Result<(), String> {
        let r = unsafe { libc::syscall(libc::SYS_keyctl, KEYCTL_READ, serial as libc::c_long, out.as_mut_ptr(), 32usize) };
        if r != 32 { Err(if r < 0 { err("keyctl read") } else { format!("keyctl read: {r} bytes, not 32") }) } else { Ok(()) }
    }

    pub fn invalidate(serial: i64) -> Result<(), String> {
        let r = unsafe { libc::syscall(libc::SYS_keyctl, KEYCTL_INVALIDATE, serial as libc::c_long) };
        if r < 0 { Err(err("keyctl invalidate")) } else { Ok(()) }
    }
}

#[cfg(not(target_os = "linux"))]
mod kr {
    pub fn persistent() -> Result<i64, String> {
        Err("no kernel keyring on this OS".into())
    }
    pub fn add(_: &str, _: &[u8], _: i64) -> Result<i64, String> {
        Err("no kernel keyring on this OS".into())
    }
    pub fn search(_: &str, _: i64) -> Option<i64> {
        None
    }
    pub fn read(_: i64, _: &mut [u8; 32]) -> Result<(), String> {
        Err("no kernel keyring on this OS".into())
    }
    pub fn invalidate(_: i64) -> Result<(), String> {
        Err("no kernel keyring on this OS".into())
    }
}

/// Whether a file key of this name is in the uid's persistent keyring (the post-erasure check: false).
pub fn present(name: &str) -> bool {
    kr::persistent().ok().and_then(|r| kr::search(name, r)).is_some()
}

impl Vault {
    /// A fresh file key, stored in the persistent keyring (`keyring: false`: memory only, it dies with the process;
    /// the Mac's tests). Refuses if a key of this name exists (a new epoch's key is new).
    pub fn create(name: &str, keyring: bool) -> Result<Vault, String> {
        let mut key = Box::new([0u8; 32]);
        getrandom::getrandom(&mut key[..]).map_err(|e| e.to_string())?;
        let serial = if keyring {
            let r = kr::persistent()?;
            if kr::search(name, r).is_some() {
                return Err(format!("vault {name}: a file key of this name exists already"));
            }
            Some(kr::add(name, &key[..], r)?)
        } else {
            None
        };
        Ok(Vault { name: name.to_string(), key, serial })
    }

    /// The file key from the persistent keyring (a restarted process: `serve --resume`).
    pub fn load(name: &str) -> Result<Vault, String> {
        let r = kr::persistent()?;
        let s = kr::search(name, r).ok_or_else(|| format!("vault {name}: no file key in the keyring (erased, rebooted or never made)"))?;
        let mut key = Box::new([0u8; 32]);
        kr::read(s, &mut key)?;
        Ok(Vault { name: name.to_string(), key, serial: Some(s) })
    }

    /// A vault of a given key, in memory only (the post-erasure attempt with the zero key; tests).
    pub fn with_key(name: &str, key: [u8; 32]) -> Vault {
        Vault { name: name.to_string(), key: Box::new(key), serial: None }
    }

    /// The key's 8-byte words, for the memory scan's canaries.
    pub fn key_words(&self) -> [u64; 4] {
        std::array::from_fn(|i| u64::from_le_bytes(self.key[8 * i..8 * i + 8].try_into().unwrap()))
    }

    pub fn key_bytes(&self) -> &[u8; 32] {
        &self.key
    }

    fn aead(&self) -> Box<LessSafeKey> {
        Box::new(LessSafeKey::new(UnboundKey::new(&CHACHA20_POLY1305, &self.key[..]).expect("32-byte key")))
    }

    fn aad(&self, role: &str) -> Vec<u8> {
        format!("dl-vault|{}|{role}", self.name).into_bytes()
    }

    /// Seal `plain` (encrypted in place, then consumed): header | ciphertext | tag.
    pub fn seal(&self, role: &str, mut plain: Vec<u8>) -> Vec<u8> {
        let mut nonce = [0u8; NONCE];
        getrandom::getrandom(&mut nonce).expect("os rng");
        let tag = self.aead().seal_in_place_separate_tag(Nonce::assume_unique_for_key(nonce), Aad::from(self.aad(role)), &mut plain).expect("seal");
        let mut out = Vec::with_capacity(8 + NONCE + plain.len() + TAG);
        out.extend_from_slice(MAGIC);
        out.extend_from_slice(&nonce);
        out.extend_from_slice(&plain);
        out.extend_from_slice(tag.as_ref());
        out
    }

    /// Open a sealed blob (consumed; decrypted in place). Any other key, name or role, or any changed byte: Err.
    pub fn open(&self, role: &str, mut blob: Vec<u8>) -> Result<Vec<u8>, String> {
        if blob.len() < 8 + NONCE + TAG || &blob[..8] != MAGIC {
            return Err("vault: not a sealed file".into());
        }
        let nonce: [u8; NONCE] = blob[8..8 + NONCE].try_into().unwrap();
        let n = self.aead().open_within(Nonce::assume_unique_for_key(nonce), Aad::from(self.aad(role)), &mut blob, 8 + NONCE..).map_err(|_| "vault: the file does not open under this key".to_string())?.len();
        blob.truncate(n);
        Ok(blob)
    }

    /// Seal `plain` into `path`: a temporary file (mode 0600), synced, renamed over it.
    pub fn seal_to(&self, path: &Path, role: &str, plain: Vec<u8>) -> std::io::Result<()> {
        let blob = self.seal(role, plain);
        let tmp = path.with_extension("sealing");
        {
            let mut f = darkstep::serve::open_private(&tmp)?;
            f.write_all(&blob)?;
            f.sync_all()?;
        }
        std::fs::rename(tmp, path)
    }

    pub fn open_file(&self, path: &Path, role: &str) -> Result<Vec<u8>, String> {
        self.open(role, std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?)
    }

    /// Erase: invalidate the kernel key and zero the in-memory copy. Returns the report: whether it was in the
    /// keyring, the invalidation's error if any, and whether a key of the name is still found afterwards.
    pub fn destroy(mut self) -> serde_json::Value {
        let had = self.serial.is_some();
        let inv = self.serial.take().map(kr::invalidate);
        unsafe { crate::erase::zero_raw(self.key.as_mut_ptr(), 32) };
        let left = present(&self.name);
        serde_json::json!({
            "name": self.name, "in_keyring": had,
            "invalidate_error": inv.and_then(|r| r.err()),
            "key_in_keyring_after": left,
        })
    }
}
