//! MP-SPDZ glue: the Transactions file of one party, and driving the three `mascot-party.x` processes.

use crate::field::Fp;
use std::path::{Path, PathBuf};

/// One party's `Persistence/Transactions-P<i>.data`: header (type "SPDZ gfp", the prime, the party's MAC key
/// share), then (share, MAC share) pairs, each a 64-bit Montgomery residue (R = 2^64 mod p).
/// The (share, MAC share) pairs are decoded on access from the file's bytes (a read-only mapping for `read`), so a
/// release-sized file (hundreds of millions of pairs) never has to be resident twice.
pub struct Transactions {
    pub fp: Fp,
    pub alpha_i: u64,
    body: Body,
    off: usize,
    n: usize,
    rinv: u64,
}

enum Body {
    Owned(Vec<u8>),
    Mapped(*const u8, usize),
}

// the mapping is read-only and private to this value
unsafe impl Send for Body {}
unsafe impl Sync for Body {}

impl Drop for Body {
    fn drop(&mut self) {
        if let Body::Mapped(p, len) = *self {
            unsafe { libc::munmap(p as *mut libc::c_void, len) };
        }
    }
}

impl Body {
    fn bytes(&self) -> &[u8] {
        match self {
            Body::Owned(v) => v,
            Body::Mapped(p, len) => unsafe { std::slice::from_raw_parts(*p, *len) },
        }
    }
}

impl Transactions {
    /// Number of (share, mac) pairs.
    pub fn len(&self) -> usize {
        self.n
    }
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }
    /// Pair `i`, canonical (out of Montgomery form).
    #[inline]
    pub fn share(&self, i: usize) -> (u64, u64) {
        assert!(i < self.n, "share {i} of {}", self.n);
        let b = &self.body.bytes()[self.off + 16 * i..self.off + 16 * i + 16];
        let p = self.fp.p;
        let fm = |x: u64| self.fp.mul(x % p, self.rinv);
        (fm(u64::from_le_bytes(b[0..8].try_into().unwrap())), fm(u64::from_le_bytes(b[8..16].try_into().unwrap())))
    }

    pub fn parse(bytes: &[u8], p: u64) -> Result<Self, String> {
        Self::from_body(Body::Owned(bytes.to_vec()), p)
    }

    fn from_body(body: Body, p: u64) -> Result<Self, String> {
        let bytes = body.bytes();
        let fp = Fp::new(p);
        let u64le = |b: &[u8]| u64::from_le_bytes(b.try_into().unwrap());
        let u32le = |b: &[u8]| u32::from_le_bytes(b.try_into().unwrap());
        if bytes.len() < 8 {
            return Err("short file".into());
        }
        let hlen = u64le(&bytes[0..8]) as usize;
        let h = bytes.get(8..8 + hlen).ok_or("short header")?;
        let name = b"SPDZ gfp\0";
        if !h.starts_with(name) {
            return Err(format!("unexpected share type in header: {:?}", &h[..h.len().min(16)]));
        }
        let mut o = name.len();
        let plen = u32le(&h[o..o + 4]) as usize;
        o += 4;
        if plen != 8 {
            return Err(format!("prime is {plen} bytes, want 8 (a 61-bit field in one limb)"));
        }
        let prime = u64::from_be_bytes(h[o..o + 8].try_into().unwrap());
        o += 8;
        if prime != p {
            return Err(format!("file prime {prime} != expected {p}"));
        }
        let mont = u32le(&h[o..o + 4]);
        o += 4;
        if mont != 1 {
            return Err("expected Montgomery representation".into());
        }
        if hlen != o + 8 {
            return Err(format!("unexpected header length {hlen}"));
        }
        let rinv = fp.inv(((1u128 << 64) % p as u128) as u64);
        let from_mont = |x: u64| fp.mul(x % p, rinv);
        let alpha_i = from_mont(u64le(&h[o..o + 8]));
        let off = 8 + hlen;
        let blen = bytes.len() - off;
        if blen % 16 != 0 {
            return Err("body is not a whole number of (share, mac) pairs".into());
        }
        Ok(Transactions { fp, alpha_i, off, n: blen / 16, rinv, body })
    }

    /// Map the file read-only (it is not copied into memory).
    pub fn read(path: &Path, p: u64) -> Result<Self, String> {
        use std::os::unix::io::AsRawFd;
        let f = std::fs::File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let len = f.metadata().map_err(|e| e.to_string())?.len() as usize;
        if len == 0 {
            return Self::parse(&[], p);
        }
        let ptr = unsafe { libc::mmap(std::ptr::null_mut(), len, libc::PROT_READ, libc::MAP_PRIVATE, f.as_raw_fd(), 0) };
        if ptr == libc::MAP_FAILED {
            return Err(format!("{}: mmap failed: {}", path.display(), std::io::Error::last_os_error()));
        }
        Self::from_body(Body::Mapped(ptr as *const u8, len), p)
    }
}

/// Per-party result of one MASCOT run.
#[derive(Clone, Debug, Default)]
pub struct PartyStats {
    pub time_s: f64,
    pub sent_bytes: f64,
    pub rounds: u64,
}

/// Parse "Time = X seconds" and "Data sent = Y MB in ~R rounds" (MB = 1e6 bytes) from a party's stderr.
pub fn parse_stats(log: &str) -> Option<PartyStats> {
    let mut st = PartyStats::default();
    let mut got = (false, false);
    for line in log.lines() {
        if let Some(r) = line.strip_prefix("Time = ") {
            st.time_s = r.split_whitespace().next()?.parse().ok()?;
            got.0 = true;
        }
        if let Some(r) = line.strip_prefix("Data sent = ") {
            let mut it = r.split_whitespace();
            st.sent_bytes = it.next()?.parse::<f64>().ok()? * 1e6;
            st.rounds = it.nth(2).map(|s| s.trim_start_matches('~').parse().unwrap_or(0)).unwrap_or(0);
            got.1 = true;
        }
    }
    (got.0 && got.1).then_some(st)
}

pub struct Run {
    pub mpspdz: PathBuf,
    pub prog: String,
    pub p: u64,
    pub port_base: u16,
    pub extra: Vec<String>,
    /// directory for logs and PID files
    pub workdir: PathBuf,
}

impl Run {
    /// Compile the program (args after the program name) with MP-SPDZ's compiler.
    pub fn compile(mpspdz: &Path, args: &[String]) -> Result<String, String> {
        let out = std::process::Command::new("./compile.py")
            .current_dir(mpspdz)
            .arg("-F")
            .arg("61")
            .arg("darkprep")
            .args(args)
            .output()
            .map_err(|e| e.to_string())?;
        if !out.status.success() {
            return Err(String::from_utf8_lossy(&out.stderr).into_owned());
        }
        Ok(format!("darkprep-{}", args.join("-")))
    }

    /// Launch the three custodians as separate processes on 127.0.0.1 (PID file per party), wait for all.
    /// Returns (wall seconds, per-party stats).
    pub fn execute(&self) -> Result<(f64, Vec<PartyStats>), String> {
        let pers = self.mpspdz.join("Persistence");
        for i in 0..3 {
            let _ = std::fs::remove_file(pers.join(format!("Transactions-P{i}.data")));
        }
        std::fs::create_dir_all(&self.workdir).map_err(|e| e.to_string())?;
        let t0 = std::time::Instant::now();
        let mut kids = Vec::new();
        for i in 0..3 {
            let log = std::fs::File::create(self.workdir.join(format!("P{i}.log"))).map_err(|e| e.to_string())?;
            let child = std::process::Command::new("./mascot-party.x")
                .current_dir(&self.mpspdz)
                .args(["-N", "3", "-p", &i.to_string(), "-h", "127.0.0.1", "-pn", &self.port_base.to_string()])
                .arg("-P")
                .arg(self.p.to_string())
                .args(&self.extra)
                .arg(&self.prog)
                .stdout(log.try_clone().map_err(|e| e.to_string())?)
                .stderr(log)
                .spawn()
                .map_err(|e| e.to_string())?;
            std::fs::write(self.workdir.join(format!("P{i}.pid")), child.id().to_string()).map_err(|e| e.to_string())?;
            kids.push(child);
        }
        let mut ok = true;
        for k in kids.iter_mut() {
            ok &= k.wait().map_err(|e| e.to_string())?.success();
        }
        let wall = t0.elapsed().as_secs_f64();
        for i in 0..3 {
            let _ = std::fs::remove_file(self.workdir.join(format!("P{i}.pid")));
        }
        if !ok {
            let retired = self.retire_mac_keys();
            return Err(format!("a party failed (abort); see {}/P*.log; MAC key shares retired: {retired:?}", self.workdir.display()));
        }
        let mut stats = Vec::new();
        for i in 0..3 {
            let log = std::fs::read_to_string(self.workdir.join(format!("P{i}.log"))).map_err(|e| e.to_string())?;
            stats.push(parse_stats(&log).ok_or(format!("no stats in P{i}.log"))?);
        }
        Ok((wall, stats))
    }

    /// After an abort, never reuse the MAC key: a selective failure in MASCOT's authentication can leak bits of an
    /// honest alpha_i, and the leak only stays bounded if the key that leaked is discarded. MP-SPDZ keeps alpha_i in
    /// `Player-Data/Mascot-Secrets-p-*`; erasing the files makes the next run generate fresh keys (tapes not yet
    /// consumed under the old key must be regenerated). Files are overwritten, synced and unlinked (wipe_file): a
    /// retired alpha share left on disk would defeat the erasure the handover proves.
    pub fn retire_mac_keys(&self) -> Vec<PathBuf> {
        retire_mac_keys(&self.mpspdz, None)
    }
}

/// Overwrite a file's contents with zeros in place, sync, then unlink it (every hard-linked name sees the zeros).
pub fn wipe_file(path: &Path) -> std::io::Result<()> {
    use std::io::{Seek, SeekFrom, Write};
    let mut f = std::fs::OpenOptions::new().write(true).open(path)?;
    let len = f.metadata()?.len();
    f.seek(SeekFrom::Start(0))?;
    let z = vec![0u8; 1 << 20];
    let mut left = len;
    while left > 0 {
        let k = left.min(z.len() as u64) as usize;
        f.write_all(&z[..k])?;
        left -= k as u64;
    }
    f.sync_all()?;
    drop(f);
    std::fs::remove_file(path)
}

/// Retire (wipe: overwrite, sync, unlink) the MAC key files of the 61-bit field, for one party (a custodian box) or
/// all of them (a loopback test): `Mascot-Secrets-p-61-*`, `LowGear-` / `HighGear-Secrets-*` and
/// `3-p-61/Player-MAC-Keys-p-P<i>`, and any `*.retired-*` copy an older build left by renaming. Other fields'
/// material in the same directory is left alone.
pub fn retire_mac_keys(mpspdz: &Path, party: Option<usize>) -> Vec<PathBuf> {
    {
        let dir = mpspdz.join("Player-Data");
        let mut out = Vec::new();
        if let Ok(rd) = std::fs::read_dir(&dir) {
            for e in rd.flatten() {
                let name = e.file_name().to_string_lossy().into_owned();
                let mine = party.map(|i| name.contains(&format!("-P{i}-"))).unwrap_or(true);
                // MASCOT keeps alpha_i in Mascot-Secrets-p-61-*; LowGear/HighGear in LowGear-/HighGear-Secrets-*
                let keyfile = name.starts_with("Mascot-Secrets-p-61-") || name.starts_with("LowGear-Secrets-") || name.starts_with("HighGear-Secrets-");
                if keyfile && mine && wipe_file(&e.path()).is_ok() {
                    out.push(e.path());
                }
            }
        }
        // MP-SPDZ also writes a copy of alpha_i to Player-Data/<n>-p-61/Player-MAC-Keys-p-P<i>
        if let Ok(rd) = std::fs::read_dir(dir.join("3-p-61")) {
            for e in rd.flatten() {
                let name = e.file_name().to_string_lossy().into_owned();
                let mine = party.map(|i| name == format!("Player-MAC-Keys-p-P{i}")).unwrap_or(true);
                let mine = mine || party.map(|i| name.starts_with(&format!("Player-MAC-Keys-p-P{i}.retired-"))).unwrap_or(false);
                if name.starts_with("Player-MAC-Keys-p-P") && mine && wipe_file(&e.path()).is_ok() {
                    out.push(e.path());
                }
            }
        }
        out
    }
}

/// One custodian's MASCOT process on its own box (the distributed run): `mascot-party.x -p I --ip-file-name F`,
/// TLS (`-e`) unless `plaintext`, measured: wall, the process's own CPU and peak RSS (wait4), MP-SPDZ's byte counter,
/// and wire bytes per peer from the kernel's TCP counters (`ss -tinp`, sampled while it runs; TLS records included).
pub struct PartyRun {
    /// "mascot" (default), "lowgear" or "highgear": the MP-SPDZ binary <backend>-party.x
    pub backend: String,
    pub mpspdz: PathBuf,
    pub prog: String,
    pub p: u64,
    pub party: usize,
    pub ipfile: PathBuf,
    pub plaintext: bool,
    pub extra: Vec<String>,
    pub workdir: PathBuf,
}

#[derive(Clone, Debug, Default)]
pub struct PartyResult {
    pub wall_s: f64,
    pub stats: PartyStats,
    pub cpu_user_s: f64,
    pub cpu_sys_s: f64,
    pub max_rss_kb: i64,
    /// (peer ip, bytes_acked we sent, bytes_received), summed over sockets, last sample before close
    pub links: Vec<(String, u64, u64)>,
}

fn ss_sample(pid: u32, acc: &mut std::collections::BTreeMap<(String, String), (u64, u64)>) {
    let Ok(out) = std::process::Command::new("ss").args(["-tinpH"]).output() else { return };
    let txt = String::from_utf8_lossy(&out.stdout);
    let mut cur: Option<(String, String)> = None;
    let tag = format!("pid={pid},");
    for line in txt.lines() {
        if !line.starts_with(char::is_whitespace) {
            cur = None;
            if line.contains(&tag) {
                let f: Vec<&str> = line.split_whitespace().collect();
                if f.len() >= 5 {
                    cur = Some((f[3].to_string(), f[4].to_string()));
                }
            }
        } else if let Some(k) = &cur {
            let get = |key: &str| {
                line.split_whitespace().find_map(|w| w.strip_prefix(key)).and_then(|v| v.parse::<u64>().ok()).unwrap_or(0)
            };
            let e = acc.entry(k.clone()).or_default();
            e.0 = e.0.max(get("bytes_acked:"));
            e.1 = e.1.max(get("bytes_received:"));
        }
    }
}

impl PartyRun {
    pub fn execute(&self) -> Result<PartyResult, String> {
        let pers = self.mpspdz.join("Persistence");
        let _ = std::fs::remove_file(pers.join(format!("Transactions-P{}.data", self.party)));
        std::fs::create_dir_all(&self.workdir).map_err(|e| e.to_string())?;
        let log = std::fs::File::create(self.workdir.join(format!("P{}.log", self.party))).map_err(|e| e.to_string())?;
        let mut cmd = std::process::Command::new(format!("./{}-party.x", self.backend));
        cmd.current_dir(&self.mpspdz)
            .args(["-N", "3", "-p", &self.party.to_string(), "--ip-file-name"])
            .arg(&self.ipfile)
            .arg("-P")
            .arg(self.p.to_string());
        if !self.plaintext {
            cmd.arg("-e");
        }
        cmd.args(&self.extra).arg(&self.prog).stdout(log.try_clone().map_err(|e| e.to_string())?).stderr(log);
        let t0 = std::time::Instant::now();
        let child = cmd.spawn().map_err(|e| e.to_string())?;
        let pid = child.id();
        let pidfile = self.workdir.join(format!("mascot-P{}.pid", self.party));
        std::fs::write(&pidfile, pid.to_string()).map_err(|e| e.to_string())?;
        let done = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let d2 = done.clone();
        let sampler = std::thread::spawn(move || {
            let mut acc = std::collections::BTreeMap::new();
            while !d2.load(std::sync::atomic::Ordering::Relaxed) {
                ss_sample(pid, &mut acc);
                std::thread::sleep(std::time::Duration::from_millis(250));
            }
            acc
        });
        let mut status = 0i32;
        let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
        let r = unsafe { libc::wait4(pid as i32, &mut status, 0, &mut ru) };
        let wall = t0.elapsed().as_secs_f64();
        done.store(true, std::sync::atomic::Ordering::Relaxed);
        let acc = sampler.join().unwrap_or_default();
        let _ = std::fs::remove_file(&pidfile);
        drop(child);
        let ok = r == pid as i32 && libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0;
        if !ok {
            let retired = retire_mac_keys(&self.mpspdz, Some(self.party));
            return Err(format!("party {} failed (abort, status {status}); see {}; MAC key share retired: {retired:?}",
                               self.party, self.workdir.join(format!("P{}.log", self.party)).display()));
        }
        let logtxt = std::fs::read_to_string(self.workdir.join(format!("P{}.log", self.party))).map_err(|e| e.to_string())?;
        let stats = parse_stats(&logtxt).ok_or("no stats in the party log")?;
        let mut by_peer: std::collections::BTreeMap<String, (u64, u64)> = Default::default();
        for ((_local, peer), (s, rcv)) in acc {
            let ip = peer.rsplit_once(':').map(|x| x.0.to_string()).unwrap_or(peer);
            let e = by_peer.entry(ip).or_default();
            e.0 += s;
            e.1 += rcv;
        }
        let tv = |t: libc::timeval| t.tv_sec as f64 + t.tv_usec as f64 * 1e-6;
        Ok(PartyResult {
            wall_s: wall,
            stats,
            cpu_user_s: tv(ru.ru_utime),
            cpu_sys_s: tv(ru.ru_stime),
            max_rss_kb: ru.ru_maxrss as i64,
            links: by_peer.into_iter().map(|(k, (a, b))| (k, a, b)).collect(),
        })
    }
}
