//! MP-SPDZ glue: the Transactions file of one party, and driving the three `mascot-party.x` processes.

use crate::field::Fp;
use std::path::{Path, PathBuf};

/// One party's `Persistence/Transactions-P<i>.data`: header (type "SPDZ gfp", the prime, the party's MAC key
/// share), then (share, MAC share) pairs, each a 64-bit Montgomery residue (R = 2^64 mod p).
pub struct Transactions {
    pub fp: Fp,
    pub alpha_i: u64,
    /// canonical (share, mac) pairs
    pub shares: Vec<(u64, u64)>,
}

impl Transactions {
    pub fn parse(bytes: &[u8], p: u64) -> Result<Self, String> {
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
        let body = &bytes[8 + hlen..];
        if body.len() % 16 != 0 {
            return Err("body is not a whole number of (share, mac) pairs".into());
        }
        let shares = body
            .chunks_exact(16)
            .map(|c| (from_mont(u64le(&c[0..8])), from_mont(u64le(&c[8..16]))))
            .collect();
        Ok(Transactions { fp, alpha_i, shares })
    }

    pub fn read(path: &Path, p: u64) -> Result<Self, String> {
        let b = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
        Self::parse(&b, p)
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
    /// `Player-Data/Mascot-Secrets-p-*`; renaming the files makes the next run generate fresh keys (tapes not yet
    /// consumed under the old key must be regenerated). Files are renamed, not deleted.
    pub fn retire_mac_keys(&self) -> Vec<PathBuf> {
        let dir = self.mpspdz.join("Player-Data");
        let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0);
        let mut out = Vec::new();
        if let Ok(rd) = std::fs::read_dir(&dir) {
            for e in rd.flatten() {
                let name = e.file_name().to_string_lossy().into_owned();
                if name.starts_with("Mascot-Secrets-p-") && !name.contains(".retired-") {
                    let to = dir.join(format!("{name}.retired-{stamp}"));
                    if std::fs::rename(e.path(), &to).is_ok() {
                        out.push(to);
                    }
                }
            }
        }
        out
    }
}
