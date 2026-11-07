//! The multi-step custodian: one process per custodian holds its weight shares across steps (they never leave it),
//! takes each step's inputs from the data owner, checkpoints after every step, and can stop at a step boundary and
//! resume from its checkpoint (forge's nightly pause). The links are `Net::connect_tls`; the owner link is TLS too.
use crate::he::He;
use crate::net::{self, bytes_to_u64s, u64s_to_bytes, Net};
use crate::node::{setup_he, Prof, MV_SEED, OU_SEED};
use crate::party::{Party, Sh, Transcript};
use crate::step::*;
use crate::tape::Tape;
use serde_json::json;
use std::io::{Read, Write};
use std::time::Instant;

pub type Shares = (Vec<Vec<Sh>>, Vec<Vec<Sh>>);

/// Everything a custodian holds across steps. Its key material is in `he` (key, gate), its weight shares in `w`.
pub struct CustodianState {
    pub i: usize,
    pub pf: Prof,
    pub he: He,
    pub pt: Party,
    pub w: Option<Shares>,
    /// the next step's index (0 = genesis)
    pub step: usize,
    pub tab: Vec<Vec<u64>>,
    pool: rayon::ThreadPool,
    last_sent: Vec<[u64; 5]>,
    last_gate: [f64; 3],
    last_proof_bytes: u64,
}

/// Process CPU seconds (user + system) and peak RSS (kB), where /proc exists.
pub fn proc_usage() -> (Option<f64>, Option<u64>) {
    let cpu = std::fs::read_to_string("/proc/self/stat").ok().and_then(|st| {
        let rest = &st[st.rfind(')')? + 2..];
        let f: Vec<&str> = rest.split_whitespace().collect();
        let tck = 100.0; // USER_HZ on Linux
        Some((f.get(11)?.parse::<f64>().ok()? + f.get(12)?.parse::<f64>().ok()?) / tck)
    });
    let rss = std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|st| st.lines().find_map(|l| l.strip_prefix("VmHWM:")).and_then(|r| r.trim().trim_end_matches("kB").trim().parse().ok()));
    (cpu, rss)
}

impl CustodianState {
    /// Keys (the ceremony when gated) over `net`, then a party on `tape` at cursor `cur`.
    pub fn new(i: usize, pf: Prof, net: Net, tape: Tape, attack: Option<(String, usize)>) -> Result<Self, (String, Net)> {
        let he = match setup_he(i, &pf, &net, attack) {
            Ok(h) => h,
            Err(e) => return Err((e, net)),
        };
        let tab = pf.program.tables(pf.t);
        let pool = rayon::ThreadPoolBuilder::new().num_threads(pf.threads).build().unwrap();
        let n = net.n;
        let pt = Party::new(i, pf.t, net, tape);
        Ok(CustodianState { i, pf, he, pt, w: None, step: 0, tab, pool, last_sent: vec![[0; 5]; n], last_gate: [0.0; 3], last_proof_bytes: 0 })
    }

    /// Continue on a new tape (the next chunk). Its MAC key share must be the one the carried shares are under.
    pub fn load_tape(&mut self, tape: Tape) -> Result<(), String> {
        if tape.alpha_i != self.pt.tape.alpha_i {
            return Err("tape: a new MAC key share; the carried weight shares are not under it (halt)".into());
        }
        self.pt.tape = tape;
        self.pt.cur = 0;
        Ok(())
    }

    /// One step on the owner's broadcasts `cs` (genesis: W1, W2, x, y; carried: x, y). Returns the step's report and
    /// its proof record; the new weight shares stay in `self.w`.
    pub fn run(&mut self, cs: &[u64]) -> Result<(serde_json::Value, ProofRecord), String> {
        let d = self.pf.d;
        let k = self.step;
        let (cpu0, _) = proc_usage();
        // per-step public state: the transcript, the MAC-check log and the proof atoms cover this step only
        self.pt.tr = Transcript::default();
        self.pt.open_log.clear();
        self.pt.atom_log.clear();
        self.pt.wire.clear();
        self.pt.nopen = 0;
        let cur0 = self.pt.cur;
        self.he.context.1 = k as u64;
        self.he.mv_calls = 0;
        self.he.ou_calls = 0;
        // reference coins (test harness only): the proof lane's per-step seeds; secure coins: a fresh return key
        self.he.mv_seed = MV_SEED + 100 * k as u64;
        self.he.ou_seed = OU_SEED + 100 * k as u64;
        self.he.key.refresh_return_key();
        let t0 = Instant::now();
        let pg = self.pf.program;
        let (pt, he, tab) = (&mut self.pt, &mut self.he, &self.tab);
        let w = self.w.take();
        let res = self.pool.install(|| match w {
            None => {
                if cs.len() != 2 * d * d + 2 * d {
                    return Err(format!("genesis step: {} owner inputs, want 2d^2 + 2d", cs.len()));
                }
                run_step_prog(pt, he, cs, d, tab, &pg)
            }
            Some((m1, m2)) => {
                if cs.len() != 2 * d {
                    return Err(format!("carried step: {} owner inputs, want 2d", cs.len()));
                }
                let ti = Instant::now();
                let sx = pt.input_vec(&cs[..d]);
                let sy = pt.input_vec(&cs[d..]);
                let input_s = ti.elapsed().as_secs_f64();
                run_step_shares(pt, he, m1, m2, sx, sy, d, tab, &pg).map(|mut o| {
                    o.phases.insert(0, ("input", input_s));
                    o
                })
            }
        });
        let step_s = t0.elapsed().as_secs_f64();
        let out = res?;
        let per = self.pt.net.sent_per_peer();
        let links: serde_json::Map<String, serde_json::Value> = per
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != self.i)
            .map(|(j, s)| {
                let dlt: Vec<u64> = (0..5).map(|t| s[t] - self.last_sent[j][t]).collect();
                (j.to_string(), json!({"open": dlt[0], "he_ct": dlt[1], "he_ret": dlt[2], "ctrl": dlt[3], "proof": dlt[4], "total": dlt.iter().sum::<u64>()}))
            })
            .collect();
        self.last_sent = per;
        let (cpu1, rss) = proc_usage();
        let mut rep = json!({
            "party": self.i, "step": k, "verdict": "ACCEPT", "step_seconds": step_s,
            "cpu_seconds": cpu0.zip(cpu1).map(|(a, b)| b - a), "peak_rss_kb": rss,
            "transcript": transcript_digest(&self.pt.tr), "transcript_len": self.pt.tr.len(),
            "sigma": out.sigma, "tape_used": self.pt.cur - cur0,
            "phases": out.phases.iter().map(|(n, s)| json!([n, s])).collect::<Vec<_>>(),
            "bytes_sent_to": links,
        });
        if let Some(g) = &self.he.gate {
            rep["gate"] = json!({
                "prove_seconds": g.prove_s - self.last_gate[0], "verify_seconds": g.verify_s - self.last_gate[1],
                "zk_lock_wait_seconds": g.wait_s - self.last_gate[2], "proof_bytes_sent": g.proof_bytes_sent - self.last_proof_bytes,
            });
            self.last_gate = [g.prove_s, g.verify_s, g.wait_s];
            self.last_proof_bytes = g.proof_bytes_sent;
        }
        self.w = Some((out.w1n, out.w2n));
        self.step += 1;
        Ok((rep, out.record))
    }

    /// The custodian's own checkpoint: next step index, tape cursor, its MAC key share (to check the next tape
    /// against) and its weight shares. Written to a temporary file and renamed, mode 0600.
    pub fn checkpoint(&self, path: &std::path::Path) -> std::io::Result<()> {
        let (w1, w2) = self.w.as_ref().expect("no weights before the genesis step");
        let tmp = path.with_extension("tmp");
        {
            let mut f = std::io::BufWriter::new(open_private(&tmp)?);
            f.write_all(b"DLCKPT01")?;
            for x in [self.i as u64, self.step as u64, self.pf.d as u64, self.pt.tape.alpha_i, self.pt.cur as u64] {
                f.write_all(&x.to_le_bytes())?;
            }
            for m in [w1, w2] {
                for row in m {
                    let flat: Vec<u64> = row.iter().flat_map(|x| [x.s, x.m]).collect();
                    f.write_all(&u64s_to_bytes(&flat))?;
                }
            }
            f.flush()?;
            f.get_ref().sync_all()?;
        }
        std::fs::rename(tmp, path)
    }
}

pub struct Checkpoint {
    pub i: usize,
    pub step: usize,
    pub d: usize,
    pub alpha_i: u64,
    pub cur: usize,
    pub w: Shares,
}

pub fn read_checkpoint(path: &std::path::Path) -> Result<Checkpoint, String> {
    let b = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if b.len() < 48 || &b[..8] != b"DLCKPT01" {
        return Err("not a darkstep checkpoint".into());
    }
    let h = bytes_to_u64s(&b[8..48]);
    let d = h[2] as usize;
    let v = bytes_to_u64s(&b[48..]);
    if v.len() != 4 * d * d {
        return Err("checkpoint: wrong length".into());
    }
    let sh: Vec<Sh> = v.chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect();
    let rows: Vec<Vec<Sh>> = sh.chunks(d).map(|r| r.to_vec()).collect();
    Ok(Checkpoint { i: h[0] as usize, step: h[1] as usize, d, alpha_i: h[3], cur: h[4] as usize, w: (rows[..d].to_vec(), rows[d..].to_vec()) })
}

pub fn open_private(p: &std::path::Path) -> std::io::Result<std::fs::File> {
    let mut o = std::fs::OpenOptions::new();
    o.write(true).create(true).truncate(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        o.mode(0o600);
    }
    o.open(p)
}

impl CustodianState {
    /// Resume from `ck`: the weight shares and the step index; the tape at the checkpoint's cursor.
    pub fn resume(&mut self, ck: Checkpoint) -> Result<(), String> {
        if ck.i != self.i || ck.d != self.pf.d {
            return Err("checkpoint: another custodian's or another width's".into());
        }
        if ck.alpha_i != self.pt.tape.alpha_i {
            return Err("checkpoint: under another MAC key share than this tape".into());
        }
        self.w = Some(ck.w);
        self.step = ck.step;
        self.pt.cur = ck.cur;
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------------------- owner link
// Frames on the owner link: u64 LE length | payload. Custodian -> owner: u64 step | its owner message (may be
// empty: the test dealer's owner needs none). Owner -> custodian: u64 step | the step's broadcasts c = v - r.

pub fn write_frame(w: &mut impl Write, b: &[u8]) -> std::io::Result<()> {
    w.write_all(&(b.len() as u64).to_le_bytes())?;
    w.write_all(b)?;
    w.flush()
}

pub fn read_frame(r: &mut impl Read) -> std::io::Result<Vec<u8>> {
    let mut l = [0u8; 8];
    r.read_exact(&mut l)?;
    let n = u64::from_le_bytes(l) as usize;
    if n > (1 << 34) {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "frame too long"));
    }
    let mut b = vec![0u8; n];
    r.read_exact(&mut b)?;
    Ok(b)
}

pub type OwnerStream = rustls::StreamOwned<rustls::ClientConnection, std::net::TcpStream>;

/// Custodian side: dial the owner (it must present `owner_cert`), authenticated by this custodian's identity.
pub fn dial_owner(addr: std::net::SocketAddr, id: &crate::tls::Identity, owner_cert: &[u8], timeout: std::time::Duration) -> Result<OwnerStream, String> {
    let deadline = Instant::now() + timeout;
    let s = loop {
        match std::net::TcpStream::connect(addr) {
            Ok(s) => break s,
            Err(e) if Instant::now() > deadline => return Err(format!("owner at {addr}: {e}")),
            Err(_) => std::thread::sleep(std::time::Duration::from_millis(100)),
        }
    };
    s.set_nodelay(true).ok();
    let name = rustls::pki_types::ServerName::try_from("data-owner").unwrap();
    let c = rustls::ClientConnection::new(crate::tls::client_config(id, owner_cert), name).map_err(|e| e.to_string())?;
    let mut st = rustls::StreamOwned::new(c, s);
    while st.conn.is_handshaking() {
        st.conn.complete_io(&mut st.sock).map_err(|e| format!("owner TLS handshake refused: {e}"))?;
    }
    Ok(st)
}

/// Ask the owner for step `k`'s broadcasts (sending this custodian's owner message), then check with the other
/// custodians that all three received the same bytes (an owner that equivocates is caught here).
pub fn owner_inputs(owner: &mut OwnerStream, net: &Net, k: usize, msg: &[u8]) -> Result<Vec<u64>, String> {
    let mut req = (k as u64).to_le_bytes().to_vec();
    req.extend_from_slice(msg);
    write_frame(owner, &req).map_err(|e| format!("owner: {e}"))?;
    let b = read_frame(owner).map_err(|e| format!("owner: {e}"))?;
    if b.len() < 8 || u64::from_le_bytes(b[..8].try_into().unwrap()) != k as u64 {
        return Err(format!("owner: no inputs for step {k}"));
    }
    let cs = bytes_to_u64s(&b[8..]);
    use sha2::{Digest, Sha256};
    let mine = Sha256::digest(&b[8..]).to_vec();
    let all = net.exchange_bytes(net::CTRL, &mine);
    if all.iter().any(|h| h != &mine) {
        return Err(format!("owner equivocated at step {k}: the custodians received different inputs"));
    }
    Ok(cs)
}

/// The owner side. Accept the three custodians (each must present its pinned certificate), then serve steps:
/// for each step all three ask (step k, owner message); `inputs(k, msgs)` gives the broadcasts c, sent to all three.
/// Ends when a custodian closes (step u64::MAX) or `inputs` fails. Returns one record per step served.
pub fn owner_serve(
    listener: std::net::TcpListener,
    id: &crate::tls::Identity,
    certs: &[Vec<u8>],
    mut inputs: impl FnMut(usize, &[Vec<u8>]) -> Result<Vec<u64>, String>,
) -> Result<Vec<serde_json::Value>, String> {
    let scfg = crate::tls::server_config(id, certs);
    let mut conns: Vec<Option<rustls::StreamOwned<rustls::ServerConnection, std::net::TcpStream>>> = (0..certs.len()).map(|_| None).collect();
    while conns.iter().any(|c| c.is_none()) {
        let (mut s, from) = listener.accept().map_err(|e| e.to_string())?;
        s.set_nodelay(true).ok();
        let mut c = rustls::ServerConnection::new(scfg.clone()).map_err(|e| e.to_string())?;
        let ok = (|| {
            while c.is_handshaking() {
                c.complete_io(&mut s).map_err(|e| e.to_string())?;
            }
            let pc = c.peer_certificates().and_then(|v| v.first()).ok_or("no certificate")?.as_ref().to_vec();
            certs.iter().position(|x| *x == pc).ok_or_else(|| "unpinned".to_string())
        })();
        match ok {
            Ok(j) if conns[j].is_none() => conns[j] = Some(rustls::StreamOwned::new(c, s)),
            Ok(j) => eprintln!("owner: refused a second connection from custodian {j}"),
            Err(e) => eprintln!("owner: refused {from}: {e}"),
        }
    }
    let mut conns: Vec<_> = conns.into_iter().map(|c| c.unwrap()).collect();
    let mut log = Vec::new();
    let res = loop {
        let reqs: Vec<Vec<u8>> = conns.iter_mut().map(|c| read_frame(c).unwrap_or_default()).collect();
        if reqs.iter().any(|r| r.len() < 8 || u64::from_le_bytes(r[..8].try_into().unwrap()) == u64::MAX) {
            break Ok(log);
        }
        let ks: Vec<u64> = reqs.iter().map(|r| u64::from_le_bytes(r[..8].try_into().unwrap())).collect();
        if ks.iter().any(|&k| k != ks[0]) {
            break Err(format!("owner: custodians ask for different steps {ks:?}"));
        }
        let k = ks[0] as usize;
        let t0 = Instant::now();
        let msgs: Vec<Vec<u8>> = reqs.iter().map(|r| r[8..].to_vec()).collect();
        let cs = match inputs(k, &msgs) {
            Ok(c) => c,
            Err(e) => break Err(e),
        };
        let mut out = (k as u64).to_le_bytes().to_vec();
        out.extend_from_slice(&u64s_to_bytes(&cs));
        for c in conns.iter_mut() {
            write_frame(c, &out).map_err(|e| e.to_string())?;
        }
        use sha2::{Digest, Sha256};
        let rec = json!({"step": k, "inputs": cs.len(), "sha256": pycompat::repr::hex(&Sha256::digest(&out[8..])), "seconds": t0.elapsed().as_secs_f64()});
        println!("{rec}");
        log.push(rec);
    };
    for c in conns.iter_mut() {
        c.conn.send_close_notify();
        let _ = c.conn.complete_io(&mut c.sock);
    }
    res
}
