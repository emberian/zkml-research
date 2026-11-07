//! A full mesh of TCP connections between the custodians. Every connection has a writer thread fed by a bounded
//! queue and a reader thread that dispatches frames by stream tag into bounded per-tag queues, so a party computing
//! HE returns never blocks the delivery of what its peers need (no head-of-line deadlock between the tags).
//! Frame: tag u8 | len u64 LE | payload.
use std::collections::HashMap;
use std::io::{BufReader, BufWriter, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{sync_channel, Receiver, SyncSender};
use std::sync::{Arc, Mutex};
use std::thread;

pub const OPEN: u8 = 0;
pub const HE_CT: u8 = 1;
pub const HE_RET: u8 = 2;
pub const CTRL: u8 = 3;
/// The collaborative proof's exchanges (Beaver openings, share broadcasts, commitments) between custodians.
pub const PROOF: u8 = 4;
/// The handover's resharing (old committee to new), point to point.
pub const RESHARE: u8 = 5;
/// The relay's multiplexed TCP streams (`relay`).
pub const RELAY: u8 = 6;
pub const NTAGS: usize = 7;
const QCAP: usize = 64;

struct Peer {
    tx: SyncSender<(u8, Vec<u8>)>,
    rx: Vec<Mutex<Receiver<Vec<u8>>>>,
}

pub struct Net {
    pub me: usize,
    pub n: usize,
    peers: Vec<Option<Peer>>,
    pub sent_bytes: Arc<[AtomicU64; NTAGS]>,
    /// Bytes written to each peer, per tag (frame headers included); the own entry stays zero.
    pub sent_by_peer: Arc<Vec<[AtomicU64; NTAGS]>>,
    threads: Vec<thread::JoinHandle<()>>,
    critical: Arc<AtomicBool>,
    closed: Arc<AtomicBool>,
    sessions: Vec<Option<Arc<crate::resil::Session>>>,
}

/// TEST ONLY (feature test-harness): DS_TEST_KILL=peer,bytes kills the link to `peer` once after `bytes` sent to it;
/// DS_TEST_KILL=peer,critical kills it the first time the mesh is critical.
fn test_kill() -> Option<(usize, u64, bool)> {
    #[cfg(feature = "test-harness")]
    {
        let v = std::env::var("DS_TEST_KILL").ok()?;
        let (p, b) = v.split_once(',')?;
        let p: usize = p.parse().ok()?;
        if b == "critical" {
            return Some((p, 0, true));
        }
        return Some((p, b.parse().ok()?, false));
    }
    #[allow(unreachable_code)]
    None
}

/// The writing half of one link: plain TCP or a TLS client stream (each direction of a TLS mesh is its own
/// connection, so one thread owns each TLS session).
trait Sink: Write + Send + 'static {
    fn close(&mut self);
}

impl Sink for TcpStream {
    fn close(&mut self) {
        let _ = self.shutdown(std::net::Shutdown::Write);
    }
}

fn wire_up(stream: TcpStream, peer: usize, sent: Arc<[AtomicU64; NTAGS]>, by_peer: Arc<Vec<[AtomicU64; NTAGS]>>, threads: &mut Vec<thread::JoinHandle<()>>) -> Peer {
    stream.set_nodelay(true).ok();
    let rd = stream.try_clone().unwrap();
    wire(rd, stream, peer, sent, by_peer, threads)
}

fn wire<R: Read + Send + 'static, W: Sink>(
    rd: R,
    wr: W,
    peer: usize,
    sent: Arc<[AtomicU64; NTAGS]>,
    by_peer: Arc<Vec<[AtomicU64; NTAGS]>>,
    threads: &mut Vec<thread::JoinHandle<()>>,
) -> Peer {
    let (tx, wrx) = sync_channel::<(u8, Vec<u8>)>(QCAP);
    threads.push(thread::spawn(move || {
        let mut w = BufWriter::with_capacity(1 << 20, wr);
        while let Ok((tag, buf)) = wrx.recv() {
            let mut hdr = [0u8; 9];
            hdr[0] = tag;
            hdr[1..].copy_from_slice(&(buf.len() as u64).to_le_bytes());
            if w.write_all(&hdr).and_then(|_| w.write_all(&buf)).is_err() {
                return;
            }
            sent[tag as usize].fetch_add(9 + buf.len() as u64, Ordering::Relaxed);
            by_peer[peer][tag as usize].fetch_add(9 + buf.len() as u64, Ordering::Relaxed);
            if w.flush().is_err() {
                return;
            }
        }
        let _ = w.flush();
        if let Ok(mut inner) = w.into_inner() {
            inner.close();
        }
    }));
    let mut txs = Vec::new();
    let mut rxs = Vec::new();
    for _ in 0..NTAGS {
        let (t, r) = sync_channel::<Vec<u8>>(QCAP);
        txs.push(t);
        rxs.push(Mutex::new(r));
    }
    threads.push(thread::spawn(move || {
        let mut r = BufReader::with_capacity(1 << 20, rd);
        loop {
            let mut hdr = [0u8; 9];
            if r.read_exact(&mut hdr).is_err() {
                return;
            }
            if hdr[0] as usize >= NTAGS {
                return;
            }
            let len = u64::from_le_bytes(hdr[1..].try_into().unwrap()) as usize;
            let mut buf = vec![0u8; len];
            if r.read_exact(&mut buf).is_err() {
                return;
            }
            if txs[hdr[0] as usize].send(buf).is_err() {
                return;
            }
        }
    }));
    Peer { tx, rx: rxs }
}

impl Net {
    /// Party `me` listens on `listener` (its own address in `addrs`), dials every lower-numbered party, and accepts
    /// every higher-numbered one; each dialer announces its index.
    pub fn connect(me: usize, listener: TcpListener, addrs: &[SocketAddr]) -> Net {
        let n = addrs.len();
        let sent: Arc<[AtomicU64; NTAGS]> = Arc::new(Default::default());
        let by_peer: Arc<Vec<[AtomicU64; NTAGS]>> = Arc::new((0..n).map(|_| Default::default()).collect());
        let mut threads = Vec::new();
        let mut streams: HashMap<usize, TcpStream> = HashMap::new();
        for j in 0..me {
            let s = loop {
                match TcpStream::connect(addrs[j]) {
                    Ok(s) => break s,
                    Err(_) => thread::sleep(std::time::Duration::from_millis(20)),
                }
            };
            let mut s2 = s.try_clone().unwrap();
            s2.write_all(&(me as u64).to_le_bytes()).unwrap();
            streams.insert(j, s);
        }
        for _ in me + 1..n {
            let (mut s, _) = listener.accept().unwrap();
            let mut b = [0u8; 8];
            s.read_exact(&mut b).unwrap();
            streams.insert(u64::from_le_bytes(b) as usize, s);
        }
        let mut peers = Vec::new();
        for j in 0..n {
            peers.push(streams.remove(&j).map(|s| wire_up(s, j, sent.clone(), by_peer.clone(), &mut threads)));
        }
        Net { me, n, peers, sent_bytes: sent, sent_by_peer: by_peer, threads, critical: Arc::new(AtomicBool::new(false)), closed: Arc::new(AtomicBool::new(false)), sessions: vec![] }
    }

    /// The same mesh over mutual TLS 1.3 with pinned certificates (`tls`): party `me` dials every lower-numbered
    /// party and accepts every higher-numbered one, so the highest-numbered seat only dials (a box behind NAT).
    /// `certs[j]` is party j's certificate; an accepted dialer is identified by the certificate it presents, and a
    /// connection presenting anything else is refused. Fails if the mesh is not complete within `timeout`.
    pub fn connect_tls(me: usize, listener: Option<TcpListener>, addrs: &[SocketAddr], id: &crate::tls::Identity, certs: &[Vec<u8>], timeout: std::time::Duration) -> Result<Net, String> {
        use crate::resil::{self, Session};
        use std::time::{Duration, Instant};
        let n = addrs.len();
        let deadline = Instant::now() + timeout;
        let budget = Duration::from_secs(std::env::var("DS_RECONNECT_SECS").ok().and_then(|s| s.parse().ok()).unwrap_or(600));
        let critical = Arc::new(AtomicBool::new(false));
        let closed = Arc::new(AtomicBool::new(false));
        let sessions: Vec<Option<Arc<Session>>> = (0..n).map(|j| (j != me).then(|| Session::new(j, critical.clone(), budget))).collect();
        let mut threads = Vec::new();
        if me + 1 < n {
            let listener = listener.ok_or("party must listen: higher-numbered parties dial it")?;
            let others: Vec<Vec<u8>> = (me + 1..n).map(|j| certs[j].clone()).collect();
            let scfg = crate::tls::server_config(id, &others);
            let idx: Vec<(usize, Vec<u8>)> = (me + 1..n).map(|j| (j, certs[j].clone())).collect();
            let (ss, cl) = (sessions.clone(), closed.clone());
            threads.push(thread::spawn(move || resil::acceptor(listener, scfg, idx, ss, cl, me)));
        }
        let ccfgs: Vec<Option<Arc<rustls::ClientConfig>>> = (0..n).map(|j| (j < me).then(|| crate::tls::client_config(id, &certs[j]))).collect();
        for j in 0..me {
            let s = sessions[j].as_ref().unwrap();
            loop {
                match resil::dial(s, addrs[j], ccfgs[j].clone().unwrap(), j, Duration::from_secs(10)) {
                    Ok(()) => break,
                    Err(e) if e.contains("TLS handshake") => {
                        closed.store(true, Ordering::Relaxed);
                        return Err(format!("party {me}: {e}"));
                    }
                    Err(e) => {
                        if Instant::now() > deadline {
                            closed.store(true, Ordering::Relaxed);
                            return Err(format!("party {me}: {e}"));
                        }
                        thread::sleep(Duration::from_millis(50));
                    }
                }
            }
        }
        // the higher-numbered parties' first connections
        loop {
            let missing: Vec<usize> = (me + 1..n).filter(|&j| sessions[j].as_ref().unwrap().is_down()).collect();
            if missing.is_empty() {
                break;
            }
            if Instant::now() > deadline {
                closed.store(true, Ordering::Relaxed);
                return Err(format!("party {me}: no authenticated connection from {missing:?} in time"));
            }
            thread::sleep(Duration::from_millis(10));
        }
        let sent: Arc<[AtomicU64; NTAGS]> = Arc::new(Default::default());
        let by_peer: Arc<Vec<[AtomicU64; NTAGS]>> = Arc::new((0..n).map(|_| Default::default()).collect());
        let kill = test_kill();
        let mut peers = Vec::new();
        for j in 0..n {
            peers.push(sessions[j].clone().map(|s| {
                let (tx, wrx) = sync_channel::<(u8, Vec<u8>)>(QCAP);
                let (sent, by_peer) = (sent.clone(), by_peer.clone());
                let k = kill.filter(|k| k.0 == j).map(|k| (k.1, k.2));
                let s2 = s.clone();
                threads.push(thread::spawn(move || {
                    resil::writer(s2, wrx, move |tag, b| {
                        sent[tag as usize].fetch_add(b, Ordering::Relaxed);
                        by_peer[j][tag as usize].fetch_add(b, Ordering::Relaxed);
                    }, k)
                }));
                let mut txs = Vec::new();
                let mut rxs = Vec::new();
                for _ in 0..NTAGS {
                    let (t, r) = sync_channel::<Vec<u8>>(QCAP);
                    txs.push(t);
                    rxs.push(Mutex::new(r));
                }
                let s3 = s.clone();
                threads.push(thread::spawn(move || resil::reader(s3, txs)));
                if j < me {
                    let s4 = s.clone();
                    let (addr, cfg) = (addrs[j], ccfgs[j].clone().unwrap());
                    threads.push(thread::spawn(move || resil::reconnector(s4, addr, cfg, j)));
                }
                Peer { tx, rx: rxs }
            }));
        }
        Ok(Net { me, n, peers, sent_bytes: sent, sent_by_peer: by_peer, threads, critical, closed, sessions })
    }

    /// Mark the check phases (MAC check, Freivalds): a link drop now is an abort, not a resume (TLS mesh only).
    pub fn set_critical(&self, on: bool) {
        self.critical.store(on, Ordering::Relaxed);
    }

    /// TEST ONLY: cut the current connection to peer j (as a network drop would).
    #[cfg(feature = "test-harness")]
    pub fn test_kill_link(&self, j: usize) {
        if let Some(s) = self.sessions[j].as_ref() {
            s.kill_current();
        }
    }

    /// Abort: every peer is told at once (TLS mesh), so their receives fail instead of waiting for a resume.
    pub fn abort(&self) {
        for s in self.sessions.iter().flatten() {
            s.abort_req.store(true, Ordering::Relaxed);
        }
        let t = std::time::Instant::now();
        while self.sessions.iter().flatten().any(|s| !s.dead.load(Ordering::Relaxed)) && t.elapsed() < std::time::Duration::from_secs(5) {
            thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    /// Is the session to peer j dead (a drop in a check phase, or an outage past the budget)?
    pub fn link_dead(&self, j: usize) -> bool {
        self.sessions.get(j).and_then(|s| s.as_ref()).map(|s| s.dead.load(Ordering::Relaxed)).unwrap_or(false)
    }

    /// Reconnections per peer so far (TLS mesh).
    pub fn reconnects(&self) -> Vec<u64> {
        self.sessions.iter().map(|s| s.as_ref().map(|s| s.reconnects.load(Ordering::Relaxed)).unwrap_or(0)).collect()
    }

    pub fn send(&self, to: usize, tag: u8, buf: Vec<u8>) {
        self.peers[to].as_ref().expect("no self-send").tx.send((tag, buf)).expect("peer writer gone");
    }

    pub fn sender(&self, to: usize) -> SyncSender<(u8, Vec<u8>)> {
        self.peers[to].as_ref().unwrap().tx.clone()
    }

    pub fn recv(&self, from: usize, tag: u8) -> Vec<u8> {
        self.peers[from].as_ref().expect("no self-recv").rx[tag as usize].lock().unwrap().recv().expect("peer gone")
    }

    pub fn others(&self) -> Vec<usize> {
        (0..self.n).filter(|&j| j != self.me).collect()
    }

    /// Send `mine` to every other party and receive theirs; index by party (own entry included).
    pub fn exchange(&self, tag: u8, mine: &[u64]) -> Vec<Vec<u64>> {
        let b = u64s_to_bytes(mine);
        for j in self.others() {
            self.send(j, tag, b.clone());
        }
        (0..self.n)
            .map(|j| if j == self.me { mine.to_vec() } else { bytes_to_u64s(&self.recv(j, tag)) })
            .collect()
    }

    pub fn exchange_bytes(&self, tag: u8, mine: &[u8]) -> Vec<Vec<u8>> {
        for j in self.others() {
            self.send(j, tag, mine.to_vec());
        }
        (0..self.n).map(|j| if j == self.me { mine.to_vec() } else { self.recv(j, tag) }).collect()
    }

    pub fn total_sent(&self) -> [u64; NTAGS] {
        let mut o = [0; NTAGS];
        for (k, x) in self.sent_bytes.iter().enumerate() {
            o[k] = x.load(Ordering::Relaxed);
        }
        o
    }

    /// Bytes sent to each peer, per tag: `[peer][tag]`.
    pub fn sent_per_peer(&self) -> Vec<[u64; NTAGS]> {
        self.sent_by_peer.iter().map(|row| std::array::from_fn(|k| row[k].load(Ordering::Relaxed))).collect()
    }

    /// Close the writers (dropping the queues ends the writer threads) and join everything.
    pub fn shutdown(mut self) {
        self.peers.clear();
        // writers drain and say goodbye; the acceptor stops once every writer and reader has finished
        let closed = self.closed.clone();
        let sessions = self.sessions.clone();
        thread::spawn(move || {
            while sessions.iter().flatten().any(|s| !(s.closing.load(Ordering::Relaxed) || s.dead.load(Ordering::Relaxed))) {
                thread::sleep(std::time::Duration::from_millis(20));
            }
            thread::sleep(std::time::Duration::from_millis(200));
            closed.store(true, Ordering::Relaxed);
        });
        for (k, t) in self.threads.drain(..).enumerate() {
            if std::env::var("DS_DEBUG_JOIN").is_ok() {
                eprintln!("party {}: joining thread {k}", self.me);
            }
            let _ = t.join();
        }
    }
}

pub fn u64s_to_bytes(v: &[u64]) -> Vec<u8> {
    let mut b = Vec::with_capacity(v.len() * 8);
    for x in v {
        b.extend_from_slice(&x.to_le_bytes());
    }
    b
}

pub fn bytes_to_u64s(b: &[u8]) -> Vec<u64> {
    b.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect()
}
