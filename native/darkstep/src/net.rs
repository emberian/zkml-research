//! A full mesh of TCP connections between the custodians. Every connection has a writer thread fed by a bounded
//! queue and a reader thread that dispatches frames by stream tag into bounded per-tag queues, so a party computing
//! HE returns never blocks the delivery of what its peers need (no head-of-line deadlock between the tags).
//! Frame: tag u8 | len u64 LE | payload.
use std::collections::HashMap;
use std::io::{BufReader, BufWriter, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{sync_channel, Receiver, SyncSender};
use std::sync::{Arc, Mutex};
use std::thread;

pub const OPEN: u8 = 0;
pub const HE_CT: u8 = 1;
pub const HE_RET: u8 = 2;
pub const CTRL: u8 = 3;
/// The collaborative proof's exchanges (Beaver openings, share broadcasts, commitments) between custodians.
pub const PROOF: u8 = 4;
const NTAGS: usize = 5;
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

/// One TLS session shared by a link's reader and writer threads. Lock order: `sock_w`, then `conn`; nothing blocks
/// on the network while `conn` is held, so the reader keeps decrypting while the writer waits on the socket. Every
/// TLS record leaves through `sock_w` in the order `conn` made it.
struct TlsLink {
    conn: Mutex<rustls::Connection>,
    sock_w: Mutex<TcpStream>,
}

impl TlsLink {
    /// Encrypt-and-send whatever the session has queued (called with `sock_w` held).
    fn drain(&self, sock: &mut TcpStream) -> std::io::Result<()> {
        let mut out = Vec::new();
        {
            let mut c = self.conn.lock().unwrap();
            while c.wants_write() {
                c.write_tls(&mut out)?;
            }
        }
        sock.write_all(&out)
    }
}

struct TlsWriter(Arc<TlsLink>);

impl Write for TlsWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let mut sock = self.0.sock_w.lock().unwrap();
        let n = {
            let mut c = self.0.conn.lock().unwrap();
            c.writer().write(&buf[..buf.len().min(1 << 20)])?
        };
        self.0.drain(&mut sock)?;
        Ok(n)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        let mut sock = self.0.sock_w.lock().unwrap();
        self.0.drain(&mut sock)?;
        sock.flush()
    }
}

impl Sink for TlsWriter {
    fn close(&mut self) {
        let mut sock = self.0.sock_w.lock().unwrap();
        self.0.conn.lock().unwrap().send_close_notify();
        let _ = self.0.drain(&mut sock);
        let _ = sock.shutdown(std::net::Shutdown::Write);
    }
}

struct TlsReader {
    link: Arc<TlsLink>,
    sock: TcpStream,
    raw: Vec<u8>,
    at: usize,
}

impl Read for TlsReader {
    fn read(&mut self, out: &mut [u8]) -> std::io::Result<usize> {
        loop {
            {
                let mut c = self.link.conn.lock().unwrap();
                match c.reader().read(out) {
                    Ok(n) => return Ok(n),
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                    Err(e) => return Err(e),
                }
                if self.at < self.raw.len() {
                    let mut rest = &self.raw[self.at..];
                    let k = c.read_tls(&mut rest)?;
                    self.at += k;
                    c.process_new_packets().map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
                    let ww = c.wants_write();
                    drop(c);
                    // a record the session must send back (an alert, a key update reply); if the writer holds
                    // the socket it drains the session itself, so never wait for it here
                    if ww {
                        if let Ok(mut sock) = self.link.sock_w.try_lock() {
                            self.link.drain(&mut sock)?;
                        }
                    }
                    continue;
                }
            }
            self.raw.resize(1 << 20, 0);
            let n = self.sock.read(&mut self.raw)?;
            if n == 0 {
                return Ok(0);
            }
            self.raw.truncate(n);
            self.at = 0;
        }
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
        Net { me, n, peers, sent_bytes: sent, sent_by_peer: by_peer, threads }
    }

    /// The same mesh over mutual TLS 1.3 with pinned certificates (`tls`): party `me` dials every lower-numbered
    /// party and accepts every higher-numbered one, so the highest-numbered seat only dials (a box behind NAT).
    /// `certs[j]` is party j's certificate; an accepted dialer is identified by the certificate it presents, and a
    /// connection presenting anything else is refused. Fails if the mesh is not complete within `timeout`.
    pub fn connect_tls(me: usize, listener: Option<TcpListener>, addrs: &[SocketAddr], id: &crate::tls::Identity, certs: &[Vec<u8>], timeout: std::time::Duration) -> Result<Net, String> {
        use std::time::Instant;
        let n = addrs.len();
        let deadline = Instant::now() + timeout;
        let left = || deadline.saturating_duration_since(Instant::now()).max(std::time::Duration::from_millis(1));
        let mut links: HashMap<usize, (TcpStream, rustls::Connection)> = HashMap::new();
        // accept the higher-numbered parties in a thread while dialing the lower ones
        let want_in = n - 1 - me;
        let acc = if want_in > 0 {
            let listener = listener.ok_or("party must listen: higher-numbered parties dial it")?;
            let others: Vec<Vec<u8>> = (me + 1..n).map(|j| certs[j].clone()).collect();
            let scfg = crate::tls::server_config(id, &others);
            let idx: Vec<(usize, Vec<u8>)> = (me + 1..n).map(|j| (j, certs[j].clone())).collect();
            listener.set_nonblocking(true).map_err(|e| e.to_string())?;
            Some(thread::spawn(move || -> Result<Vec<(usize, TcpStream, rustls::Connection)>, String> {
                let (htx, hrx) = std::sync::mpsc::channel();
                let mut got: Vec<(usize, TcpStream, rustls::Connection)> = Vec::new();
                while got.len() < want_in {
                    if Instant::now() > deadline {
                        let have: Vec<usize> = got.iter().map(|g| g.0).collect();
                        return Err(format!("party {me}: no authenticated connection from {:?} in time (have {have:?})",
                            (me + 1..n).filter(|j| !have.contains(j)).collect::<Vec<_>>()));
                    }
                    match listener.accept() {
                        Ok((mut s, from)) => {
                            let scfg = scfg.clone();
                            let idx = idx.clone();
                            let htx = htx.clone();
                            thread::spawn(move || {
                                let r = (|| -> Result<(usize, TcpStream, rustls::Connection), String> {
                                    s.set_nonblocking(false).map_err(|e| e.to_string())?;
                                    s.set_read_timeout(Some(deadline.saturating_duration_since(Instant::now()).max(std::time::Duration::from_millis(1)))).ok();
                                    let mut c = rustls::ServerConnection::new(scfg).map_err(|e| e.to_string())?;
                                    while c.is_handshaking() {
                                        c.complete_io(&mut s).map_err(|e| format!("handshake from {from}: {e}"))?;
                                    }
                                    let pc = c.peer_certificates().and_then(|v| v.first()).ok_or("no client certificate")?;
                                    let j = idx.iter().find(|(_, d)| d.as_slice() == pc.as_ref()).map(|x| x.0).ok_or("unpinned client")?;
                                    s.set_read_timeout(None).ok();
                                    Ok((j, s, rustls::Connection::Server(c)))
                                })();
                                let _ = htx.send(r);
                            });
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => thread::sleep(std::time::Duration::from_millis(10)),
                        Err(e) => return Err(e.to_string()),
                    }
                    while let Ok(r) = hrx.try_recv() {
                        match r {
                            Ok((j, s, c)) if !got.iter().any(|g| g.0 == j) => got.push((j, s, c)),
                            Ok((j, _, _)) => eprintln!("party {me}: refused a second connection from party {j}"),
                            Err(e) => eprintln!("party {me}: refused a connection: {e}"),
                        }
                    }
                }
                Ok(got)
            }))
        } else {
            None
        };
        for j in 0..me {
            let mut s = loop {
                match TcpStream::connect_timeout(&addrs[j], left()) {
                    Ok(s) => break s,
                    Err(e) => {
                        if Instant::now() > deadline {
                            return Err(format!("party {me}: cannot reach party {j} at {}: {e}", addrs[j]));
                        }
                        thread::sleep(std::time::Duration::from_millis(50));
                    }
                }
            };
            s.set_read_timeout(Some(left())).ok();
            let name = rustls::pki_types::ServerName::try_from(format!("custodian-{j}")).map_err(|e| e.to_string())?;
            let mut c = rustls::ClientConnection::new(crate::tls::client_config(id, &certs[j]), name).map_err(|e| e.to_string())?;
            while c.is_handshaking() {
                c.complete_io(&mut s).map_err(|e| format!("party {me}: TLS handshake with party {j} refused: {e}"))?;
            }
            s.set_read_timeout(None).ok();
            links.insert(j, (s, rustls::Connection::Client(c)));
        }
        if let Some(h) = acc {
            for (j, s, c) in h.join().map_err(|_| "acceptor panicked")?? {
                links.insert(j, (s, c));
            }
        }
        let sent: Arc<[AtomicU64; NTAGS]> = Arc::new(Default::default());
        let by_peer: Arc<Vec<[AtomicU64; NTAGS]>> = Arc::new((0..n).map(|_| Default::default()).collect());
        let mut threads = Vec::new();
        let mut peers = Vec::new();
        for j in 0..n {
            peers.push(links.remove(&j).map(|(s, c)| {
                s.set_nodelay(true).ok();
                let rd = s.try_clone().unwrap();
                let link = Arc::new(TlsLink { conn: Mutex::new(c), sock_w: Mutex::new(s) });
                let reader = TlsReader { link: link.clone(), sock: rd, raw: Vec::new(), at: 0 };
                wire(reader, TlsWriter(link), j, sent.clone(), by_peer.clone(), &mut threads)
            }));
        }
        Ok(Net { me, n, peers, sent_bytes: sent, sent_by_peer: by_peer, threads })
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
        for t in self.threads.drain(..) {
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
