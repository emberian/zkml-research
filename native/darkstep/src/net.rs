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

fn wire_up(
    stream: TcpStream,
    peer: usize,
    sent: Arc<[AtomicU64; NTAGS]>,
    by_peer: Arc<Vec<[AtomicU64; NTAGS]>>,
    threads: &mut Vec<thread::JoinHandle<()>>,
) -> Peer {
    stream.set_nodelay(true).ok();
    let rd = stream.try_clone().unwrap();
    let (tx, wrx) = sync_channel::<(u8, Vec<u8>)>(QCAP);
    threads.push(thread::spawn(move || {
        let mut w = BufWriter::with_capacity(1 << 20, stream);
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
        let _ = w.get_ref().shutdown(std::net::Shutdown::Write);
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
