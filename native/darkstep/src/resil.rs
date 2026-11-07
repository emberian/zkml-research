//! Resumable links for the TLS mesh. A link drop (a home Wi-Fi hiccup, a TCP write timeout) is not an abort: every
//! frame carries a sequence number, the receiver acknowledges, the sender keeps every unacknowledged frame, and the
//! dialing side reconnects under the same pinned TLS identities (bounded retry). After the new handshake each side
//! states the next sequence number it expects and the other retransmits from there, so every tag queue sees exactly
//! the frames it would have seen, once, in order.
//! A drop while the mesh is marked critical (`Net::set_critical`: the MAC check's and the Freivalds checks'
//! openings) is not resumed: that link is dead and the step aborts.
//! Frame on the wire: tag u8 | seq u64 LE | len u64 LE | payload. tag ACK: seq = the next sequence number expected;
//! tag BYE: the sender is done (a clean close, not a drop).
use std::collections::VecDeque;
use std::io::{BufReader, BufWriter, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, SyncSender};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

const ACK: u8 = 0xFF;
const BYE: u8 = 0xFE;
const ABORT: u8 = 0xFD;

pub struct Link {
    pub(crate) conn: Mutex<rustls::Connection>,
    pub(crate) sock_w: Mutex<TcpStream>,
}

impl Link {
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
    fn kill(&self) {
        let _ = self.sock_w.lock().unwrap().shutdown(std::net::Shutdown::Both);
    }
}

struct LinkWriter(Arc<Link>);

impl Write for LinkWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let mut sock = self.0.sock_w.lock().unwrap();
        let n = self.0.conn.lock().unwrap().writer().write(&buf[..buf.len().min(1 << 20)])?;
        self.0.drain(&mut sock)?;
        Ok(n)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        let mut sock = self.0.sock_w.lock().unwrap();
        self.0.drain(&mut sock)?;
        sock.flush()
    }
}

struct LinkReader {
    link: Arc<Link>,
    sock: TcpStream,
    raw: Vec<u8>,
    at: usize,
}

impl Read for LinkReader {
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

struct State {
    gen: u64,
    link: Option<(Arc<Link>, TcpStream)>,
    /// the next sequence number the peer expects (from the latest resume handshake)
    peer_expected: u64,
    /// first break of the current outage
    down_since: Option<Instant>,
}

/// One peer's resumable session (both directions).
pub struct Session {
    pub peer: usize,
    st: Mutex<State>,
    cv: Condvar,
    pub recv_next: AtomicU64,
    ack_pending: AtomicBool,
    unacked: Mutex<VecDeque<(u64, u8, Arc<Vec<u8>>)>>,
    pub dead: AtomicBool,
    pub closing: AtomicBool,
    critical: Arc<AtomicBool>,
    budget: Duration,
    pub reconnects: AtomicU64,
    peer_done: AtomicBool,
    /// this party aborts: tell the peer at once (its receives then fail too)
    pub abort_req: AtomicBool,
}

impl Session {
    pub fn new(peer: usize, critical: Arc<AtomicBool>, budget: Duration) -> Arc<Session> {
        Arc::new(Session {
            peer,
            st: Mutex::new(State { gen: 0, link: None, peer_expected: 0, down_since: Some(Instant::now()) }),
            cv: Condvar::new(),
            recv_next: AtomicU64::new(0),
            ack_pending: AtomicBool::new(false),
            unacked: Mutex::new(VecDeque::new()),
            dead: AtomicBool::new(false),
            closing: AtomicBool::new(false),
            critical,
            budget,
            reconnects: AtomicU64::new(0),
            peer_done: AtomicBool::new(false),
            abort_req: AtomicBool::new(false),
        })
    }

    /// A new connection for this session (after its TLS and resume handshakes).
    pub fn install(&self, sock: TcpStream, conn: rustls::Connection, peer_expected: u64) {
        sock.set_nodelay(true).ok();
        let rd = sock.try_clone().unwrap();
        let link = Arc::new(Link { conn: Mutex::new(conn), sock_w: Mutex::new(sock) });
        let mut st = self.st.lock().unwrap();
        if let Some((old, _)) = st.link.take() {
            old.kill();
        }
        if st.gen > 0 {
            self.reconnects.fetch_add(1, Ordering::Relaxed);
        }
        st.gen += 1;
        st.link = Some((link, rd));
        st.peer_expected = peer_expected;
        st.down_since = None;
        self.cv.notify_all();
    }

    /// The link of generation `gen` failed.
    fn broken(&self, gen: u64, why: &str) {
        let mut st = self.st.lock().unwrap();
        if st.gen != gen || st.link.is_none() {
            return;
        }
        if let Some((l, _)) = st.link.take() {
            l.kill();
        }
        if self.closing.load(Ordering::Relaxed) && self.peer_done.load(Ordering::Relaxed) {
            return;
        }
        if self.critical.load(Ordering::Relaxed) {
            eprintln!("link to party {}: dropped during a check phase ({why}): abort", self.peer);
            self.dead.store(true, Ordering::Relaxed);
        } else {
            eprintln!("link to party {}: dropped ({why}); resuming", self.peer);
        }
        st.down_since = Some(Instant::now());
        self.cv.notify_all();
    }

    pub fn is_down(&self) -> bool {
        self.st.lock().unwrap().link.is_none()
    }

    /// Wait until a link newer than `seen` is up; None when the session is dead (or the outage outlasts the budget).
    fn wait_link(&self, seen: u64) -> Option<(u64, Arc<Link>, Option<TcpStream>, u64)> {
        let mut st = self.st.lock().unwrap();
        loop {
            if self.dead.load(Ordering::Relaxed) {
                return None;
            }
            if st.gen > seen {
                if let Some((l, rd)) = &st.link {
                    return Some((st.gen, l.clone(), rd.try_clone().ok(), st.peer_expected));
                }
            }
            if let Some(t) = st.down_since {
                if t.elapsed() > self.budget {
                    eprintln!("link to party {}: down for over {:?}: abort", self.peer, self.budget);
                    self.dead.store(true, Ordering::Relaxed);
                    self.cv.notify_all();
                    return None;
                }
            }
            st = self.cv.wait_timeout(st, Duration::from_millis(200)).unwrap().0;
        }
    }

    /// Block while the session is up (for the reconnecting side); returns when it is down, or false when dead or
    /// closed.
    pub fn wait_down(&self) -> bool {
        let mut st = self.st.lock().unwrap();
        loop {
            if self.dead.load(Ordering::Relaxed) || (self.closing.load(Ordering::Relaxed) && self.peer_done.load(Ordering::Relaxed)) {
                return false;
            }
            if st.link.is_none() && st.gen > 0 {
                return true;
            }
            st = self.cv.wait_timeout(st, Duration::from_millis(200)).unwrap().0;
        }
    }

    pub fn out_of_budget(&self) -> bool {
        let st = self.st.lock().unwrap();
        st.down_since.map(|t| t.elapsed() > self.budget).unwrap_or(false)
    }

    pub fn kill_current(&self) {
        if let Some((l, _)) = &self.st.lock().unwrap().link {
            l.kill();
        }
    }
}

fn hdr(tag: u8, seq: u64, len: u64) -> [u8; 17] {
    let mut h = [0u8; 17];
    h[0] = tag;
    h[1..9].copy_from_slice(&seq.to_le_bytes());
    h[9..].copy_from_slice(&len.to_le_bytes());
    h
}

/// The writer thread of one session: frames from `wrx`, numbered, kept until acknowledged, resent after a resume.
#[allow(clippy::type_complexity)]
pub fn writer(s: Arc<Session>, wrx: Receiver<(u8, Vec<u8>)>, on_sent: impl Fn(u8, u64) + Send + 'static, kill_after: Option<(u64, bool)>) {
    let mut next: u64 = 0;
    let mut seen = 0u64;
    let mut sent_total = 0u64;
    let mut killed = false;
    'outer: loop {
        let Some((gen, link, _, peer_expected)) = s.wait_link(seen) else { return };
        seen = gen;
        let mut w = BufWriter::with_capacity(1 << 20, LinkWriter(link.clone()));
        // resume: drop what the peer has, resend the rest in order
        let resend: Vec<(u64, u8, Arc<Vec<u8>>)> = {
            let mut u = s.unacked.lock().unwrap();
            while u.front().is_some_and(|f| f.0 < peer_expected) {
                u.pop_front();
            }
            u.iter().cloned().collect()
        };
        for (seq, tag, buf) in resend {
            if w.write_all(&hdr(tag, seq, buf.len() as u64)).and_then(|_| w.write_all(&buf)).and_then(|_| w.flush()).is_err() {
                s.broken(gen, "write (resend)");
                continue 'outer;
            }
        }
        loop {
            if s.abort_req.load(Ordering::Relaxed) {
                let _ = w.write_all(&hdr(ABORT, 0, 0)).and_then(|_| w.flush());
                s.dead.store(true, Ordering::Relaxed);
                s.cv.notify_all();
                return;
            }
            if s.ack_pending.swap(false, Ordering::Relaxed) {
                let a = s.recv_next.load(Ordering::Relaxed);
                if w.write_all(&hdr(ACK, a, 0)).and_then(|_| w.flush()).is_err() {
                    s.ack_pending.store(true, Ordering::Relaxed);
                    s.broken(gen, "write (ack)");
                    continue 'outer;
                }
            }
            match wrx.recv_timeout(Duration::from_millis(20)) {
                Ok((tag, buf)) => {
                    let seq = next;
                    next += 1;
                    let buf = Arc::new(buf);
                    s.unacked.lock().unwrap().push_back((seq, tag, buf.clone()));
                    on_sent(tag, 17 + buf.len() as u64);
                    sent_total += 17 + buf.len() as u64;
                    if let Some((at, crit)) = kill_after {
                        let fire = if crit { s.critical.load(Ordering::Relaxed) } else { sent_total >= at };
                        if !killed && fire {
                            killed = true;
                            eprintln!("TEST: killing the link to party {} after {sent_total} bytes", s.peer);
                            link.kill();
                        }
                    }
                    if w.write_all(&hdr(tag, seq, buf.len() as u64)).and_then(|_| w.write_all(&buf)).and_then(|_| w.flush()).is_err() {
                        s.broken(gen, "write");
                        continue 'outer;
                    }
                }
                Err(RecvTimeoutError::Timeout) => {
                    if s.st.lock().unwrap().gen != gen {
                        continue 'outer;
                    }
                }
                Err(RecvTimeoutError::Disconnected) => {
                    // done sending: say so once per link, then keep acknowledging until the peer is done too and
                    // has everything of ours (a drop here resumes like any other)
                    s.closing.store(true, Ordering::Relaxed);
                    if w.write_all(&hdr(BYE, next, 0)).and_then(|_| w.flush()).is_err() {
                        s.broken(gen, "write (bye)");
                        continue 'outer;
                    }
                    let t = Instant::now();
                    loop {
                        if s.dead.load(Ordering::Relaxed) || t.elapsed() > s.budget {
                            return;
                        }
                        if s.st.lock().unwrap().gen != gen || s.is_down() {
                            continue 'outer;
                        }
                        if s.ack_pending.swap(false, Ordering::Relaxed) {
                            let a = s.recv_next.load(Ordering::Relaxed);
                            if w.write_all(&hdr(ACK, a, 0)).and_then(|_| w.flush()).is_err() {
                                s.ack_pending.store(true, Ordering::Relaxed);
                                s.broken(gen, "write (ack)");
                                continue 'outer;
                            }
                        }
                        if s.unacked.lock().unwrap().is_empty() && s.peer_done.load(Ordering::Relaxed) && !s.ack_pending.load(Ordering::Relaxed) {
                            // both directions complete: end the TCP stream so the peer's reader sees a clean EOF
                            let _ = w.flush();
                            if let Ok(lw) = w.into_inner() {
                                let mut sock = lw.0.sock_w.lock().unwrap();
                                lw.0.conn.lock().unwrap().send_close_notify();
                                let _ = lw.0.drain(&mut sock);
                                let _ = sock.shutdown(std::net::Shutdown::Write);
                            }
                            return;
                        }
                        thread::sleep(Duration::from_millis(10));
                    }
                }
            }
        }
    }
}

/// The reader thread of one session: frames in order into the tag queues, duplicates (after a resume) dropped.
pub fn reader(s: Arc<Session>, txs: Vec<SyncSender<Vec<u8>>>) {
    let mut seen = 0u64;
    loop {
        if s.peer_done.load(Ordering::Relaxed) && s.closing.load(Ordering::Relaxed) {
            return;
        }
        let Some((gen, link, Some(sock), _)) = s.wait_link(seen) else { return };
        seen = gen;
        let mut r = BufReader::with_capacity(1 << 20, LinkReader { link, sock, raw: Vec::new(), at: 0 });
        loop {
            let mut h = [0u8; 17];
            if r.read_exact(&mut h).is_err() {
                if s.peer_done.load(Ordering::Relaxed) {
                    return;
                }
                s.broken(gen, "read");
                break;
            }
            let tag = h[0];
            let seq = u64::from_le_bytes(h[1..9].try_into().unwrap());
            let len = u64::from_le_bytes(h[9..].try_into().unwrap()) as usize;
            if tag == ACK {
                let mut u = s.unacked.lock().unwrap();
                while u.front().is_some_and(|f| f.0 < seq) {
                    u.pop_front();
                }
                continue;
            }
            if tag == ABORT {
                eprintln!("party {} aborted the run", s.peer);
                s.dead.store(true, Ordering::Relaxed);
                s.cv.notify_all();
                return;
            }
            if tag == BYE {
                // the peer sent everything; keep reading its acknowledgements until it closes
                if seq == s.recv_next.load(Ordering::Relaxed) {
                    s.peer_done.store(true, Ordering::Relaxed);
                    s.ack_pending.store(true, Ordering::Relaxed);
                }
                continue;
            }
            if tag as usize >= txs.len() || len > (1 << 34) {
                eprintln!("link to party {}: malformed frame: abort", s.peer);
                s.dead.store(true, Ordering::Relaxed);
                return;
            }
            let mut buf = vec![0u8; len];
            if r.read_exact(&mut buf).is_err() {
                s.broken(gen, "read");
                break;
            }
            let want = s.recv_next.load(Ordering::Relaxed);
            if seq < want {
                s.ack_pending.store(true, Ordering::Relaxed);
                continue;
            }
            if seq > want {
                eprintln!("link to party {}: frame {seq} while expecting {want}: abort", s.peer);
                s.dead.store(true, Ordering::Relaxed);
                return;
            }
            if txs[tag as usize].send(buf).is_err() {
                return;
            }
            s.recv_next.store(want + 1, Ordering::Relaxed);
            s.ack_pending.store(true, Ordering::Relaxed);
        }
    }
}

fn c_write(c: &mut rustls::Connection, sock: &mut TcpStream, data: &[u8]) -> std::io::Result<()> {
    c.writer().write_all(data)?;
    while c.wants_write() {
        c.write_tls(sock)?;
    }
    sock.flush()
}

fn c_read_exact(c: &mut rustls::Connection, sock: &mut TcpStream, buf: &mut [u8]) -> std::io::Result<()> {
    let mut got = 0;
    while got < buf.len() {
        match c.reader().read(&mut buf[got..]) {
            Ok(0) => return Err(std::io::ErrorKind::UnexpectedEof.into()),
            Ok(k) => got += k,
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                if c.read_tls(sock)? == 0 {
                    return Err(std::io::ErrorKind::UnexpectedEof.into());
                }
                c.process_new_packets().map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
            }
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

/// After the TLS handshake: the dialer states the next sequence number it expects, then the acceptor does.
fn resume_dialer(stream: &mut TcpStream, c: &mut rustls::Connection, mine: u64) -> std::io::Result<u64> {
    c_write(c, stream, &mine.to_le_bytes())?;
    let mut b = [0u8; 8];
    c_read_exact(c, stream, &mut b)?;
    Ok(u64::from_le_bytes(b))
}

fn resume_acceptor(stream: &mut TcpStream, c: &mut rustls::Connection, mine: impl Fn() -> u64) -> std::io::Result<u64> {
    let mut b = [0u8; 8];
    c_read_exact(c, stream, &mut b)?;
    c_write(c, stream, &mine().to_le_bytes())?;
    Ok(u64::from_le_bytes(b))
}

/// Dial party j (TLS client pinned to its certificate) and resume the session.
pub fn dial(s: &Session, addr: SocketAddr, cfg: Arc<rustls::ClientConfig>, j: usize, timeout: Duration) -> Result<(), String> {
    let mut sock = TcpStream::connect_timeout(&addr, timeout).map_err(|e| format!("cannot reach party {j} at {addr}: {e}"))?;
    // a port in the ephemeral range with no listener yet can connect to itself (TCP simultaneous open from the same
    // source port): that is not the peer, so drop it and let the caller retry (run 12 died of this on forge)
    if sock.local_addr().ok() == sock.peer_addr().ok() {
        return Err(format!("cannot reach party {j} at {addr}: the socket connected to itself (no listener yet)"));
    }
    sock.set_read_timeout(Some(timeout)).ok();
    sock.set_write_timeout(Some(timeout)).ok();
    let name = rustls::pki_types::ServerName::try_from(format!("custodian-{j}")).map_err(|e| e.to_string())?;
    let mut c = rustls::Connection::Client(rustls::ClientConnection::new(cfg, name).map_err(|e| e.to_string())?);
    while c.is_handshaking() {
        c.complete_io(&mut sock).map_err(|e| format!("TLS handshake with party {j} refused: {e}"))?;
    }
    let peer_expected = resume_dialer(&mut sock, &mut c, s.recv_next.load(Ordering::Relaxed)).map_err(|e| format!("resume with party {j}: {e}"))?;
    sock.set_read_timeout(None).ok();
    sock.set_write_timeout(Some(Duration::from_secs(120))).ok();
    s.install(sock, c, peer_expected);
    Ok(())
}

/// Accept one dialer: TLS server with the pinned peer certificates; identify it; resume its session.
pub fn accept_one(mut sock: TcpStream, scfg: Arc<rustls::ServerConfig>, idx: &[(usize, Vec<u8>)], sessions: &[Option<Arc<Session>>], timeout: Duration) -> Result<usize, String> {
    sock.set_nonblocking(false).map_err(|e| e.to_string())?;
    sock.set_read_timeout(Some(timeout)).ok();
    sock.set_write_timeout(Some(timeout)).ok();
    let mut c = rustls::ServerConnection::new(scfg).map_err(|e| e.to_string())?;
    while c.is_handshaking() {
        c.complete_io(&mut sock).map_err(|e| format!("handshake: {e}"))?;
    }
    let pc = c.peer_certificates().and_then(|v| v.first()).ok_or("no client certificate")?.as_ref().to_vec();
    let j = idx.iter().find(|(_, d)| *d == pc).map(|x| x.0).ok_or("unpinned client")?;
    let s = sessions[j].as_ref().ok_or("no session")?;
    let mut c = rustls::Connection::Server(c);
    let peer_expected = resume_acceptor(&mut sock, &mut c, || s.recv_next.load(Ordering::Relaxed)).map_err(|e| format!("resume with party {j}: {e}"))?;
    sock.set_read_timeout(None).ok();
    sock.set_write_timeout(Some(Duration::from_secs(120))).ok();
    s.install(sock, c, peer_expected);
    Ok(j)
}

/// Keep accepting (re)connections from the higher-numbered parties until `closed`.
pub fn acceptor(listener: TcpListener, scfg: Arc<rustls::ServerConfig>, idx: Vec<(usize, Vec<u8>)>, sessions: Vec<Option<Arc<Session>>>, closed: Arc<AtomicBool>, me: usize) {
    listener.set_nonblocking(true).ok();
    while !closed.load(Ordering::Relaxed) {
        match listener.accept() {
            Ok((sock, from)) => {
                let (scfg, idx, sessions) = (scfg.clone(), idx.clone(), sessions.clone());
                thread::spawn(move || {
                    if let Err(e) = accept_one(sock, scfg, &idx, &sessions, Duration::from_secs(30)) {
                        eprintln!("party {me}: refused a connection from {from}: {e}");
                    }
                });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => thread::sleep(Duration::from_millis(20)),
            Err(_) => thread::sleep(Duration::from_millis(100)),
        }
    }
}

/// The dialing side's reconnector for one session: whenever it is down, redial with backoff within the budget.
pub fn reconnector(s: Arc<Session>, addr: SocketAddr, cfg: Arc<rustls::ClientConfig>, j: usize) {
    while s.wait_down() {
        let mut wait = Duration::from_millis(100);
        loop {
            if s.dead.load(Ordering::Relaxed) {
                return;
            }
            if s.out_of_budget() {
                s.dead.store(true, Ordering::Relaxed);
                s.cv.notify_all();
                return;
            }
            match dial(&s, addr, cfg.clone(), j, Duration::from_secs(15)) {
                Ok(()) => {
                    eprintln!("link to party {j}: resumed (reconnect {})", s.reconnects.load(Ordering::Relaxed));
                    break;
                }
                Err(e) => {
                    eprintln!("link to party {j}: {e}; retrying in {wait:?}");
                    thread::sleep(wait);
                    wait = (wait * 2).min(Duration::from_secs(5));
                }
            }
        }
    }
}
