//! A resumable TCP relay over the custodian mesh (like `ssh -L`, but a link drop is a stall, not a reset): for each
//! peer j, local connections to 127.0.0.1:(forward_base + j) become streams to peer j's relay, which opens a plain TCP
//! connection to its own local service (`local`). Any number of streams per peer; bytes flow both ways in order;
//! a half-close on either end propagates. The mesh is `Net::connect_tls` (pinned identities, seq/ack, reconnect), so
//! the relayed program (MP-SPDZ) never sees a drop shorter than the reconnect budget.
//! Messages on tag RELAY: kind u8 | stream id u64 | payload. Stream ids: (opener party << 48) | counter.
use crate::net::{Net, RELAY};
use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream};
use std::sync::mpsc::{channel, Sender};
use std::sync::{Arc, Mutex};
use std::thread;

const OPEN: u8 = 1;
const DATA: u8 = 2;
const FIN: u8 = 3;

fn msg(kind: u8, sid: u64, payload: &[u8]) -> Vec<u8> {
    let mut m = Vec::with_capacity(9 + payload.len());
    m.push(kind);
    m.extend_from_slice(&sid.to_le_bytes());
    m.extend_from_slice(payload);
    m
}

/// local socket -> peer, until EOF; then FIN.
fn pump_out(net: Arc<Net>, peer: usize, sid: u64, mut s: TcpStream) {
    let mut buf = vec![0u8; 256 << 10];
    loop {
        match s.read(&mut buf) {
            Ok(0) | Err(_) => {
                net.send(peer, RELAY, msg(FIN, sid, &[]));
                return;
            }
            Ok(n) => net.send(peer, RELAY, msg(DATA, sid, &buf[..n])),
        }
    }
}

/// peer -> local socket, from this stream's queue (one writer per stream: a slow local reader holds up no other).
fn pump_in(rx: std::sync::mpsc::Receiver<Option<Vec<u8>>>, mut s: TcpStream) {
    while let Ok(m) = rx.recv() {
        match m {
            Some(b) => {
                if s.write_all(&b).is_err() {
                    // the local end is gone: drain and drop the rest
                    while rx.recv().is_ok() {}
                    return;
                }
            }
            None => {
                let _ = s.shutdown(Shutdown::Write);
                return;
            }
        }
    }
}

type Streams = Arc<Mutex<HashMap<(usize, u64), Sender<Option<Vec<u8>>>>>>;

/// Run the relay for party `me` on `net` until every peer link closes. `forward_base`: listen on 127.0.0.1:(base + j)
/// for peer j; `local`: this box's service the peers' streams reach.
pub fn run(net: Arc<Net>, forward_base: u16, local: SocketAddr) -> Result<(), String> {
    let me = net.me;
    let streams: Streams = Arc::new(Mutex::new(HashMap::new()));
    let mut hs = Vec::new();
    for j in net.others() {
        // outbound: local programs connecting to the forward port for j
        let l = TcpListener::bind(("127.0.0.1", forward_base + j as u16)).map_err(|e| format!("bind 127.0.0.1:{}: {e}", forward_base + j as u16))?;
        let (net2, streams2) = (net.clone(), streams.clone());
        hs.push(thread::spawn(move || {
            let mut ctr: u64 = 0;
            for c in l.incoming() {
                let Ok(s) = c else { continue };
                s.set_nodelay(true).ok();
                ctr += 1;
                let sid = ((me as u64) << 48) | ctr;
                let (tx, rx) = channel();
                streams2.lock().unwrap().insert((j, sid), tx);
                net2.send(j, RELAY, msg(OPEN, sid, &[]));
                let s2 = s.try_clone().unwrap();
                thread::spawn(move || pump_in(rx, s2));
                let n3 = net2.clone();
                thread::spawn(move || pump_out(n3, j, sid, s));
            }
        }));
        // inbound: peer j's messages
        let (net2, streams2) = (net.clone(), streams.clone());
        hs.push(thread::spawn(move || loop {
            let m = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| net2.recv(j, RELAY))) {
                Ok(m) => m,
                Err(_) => return,
            };
            if m.len() < 9 {
                continue;
            }
            let sid = u64::from_le_bytes(m[1..9].try_into().unwrap());
            match m[0] {
                OPEN => {
                    let s = match TcpStream::connect(local) {
                        Ok(s) => s,
                        Err(e) => {
                            eprintln!("relay: stream {sid:x} from party {j}: cannot reach {local}: {e}");
                            net2.send(j, RELAY, msg(FIN, sid, &[]));
                            continue;
                        }
                    };
                    s.set_nodelay(true).ok();
                    let (tx, rx) = channel();
                    streams2.lock().unwrap().insert((j, sid), tx);
                    let s2 = s.try_clone().unwrap();
                    thread::spawn(move || pump_in(rx, s2));
                    let n3 = net2.clone();
                    thread::spawn(move || pump_out(n3, j, sid, s));
                }
                DATA => {
                    if let Some(tx) = streams2.lock().unwrap().get(&(j, sid)) {
                        let _ = tx.send(Some(m[9..].to_vec()));
                    }
                }
                FIN => {
                    if let Some(tx) = streams2.lock().unwrap().remove(&(j, sid)) {
                        let _ = tx.send(None);
                    }
                }
                _ => {}
            }
        }));
    }
    for h in hs {
        let _ = h.join();
    }
    Ok(())
}
