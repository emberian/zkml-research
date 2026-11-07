//! The resumable relay: streams from local clients on one seat reach a local service on another seat through the
//! TLS mesh, in order, both ways, with half-close; a link killed mid-transfer is a stall, not a reset.
use darkstep::net::Net;
use darkstep::tls::{generate, Identity};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

/// A local service: echoes everything back, then closes after the client's half-close.
fn echo() -> SocketAddr {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let a = l.local_addr().unwrap();
    thread::spawn(move || {
        for c in l.incoming() {
            let mut s = c.unwrap();
            thread::spawn(move || {
                let mut b = vec![0u8; 1 << 16];
                loop {
                    match s.read(&mut b) {
                        Ok(0) | Err(_) => {
                            let _ = s.shutdown(std::net::Shutdown::Write);
                            return;
                        }
                        Ok(n) => s.write_all(&b[..n]).unwrap(),
                    }
                }
            });
        }
    });
    a
}

fn free_run(k: u16) -> u16 {
    // k consecutive free ports
    loop {
        let p = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        if p < 60000 && (0..k).all(|j| TcpListener::bind(("127.0.0.1", p + j)).is_ok()) {
            return p;
        }
    }
}

#[test]
fn relay_streams_survive_a_link_drop() {
    let ids: Vec<Identity> = (0..3).map(generate).collect();
    let certs: Vec<Vec<u8>> = ids.iter().map(|x| x.cert_der.clone()).collect();
    let ls: Vec<TcpListener> = (0..3).map(|_| TcpListener::bind("127.0.0.1:0").unwrap()).collect();
    let addrs: Vec<SocketAddr> = ls.iter().map(|l| l.local_addr().unwrap()).collect();
    let hs: Vec<_> = ids
        .into_iter()
        .zip(ls)
        .enumerate()
        .map(|(i, (id, l))| {
            let (addrs, certs) = (addrs.clone(), certs.clone());
            thread::spawn(move || Net::connect_tls(i, if i < 2 { Some(l) } else { None }, &addrs, &id, &certs, Duration::from_secs(20)).unwrap())
        })
        .collect();
    let nets: Vec<Arc<Net>> = hs.into_iter().map(|h| Arc::new(h.join().unwrap())).collect();
    let services: Vec<SocketAddr> = (0..3).map(|_| echo()).collect();
    let b0 = free_run(9);
    let bases: Vec<u16> = (0..3).map(|i| b0 + 3 * i as u16).collect();
    for i in 0..3 {
        let (n, b, s) = (nets[i].clone(), bases[i], services[i]);
        thread::spawn(move || darkstep::relay::run(n, b, s).unwrap());
    }
    thread::sleep(Duration::from_millis(200));
    // party 2 (dial-only) talks to party 0's service, party 0 to party 1's: 3 streams each, 6 MB per stream
    let mut clients = Vec::new();
    for (from, to) in [(2usize, 0usize), (0, 1)] {
        for k in 0..3u8 {
            let port = bases[from] + to as u16;
            clients.push(thread::spawn(move || {
                let mut s = TcpStream::connect(("127.0.0.1", port)).unwrap();
                let data: Vec<u8> = (0..6 << 20).map(|x: u32| (x.wrapping_mul(2654435761) >> 13) as u8 ^ k).collect();
                let mut r = s.try_clone().unwrap();
                let reader = thread::spawn(move || {
                    let mut got = Vec::new();
                    r.read_to_end(&mut got).unwrap();
                    got
                });
                for c in data.chunks(100_000) {
                    s.write_all(c).unwrap();
                    thread::sleep(Duration::from_millis(8));
                }
                s.shutdown(std::net::Shutdown::Write).unwrap();
                assert_eq!(reader.join().unwrap(), data, "stream {from}->{to}/{k}: every byte back, in order, then EOF");
            }));
        }
    }
    thread::sleep(Duration::from_millis(120));
    nets[2].test_kill_link(0);
    thread::sleep(Duration::from_millis(120));
    nets[1].test_kill_link(0);
    let t = std::time::Instant::now();
    let resumed = || nets[2].reconnects()[0] >= 1 && nets[1].reconnects()[0] >= 1;
    while !resumed() && t.elapsed() < Duration::from_secs(10) {
        thread::sleep(Duration::from_millis(20));
    }
    assert!(resumed(), "both links were resumed");
    let mid = clients.iter().filter(|c| !c.is_finished()).count();
    assert!(mid > 0, "the drops happened while streams were open");
    for c in clients {
        c.join().unwrap();
    }
}
