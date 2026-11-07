//! The custodian mesh over mutual TLS with pinned certificates (Net::connect_tls).
use darkstep::net::{Net, CTRL, HE_CT, HE_RET};
use darkstep::tls::{generate, Identity};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

const MARK: &[u8] = b"DARKSTEP-PLAINTEXT-MARKER-0123456789";

fn listeners() -> (Vec<TcpListener>, Vec<SocketAddr>) {
    let l: Vec<TcpListener> = (0..3).map(|_| TcpListener::bind("127.0.0.1:0").unwrap()).collect();
    let a = l.iter().map(|x| x.local_addr().unwrap()).collect();
    (l, a)
}

/// A TCP relay in front of `to`; returns its address and everything that crossed it (both directions).
fn relay(to: SocketAddr) -> (SocketAddr, Arc<Mutex<Vec<u8>>>) {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let at = l.local_addr().unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let s2 = seen.clone();
    thread::spawn(move || {
        for c in l.incoming() {
            let a = c.unwrap();
            let b = TcpStream::connect(to).unwrap();
            for (mut x, mut y) in [(a.try_clone().unwrap(), b.try_clone().unwrap()), (b, a)] {
                let seen = s2.clone();
                thread::spawn(move || {
                    let mut buf = vec![0u8; 1 << 16];
                    loop {
                        let n = match x.read(&mut buf) {
                            Ok(0) | Err(_) => {
                                let _ = y.shutdown(std::net::Shutdown::Write);
                                return;
                            }
                            Ok(n) => n,
                        };
                        seen.lock().unwrap().extend_from_slice(&buf[..n]);
                        if y.write_all(&buf[..n]).is_err() {
                            return;
                        }
                    }
                });
            }
        }
    });
    (at, seen)
}

fn payload(i: usize, j: usize, k: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(k);
    while v.len() < k {
        v.extend_from_slice(MARK);
        v.extend_from_slice(format!("{i}->{j}|").as_bytes());
    }
    v.truncate(k);
    v
}

fn mesh(ids: Vec<Identity>, pinned: Vec<Vec<u8>>, ls: Vec<TcpListener>, addrs_of: Vec<Vec<SocketAddr>>, t: Duration) -> Vec<Result<Net, String>> {
    let pinned = Arc::new(pinned);
    let hs: Vec<_> = ids
        .into_iter()
        .zip(ls)
        .zip(addrs_of)
        .enumerate()
        .map(|(i, ((id, l), addrs))| {
            let pinned = pinned.clone();
            thread::spawn(move || Net::connect_tls(i, if i < 2 { Some(l) } else { None }, &addrs, &id, &pinned, t))
        })
        .collect();
    hs.into_iter().map(|h| h.join().unwrap()).collect()
}

#[test]
fn tls_mesh_moves_bytes_encrypted_and_counts_links() {
    let ids: Vec<Identity> = (0..3).map(generate).collect();
    let pinned: Vec<Vec<u8>> = ids.iter().map(|x| x.cert_der.clone()).collect();
    let (ls, addrs) = listeners();
    // party 1 reaches party 0 through a recording relay
    let (via, seen) = relay(addrs[0]);
    let mut a1 = addrs.clone();
    a1[0] = via;
    let nets = mesh(ids, pinned, ls, vec![addrs.clone(), a1, addrs.clone()], Duration::from_secs(20));
    let nets: Vec<Net> = nets.into_iter().map(|r| r.unwrap()).collect();
    eprintln!("mesh up");
    let big = 24 << 20;
    thread::scope(|sc| {
        for net in &nets {
            sc.spawn(move || {
                let i = net.me;
                for j in net.others() {
                    net.send(j, HE_RET, payload(i, j, big));
                    net.send(j, HE_CT, payload(i, j, 1000));
                }
                for j in net.others() {
                    // tags are independent queues: read HE_CT first although HE_RET was sent first
                    assert_eq!(net.recv(j, HE_CT), payload(j, i, 1000));
                    assert_eq!(net.recv(j, HE_RET), payload(j, i, big));
                }
                let all = net.exchange(CTRL, &[i as u64 * 7]);
                assert_eq!(all, vec![vec![0], vec![7], vec![14]]);
            });
        }
    });
    eprintln!("data moved");
    for net in &nets {
        let per = net.sent_per_peer();
        for j in net.others() {
            assert_eq!(per[j][HE_RET as usize], 17 + big as u64, "TLS frames: tag, seq, len");
            assert_eq!(per[j][HE_CT as usize], 17 + 1000);
        }
    }
    // each party closes on its own (its readers end when the peers close)
    let hs: Vec<_> = nets.into_iter().map(|n| thread::spawn(move || n.shutdown())).collect();
    for h in hs {
        h.join().unwrap();
    }
    let seen = seen.lock().unwrap();
    assert!(seen.len() > 2 * big, "the relay carried the 0 <-> 1 link ({} bytes)", seen.len());
    assert!(!seen.windows(MARK.len()).any(|w| w == MARK), "plaintext visible on the wire");
}

#[test]
fn an_unpinned_dialer_is_refused() {
    let ids: Vec<Identity> = (0..3).map(generate).collect();
    let pinned: Vec<Vec<u8>> = ids.iter().map(|x| x.cert_der.clone()).collect();
    // party 2 presents a different certificate from the one the run pinned for it
    let mut ids = ids;
    ids[2] = generate(2);
    let (ls, addrs) = listeners();
    let r = mesh(ids, pinned, ls, vec![addrs.clone(); 3], Duration::from_secs(4));
    for i in 0..2 {
        let e = r[i].as_ref().err().unwrap_or_else(|| panic!("party {i} accepted an unpinned party 2"));
        assert!(e.contains("no authenticated connection from [2]"), "party {i}: {e}");
    }
}

#[test]
fn an_unpinned_listener_is_refused() {
    let ids: Vec<Identity> = (0..3).map(generate).collect();
    let pinned: Vec<Vec<u8>> = ids.iter().map(|x| x.cert_der.clone()).collect();
    // party 0 (listening) presents a certificate nobody pinned: its dialers must refuse it
    let mut ids = ids;
    ids[0] = generate(0);
    let (ls, addrs) = listeners();
    let r = mesh(ids, pinned, ls, vec![addrs.clone(); 3], Duration::from_secs(4));
    for i in 1..3 {
        let e = r[i].as_ref().err().unwrap_or_else(|| panic!("party {i} accepted an unpinned party 0"));
        assert!(e.contains("TLS handshake with party 0 refused") || e.contains("no authenticated connection"), "party {i}: {e}");
    }
    assert!(r[1].as_ref().err().unwrap().contains("TLS handshake with party 0 refused"));
}

/// Control for the wire check above: over the plain TCP mesh the same relay sees the plaintext.
#[test]
fn control_plain_tcp_shows_plaintext_on_the_relay() {
    let (ls, addrs) = listeners();
    let (via, seen) = relay(addrs[0]);
    let mut a1 = addrs.clone();
    a1[0] = via;
    let addrs_of = [addrs.clone(), a1, addrs.clone()];
    let hs: Vec<_> = ls
        .into_iter()
        .enumerate()
        .map(|(i, l)| {
            let a = addrs_of[i].clone();
            thread::spawn(move || {
                let net = Net::connect(i, l, &a);
                for j in net.others() {
                    net.send(j, HE_RET, payload(i, j, 4096));
                }
                for j in net.others() {
                    assert_eq!(net.recv(j, HE_RET), payload(j, i, 4096));
                }
                net
            })
        })
        .collect();
    let nets: Vec<Net> = hs.into_iter().map(|h| h.join().unwrap()).collect();
    let hs: Vec<_> = nets.into_iter().map(|n| thread::spawn(move || n.shutdown())).collect();
    for h in hs {
        h.join().unwrap();
    }
    assert!(seen.lock().unwrap().windows(MARK.len()).any(|w| w == MARK));
}

fn clean_mesh(t: Duration) -> Vec<Net> {
    let ids: Vec<Identity> = (0..3).map(generate).collect();
    let pinned: Vec<Vec<u8>> = ids.iter().map(|x| x.cert_der.clone()).collect();
    let (ls, addrs) = listeners();
    mesh(ids, pinned, ls, vec![addrs.clone(); 3], t).into_iter().map(|r| r.unwrap()).collect()
}

/// A connection killed mid-transfer (twice, on two links) is resumed: every frame arrives once, in order.
#[test]
fn a_dropped_link_resumes_and_delivers_every_frame_once() {
    let nets = clean_mesh(Duration::from_secs(20));
    let big = 8 << 20;
    thread::scope(|sc| {
        for net in &nets {
            sc.spawn(move || {
                let i = net.me;
                for j in net.others() {
                    for r in 0..6 {
                        net.send(j, HE_RET, payload(i, j + 10 * r, big));
                    }
                }
                for j in net.others() {
                    for r in 0..6 {
                        assert_eq!(net.recv(j, HE_RET), payload(j, i + 10 * r, big), "{j} -> {i} frame {r}");
                    }
                }
                assert_eq!(net.exchange(CTRL, &[i as u64]), vec![vec![0], vec![1], vec![2]]);
            });
        }
        let n = &nets;
        sc.spawn(move || {
            thread::sleep(Duration::from_millis(40));
            n[1].test_kill_link(0);
            thread::sleep(Duration::from_millis(60));
            n[0].test_kill_link(2);
        });
    });
    assert!(nets[1].reconnects()[0] >= 1, "link 1-0 was resumed: {:?}", nets[1].reconnects());
    assert!(nets[2].reconnects()[0] >= 1, "link 2-0 was resumed: {:?}", nets[2].reconnects());
    let hs: Vec<_> = nets.into_iter().map(|n| thread::spawn(move || n.shutdown())).collect();
    for h in hs {
        h.join().unwrap();
    }
}

/// The same drop while the mesh is in a check phase is an abort: the link is dead and a receive on it fails.
#[test]
fn a_drop_in_a_check_phase_is_an_abort() {
    let nets = clean_mesh(Duration::from_secs(20));
    for n in &nets {
        n.set_critical(true);
    }
    nets[1].test_kill_link(0);
    let t = std::time::Instant::now();
    while !(nets[0].link_dead(1) && nets[1].link_dead(0)) && t.elapsed() < Duration::from_secs(10) {
        thread::sleep(Duration::from_millis(20));
    }
    assert!(nets[0].link_dead(1) && nets[1].link_dead(0), "both ends of the dropped link are dead");
    assert!(!nets[2].link_dead(0) && !nets[2].link_dead(1), "the other links are not");
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| nets[0].recv(1, HE_RET)));
    assert!(r.is_err(), "a receive on a dead link fails");
}

/// A NAT seat (Net::connect_tls_nat): seat 0, which normally listens for both others, binds nothing and dials
/// them; its advertised address is a port held by a listener that never accepts. The mesh comes up and moves
/// bytes both ways. Control: the same addresses without the NAT role fail (seat 1 and 2 dial the dead port).
#[test]
fn a_nat_seat_dials_every_peer_and_binds_nothing() {
    use darkstep::net::{check_nat, dials};
    assert!(dials(0, 1, &[0]) && dials(0, 2, &[0]) && !dials(1, 0, &[0]) && dials(2, 1, &[0]));
    assert!(dials(2, 0, &[]) && !dials(0, 2, &[]));
    let lo: SocketAddr = "127.0.0.1:1".parse().unwrap();
    let far: SocketAddr = "10.1.2.3:1".parse().unwrap();
    assert!(check_nat(&[lo, far, far], &[0, 2]).is_ok(), "two NAT seats on one box: the lower one's loopback address");
    assert!(check_nat(&[far, far, lo], &[0, 2]).unwrap_err().contains("need a relay"), "two NAT seats on two boxes are refused");
    let run = |nat: Vec<usize>| -> Vec<Result<Net, String>> {
        let ids: Vec<Identity> = (0..3).map(generate).collect();
        let pinned = Arc::new(ids.iter().map(|x| x.cert_der.clone()).collect::<Vec<_>>());
        let dead = TcpListener::bind("127.0.0.1:0").unwrap();
        let (ls, mut addrs) = listeners();
        addrs[0] = dead.local_addr().unwrap();
        let mut ls: Vec<Option<TcpListener>> = ls.into_iter().map(Some).collect();
        ls[0] = None;
        let hs: Vec<_> = ids
            .into_iter()
            .zip(ls)
            .enumerate()
            .map(|(i, (id, l))| {
                let (pinned, addrs, nat) = (pinned.clone(), addrs.clone(), nat.clone());
                // a seat listens iff a peer dials it; seat 0 never has a listener of its own (without the NAT role the
                // others dial its dead port)
                let l = if (0..3).any(|j| j != i && dials(j, i, &nat)) { l } else { None };
                thread::spawn(move || {
                    let r = Net::connect_tls_nat(i, l, &addrs, &id, &pinned, Duration::from_secs(15), &nat);
                    r
                })
            })
            .collect();
        let r = hs.into_iter().map(|h| h.join().unwrap()).collect();
        drop(dead);
        r
    };
    let nets: Vec<Net> = run(vec![0]).into_iter().map(|r| r.unwrap()).collect();
    thread::scope(|sc| {
        for net in &nets {
            sc.spawn(move || {
                let i = net.me;
                for j in net.others() {
                    net.send(j, CTRL, payload(i, j, 4096));
                }
                for j in net.others() {
                    assert_eq!(net.recv(j, CTRL), payload(j, i, 4096));
                }
            });
        }
    });
    // the three close together (a shutdown waits for its peers' close)
    let hs: Vec<_> = nets.into_iter().map(|n| thread::spawn(move || n.shutdown())).collect();
    for h in hs {
        h.join().unwrap();
    }
    let ctl = run(vec![]);
    eprintln!("control: {:?}", ctl.iter().map(|r| r.as_ref().err()).collect::<Vec<_>>());
    assert!(ctl.iter().any(|r| r.is_err()), "control: without the NAT role the mesh cannot form");
}
