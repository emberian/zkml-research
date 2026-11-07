//! The HE-assisted matvec (he_matvec.HEMatvec) and outer product (he_outer.HEOuter) from one custodian's seat, in
//! the harness's per-return-stream mode. As sender j a party encrypts its share blocks under its own key and sends
//! them to both others; as returner i it multiplies by its plaintext share blocks and returns masked, flooded
//! ciphertexts; as recipient j it decrypts its returns. The recipient runs on its own thread so returners never wait
//! on it.
use crate::arith::*;
use crate::bfv::{make_return, Ct, OwnKey, PubKey};
use crate::net::{self, bytes_to_u64s, u64s_to_bytes};
use crate::party::*;
use crate::rns::Rns;
use pycompat::{PyRandom, ReprHasher};
use rayon::prelude::*;
use std::sync::Arc;

pub struct He {
    pub rns: Arc<Rns>,
    pub key: OwnKey,
    pub pks: Vec<PubKey>,
    pub f_bits: u32,
    pub mv_seed: u64,
    pub ou_seed: u64,
    pub mv_calls: u64,
    pub ou_calls: u64,
    pub context: (String, u64, u64),
    pub he_send: u64,
    pub he_return: u64,
    pub ou_send: u64,
    pub ou_return: u64,
    pub ou_commit: u64,
    pub cts_sent: u64,
    pub cts_returned: u64,
    pub attack: Option<(String, usize)>,
    /// the recipient's ZKPoPK gate (None: the ungated OwnKey path, bit-exact with native_ref.py)
    pub gate: Option<crate::gate::Gate>,
}

fn ct_bytes(hdr: &[u64], ct: &Ct) -> Vec<u8> {
    let mut v = hdr.to_vec();
    v.extend_from_slice(&ct.c0);
    v.extend_from_slice(&ct.c1);
    u64s_to_bytes(&v)
}

fn ct_parse(b: &[u8], nh: usize, ln: usize) -> (Vec<u64>, Ct) {
    let v = bytes_to_u64s(b);
    assert_eq!(v.len(), nh + 2 * ln, "ciphertext frame length");
    (v[..nh].to_vec(), Ct { c0: v[nh..nh + ln].to_vec(), c1: v[nh + ln..].to_vec() })
}

/// Decryption threads per recipient (std threads, not rayon: a rayon worker blocked on a socket could starve the
/// returner jobs the peers are waiting for).
pub const DEC_THREADS: usize = 4;

/// Receive `per_peer` returns from each of `peers`, decrypt each at `coefs`, and hand (header, plaintexts) to `sink`.
/// Every peer has its own decryption threads, so a slow peer never holds up the drain of another (the returners'
/// bounded queues would otherwise couple all three parties into a wait cycle).
fn recv_decrypt<F: Fn(&[u64], &[u64]) + Sync>(net: &crate::net::Net, key: &OwnKey, peers: &[usize], per_peer: usize, nh: usize, coefs: &[usize], sink: F) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let ln = key.rns.l() * key.rns.n;
    let claimed: Vec<AtomicUsize> = peers.iter().map(|_| AtomicUsize::new(0)).collect();
    let per_thread = (DEC_THREADS / peers.len().max(1)).max(1);
    std::thread::scope(|sc| {
        for (pi, &i) in peers.iter().enumerate() {
            for _ in 0..per_thread {
                let (claimed, sink) = (&claimed, &sink);
                sc.spawn(move || {
                    while claimed[pi].fetch_add(1, Ordering::Relaxed) < per_peer {
                        let b = net.recv(i, net::HE_RET);
                        let (h, dec) = if key.compress.is_some() {
                            let v = bytes_to_u64s(&b);
                            (v[..nh].to_vec(), key.decrypt_compressed(&v[nh..], coefs))
                        } else {
                            let (h, ct) = ct_parse(&b, nh, ln);
                            (h, key.decrypt(&ct, Some(coefs)))
                        };
                        sink(&h, &dec);
                    }
                });
            }
        }
    });
}

/// Raw pointer for disjoint parallel writes into one matrix.
#[derive(Clone, Copy)]
struct SyncPtr(*mut u64);
unsafe impl Send for SyncPtr {}
unsafe impl Sync for SyncPtr {}

pub fn layout(d: usize, n: usize) -> (usize, usize) {
    (d.min(64), d.min(n / 64))
}

impl He {
    /// One HE return on the wire: header, then the full ciphertext, or (compressed returns) the modulus-switched
    /// c0 at the recipient's coefficients and c1.
    fn return_bytes(&self, hdr: &[u64], ct: &Ct, coefs: &[usize]) -> Vec<u8> {
        match &self.key.compress {
            None => ct_bytes(hdr, ct),
            Some(c) => {
                let mut v = hdr.to_vec();
                let w = crate::bfv::compress_return(&self.rns, ct, c.small.l(), coefs);
                match c.round {
                    None => v.extend(w),
                    Some((b0, b1)) => v.extend(crate::bfv::round_wire(&c.small, &w, coefs.len(), b0, b1)),
                }
                u64s_to_bytes(&v)
            }
        }
    }

    fn ntt_ct(&self, ct: &Ct) -> (Vec<u64>, Vec<u64>) {
        let (mut a, mut b) = (ct.c0.clone(), ct.c1.clone());
        self.rns.fwd(&mut a);
        self.rns.fwd(&mut b);
        (a, b)
    }

    fn poly_ntt(&self, coeffs: &[(usize, i64)]) -> Vec<u64> {
        let rns = &self.rns;
        let n = rns.n;
        let mut out = rns.zero();
        for (k, &q) in rns.qs.iter().enumerate() {
            for &(i, c) in coeffs {
                out[k * n + i] = from_i64(c, q);
            }
        }
        rns.fwd(&mut out);
        out
    }

    /// Send my ciphertexts to both other parties; receive theirs (index by party). Gated: my batch's ZKPoPK follows
    /// my ciphertexts on HE_CT, and I verify both senders' batches (and all three agree on the verdicts) before
    /// returning, so no ptxct ever touches an unverified ciphertext.
    fn swap_cts(&mut self, pt: &Party, mut msgs: Vec<Vec<u64>>, kind: &str, call: u64, transpose: bool, slots: &[usize]) -> Result<Vec<Vec<Ct>>, String> {
        let me = pt.i;
        let mut forge = false;
        if let (Some(_), Some((ak, who))) = (&self.gate, &self.attack) {
            // falsifier: my first matvec batch carries a plaintext coefficient off the layout, with a forged proof
            if ak == "zk_off_layout" && *who == me && kind == "mv" && call == 1 {
                let off = (0..self.rns.n).find(|k| !slots.contains(k)).unwrap();
                msgs[0][off] = 12345;
                forge = true;
            }
        }
        let enc: Vec<(Ct, Vec<i64>, Option<[u8; 32]>)> = msgs.iter().map(|m| self.key.encrypt_seeded(m)).collect();
        let ln = self.rns.l() * self.rns.n;
        // a seeded ciphertext travels as c0 and the 32-byte seed of a (half the bytes)
        let wires: Vec<Vec<u8>> = enc
            .iter()
            .map(|(ct, _, sd)| match sd {
                None => ct_bytes(&[], ct),
                Some(sd) => {
                    let mut b = u64s_to_bytes(&ct.c0);
                    b.extend_from_slice(sd);
                    b
                }
            })
            .collect();
        for j in pt.net.others() {
            for w in &wires {
                pt.net.send(j, net::HE_CT, w.clone());
            }
        }
        drop(wires);
        let (cts, es): (Vec<Ct>, Vec<Vec<i64>>) = enc.into_iter().map(|(c, e, _)| (c, e)).unzip();
        if let Some(g) = self.gate.as_mut() {
            let ws: Vec<dzkpopk::SkCt> = msgs.iter().zip(es).map(|(m, e)| dzkpopk::SkCt { e, r: crate::gate::witness_r(&self.rns, m, slots) }).collect();
            let ctx = crate::gate::context(kind, call, transpose, me);
            let proof = g.prove(&self.rns, me, &cts, ws, slots, ctx, &crate::gate::label(kind, call, transpose, me), forge)?;
            for j in pt.net.others() {
                pt.net.send(j, net::HE_CT, proof.clone());
            }
        }
        let k = cts.len();
        let mut proofs: Vec<Vec<u8>> = vec![Vec::new(); pt.n];
        let theirs: Vec<Vec<Ct>> = (0..pt.n)
            .map(|j| {
                if j == pt.i {
                    Vec::new()
                } else {
                    let v = (0..k)
                        .map(|_| {
                            let b = pt.net.recv(j, net::HE_CT);
                            if b.len() == ln * 8 + 32 {
                                let sd: [u8; 32] = b[ln * 8..].try_into().unwrap();
                                Ct { c0: bytes_to_u64s(&b[..ln * 8]), c1: crate::bfv::expand_a(&self.rns, &sd) }
                            } else {
                                ct_parse(&b, 0, ln).1
                            }
                        })
                        .collect();
                    if self.gate.is_some() {
                        proofs[j] = pt.net.recv(j, net::HE_CT);
                    }
                    v
                }
            })
            .collect();
        if let Some(g) = self.gate.as_mut() {
            // one batch at a time (memory); each verification is internally parallel
            let mut refusals: Vec<(usize, String)> = vec![];
            for j in pt.net.others() {
                if let Err(e) = g.verify(&self.rns, j, &theirs[j], slots, crate::gate::context(kind, call, transpose, j), &proofs[j]) {
                    refusals.push((j, e));
                }
            }
            crate::gate::agree(&pt.net, me, &refusals, &format!("{kind} call {call}"))?;
        }
        Ok(theirs)
    }

    /// [z] = [W][v] (or W^T v), he_matvec.HEMatvec.__call__.
    pub fn matvec(&mut self, pt: &mut Party, w: &[Vec<Sh>], v: &[Sh], transpose: bool) -> Result<Vec<Sh>, String> {
        let p = pt.p;
        let d = v.len();
        let n_ring = self.rns.n;
        let (dc, dr) = layout(d, n_ring);
        let (nrb, ncb) = (d / dr, d / dc);
        self.mv_calls += 1;
        let calls = self.mv_calls;
        let wsh: Vec<Vec<i64>> = w.iter().map(|r| r.iter().map(|x| pt.centered(x.s)).collect()).collect();
        let vsh: Vec<i64> = v.iter().map(|x| pt.centered(x.s)).collect();
        let mut z: Vec<u64> = (0..d)
            .map(|r| {
                let mut acc: i128 = 0;
                for c in 0..d {
                    let wv = if transpose { wsh[c][r] } else { wsh[r][c] };
                    acc = (acc + wv as i128 * vsh[c] as i128).rem_euclid(p as i128);
                }
                acc as u64
            })
            .collect();
        // sender: my blocks under my key
        let msgs: Vec<Vec<u64>> = if !transpose {
            (0..ncb)
                .map(|b| {
                    let mut m = vec![0u64; n_ring];
                    for c in 0..dc {
                        m[63 - c] = v[b * dc + c].s;
                    }
                    m
                })
                .collect()
        } else {
            (0..nrb)
                .map(|a| {
                    let mut m = vec![0u64; n_ring];
                    for r in 0..dr {
                        m[64 * (dr - 1 - r)] = v[a * dr + r].s;
                    }
                    m
                })
                .collect()
        };
        let nsent = msgs.len() as u64;
        let slots: Vec<usize> = if !transpose { (64 - dc..64).collect() } else { (0..dr).map(|k| 64 * k).collect() };
        let theirs = self.swap_cts(pt, msgs, "mv", calls, transpose, &slots)?;
        self.he_send += 2 * nsent * 2 * n_ring as u64 * 3;
        self.cts_sent += 2 * nsent;
        let me = pt.i;
        let others = pt.net.others();
        let nouts = if !transpose { nrb } else { ncb };
        let idx_of = |o: usize| -> Vec<(usize, usize)> {
            if !transpose {
                (0..dr).map(|r| (64 * r + 63, o * dr + r)).collect()
            } else {
                (0..dc).map(|c| (64 * (dr - 1) + c, o * dc + c)).collect()
            }
        };
        let he = &*self;
        let net_ref = &pt.net;
        let mv_coefs: Vec<usize> = idx_of(0).iter().map(|x| x.0).collect();
        let (zadd, zsub) = std::thread::scope(|sc| {
            // recipient: decrypt the returns others make for me
            let recv = sc.spawn(|| {
                let add = std::sync::Mutex::new(vec![0u64; d]);
                let coefs_of = |o: usize| idx_of(o).iter().map(|x| x.0).collect::<Vec<usize>>();
                // the decrypted coefficient set depends on o; decrypt the union (one output block's layout positions
                // are the same for every o), then pick
                let coefs = coefs_of(0);
                recv_decrypt(net_ref, &he.key, &others, nouts, 1, &coefs, |h, dec| {
                    let ix = idx_of(h[0] as usize);
                    let mut a = add.lock().unwrap();
                    for (k, &(_, out)) in ix.iter().enumerate() {
                        a[out] = addmod(a[out], dec[k], p);
                    }
                });
                add.into_inner().unwrap()
            });
            // returner: my plaintext blocks times each recipient's ciphertexts
            let ctn: Vec<Vec<(Vec<u64>, Vec<u64>)>> =
                theirs.iter().map(|v| v.par_iter().map(|ct| he.ntt_ct(ct)).collect()).collect();
            let senders: Vec<_> = others.iter().map(|&j| (j, net_ref.sender(j))).collect();
            let sub: Vec<Vec<(usize, u64)>> = (0..nouts)
                .into_par_iter()
                .map(|o| {
                    let blocks: Vec<(usize, usize)> =
                        if !transpose { (0..ncb).map(|b| (o, b)).collect() } else { (0..nrb).map(|a| (a, o)).collect() };
                    let mut accs: Vec<(Vec<u64>, Vec<u64>)> = others.iter().map(|_| (he.rns.zero(), he.rns.zero())).collect();
                    for &(a, b) in &blocks {
                        let mut coeffs = Vec::with_capacity(dr * dc);
                        for r in 0..dr {
                            for c in 0..dc {
                                coeffs.push((64 * r + c, wsh[a * dr + r][b * dc + c]));
                            }
                        }
                        let pn = he.poly_ntt(&coeffs);
                        let src = if !transpose { b } else { a };
                        for (jj, &j) in others.iter().enumerate() {
                            let (c0, c1) = &ctn[j][src];
                            he.rns.mul_acc(&mut accs[jj].0, &pn, c0);
                            he.rns.mul_acc(&mut accs[jj].1, &pn, c1);
                        }
                    }
                    let mut keep = Vec::new();
                    for (jj, &(j, ref tx)) in senders.iter().enumerate() {
                        let mut rg = he.key.return_coins(&format!(
                            "hm|{}|{}|{}|{}|{}|{}",
                            he.mv_seed, calls, transpose as u8, me, j, o
                        ));
                        let (ct, m) = make_return(&he.rns, &he.pks[j], (&accs[jj].0, &accs[jj].1), &mut rg, he.f_bits);
                        tx.send((net::HE_RET, he.return_bytes(&[o as u64], &ct, &mv_coefs))).expect("peer writer gone");
                        for &(coef, out) in &idx_of(o) {
                            keep.push((out, m[coef]));
                        }
                    }
                    keep
                })
                .collect();
            (recv.join().unwrap(), sub)
        });
        for k in 0..d {
            z[k] = addmod(z[k], zadd[k], p);
        }
        for list in zsub {
            for (out, m) in list {
                z[out] = submod(z[out], m, p);
            }
        }
        if let Some((kind, who)) = &self.attack {
            if kind == "mv_wrong_return" && *who == me {
                z[0] = addmod(z[0], 1, p);
            }
        }
        self.he_return += (pt.n as u64 - 1) * nouts as u64 * 2 * n_ring as u64 * 3;
        self.cts_returned += (pt.n as u64 - 1) * nouts as u64;
        let zs = pt.auth_plain_vec(&z, PH_HE_AUTH);
        // Freivalds coins on the whole transcript
        let mut h = ReprHasher::new();
        h.raw(b"(");
        h.s("freivalds");
        h.raw(b", (");
        h.s(&self.context.0);
        h.raw(format!(", {}, {}), ", self.context.1, self.context.2).as_bytes());
        h.u64(calls);
        h.sep();
        h.u64(d as u64);
        h.sep();
        h.bool(transpose);
        h.sep();
        pt.tr.repr_into(&mut h);
        h.raw(b")");
        let mut rr = PyRandom::from_hex_int(&h.finish_hex());
        let rho: Vec<u64> = (0..d).map(|_| rr.randrange_u64(p)).collect();
        let lhs = pt.lin(&(0..d).map(|r| (rho[r], zs[r])).collect::<Vec<_>>(), 0);
        let u: Vec<Sh> = (0..d)
            .map(|c| {
                if !transpose {
                    pt.lin(&(0..d).map(|r| (rho[r], w[r][c])).collect::<Vec<_>>(), 0)
                } else {
                    pt.lin(&(0..d).map(|cc| (rho[cc], w[c][cc])).collect::<Vec<_>>(), 0)
                }
            })
            .collect();
        // the check's openings: a link drop from here on is an abort, not a resume
        pt.net.set_critical(true);
        let prods = pt.mul_vec(&u, v);
        let mut ip = prods[0];
        for x in &prods[1..] {
            ip = pt.add(ip, *x);
        }
        let chk = pt.open_vec(&[pt.sub(lhs, ip)], PH_FREIVALDS);
        pt.net.set_critical(false);
        if chk[0] != 0 {
            return Err("HE matvec: Freivalds check failed (a custodian's vector, product or share is wrong)".into());
        }
        Ok(zs)
    }

    /// [G] = [a] (x) [x], he_outer.HEOuter.__call__.
    pub fn outer(&mut self, pt: &mut Party, a: &[Sh], x: &[Sh]) -> Result<Vec<Vec<Sh>>, String> {
        let p = pt.p;
        let (d1, d2) = (a.len(), x.len());
        let n_ring = self.rns.n;
        let (dc, dr) = (d2.min(64), d1.min(n_ring / 64));
        let (nab, nb) = (d1 / dr, d2 / dc);
        self.ou_calls += 1;
        let calls = self.ou_calls;
        let tr0 = std::time::Instant::now();
        let trace = std::env::var("DS_TRACE").is_ok() && pt.i == 0;
        let tl = |what: &str| if trace { eprintln!("[outer {calls}] {what} {:.3}", tr0.elapsed().as_secs_f64()) };
        let am: Vec<i64> = a.iter().map(|v| pt.centered(v.s)).collect();
        let amm: Vec<i64> = a.iter().map(|v| pt.centered(v.m)).collect();
        let xm: Vec<i64> = x.iter().map(|v| pt.centered(v.s)).collect();
        let mut g: Vec<u64> = vec![0; d1 * d2];
        let mut gm: Vec<u64> = vec![0; d1 * d2];
        {
            use rayon::prelude::*;
            g.par_chunks_mut(d2).zip(gm.par_chunks_mut(d2)).enumerate().for_each(|(r, (gr, gmr))| {
                for c in 0..d2 {
                    gr[c] = from_i128(am[r] as i128 * xm[c] as i128, p);
                    gmr[c] = from_i128(amm[r] as i128 * xm[c] as i128, p);
                }
            });
        }
        let msgs: Vec<Vec<u64>> = (0..nb)
            .map(|b| {
                let mut m = vec![0u64; n_ring];
                for c in 0..dc {
                    m[c] = x[b * dc + c].s;
                }
                m
            })
            .collect();
        let nsent = msgs.len() as u64;
        tl("local G");
        let slots: Vec<usize> = (0..dc).collect();
        let theirs = self.swap_cts(pt, msgs, "ou", calls, false, &slots)?;
        tl("swap cts");
        self.ou_send += 2 * nsent * 2 * n_ring as u64 * 3;
        self.cts_sent += 2 * nsent;
        let me = pt.i;
        let others = pt.net.others();
        let nret = nab * nb * 2;
        let he = &*self;
        let net_ref = &pt.net;
        let coefs: Vec<usize> = (0..dr).flat_map(|r| (0..dc).map(move |c| 64 * r + c)).collect();
        let gp = SyncPtr(g.as_mut_ptr());
        let gmp = SyncPtr(gm.as_mut_ptr());
        let (addv, addm) = std::thread::scope(|sc| {
            let recv = sc.spawn(|| {
                let rows: Vec<std::sync::Mutex<(Vec<u64>, Vec<u64>)>> =
                    (0..nab).map(|_| std::sync::Mutex::new((vec![0u64; dr * d2], vec![0u64; dr * d2]))).collect();
                recv_decrypt(net_ref, &he.key, &others, nret, 3, &coefs, |h, dec| {
                    let (ab, b, kind) = (h[0] as usize, h[1] as usize, h[2]);
                    let mut blk = rows[ab].lock().unwrap();
                    let tgt = if kind == 0 { &mut blk.0 } else { &mut blk.1 };
                    for r in 0..dr {
                        for c in 0..dc {
                            let ix = r * d2 + b * dc + c;
                            tgt[ix] = addmod(tgt[ix], dec[r * dc + c], p);
                        }
                    }
                });
                let mut addv = Vec::with_capacity(d1 * d2);
                let mut addm = Vec::with_capacity(d1 * d2);
                for m in rows {
                    let (v, mm) = m.into_inner().unwrap();
                    addv.extend(v);
                    addm.extend(mm);
                }
                (addv, addm)
            });
            let ctn: Vec<Vec<(Vec<u64>, Vec<u64>)>> =
                theirs.iter().map(|v| v.par_iter().map(|ct| he.ntt_ct(ct)).collect()).collect();
            // D_a and D'_a in NTT form, once per (row block, kind)
            let pns: Vec<Vec<u64>> = (0..nab * 2)
                .into_par_iter()
                .map(|z| {
                    let (ab, kind) = (z / 2, z % 2);
                    let src = if kind == 0 { &am } else { &amm };
                    let coeffs: Vec<(usize, i64)> = (0..dr).map(|r| (64 * r, src[ab * dr + r])).collect();
                    he.poly_ntt(&coeffs)
                })
                .collect();
            let senders: Vec<_> = others.iter().map(|&j| (j, net_ref.sender(j))).collect();
            let jobs: Vec<(usize, usize)> = (0..nab).flat_map(|ab| (0..nb).map(move |b| (ab, b))).collect();
            jobs.par_iter().for_each(|&(ab, b)| {
                for kind in 0..2usize {
                    let pn = &pns[ab * 2 + kind];
                    for &(j, ref tx) in &senders {
                        let (c0, c1) = &ctn[j][b];
                        let acc0 = he.rns.mul_pw(pn, c0);
                        let acc1 = he.rns.mul_pw(pn, c1);
                        let kname = if kind == 0 { "val" } else { "mac" };
                        let mut rg = he.key.return_coins(&format!(
                            "ho|{}|{}|{}|{}|{}|{}|{}",
                            he.ou_seed, calls, me, j, ab, b, kname
                        ));
                        let (ct, m) = make_return(&he.rns, &he.pks[j], (&acc0, &acc1), &mut rg, he.f_bits);
                        tx.send((net::HE_RET, he.return_bytes(&[ab as u64, b as u64, kind as u64], &ct, &coefs))).expect("peer gone");
                        let base = if kind == 0 { gp } else { gmp };
                        // block (ab, b) is written by this job only
                        for r in 0..dr {
                            for c in 0..dc {
                                let ix = (ab * dr + r) * d2 + b * dc + c;
                                unsafe {
                                    let ptr = base.0.add(ix);
                                    *ptr = submod(*ptr, m[64 * r + c], p);
                                }
                            }
                        }
                    }
                }
            });
            tl("returns made");
            let r = recv.join().unwrap();
            tl("returns decrypted");
            r
        });
        {
            use rayon::prelude::*;
            g.par_iter_mut().zip(addv.par_iter()).for_each(|(a, b)| *a = addmod(*a, *b, p));
            gm.par_iter_mut().zip(addm.par_iter()).for_each(|(a, b)| *a = addmod(*a, *b, p));
        }
        if let Some((kind, who)) = &self.attack {
            if kind == "wrong_return" && *who == me {
                // he_outer attack ("wrong_return", i): i's value share of G[0][0] shifted, once per (j, ab = 0, b = 0)
                g[0] = addmod(g[0], (pt.n - 1) as u64, p);
            }
        }
        self.ou_return += (pt.n as u64 - 1) * nret as u64 * 2 * n_ring as u64 * 3;
        self.cts_returned += (pt.n as u64 - 1) * nret as u64;
        // commit to (G_i, Gm_i), then coins from the transcript
        let mut hc = ReprHasher::new();
        hc.raw(b"(");
        repr_matrix(&mut hc, &g, d2);
        hc.sep();
        repr_matrix(&mut hc, &gm, d2);
        hc.raw(b")");
        let com = hc.finish_hex();
        tl("commit hash");
        let coms = pt.net.exchange_bytes(net::CTRL, com.as_bytes());
        let coms: [String; 3] = std::array::from_fn(|j| String::from_utf8(coms[j].clone()).expect("hex"));
        pt.tr.phase.push(PH_OUTER_COMMIT);
        pt.tr.v.push(0);
        pt.tr.commits.push(coms);
        self.ou_commit += (pt.n * (pt.n - 1) * 5) as u64;
        let mut h = ReprHasher::new();
        h.raw(b"(");
        h.s("he_outer");
        h.raw(b", (");
        h.s(&self.context.0);
        h.raw(format!(", {}, {}), ", self.context.1, self.context.2).as_bytes());
        h.u64(calls);
        h.sep();
        h.u64(d1 as u64);
        h.sep();
        h.u64(d2 as u64);
        h.sep();
        pt.tr.repr_into(&mut h);
        h.raw(b")");
        let mut rr = PyRandom::from_hex_int(&h.finish_hex());
        tl("coins");
        let r1: Vec<u64> = (0..d1).map(|_| rr.randrange_u64(p)).collect();
        let r2: Vec<u64> = (0..d2).map(|_| rr.randrange_u64(p)).collect();
        let out: Vec<Vec<Sh>> = (0..d1).map(|r| (0..d2).map(|c| Sh { s: g[r * d2 + c], m: gm[r * d2 + c] }).collect()).collect();
        drop(g);
        drop(gm);
        let lhs = {
            use rayon::prelude::*;
            let rows: Vec<Sh> = (0..d1)
                .into_par_iter()
                .map(|r| pt.lin(&(0..d2).map(|c| (mulmod(r1[r], r2[c], p), out[r][c])).collect::<Vec<_>>(), 0))
                .collect();
            let mut acc = Sh::default();
            for x in rows {
                acc = pt.add(acc, x);
            }
            acc
        };
        let ra = pt.lin(&(0..d1).map(|r| (r1[r], a[r])).collect::<Vec<_>>(), 0);
        let xr = pt.lin(&(0..d2).map(|c| (r2[c], x[c])).collect::<Vec<_>>(), 0);
        tl("lin");
        pt.net.set_critical(true);
        let prod = pt.mul_vec(&[ra], &[xr])[0];
        let chk = pt.open_vec(&[pt.sub(lhs, prod)], PH_OUTER_CHECK);
        pt.net.set_critical(false);
        if chk[0] != 0 {
            return Err("HE outer: Freivalds check failed (a custodian's vector, product or share is wrong)".into());
        }
        Ok(out)
    }
}

/// repr of a list of lists of ints (row-major flat, `cols` per row); rows rendered in parallel windows.
pub fn repr_matrix(h: &mut ReprHasher, m: &[u64], cols: usize) {
    use rayon::prelude::*;
    let rows = m.len() / cols.max(1);
    if rows < 64 {
        return repr_matrix_seq(h, m, cols);
    }
    h.raw(b"[");
    let per = 16usize;
    let window = per * 4 * rayon::current_num_threads().max(1);
    let mut r0 = 0;
    while r0 < rows {
        let r1 = (r0 + window).min(rows);
        let bufs: Vec<Vec<u8>> = (r0..r1)
            .step_by(per)
            .collect::<Vec<_>>()
            .into_par_iter()
            .map(|a| {
                let mut sub = ReprHasher::new_buffer();
                for r in a..(a + per).min(r1) {
                    if r > 0 {
                        sub.sep();
                    }
                    sub.list_u64(&m[r * cols..(r + 1) * cols]);
                }
                sub.into_buffer()
            })
            .collect();
        for b in bufs {
            h.raw(&b);
        }
        r0 = r1;
    }
    h.raw(b"]");
}

fn repr_matrix_seq(h: &mut ReprHasher, m: &[u64], cols: usize) {
    h.raw(b"[");
    for (k, row) in m.chunks(cols).enumerate() {
        if k > 0 {
            h.sep();
        }
        h.list_u64(row);
    }
    h.raw(b"]");
}
