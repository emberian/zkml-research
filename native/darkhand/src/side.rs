//! What a custodian process does at the handover. Six parties on one mesh: the old committee 0..n_old, the new one
//! n_old..n_old + n_new (the new committee also has its own three-party mesh for its ceremony and its SPDZ).
//!
//! Old custodian i (`old_side`): split each plain W share into n_new uniform subshares from OS coins (summing to the
//! share), send subshare j to new custodian j (one message per matrix, the buffers wiped as they go), take part in
//! the joint handover proof with its carried child commitment (second life), then ERASE: wipe its W shares and MAC
//! shares, the commitment's rows, tails, salts and tree, its ceremony secret (s, e, r, salt), its tape and its alpha
//! share, drop its HE key, and wipe its state files. It then scans its own memory for canaries of all of these
//! (`scan`), tries to decrypt a ciphertext under its old key with what it still holds, and returns.
//!
//! New custodian j (`new_side`): its own key ceremony at the new epoch over the new mesh, receive and add the
//! subshares, commit them (first life), the joint proof, then authenticate the new shares under its own MAC key
//! (Party::auth_plain_vec on its own tape) and MAC-check a few openings. It returns its keys, its authenticated W
//! wires and its commitment parts: the state for the next step.
use crate::erase::{wipe_file, Wipe};
use crate::scan::{Canaries, ScanReport};
use darkproof::handover::{self, HandoverCtx};
use darkproof::ligero::LigParams;
use darkproof::net::TcpNet;
use darkproof::pcs::PcsParty;
use darkproof::rng::Det;
use darkproof::Profile;
use darkstep::bfv::{Ct, OwnKey};
use darkstep::net::{bytes_to_u64s, u64s_to_bytes, Net};
use darkstep::party::{Party, Sh};
use darkstep::rns::Rns;
use darkstep::tape::Tape;
use dzkpopk::ceremony::{Ceremony, Custodian};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

/// The resharing messages travel point to point on this tag (FIFO per peer, all before the proof's exchanges).
/// The resharing messages travel point to point on darkstep's RESHARE stream (FIFO per peer).
pub const RESHARE: u8 = darkstep::net::RESHARE;
pub const KINDS: [&str; 2] = ["W1", "W2"];

pub struct Common {
    pub pr: Profile,
    pub lp: LigParams,
    pub d: usize,
    pub n_old: usize,
    pub n_new: usize,
    pub ctx: HandoverCtx,
    pub rns: Arc<Rns>,
    pub t: u64,
}

/// Uniform field elements from OS coins (rejection on 61 bits); the byte buffer is wiped.
pub fn os_field(n: usize, p: u64) -> Vec<u64> {
    let mut out = Vec::with_capacity(n);
    let mut buf = vec![0u8; 8 * 4096];
    while out.len() < n {
        getrandom::getrandom(&mut buf).expect("os rng");
        for c in buf.chunks_exact(8) {
            let x = u64::from_le_bytes(c.try_into().unwrap()) & ((1u64 << 61) - 1);
            if x < p && out.len() < n {
                out.push(x);
            }
        }
    }
    buf.wipe();
    out
}

pub fn ct_bytes(c: &Ct) -> Vec<u8> {
    let mut v = vec![c.c0.len() as u64];
    v.extend_from_slice(&c.c0);
    v.extend_from_slice(&c.c1);
    u64s_to_bytes(&v)
}

pub fn ct_parse(b: &[u8]) -> Option<Ct> {
    let v = bytes_to_u64s(b);
    let n = *v.first()? as usize;
    if v.len() != 1 + 2 * n {
        return None;
    }
    Some(Ct { c0: v[1..1 + n].to_vec(), c1: v[1 + n..].to_vec() })
}

pub fn digest(xs: &[u64]) -> String {
    let mut h = Sha256::new();
    for x in xs {
        h.update(x.to_le_bytes());
    }
    pycompat::repr::hex(&h.finalize())
}

fn scan_json(r: &ScanReport) -> Value {
    json!({"available": r.available, "regions": r.regions, "bytes": r.bytes, "hits": r.hits, "where": r.where_,
           "hits_by_kind": r.by_kind, "seconds": r.seconds})
}

/// An old custodian's state at the end of step k (everything it must erase).
/// A custodian's HE key secret: its key s and key error e, and its registered public key (b, a).
pub struct HeSecret {
    pub s: Vec<i64>,
    pub e: Vec<i64>,
    pub reg: Arc<dzkpopk::KeyRegistry>,
}

impl HeSecret {
    pub fn from_ceremony(cust: Custodian, cer: &Ceremony) -> Self {
        let mut cust = cust;
        let reg = cer.registry(cust.i).expect("own key registered");
        HeSecret { s: std::mem::take(&mut cust.s), e: std::mem::take(&mut cust.e), reg }
    }
}

pub struct OldCustodian {
    pub i: usize,
    /// authenticated W1, W2 shares (d * d each, row-major)
    pub w: BTreeMap<String, Vec<Sh>>,
    pub tape: Tape,
    /// the HE key's ceremony secret and view, and the key: Some in a rotation (erased with the rest); None in a
    /// self-handover, where the same custodian keeps its HE key and only the MAC key is retired
    pub keys: Option<HeSecret>,
    pub key: Option<OwnKey>,
    /// the child commitment's parts (first life spent in step k)
    pub carry: BTreeMap<String, PcsParty>,
    /// state files on disk (key, shares, tape)
    pub files: Vec<PathBuf>,
    /// a ciphertext under this custodian's key from before the handover (an eavesdropper's capture of its HE_CT)
    /// and the digest of its plaintext
    pub captured: Option<(Ct, String)>,
}

/// What the shallow frame needs after the erasure: the canaries, the public pieces of the decryption attempt, the
/// files, and the report so far.
struct Erased {
    rep: Value,
    can: Canaries,
    captured: Option<(Ct, String)>,
    s_left: Vec<i64>,
    b: Vec<Vec<u64>>,
    a: Vec<Vec<u64>>,
    files: Vec<PathBuf>,
}

/// Overwrite `kb` KiB of the stack below the caller's frame (the dead frames of the setup and the handover, which
/// held keys and shares by value: Rust moves are copies and leave the old bytes behind).
#[inline(never)]
pub fn scrub_stack(kb: usize) {
    #[inline(never)]
    fn page(left: usize) {
        let mut buf = [0u8; 16384];
        unsafe { crate::erase::zero_raw(buf.as_mut_ptr(), buf.len()) };
        std::hint::black_box(&mut buf);
        if left > 1 {
            page(left - 1);
        }
    }
    page(kb.div_ceil(16));
}

/// The old custodian's part. `setup` builds its state (keys, shares, commitment) on the heap in a frame that is
/// dead and scrubbed before the final scan; `connect6` then joins the six-party mesh. Returns its report; the caller
/// exits the process.
pub fn old_side(c: &Common, setup: impl FnOnce() -> Box<OldCustodian>, connect6: impl FnOnce() -> Net) -> Result<Value, String> {
    let t0 = Instant::now();
    let st = setup();
    let e = old_side_erase(c, st, connect6())?;
    scrub_stack(4096);
    let post = e.can.scan();
    // ---- the attempt: decrypt the captured ciphertext with the key material this custodian still holds
    let post_dec = e.captured.as_ref().map(|(ct, dg)| {
        let rem = OwnKey::from_ceremony_secure(c.rns.clone(), &e.s_left, &e.b, &e.a);
        digest(&rem.decrypt(ct, None)) == *dg
    });
    let files_left: Vec<String> = e.files.iter().filter(|f| f.exists()).map(|f| f.display().to_string()).collect();
    let mut rep = e.rep;
    rep["scan_after_erasure"] = scan_json(&post);
    rep["canary_kinds"] = json!(e.can.kinds);
    rep["decrypts_captured_after_erasure"] = json!(post_dec);
    rep["state_files_left"] = json!(files_left);
    rep["allocator_wiped_bytes"] = json!(crate::erase::WIPED_BYTES.load(std::sync::atomic::Ordering::Relaxed));
    rep["seconds"] = json!(t0.elapsed().as_secs_f64());
    Ok(rep)
}

#[inline(never)]
fn old_side_erase(c: &Common, mut st: Box<OldCustodian>, net6: Net) -> Result<Erased, String> {
    let (n_old, n_new) = (c.n_old, c.n_new);
    let i = st.i;
    assert!(net6.me == i && net6.n == n_old + n_new);
    // ---- resharing: per matrix, n_new - 1 uniform subshares and the remainder, each sent then wiped
    let tr = Instant::now();
    for k in KINDS {
        let mut acc = vec![0u64; c.d * c.d];
        for j in 0..n_new {
            let mut sub = if j + 1 < n_new {
                let r = os_field(c.d * c.d, c.t);
                for (a, &x) in acc.iter_mut().zip(&r) {
                    *a = darkstep::arith::addmod(*a, x, c.t);
                }
                r
            } else {
                st.w[k].iter().zip(&acc).map(|(s, &a)| darkstep::arith::submod(s.s, a, c.t)).collect()
            };
            net6.send(n_old + j, RESHARE, u64s_to_bytes(&sub));
            sub.wipe();
        }
        acc.wipe();
    }
    let reshare_s = tr.elapsed().as_secs_f64();
    // ---- the joint proof
    let tp = Instant::now();
    let mut tn = TcpNet(net6);
    let proof = handover::prove(&c.pr, &c.lp, c.d, n_old, n_new, &c.ctx, &mut st.carry, &mut tn, &Det(None))?;
    let prove_s = tp.elapsed().as_secs_f64();
    let blob = handover::encode(&c.pr, c.d, &proof);
    let proof_digest = pycompat::repr::hex(&Sha256::digest(&blob));
    drop(blob);
    // the opened columns' salts are in the proof (public); the others must go
    let opened: BTreeMap<String, Vec<usize>> = KINDS.iter().map(|k| (k.to_string(), proof.cols_old[*k].j.clone())).collect();
    drop(proof);
    tn.0.shutdown();
    // ---- canaries of everything this custodian must erase (one-way tags, sampled)
    let mut can = Canaries::new();
    for k in KINDS {
        let s: Vec<u64> = st.w[k].iter().map(|x| x.s).collect();
        let m: Vec<u64> = st.w[k].iter().map(|x| x.m).collect();
        can.add_words(&format!("{k} share"), &s, 1 << 16);
        can.add_words(&format!("{k} MAC share"), &m, 1 << 16);
        let mut s = s;
        let mut m = m;
        s.wipe();
        m.wipe();
        can.add_words(&format!("{k} commitment rows and tails"), &st.carry[k].ext, 1 << 16);
        let mut salts: Vec<u8> = st.carry[k]
            .salts
            .iter()
            .enumerate()
            .filter(|(j, _)| !opened[k].contains(j))
            .flat_map(|(_, s)| s.iter().copied())
            .collect();
        can.add_bytes(&format!("{k} unopened commitment salts"), &salts);
        salts.wipe();
    }
    can.add_words("tape shares", &st.tape.sh, 1 << 16);
    can.add_words("tape MAC shares", &st.tape.mac, 1 << 16);
    can.add_words("alpha share", std::slice::from_ref(&st.tape.alpha_i), 1);
    if let Some(hs) = st.keys.as_ref() {
        let mut s_ntt = c.rns.from_signed(&hs.s);
        c.rns.fwd(&mut s_ntt);
        can.add_words("HE secret key (NTT form)", &s_ntt, 1 << 16);
        s_ntt.wipe();
    }
    if let Some(rk) = st.key.as_ref().and_then(|k| k.return_key.as_ref()) {
        can.add_bytes("HE return-coin key", rk);
    }
    // control: before erasure the scan finds the material, and the key decrypts the captured ciphertext
    let pre = can.scan();
    let pre_dec = st.captured.as_ref().map(|(ct, dg)| {
        let k = st.key.as_ref().unwrap();
        digest(&k.decrypt(ct, None)) == *dg
    });
    // ---- erasure
    let te = Instant::now();
    for v in st.w.values_mut() {
        v.wipe();
    }
    st.w.clear();
    for v in st.carry.values_mut() {
        v.wipe();
    }
    st.carry.clear();
    st.tape.wipe();
    if let Some(hs) = st.keys.as_mut() {
        hs.s.wipe();
        hs.e.wipe();
    }
    if let Some(k) = st.key.as_mut() {
        k.s.wipe();
        if let Some(rk) = k.return_key.as_mut() {
            rk.wipe();
        }
    }
    // drop the key in place, then zero its inline bytes (the coin PRF's keyed state lives inside the struct)
    unsafe {
        let p: *mut Option<OwnKey> = &mut st.key;
        std::ptr::drop_in_place(p);
        crate::erase::zero_raw(p as *mut u8, std::mem::size_of::<Option<OwnKey>>());
        std::ptr::write(p, None);
    }
    let mut file_errs = Vec::new();
    for f in &st.files {
        if let Err(e) = wipe_file(f) {
            file_errs.push(format!("{}: {e}", f.display()));
        }
    }
    let erase_s = te.elapsed().as_secs_f64();
    let (mut s_left, b, a) = match st.keys.as_ref() {
        Some(hs) => (hs.s.clone(), hs.reg.b_res().clone(), hs.reg.a_res().clone()),
        None => (Vec::new(), Vec::new(), Vec::new()),
    };
    s_left.resize(c.rns.n, 0);
    let rep = json!({
        "role": "old", "party": i, "reshare_seconds": reshare_s, "prove_seconds": prove_s, "erase_seconds": erase_s,
        "proof_sha256": proof_digest, "canaries": can.len(),
        "scan_before_erasure": scan_json(&pre),
        "decrypts_captured_before_erasure": pre_dec,
        "key_material_left": {"s_len": st.keys.as_ref().map(|k| k.s.len()).unwrap_or(0), "w_len": st.w.len(), "tape_len": st.tape.len(),
                              "carry_len": st.carry.len()},
        "file_wipe_errors": file_errs,
    });
    Ok(Erased {
        rep,
        can,
        captured: st.captured.take(),
        s_left,
        b,
        a,
        files: std::mem::take(&mut st.files),
    })
}

/// A new custodian's state after the handover: what the next step runs on.
pub struct NewCustodian {
    pub j: usize,
    /// the fresh ceremony's secret and view (a rotation); None in a self-handover (the seat kept its key)
    pub keys: Option<(HeSecret, Ceremony)>,
    pub key: OwnKey,
    pub party: Party,
    pub w: BTreeMap<String, Vec<Sh>>,
    pub carry: BTreeMap<String, PcsParty>,
    pub proof: Vec<u8>,
    pub new_roots: BTreeMap<String, Vec<[u8; 32]>>,
    pub report: Value,
}

/// The new custodian's part. `net3` is the new committee's own mesh (index j), `net6` the joint one (index
/// n_old + j); `tape` its own preprocessing (alpha share and at least 2 d^2 + 2 auth_plain entries, plus
/// `test_reveal` per matrix).
///
/// The check after re-authentication opens nothing secret: per matrix, one opening of sum_k rho_k w_k + r with
/// rho from the proof bytes (Fiat-Shamir, public) and r a fresh authenticated random value, then the MAC check; a
/// failed MAC check is an Err (the seat must not join). `test_reveal` > 0 (TEST ONLY: dl-hand's comparison with the
/// plaintext W) additionally opens that many leading entries of each matrix; production passes 0.
/// `keep`: Some((custodian, ceremony, key)) in a self-handover (the same seat keeps its HE key; only the MAC key is
/// new); None in a rotation (a fresh ceremony at `epoch`).
#[allow(clippy::too_many_arguments)]
pub fn new_side(c: &Common, j: usize, net3: Net, net6: Net, tape: Tape, epoch: i64, test_reveal: usize,
                keep: Option<OwnKey>) -> Result<NewCustodian, String> {
    let t0 = Instant::now();
    let (n_old, n_new) = (c.n_old, c.n_new);
    assert!(net6.me == n_old + j && net3.me == j && net3.n == n_new);
    let tc = Instant::now();
    let (keys, key) = match keep {
        Some(k) => (None, k),
        None => {
            let (cust, cer) = crate::ceremony::run(&net3, j, c.rns.n, &c.rns.qs, c.t, c.pr.t_cols, epoch)?;
            let hs = HeSecret::from_ceremony(cust, &cer);
            let key = OwnKey::from_ceremony_secure(c.rns.clone(), &hs.s, hs.reg.b_res(), hs.reg.a_res());
            (Some((hs, cer)), key)
        }
    };
    let ceremony_s = tc.elapsed().as_secs_f64();
    // ---- receive and add the subshares
    let tr = Instant::now();
    let mut plain: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for k in KINDS {
        let mut acc = vec![0u64; c.d * c.d];
        for i in 0..n_old {
            let mut b = net6.recv(i, RESHARE);
            let mut v = bytes_to_u64s(&b);
            b.wipe();
            if v.len() != acc.len() {
                return Err(format!("resharing: old custodian {i}'s {k} subshare has the wrong length"));
            }
            for (a, &x) in acc.iter_mut().zip(&v) {
                *a = darkstep::arith::addmod(*a, x, c.t);
            }
            v.wipe();
        }
        plain.insert(k.to_string(), acc);
    }
    let reshare_s = tr.elapsed().as_secs_f64();
    let tcm = Instant::now();
    let mut carry: BTreeMap<String, PcsParty> =
        KINDS.iter().map(|k| (k.to_string(), PcsParty::commit(&c.pr, &plain[*k], k, j, &Det(None)))).collect();
    let commit_s = tcm.elapsed().as_secs_f64();
    let tp = Instant::now();
    let mut tn = TcpNet(net6);
    let proof = handover::prove(&c.pr, &c.lp, c.d, n_old, n_new, &c.ctx, &mut carry, &mut tn, &Det(None))?;
    let prove_s = tp.elapsed().as_secs_f64();
    tn.0.shutdown();
    let blob = handover::encode(&c.pr, c.d, &proof);
    // ---- re-authenticate under the new MAC key, then MAC-check `check` openings of each matrix
    let ta = Instant::now();
    let mut party = Party::new(j, c.t, net3, tape);
    let mut w = BTreeMap::new();
    for k in KINDS {
        let mut pl = plain.remove(k).unwrap();
        w.insert(k.to_string(), party.auth_plain_vec(&pl, darkstep::party::PH_HE_AUTH));
        pl.wipe();
    }
    let auth_s = ta.elapsed().as_secs_f64();
    // masked random linear combination per matrix: rho_k = H(proof digest, matrix, k) mod p, r from the tape
    let pd = Sha256::digest(&blob);
    let mut masked = Vec::new();
    for (q, k) in KINDS.iter().enumerate() {
        let terms: Vec<(u64, Sh)> = w[*k]
            .iter()
            .enumerate()
            .map(|(idx, &x)| {
                let mut h = Sha256::new();
                h.update(pd);
                h.update([q as u8]);
                h.update((idx as u64).to_le_bytes());
                let b = h.finalize();
                (u64::from_le_bytes(b[..8].try_into().unwrap()) % c.t, x)
            })
            .collect();
        let pos = party.take(1);
        let r = party.tape_at(pos, darkstep::tape::Tag::Ar);
        let y = party.lin(&terms, 0);
        let y = Sh { s: darkstep::arith::addmod(y.s, r.s, c.t), m: darkstep::arith::addmod(y.m, r.m, c.t) };
        masked.push(y);
    }
    let masked_open = party.open_vec(&masked, darkstep::party::PH_HE_AUTH);
    let mut opened = BTreeMap::new();
    if test_reveal > 0 {
        for k in KINDS {
            let xs: Vec<Sh> = w[k][..test_reveal.min(c.d * c.d)].to_vec();
            opened.insert(k.to_string(), party.open_vec(&xs, darkstep::party::PH_HE_AUTH));
        }
    }
    let mac = match party.mac_check("handover") { Ok(_) => "ok".to_string(), Err(e) => e };
    if mac != "ok" {
        return Err(format!("re-authentication: {mac}"));
    }
    let _ = masked_open;
    // ---- a ciphertext under the new key (the attempt's target) and its own decryption (control)
    let mut key2 = key;
    let m = os_field(c.rns.n, c.t);
    let ct = key2.encrypt_exact(&m);
    let own_dec = digest(&key2.decrypt(&ct, None)) == digest(&m);
    let report = json!({
        "role": "new", "party": j, "ceremony_seconds": ceremony_s, "reshare_seconds": reshare_s,
        "commit_seconds": commit_s, "prove_seconds": prove_s, "auth_seconds": auth_s, "proof_bytes": blob.len(),
        "proof_sha256": pycompat::repr::hex(&Sha256::digest(&blob)), "opened": opened, "mac_check": mac,
        "alpha_differs_from_zero": party.alpha() != 0, "ct_under_new_key": pycompat::repr::hex(&ct_bytes(&ct)),
        "ct_plain_sha256": digest(&m), "decrypts_own_ct": own_dec, "seconds": t0.elapsed().as_secs_f64(),
    });
    Ok(NewCustodian { j, keys, key: key2, party, w, carry, proof: blob, new_roots: proof.new_roots, report })
}
