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
use crate::scan::{Canaries, DiskReport, ScanReport};
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

fn disk_json(r: &DiskReport) -> Value {
    json!({"files": r.files, "bytes": r.bytes, "hits": r.hits, "hits_by_kind": r.by_kind,
           "hit_files": r.hit_files.iter().map(|(p, h)| json!([p, h])).collect::<Vec<_>>(), "unreadable": r.unreadable,
           "seconds": r.seconds})
}

/// The process's peak resident set (VmHWM) in MB; 0 where /proc is absent.
pub fn peak_rss_mb() -> f64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).and_then(|l| l.split_whitespace().nth(1)?.parse::<f64>().ok()))
        .map(|kb| kb / 1024.0)
        .unwrap_or(0.0)
}

/// Bytes this party sent on `net` so far, per peer, by tag name (only the tags with traffic).
pub fn sent_json(net: &Net) -> Value {
    const NAMES: [&str; darkstep::net::NTAGS] = ["OPEN", "HE_CT", "HE_RET", "CTRL", "PROOF", "RESHARE", "RELAY"];
    let per = net.sent_per_peer();
    let mut out = serde_json::Map::new();
    for (j, row) in per.iter().enumerate() {
        if j == net.me {
            continue;
        }
        let mut m = serde_json::Map::new();
        for (k, &b) in row.iter().enumerate() {
            if b > 0 {
                m.insert(NAMES[k].to_string(), json!(b));
            }
        }
        m.insert("total".into(), json!(row.iter().sum::<u64>()));
        out.insert(j.to_string(), Value::Object(m));
    }
    Value::Object(out)
}

fn scan_json(r: &ScanReport) -> Value {
    json!({"available": r.available, "regions": r.regions, "bytes": r.bytes, "hits": r.hits, "where": r.where_,
           "hits_by_kind": r.by_kind, "seconds": r.seconds, "sp": format!("{:#x}", r.sp),
           "hits_detail": r.detail.iter().map(|(k, n, a, l, o)| json!({"kind": k, "map": n, "start": format!("{a:#x}"), "len": l, "offset": o,
                                                                       "above_sp": a + o > r.sp})).collect::<Vec<_>>()})
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
    /// files and directories scanned on disk for the durable canaries (shares, MAC shares, tape, alpha share, HE
    /// key) before and after the erasure: every place this custodian's secret inputs and state may lie
    pub scan_paths: Vec<PathBuf>,
    /// a ciphertext under this custodian's key from before the handover (an eavesdropper's capture of its HE_CT)
    /// and the digest of its plaintext
    pub captured: Option<(Ct, String)>,
    /// the epoch's file key (`vault`): its state files are sealed under it, and erasing it erases them wherever
    /// their blocks lie. None: the files are plain (wipes only).
    pub vault: Option<crate::vault::Vault>,
}

/// What the shallow frame needs after the erasure: the canaries, the public pieces of the decryption attempt, the
/// files, and the report so far.
struct Erased {
    rep: Value,
    can: Canaries,
    dcan: Canaries,
    scan_paths: Vec<PathBuf>,
    captured: Option<(Ct, String)>,
    s_left: Vec<i64>,
    b: Vec<Vec<u64>>,
    a: Vec<Vec<u64>>,
    files: Vec<PathBuf>,
    /// the vault's name and copies of the small sealed state files (role, bytes), taken before the erasure
    vault_copies: Option<(String, Vec<(String, String, Vec<u8>)>)>,
}

/// Whether a carried commitment is a PUBLIC one (darkproof's public genesis: `PcsParty::commit_public`, its tails
/// and salts drawn from public coins seeded by the committed vector). Then its rows, tails and salts are public and
/// legitimately live on (the seat recomputes the genesis), so they are no canaries. Exact: the first two tails must
/// be the public coins' first two draws.
pub fn carry_is_public(pc: &PcsParty, p: u64) -> bool {
    let s = &pc.shape;
    if s.rd == 0 || s.w < s.c + 2 || pc.ext.len() < s.rd * s.w {
        return false;
    }
    let mut share = Vec::with_capacity(s.rd * s.c);
    for r in 0..s.rd {
        share.extend_from_slice(&pc.ext[r * s.w..r * s.w + s.c]);
    }
    share.resize(1 << darkproof::pcs::bitlen(share.len().max(2) - 1), 0);
    let mut rng = darkproof::rng::public_coins(&["dl-public-genesis", &darkproof::h::h_list_hex(&share)]);
    rng.randrange_u64(p) == pc.ext[s.c] && rng.randrange_u64(p) == pc.ext[s.c + 1]
}

/// The P-256 group order n, big-endian.
const P256_N: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbc, 0xe6, 0xfa, 0xad,
    0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51,
];

/// The private scalar of a PKCS#8 ECDSA P-256 key (darkstep::tls, rcgen's serialize_der): the ECPrivateKey's
/// `INTEGER 1, OCTET STRING (32)` (02 01 01 04 20), after the ecPublicKey and prime256v1 OIDs.
pub fn p256_scalar(der: &[u8]) -> Option<[u8; 32]> {
    const OID_P256: [u8; 8] = [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];
    let has = |pat: &[u8]| der.windows(pat.len()).position(|w| w == pat);
    has(&OID_P256)?;
    let at = has(&[0x02, 0x01, 0x01, 0x04, 0x20])? + 5;
    der.get(at..at + 32).map(|b| b.try_into().unwrap())
}

/// The forms a P-256 private scalar takes in this process's memory, as aligned 64-bit words: its big-endian bytes
/// (rcgen's and the DER's copy, read as words), its little-endian limbs, and ring's Montgomery limbs (d 2^256 mod n,
/// the form ring's EcdsaKeyPair keeps).
pub fn p256_scalar_words(d: &[u8; 32]) -> [(&'static str, Vec<u64>); 3] {
    use num_bigint::BigUint;
    let be: Vec<u64> = d.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
    let limbs = |x: &BigUint| -> Vec<u64> {
        let mut v = x.to_u64_digits();
        v.resize(4, 0);
        v
    };
    let x = BigUint::from_bytes_be(d);
    let mont = (&x << 256u32) % BigUint::from_bytes_be(&P256_N);
    [
        ("TLS private scalar (big-endian bytes)", be),
        ("TLS private scalar (limbs)", limbs(&x)),
        ("TLS private scalar (Montgomery limbs)", limbs(&mont)),
    ]
}

/// Canaries of the TLS private key among the state files (`tls_*.key`, PKCS#8 DER, sealed under the vault when it
/// starts with vault::MAGIC): in memory its DER words and the scalar's three forms; on disk the scalar's first 16
/// bytes at any offset of small files. Returns the files used.
fn tls_key_canaries(can: &mut Canaries, dcan: &mut Canaries, files: &[PathBuf], vault: Option<&crate::vault::Vault>) -> Vec<String> {
    let mut used = Vec::new();
    for f in files {
        let name = f.file_name().map(|n| n.to_string_lossy().to_string()).unwrap_or_default();
        if !(name.starts_with("tls_") && name.ends_with(".key")) {
            continue;
        }
        let Ok(raw) = std::fs::read(f) else { continue };
        let mut der = if raw.starts_with(crate::vault::MAGIC) {
            match vault.map(|v| v.open(&vault_role(f), raw)) {
                Some(Ok(d)) => d,
                _ => continue,
            }
        } else {
            raw
        };
        can.add_bytes("TLS private key (PKCS#8 DER)", &der);
        if let Some(mut d) = p256_scalar(&der) {
            for (kind, mut ws) in p256_scalar_words(&d) {
                can.add_words(kind, &ws, ws.len());
                ws.wipe();
            }
            dcan.add_text16("TLS private scalar (bytes)", &d[..16]);
            unsafe { crate::erase::zero_raw(d.as_mut_ptr(), d.len()) };
        }
        der.wipe();
        used.push(f.display().to_string());
    }
    used
}

/// Overwrite ALL of this thread's stack below the caller's frame: from here down to the low end of the stack
/// mapping that holds this frame (/proc/self/maps; the main thread's [stack] has grown to the deepest page ever
/// touched, so this reaches every dead frame of earlier work), less a margin (1/16 of it, for the scrub's own frame
/// overhead, plus 64 KiB). Elsewhere (no /proc) it falls
/// back to 4 MiB. Call it at the shallowest point before the erasure, so that the frames pushed afterwards start on
/// zeroed memory (a new frame's unused slots keep whatever an earlier, deeper call left there).
#[inline(never)]
pub fn scrub_stack_all() -> usize {
    let here = 0u8;
    let sp = std::hint::black_box(&here) as *const u8 as u64;
    let low = std::fs::read_to_string("/proc/self/maps").ok().and_then(|m| {
        m.lines().find_map(|l| {
            let (a, b) = l.split_whitespace().next()?.split_once('-')?;
            let (a, b) = (u64::from_str_radix(a, 16).ok()?, u64::from_str_radix(b, 16).ok()?);
            (a <= sp && sp < b).then_some(a)
        })
    });
    let kb = match low {
        // each 16 KiB page frame of scrub_stack costs a little more than 16 KiB of stack: leave 1/16 + 64 KiB
        Some(a) if sp > a + (64 << 10) => (((sp - a) * 15 / 16 - (64 << 10)) >> 10) as usize,
        Some(_) => 0,
        None => 4096,
    };
    scrub_stack(kb);
    kb
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

/// Build the old custodian's state in a frame of its own, below old_side's and dead once it returns (then zeroed by
/// scrub_stack_all). Without this the setup closure, being generic, is inlined into old_side, and the state it takes
/// apart by value (a CustodianState carries the alpha share inline) stays in old_side's live frame: run11b found
/// one alpha copy there, 3.9 KB above the scanning frame of every seat.
#[inline(never)]
fn run_setup<F: FnOnce() -> Box<OldCustodian>>(setup: F) -> Box<OldCustodian> {
    std::hint::black_box(setup())
}

/// The old custodian's part. `setup` builds its state (keys, shares, commitment) on the heap in a frame that is
/// dead and scrubbed before the final scan; `connect6` then joins the six-party mesh. Returns its report; the caller
/// exits the process.
pub fn old_side(c: &Common, setup: impl FnOnce() -> Box<OldCustodian>, connect6: impl FnOnce() -> Net) -> Result<Value, String> {
    let t0 = Instant::now();
    let st = run_setup(setup);
    let e = old_side_erase(c, st, connect6())?;
    let scrubbed_kb = scrub_stack_all();
    let post_disk = e.dcan.scan_paths(&e.scan_paths);
    let post = e.can.scan();
    // ---- the attempt: decrypt the captured ciphertext with the key material this custodian still holds
    let post_dec = e.captured.as_ref().map(|(ct, dg)| {
        let rem = OwnKey::from_ceremony_secure(c.rns.clone(), &e.s_left, &e.b, &e.a);
        digest(&rem.decrypt(ct, None)) == *dg
    });
    let files_left: Vec<String> = e.files.iter().filter(|f| f.exists()).map(|f| f.display().to_string()).collect();
    // the sealed copies after the erasure: the keyring has no key of the vault's name, so nothing the seat (or its
    // uid) holds opens them; and the zero key, the only one memory can still give, does not either
    let vault_post = e.vault_copies.as_ref().map(|(name, copies)| {
        let load = crate::vault::Vault::load(name);
        let zero = crate::vault::Vault::with_key(name, [0u8; 32]);
        let tries: Vec<Value> = copies
            .iter()
            .map(|(f, role, b)| {
                let by_keyring = load.as_ref().map(|v| v.open(role, b.clone()).is_ok()).unwrap_or(false);
                let by_zero = zero.open(role, b.clone()).is_ok();
                json!({"file": f, "role": role, "opens_by_keyring": by_keyring, "opens_by_zero_key": by_zero})
            })
            .collect();
        json!({"name": name, "key_in_keyring": crate::vault::present(name), "load_error": load.err(), "sealed_copies": tries})
    });
    let mut rep = e.rep;
    rep["vault_after_erasure"] = json!(vault_post);
    rep["scan_after_erasure"] = scan_json(&post);
    rep["stack_scrubbed_kb"] = json!(scrubbed_kb);
    rep["disk_scan_after_erasure"] = disk_json(&post_disk);
    rep["disk_canary_kinds"] = json!(e.dcan.kinds);
    rep["scan_paths"] = json!(e.scan_paths.iter().map(|p| p.display().to_string()).collect::<Vec<_>>());
    rep["peak_rss_mb"] = json!(peak_rss_mb());
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
    let sent6 = sent_json(&tn.0);
    tn.0.shutdown();
    // ---- canaries of everything this custodian must erase (one-way tags, sampled)
    let mut can = Canaries::new();
    let mut public_carry: Vec<String> = Vec::new();
    // the durable kinds (what a file may hold: checkpoint, tapes, a key file), all below 2^61
    let mut dcan = Canaries::bounded(1u64 << 61);
    for k in KINDS {
        // a public carry commits this custodian's share itself (public genesis: custodian 0 holds the public W, the
        // others zero), so that share is public too; its MAC share (alpha W) stays secret
        let public = carry_is_public(&st.carry[k], c.t);
        let s: Vec<u64> = st.w[k].iter().map(|x| x.s).collect();
        let m: Vec<u64> = st.w[k].iter().map(|x| x.m).collect();
        let sk = if public { 0 } else { 1 << 16 };
        can.add_words(&format!("{k} share"), if public { &[] } else { &s[..] }, sk);
        can.add_words(&format!("{k} MAC share"), &m, 1 << 16);
        dcan.add_words(&format!("{k} share"), if public { &[] } else { &s[..] }, sk);
        dcan.add_words(&format!("{k} MAC share"), &m, 1 << 16);
        let mut s = s;
        let mut m = m;
        s.wipe();
        m.wipe();
        if public {
            public_carry.push(k.to_string());
            continue;
        }
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
    dcan.add_words("tape shares", &st.tape.sh, 1 << 16);
    dcan.add_words("tape MAC shares", &st.tape.mac, 1 << 16);
    dcan.add_words("alpha share", std::slice::from_ref(&st.tape.alpha_i), 1);
    // MP-SPDZ's forms of the same share (prep lane, measured): Montgomery (alpha * 2^64 mod p, LE) in its
    // Transactions file, decimal text in Player-MAC-Keys
    let r64 = ((1u128 << 64) % c.t as u128) as u64;
    let mont = ((st.tape.alpha_i as u128 * r64 as u128) % c.t as u128) as u64;
    dcan.add_words("alpha share (Montgomery form)", std::slice::from_ref(&mont), 1);
    let mut dec = st.tape.alpha_i.to_string().into_bytes();
    dcan.add_text16("alpha share (decimal text)", &dec);
    dec.wipe();
    if let Some(hs) = st.keys.as_ref() {
        let mut s_ntt = c.rns.from_signed(&hs.s);
        c.rns.fwd(&mut s_ntt);
        can.add_words("HE secret key (NTT form)", &s_ntt, 1 << 16);
        dcan.add_words("HE secret key (NTT form)", &s_ntt, 1 << 16);
        s_ntt.wipe();
    }
    if let Some(rk) = st.key.as_ref().and_then(|k| k.return_key.as_ref()) {
        can.add_bytes("HE return-coin key", rk);
    }
    // the seat's TLS private key (its identity on the meshes: kept, it could still join a mesh as this custodian)
    let tls_kinds = tls_key_canaries(&mut can, &mut dcan, &st.files, st.vault.as_ref());
    // the file key, and copies of the small sealed files (ciphertext) for the check that nothing opens them after
    let mut vault_pre = serde_json::Value::Null;
    let vault_copies = st.vault.as_ref().map(|v| {
        let kw = v.key_words();
        can.add_words("vault file key", &kw, 4);
        dcan.add_text16("vault file key", &v.key_bytes()[..16]);
        let mut copies = Vec::new();
        let mut opened = Vec::new();
        for f in &st.files {
            let Ok(b) = std::fs::read(f) else { continue };
            if b.len() > (1 << 20) || !b.starts_with(crate::vault::MAGIC) {
                continue;
            }
            let role = vault_role(f);
            let ok = v.open(&role, b.clone()).map(|mut x| x.wipe()).is_ok();
            opened.push(json!([f.display().to_string(), role, ok]));
            copies.push((f.display().to_string(), role, b));
        }
        vault_pre = json!({"name": v.name, "sealed_copies_open_before_erasure": opened});
        (v.name.clone(), copies)
    });
    // control: before erasure the scan finds the material, and the key decrypts the captured ciphertext
    let pre = can.scan();
    let pre_disk = dcan.scan_paths(&st.scan_paths);
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
    let vault_destroyed = st.vault.take().map(|v| v.destroy());
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
        "disk_scan_before_erasure": disk_json(&pre_disk),
        "public_carry": public_carry,
        "tls_key_files_canaried": tls_kinds,
        "vault_before_erasure": vault_pre,
        "vault_destroyed": vault_destroyed,
        "bytes_sent_per_peer": sent6,
        "captured_ct": st.captured.as_ref().map(|(ct, _)| pycompat::repr::hex(&ct_bytes(ct))),
        "captured_plain_sha256": st.captured.as_ref().map(|(_, dg)| dg.clone()),
        "decrypts_captured_before_erasure": pre_dec,
        "key_material_left": {"s_len": st.keys.as_ref().map(|k| k.s.len()).unwrap_or(0), "w_len": st.w.len(), "tape_len": st.tape.len(),
                              "carry_len": st.carry.len()},
        "file_wipe_errors": file_errs,
    });
    Ok(Erased {
        rep,
        can,
        dcan,
        scan_paths: std::mem::take(&mut st.scan_paths),
        captured: st.captured.take(),
        s_left,
        b,
        a,
        files: std::mem::take(&mut st.files),
        vault_copies,
    })
}

/// A sealed state file's role (the AAD's last part): its file name without the seat digits and extension, e.g.
/// "ckpt_P0.bin" -> "ckpt", "tls_2.key" -> "tls". The deploy lane seals with the same roles (`vault_role`).
pub fn vault_role(f: &std::path::Path) -> String {
    let n = f.file_name().map(|n| n.to_string_lossy().to_string()).unwrap_or_default();
    n.split(['_', '.']).next().unwrap_or("").to_string()
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
    let sent6 = sent_json(&tn.0);
    let sent3_before_auth = sent_json(&net3);
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
        "bytes_sent_per_peer_mesh6": sent6, "bytes_sent_per_peer_mesh3_ceremony": sent3_before_auth,
        "bytes_sent_per_peer_mesh3_total": sent_json(&party.net), "peak_rss_mb": peak_rss_mb(),
    });
    Ok(NewCustodian { j, keys, key: key2, party, w, carry, proof: blob, new_roots: proof.new_roots, report })
}
