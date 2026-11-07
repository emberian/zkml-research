//! The handover's entry points for darkstep's serve loop (deploy lane): take a custodian's cross-step state at the
//! end of step k apart into what `side::old_side` erases, and give the new seats' state back in serve's shapes.
//!
//! Rotation (old seats -> new seats; old processes exit after):
//!   old seat:  let parts = serve::old_from_serve(state, carry, files, true, None);
//!              let rep = side::old_side(&common, move || parts.old, || <6-party TLS Net, index i>)?;  then exit
//!   new seat:  let nc = side::new_side(&common, j, <3-party TLS Net>, <6-party TLS Net, index 3 + j>, tape,
//!                                      epoch + 1, 8, None)?;   then serve::shares_rows(&nc.w, d) are its W wires,
//!              nc.carry its parent commitment, nc.key / nc.keys its HE key, nc.party its SPDZ party; custodian 0
//!              submits nc.proof to Ledger::rotate.
//! Self-handover after an SPDZ abort (same seats, MAC key retired, HE key kept): in each seat
//!   let parts = serve::old_from_serve(state, carry, files, false, None);   // parts.he kept, parts.net3 reused
//!   the old role (old_side, index i) and the new role (new_side with keep = Some(parts.he.key), index 3 + i, the
//!   seat's net3 and its NEW tape) run as two threads on the six-party mesh; the seat continues with the new role.
use crate::side::{HeSecret, OldCustodian, KINDS};
use darkproof::pcs::PcsParty;
use darkstep::party::Sh;
use darkstep::serve::{CustodianState, Shares};
use std::collections::BTreeMap;
use std::path::PathBuf;

pub struct OldParts {
    pub old: Box<OldCustodian>,
    /// the HE side (keys, public keys, gate), kept by a self-handover; None in a rotation (it is erased)
    pub he: Option<darkstep::he::He>,
    /// the seat's three-party mesh (a self-handover reuses it for the new role's SPDZ)
    pub net3: darkstep::net::Net,
}

/// `retire_he`: a rotation (the HE key goes with the shares); false: a self-handover (it stays).
/// `files`: the custodian's state files (its checkpoint ckpt_P<i>.bin, tape, TLS key), wiped by old_side. Their
/// directories become `old.scan_paths` (the disk scan); push more onto it before old_side.
/// `captured`: optionally a ciphertext under its key from before the handover and its plaintext digest, for the
/// post-erasure decryption check (rotation only).
pub fn old_from_serve(
    st: CustodianState,
    carry: BTreeMap<String, PcsParty>,
    files: Vec<PathBuf>,
    retire_he: bool,
    captured: Option<(darkstep::bfv::Ct, String)>,
) -> OldParts {
    let CustodianState { i, he, pt, w, .. } = st;
    let mut pt = pt;
    let (w1, w2) = w.expect("the custodian holds its weight shares");
    let mut wm = BTreeMap::new();
    for (k, rows) in KINDS.iter().zip([w1, w2]) {
        wm.insert(k.to_string(), rows.into_iter().flatten().collect::<Vec<Sh>>());
    }
    let tape = std::mem::take(&mut pt.tape);
    // the open log holds this party's MAC shares of opened values
    let ol = std::mem::take(&mut pt.open_log);
    let mut flat: Vec<u64> = ol.iter().flat_map(|&(m, v)| [m, v]).collect();
    drop(ol);
    crate::erase::Wipe::wipe(&mut flat);
    let net3 = pt.net;
    let (keys, key, he) = if retire_he {
        let mut he = he;
        let keys = he.gate.as_mut().map(|g| HeSecret {
            s: std::mem::take(&mut g.s),
            e: std::mem::take(&mut g.e_pk),
            reg: g.regs[i].clone(),
        });
        (keys, Some(he.key), None)
    } else {
        (None, None, Some(he))
    };
    // default scan: the directories of the state files (the seat dir, the TLS dir, the step's tape dir); the caller
    // adds every other place its secret inputs lie (all tapes of the epoch, owner messages) to `old.scan_paths`
    let mut scan_paths: Vec<PathBuf> = files.iter().filter_map(|f| f.parent().map(|p| p.to_path_buf())).collect();
    scan_paths.sort();
    scan_paths.dedup();
    OldParts {
        old: Box::new(OldCustodian { i, w: wm, tape, keys, key, carry, files, scan_paths, captured: if retire_he { captured } else { None } }),
        he,
        net3,
    }
}

/// New custodian's W wires in serve's shape (d rows of d per matrix).
pub fn shares_rows(w: &BTreeMap<String, Vec<Sh>>, d: usize) -> Shares {
    let rows = |k: &str| w[k].chunks(d).map(|r| r.to_vec()).collect::<Vec<_>>();
    (rows("W1"), rows("W2"))
}
