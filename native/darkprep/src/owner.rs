//! The data owner's side of input preprocessing (client input, Damgard-Damgard-Nielsen-Nordholt-Toft 2016):
//! each custodian sends the owner its plain shares of an input triple (a, b, c); the owner reconstructs and
//! checks a b = c, and uses r = a as the input mask (it broadcasts v - r; the custodians hold [r] = [a]).
//! A custodian that shifts its share of a by delta passes the check only by shifting c by delta b, and b is
//! uniform and hidden from it: the check fails except with probability 1/p per tuple.

use crate::field::Fp;
use crate::mpspdz::Transactions;
use crate::schedule::{Plan, StepParams};

/// The plain shares custodian `i` sends the owner: (a_i, b_i, c_i) per input, in order.
pub fn custodian_message(sp: &StepParams, tx: &Transactions) -> Vec<[u64; 3]> {
    custodian_message_step(sp, tx, 0, 1)
}

/// Step `j` of a chunk of `steps`.
pub fn custodian_message_step(sp: &StepParams, tx: &Transactions, j: usize, steps: usize) -> Vec<[u64; 3]> {
    custodian_message_in_chunk(&vec![*sp; steps], tx, j)
}

/// Step `j` of a chunk whose steps are `chunk`.
pub fn custodian_message_in_chunk(chunk: &[StepParams], tx: &Transactions, j: usize) -> Vec<[u64; 3]> {
    let one = Plan::of(&chunk[j]).n_in;
    let o = crate::schedule::offsets(chunk, j).0;
    let sec = crate::schedule::plan_of_steps(chunk).sections();
    let (base, _, m) = sec.input;
    (o..o + one).map(|k| [0, 1, 2].map(|c| tx.share(base + c * m + k).0)).collect()
}

pub fn write_message(w: &mut impl std::io::Write, msg: &[[u64; 3]]) -> std::io::Result<()> {
    w.write_all(b"DLOMSG1\n")?;
    w.write_all(&(msg.len() as u64).to_le_bytes())?;
    let mut b = Vec::with_capacity(24 * msg.len());
    for t in msg {
        for x in t {
            b.extend_from_slice(&x.to_le_bytes());
        }
    }
    w.write_all(&b)
}

pub fn read_message(bytes: &[u8]) -> Result<Vec<[u64; 3]>, String> {
    if bytes.len() < 16 || &bytes[..8] != b"DLOMSG1\n" {
        return Err("not a DLOMSG1 owner message".into());
    }
    let n = u64::from_le_bytes(bytes[8..16].try_into().unwrap()) as usize;
    if bytes.len() != 16 + 24 * n {
        return Err("owner message length mismatch".into());
    }
    let u = |o: usize| u64::from_le_bytes(bytes[o..o + 8].try_into().unwrap());
    Ok((0..n).map(|k| [0, 1, 2].map(|c| u(16 + 24 * k + 8 * c))).collect())
}

/// The owner reconstructs, checks a b = c for every tuple, and returns the masks r = a.
pub fn owner_masks(fp: Fp, msgs: &[Vec<[u64; 3]>]) -> Result<Vec<u64>, String> {
    let m = msgs[0].len();
    let mut rs = Vec::with_capacity(m);
    for k in 0..m {
        let mut v = [0u64; 3];
        for msg in msgs {
            for c in 0..3 {
                v[c] = fp.add(v[c], msg[k][c]);
            }
        }
        if fp.mul(v[0], v[1]) != v[2] {
            return Err(format!("owner: input tuple {k} fails a b = c; a custodian sent an inconsistent share (abort)"));
        }
        rs.push(v[0]);
    }
    Ok(rs)
}
