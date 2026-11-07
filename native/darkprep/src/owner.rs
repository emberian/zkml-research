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
    let sec = Plan::of(sp).sections();
    let (base, _, m) = sec.input;
    (0..m).map(|k| [0, 1, 2].map(|c| tx.shares[base + c * m + k].0)).collect()
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
