//! TEST-ONLY whole-system check of a set of tapes: reconstructs every entry with all n parties' shares and
//! alpha = sum alpha_i (no real party can do this) and checks every relation the online step relies on:
//! MACs, the schedule (tags in program order, equal across parties), triples, truncation tuples (bits,
//! r = low + 2^s hi, range), power chains, and the owner's masks.

use crate::field::Fp;
use crate::schedule::{events, tags, Event, StepParams, DEG, KAPPA};
use crate::tape::Tape;

#[derive(Debug, Default)]
pub struct Report {
    pub entries: usize,
    pub macs: usize,
    pub triples: usize,
    pub truncs: usize,
    pub chains: usize,
    pub inputs: usize,
}

pub fn verify(tapes: &[Tape], owner: &[u64]) -> Result<Report, String> {
    if tapes[0].inputs == crate::tape::RELEASE_INPUTS || tapes[0].inputs == crate::tape::HANDOVER_INPUTS {
        return Err("a release or handover tape: its shape is not in the header; use verify_step with its StepParams".into());
    }
    verify_step(&tapes[0].step_params(), tapes, owner)
}

/// As verify, for a step whose proof atoms / proof triples are given by `sp` (the tape header carries d, the
/// input mode and the truncation parameters only).
pub fn verify_step(sp: &StepParams, tapes: &[Tape], owner: &[u64]) -> Result<Report, String> {
    let sp = *sp;
    let t0 = &tapes[0];
    let fp = Fp::new(t0.p);
    for t in tapes {
        if (t.p, t.d, t.inputs, t.trunc) != (t0.p, t0.d, t0.inputs, t0.trunc) {
            return Err("tapes disagree on parameters".into());
        }
    }
    let want = tags(&sp);
    let alpha = tapes.iter().fold(0, |a, t| fp.add(a, t.alpha_i));
    let mut vals = Vec::with_capacity(want.len());
    for (k, &w) in want.iter().enumerate() {
        let (mut x, mut m) = (0, 0);
        for t in tapes {
            let &(tag, s, mm) = t.entries.get(k).ok_or(format!("party {} tape ends at {k}", t.party))?;
            if tag != w {
                return Err(format!("party {}: entry {k} is {}, the schedule wants {}", t.party, tag.name(), w.name()));
            }
            if s >= fp.p || mm >= fp.p {
                return Err(format!("party {}: entry {k} not canonical", t.party));
            }
            x = fp.add(x, s);
            m = fp.add(m, mm);
        }
        if m != fp.mul(alpha, x) {
            return Err(format!("MAC fails at entry {k} ({})", w.name()));
        }
        vals.push(x);
    }
    for t in tapes {
        if t.entries.len() != want.len() {
            return Err(format!("party {} tape has {} entries, schedule {}", t.party, t.entries.len(), want.len()));
        }
    }
    let mut rep = Report { entries: want.len(), macs: want.len() * tapes.len(), ..Default::default() };
    let mut pos = 0usize;
    let tri = |pos: &mut usize, rep: &mut Report| -> Result<(), String> {
        let (a, b, c) = (vals[*pos], vals[*pos + 1], vals[*pos + 2]);
        if fp.mul(a, b) != c {
            return Err(format!("triple at entry {} has c != a b", *pos));
        }
        *pos += 3;
        rep.triples += 1;
        Ok(())
    };
    let mut n_in = 0;
    for e in events(&sp) {
        match e {
            Event::Input => {
                if owner.get(n_in) != Some(&vals[pos]) {
                    return Err(format!("owner mask {n_in} != the custodians' [r]"));
                }
                n_in += 1;
                rep.inputs += 1;
                pos += 1;
            }
            Event::AuthPlain => pos += 1,
            Event::Mul => tri(&mut pos, &mut rep)?,
            Event::Trunc(s, k) => {
                let r = vals[pos];
                let bits = &vals[pos + 1..pos + 1 + s as usize];
                let hi = vals[pos + 1 + s as usize];
                if bits.iter().any(|&b| b > 1) {
                    return Err(format!("truncation at entry {pos}: a low bit is not 0/1"));
                }
                let low = bits.iter().enumerate().fold(0u64, |a, (i, &b)| a | (b << i));
                if (r as u128) >= (1u128 << (k + KAPPA)) || hi >= (1u64 << (k + KAPPA - s)) || r != low + (hi << s) {
                    return Err(format!("truncation at entry {pos}: r, bits, r >> s inconsistent or out of range"));
                }
                pos += s as usize + 2;
                if sp.proof_atoms {
                    let nb = sp.trhb(s, k);
                    let hb = &vals[pos..pos + nb];
                    let want = if nb >= 64 { hi } else { hi & ((1u64 << nb) - 1) };
                    if hb.iter().any(|&b| b > 1) || hb.iter().enumerate().fold(0u64, |a, (i, &b)| a | (b << i)) != want {
                        return Err(format!("truncation at entry {pos}: the Trhb bits are not the bits of r >> s"));
                    }
                    pos += nb;
                }
                for _ in 0..2 * (s - 1) {
                    tri(&mut pos, &mut rep)?;
                }
                rep.truncs += 1;
            }
            Event::Lookup => {
                let r = vals[pos];
                for j in 1..DEG {
                    if vals[pos + j] != fp.mul(vals[pos + j - 1], r) {
                        return Err(format!("power chain at entry {pos}: r^{} wrong", j + 1));
                    }
                }
                pos += DEG;
                rep.chains += 1;
            }
        }
    }
    if n_in != owner.len() {
        return Err("owner file length != number of inputs".into());
    }
    Ok(rep)
}
