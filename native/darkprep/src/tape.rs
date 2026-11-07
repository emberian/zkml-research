//! Per-party tapes: format (see the crate doc), reading, writing, and assembly from a Transactions file.

use crate::field::Fp;
use crate::mpspdz::Transactions;
use crate::schedule::{runs, Event, Inputs, Plan, StepParams, Tag, DEG, KAPPA};
use std::io::{Read, Write};

pub const MAGIC: &[u8; 8] = b"DLTAPE1\n";
/// Tape header `inputs` byte of a release tape and of a handover tape (their shape is not in the header: verify_step).
pub const RELEASE_INPUTS: u8 = 2;
pub const HANDOVER_INPUTS: u8 = 3;
pub const OWNER_MAGIC: &[u8; 8] = b"DLOWNR1\n";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tape {
    pub p: u64,
    pub n_parties: u32,
    pub party: u32,
    pub alpha_i: u64,
    pub d: u32,
    pub inputs: u8,
    pub trunc: [(u8, u8); 4],
    pub entries: Vec<(Tag, u64, u64)>,
}

impl Tape {
    pub fn write_to(&self, w: &mut impl Write) -> std::io::Result<()> {
        let mut h = Vec::new();
        h.extend_from_slice(MAGIC);
        h.extend_from_slice(&self.p.to_le_bytes());
        h.extend_from_slice(&self.n_parties.to_le_bytes());
        h.extend_from_slice(&self.party.to_le_bytes());
        h.extend_from_slice(&self.alpha_i.to_le_bytes());
        h.extend_from_slice(&self.d.to_le_bytes());
        h.push(self.inputs);
        for (s, k) in self.trunc {
            h.push(s);
            h.push(k);
        }
        h.extend_from_slice(&(self.entries.len() as u64).to_le_bytes());
        w.write_all(&h)?;
        let mut buf = Vec::with_capacity(17 * 4096);
        for &(t, s, m) in &self.entries {
            buf.push(t as u8);
            buf.extend_from_slice(&s.to_le_bytes());
            buf.extend_from_slice(&m.to_le_bytes());
            if buf.len() >= 17 * 4096 {
                w.write_all(&buf)?;
                buf.clear();
            }
        }
        w.write_all(&buf)
    }

    pub fn read_from(r: &mut impl Read) -> Result<Tape, String> {
        let mut b = Vec::new();
        r.read_to_end(&mut b).map_err(|e| e.to_string())?;
        if b.len() < 53 || &b[0..8] != MAGIC {
            return Err("not a DLTAPE1 tape".into());
        }
        let u64at = |o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
        let u32at = |o: usize| u32::from_le_bytes(b[o..o + 4].try_into().unwrap());
        let mut trunc = [(0u8, 0u8); 4];
        for (t, tr) in trunc.iter_mut().enumerate() {
            *tr = (b[37 + 2 * t], b[38 + 2 * t]);
        }
        let n = u64at(45) as usize;
        let body = &b[53..];
        if body.len() != 17 * n {
            return Err(format!("tape body is {} bytes, header says {} entries", body.len(), n));
        }
        let mut entries = Vec::with_capacity(n);
        for c in body.chunks_exact(17) {
            let t = Tag::from_code(c[0]).ok_or(format!("bad tag code {}", c[0]))?;
            entries.push((t, u64::from_le_bytes(c[1..9].try_into().unwrap()), u64::from_le_bytes(c[9..17].try_into().unwrap())));
        }
        Ok(Tape { p: u64at(8), n_parties: u32at(16), party: u32at(20), alpha_i: u64at(24), d: u32at(32), inputs: b[36], trunc, entries })
    }

    pub fn step_params(&self) -> StepParams {
        StepParams {
            d: self.d as usize,
            inputs: if self.inputs == 0 { Inputs::Harness } else { Inputs::Steady },
            trunc: self.trunc.map(|(s, k)| (s as u32, k as u32)),
            proof_atoms: false,
            proof_triples: 0,
            phase: crate::schedule::Phase::Step,
        }
    }
}

/// Assemble party `party`'s tape from its own Transactions file (party-local: no communication).
pub fn assemble(sp: &StepParams, tx: &Transactions, party: u32) -> Result<Tape, String> {
    assemble_step(sp, tx, party, 0, 1)
}

/// Step `j` of a chunk of `steps` steps generated in one MASCOT run (Plan::of_chunk): each kind's j-th slice.
pub fn assemble_step(sp: &StepParams, tx: &Transactions, party: u32, j: usize, steps: usize) -> Result<Tape, String> {
    assemble_in_chunk(&vec![*sp; steps], tx, party, j)
}

/// Step `j` of a chunk whose steps are `chunk` (crate::schedule::plan_of_steps).
pub fn assemble_in_chunk(chunk: &[StepParams], tx: &Transactions, party: u32, j: usize) -> Result<Tape, String> {
    let mut entries = Vec::with_capacity(crate::schedule::n_entries(&chunk[j]));
    let mut t = assemble_in_chunk_emit(chunk, tx, party, j, &mut |tag, (s, m)| entries.push((tag, s, m)))?;
    t.entries = entries;
    Ok(t)
}

/// As assemble_in_chunk, streaming: each entry goes to `emit` in tape order, none is kept; the returned Tape has
/// the header only (no entries).
pub fn assemble_in_chunk_emit(chunk: &[StepParams], tx: &Transactions, party: u32, j: usize, emit: &mut dyn FnMut(Tag, (u64, u64))) -> Result<Tape, String> {
    let sp = &chunk[j];
    let fp: Fp = tx.fp;
    let one = Plan::of(sp);
    let plan = crate::schedule::plan_of_steps(chunk);
    let sec = plan.sections();
    let (o_in, o_ar, o_tri, o_lp, o_tr) = crate::schedule::offsets(chunk, j);
    if tx.len() != sec.total {
        return Err(format!("Transactions holds {} shares, the plan needs {}", tx.len(), sec.total));
    }
    let at = |(base, _nc, m): (usize, usize, usize), comp: usize, k: usize| tx.share(base + comp * m + k);
    let lin = |terms: &[(u64, (u64, u64))]| {
        terms.iter().fold((0u64, 0u64), |(s, m), &(c, (x, y))| (fp.add(s, fp.mul(c, x)), fp.add(m, fp.mul(c, y))))
    };
    let mut cur_in = o_in;
    let mut cur_ar = o_ar;
    let mut cur_tri = o_tri;
    let mut cur_lp = o_lp;
    let mut cur_tr: Vec<usize> = o_tr;
    let triple = |emit: &mut dyn FnMut(Tag, (u64, u64)), cur: &mut usize| {
        for (c, t) in [Tag::Ta, Tag::Tb, Tag::Tc].into_iter().enumerate() {
            emit(t, at(sec.tri, c, *cur));
        }
        *cur += 1;
    };
    let mut bits: Vec<(u64, u64)> = Vec::new();
    for (e, n) in runs(sp) {
        for _ in 0..n {
            match e {
                Event::Input => {
                    emit(Tag::In, at(sec.input, 0, cur_in));
                    cur_in += 1;
                }
                Event::AuthPlain => {
                    emit(Tag::Ar, at(sec.ar, 0, cur_ar));
                    cur_ar += 1;
                }
                Event::Mul => triple(emit, &mut cur_tri),
                Event::Trunc(s, k) => {
                    let c = plan.class_of(s, k);
                    let i = cur_tr[c];
                    cur_tr[c] += 1;
                    let nb = (k + KAPPA) as usize;
                    bits.clear();
                    bits.extend((0..nb).map(|j| at(sec.tr[c], j, i)));
                    let r: Vec<_> = (0..nb).map(|j| (fp.two_pow(j as u32), bits[j])).collect();
                    emit(Tag::Tr, lin(&r));
                    for b in bits.iter().take(s as usize) {
                        emit(Tag::Trb, *b);
                    }
                    let hi: Vec<_> = (s as usize..nb).map(|j| (fp.two_pow(j as u32 - s), bits[j])).collect();
                    emit(Tag::Trh, lin(&hi));
                    if sp.proof_atoms {
                        for b in &bits[s as usize..] {
                            emit(Tag::Trhb, *b);
                        }
                    }
                    for _ in 0..2 * (s - 1) {
                        triple(emit, &mut cur_tri);
                    }
                }
                Event::Lookup => {
                    for j in 0..DEG {
                        emit(Tag::Lp, at(sec.lp, j, cur_lp));
                    }
                    cur_lp += 1;
                }
            }
        }
    }
    if (cur_in, cur_ar, cur_tri, cur_lp) != (o_in + one.n_in, o_ar + one.n_ar, o_tri + one.n_tri, o_lp + one.n_lp) {
        return Err("assembly consumed a different number of objects than the plan".into());
    }
    Ok(Tape {
        p: fp.p,
        n_parties: 3,
        party,
        alpha_i: tx.alpha_i,
        d: sp.d as u32,
        inputs: match sp.phase {
            crate::schedule::Phase::Step => sp.inputs as u8,
            crate::schedule::Phase::Release(_) => RELEASE_INPUTS,
            crate::schedule::Phase::Handover(_) => HANDOVER_INPUTS,
        },
        trunc: sp.trunc.map(|(s, k)| (s as u8, k as u8)),
        entries: Vec::new(),
    })
}

/// A darkstep DLTAPE01 file written entry by entry: "DLTAPE01", alpha_i, n, then n tags, n shares, n MAC shares
/// (darkstep::tape::Tape::write_to's layout), each column through its own buffered writer at its offset.
pub struct DarkstepWriter {
    cols: [std::io::BufWriter<std::fs::File>; 3],
    n: usize,
    k: usize,
}

impl DarkstepWriter {
    pub fn create(path: &std::path::Path, alpha_i: u64, n: usize) -> std::io::Result<Self> {
        use std::io::{Seek, SeekFrom, Write};
        let mut f = std::fs::File::create(path)?;
        let mut h = b"DLTAPE01".to_vec();
        h.extend_from_slice(&alpha_i.to_le_bytes());
        h.extend_from_slice(&(n as u64).to_le_bytes());
        f.write_all(&h)?;
        f.set_len(24 + 17 * n as u64)?;
        let col = |off: u64| -> std::io::Result<std::io::BufWriter<std::fs::File>> {
            let mut g = std::fs::OpenOptions::new().write(true).open(path)?;
            g.seek(SeekFrom::Start(off))?;
            Ok(std::io::BufWriter::with_capacity(1 << 20, g))
        };
        Ok(DarkstepWriter { cols: [col(24)?, col(24 + n as u64)?, col(24 + 9 * n as u64)?], n, k: 0 })
    }
    pub fn push(&mut self, t: Tag, (s, m): (u64, u64)) -> std::io::Result<()> {
        use std::io::Write;
        if self.k == self.n {
            return Err(std::io::Error::other("more entries than the header says"));
        }
        self.k += 1;
        self.cols[0].write_all(&[t as u8 + 1])?; // darkstep numbers In = 1 .. Ar = 9, Trhb = 10
        self.cols[1].write_all(&s.to_le_bytes())?;
        self.cols[2].write_all(&m.to_le_bytes())
    }
    pub fn finish(self) -> std::io::Result<()> {
        use std::io::Write;
        if self.k != self.n {
            return Err(std::io::Error::other(format!("{} entries written, the header says {}", self.k, self.n)));
        }
        for mut c in self.cols {
            c.flush()?;
            c.get_ref().sync_data()?;
        }
        Ok(())
    }
}

pub fn write_owner(w: &mut impl Write, p: u64, rs: &[u64]) -> std::io::Result<()> {
    w.write_all(OWNER_MAGIC)?;
    w.write_all(&p.to_le_bytes())?;
    w.write_all(&(rs.len() as u64).to_le_bytes())?;
    let mut buf = Vec::with_capacity(8 * rs.len());
    for r in rs {
        buf.extend_from_slice(&r.to_le_bytes());
    }
    w.write_all(&buf)
}

pub fn read_owner(r: &mut impl Read) -> Result<(u64, Vec<u64>), String> {
    let mut b = Vec::new();
    r.read_to_end(&mut b).map_err(|e| e.to_string())?;
    if b.len() < 24 || &b[0..8] != OWNER_MAGIC {
        return Err("not a DLOWNR1 file".into());
    }
    let p = u64::from_le_bytes(b[8..16].try_into().unwrap());
    let n = u64::from_le_bytes(b[16..24].try_into().unwrap()) as usize;
    if b.len() != 24 + 8 * n {
        return Err("owner file length mismatch".into());
    }
    Ok((p, b[24..].chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect()))
}
