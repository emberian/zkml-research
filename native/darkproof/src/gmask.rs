//! Cut D (proofwire ZKSC "mask"; cosnark_zk.GMask, open_sum, check_rounds, unflat): every sumcheck's round messages
//! are opened, made uniform by a masking polynomial g = g_1(x_1) + ... + g_l(x_l) per sumcheck; all g of a proof are
//! one hidden Ligero group, committed first. One rho in F_{p^E} serves every sumcheck of the proof.
use crate::ext;
use crate::field;
use crate::h::Hash;
use crate::ligero::LigParty;
use crate::net::Net;
use crate::spine::EEm;
use crate::transcript::Transcript;
use std::collections::BTreeMap;

/// A coefficient on one g cell group: (round j, node t, element).
pub type Coef<const E: usize> = Vec<(usize, usize, [u64; E])>;

/// The masking polynomials of one proof. g_name's round j polynomial is given by its values at t = 0..deg, each an
/// F_{p^E} element; the cells of every g are packed, in spec order, into consecutive Ligero rows from row0: flat
/// index off(name) + (j (deg + 1) + t) E + k.
#[derive(Clone, Debug)]
pub struct GMask {
    pub specs: Vec<(String, usize, usize)>,
    pub row0: usize,
    pub kl: usize,
    pub e: usize,
    off: BTreeMap<String, usize>,
    ld: BTreeMap<String, (usize, usize)>,
    pub ncells: usize,
    pub nrows: usize,
}

fn pow2(k: usize) -> u64 {
    field::pow(2, k as u64)
}

impl GMask {
    pub fn new(specs: Vec<(String, usize, usize)>, row0: usize, kl: usize, e: usize) -> Self {
        let (mut off, mut ld) = (BTreeMap::new(), BTreeMap::new());
        let mut n = 0;
        for (name, l, deg) in &specs {
            off.insert(name.clone(), n);
            ld.insert(name.clone(), (*l, *deg));
            n += l * (deg + 1) * e;
        }
        GMask { specs, row0, kl, e, off, ld, ncells: n, nrows: n.div_ceil(kl) }
    }

    pub fn idx(&self, name: &str, j: usize, t: usize, k: usize) -> usize {
        let (_, deg) = self.ld[name];
        self.off[name] + (j * (deg + 1) + t) * self.e + k
    }

    pub fn cell(&self, name: &str, j: usize, t: usize, k: usize) -> (usize, usize) {
        let i = self.idx(name, j, t, k);
        (self.row0 + i / self.kl, i % self.kl)
    }

    /// G = sum over the cube of g = 2^(l-1) sum_j (g_j(0) + g_j(1)).
    pub fn g_coef<const E: usize>(&self, name: &str) -> Coef<E> {
        let (l, _) = self.ld[name];
        let c = ext::lift::<E>(pow2(l - 1));
        (0..l).flat_map(|j| [(j, 0, c), (j, 1, c)]).collect()
    }

    /// g(rs) = sum_j g_j(r_j).
    pub fn at_coef<const E: usize>(&self, name: &str, rs: &[[u64; E]]) -> Coef<E> {
        let (_, deg) = self.ld[name];
        rs.iter().enumerate().flat_map(|(j, &r)| ext::lagc(deg, r).into_iter().enumerate().map(move |(t, lc)| (j, t, lc))).collect()
    }

    /// The round-i message's g part at X = t: 2^(l-1-i) (sum_{j<i} g_j(r_j) + g_i(t)) + 2^(l-2-i) sum_{j>i}
    /// (g_j(0) + g_j(1)).
    pub fn round_coef<const E: usize>(&self, name: &str, i: usize, t: usize, rs: &[[u64; E]]) -> Coef<E> {
        let (l, deg) = self.ld[name];
        let a = ext::lift::<E>(pow2(l - 1 - i));
        let mut out: Coef<E> = Vec::new();
        for (j, &r) in rs.iter().enumerate().take(i) {
            for (tt, lc) in ext::lagc(deg, r).into_iter().enumerate() {
                out.push((j, tt, ext::mul(a, lc)));
            }
        }
        out.push((i, t, a));
        if i < l - 1 {
            let b = ext::lift::<E>(pow2(l - 2 - i));
            for j in i + 1..l {
                out.push((j, 0, b));
                out.push((j, 1, b));
            }
        }
        out
    }

    /// The form scale * sum coef * g-cell value.
    pub(crate) fn lin_form<const E: usize>(&self, em: &mut EEm<E>, name: &str, coefs: &Coef<E>, scale: [u64; E]) {
        for &(j, t, c) in coefs {
            em.var(std::array::from_fn(|k| self.cell(name, j, t, k)), ext::mul(scale, c));
        }
    }

    /// One party's share of sum coef * g-cell value, from its flat share list.
    pub fn share_val<const E: usize>(&self, sh: &[u64], name: &str, coefs: &Coef<E>) -> [u64; E] {
        let mut acc = ext::zero::<E>();
        for &(j, t, c) in coefs {
            let v: [u64; E] = std::array::from_fn(|k| sh[self.idx(name, j, t, k)]);
            acc = ext::add(acc, ext::mul(c, v));
        }
        acc
    }
}

/// cosnark_zk.specs: the spine's masking polynomials (sumcheck, rounds, degree).
pub fn spine_specs(ld: usize) -> Vec<(String, usize, usize)> {
    vec![("z1".into(), ld, 2), ("z2".into(), ld, 2), ("b".into(), ld, 2), ("bg".into(), ld, 3)]
}

/// cosnark_gates_zk.specs: the zerocheck, then one per linear sumcheck (sorted names).
pub fn middle_specs(lh: usize, lmax: usize, ks: &[String]) -> Vec<(String, usize, usize)> {
    let mut v = vec![("zc".to_string(), lh, 3)];
    v.extend(ks.iter().map(|k| (format!("l:{k}"), lmax, 2)));
    v
}

/// unflat: a flat opened round message (E components per value) as deg + 1 elements.
pub fn unflat<const E: usize>(v: &[u64]) -> Vec<[u64; E]> {
    v.chunks(E).map(|c| std::array::from_fn(|k| c[k])).collect()
}

pub fn flat<const E: usize>(v: &[[u64; E]]) -> Vec<u64> {
    v.iter().flat_map(|x| x.iter().copied()).collect()
}

/// The verifier's clear checks of one sumcheck's opened messages: shape, s_0(0) + s_0(1) = claim0 when it is
/// public, s_i(0) + s_i(1) = s_(i-1)(r_(i-1)).
pub fn check_rounds<const E: usize>(
    name: &str,
    msgs: &[Vec<[u64; E]>],
    rs: &[[u64; E]],
    deg: usize,
    claim0: Option<[u64; E]>,
) -> Result<(), String> {
    if msgs.len() != rs.len() || msgs.iter().any(|m| m.len() != deg + 1) {
        return Err(format!("sumcheck {name}: round messages of the wrong shape"));
    }
    if let Some(c) = claim0 {
        if ext::add(msgs[0][0], msgs[0][1]) != c {
            return Err(format!("sumcheck {name}: first round sum differs from the public claim"));
        }
    }
    for i in 1..msgs.len() {
        if ext::add(msgs[i][0], msgs[i][1]) != ext::interp_at(&msgs[i - 1], rs[i - 1]) {
            return Err(format!("sumcheck {name}: round {i} sum differs from the previous round at r"));
        }
    }
    Ok(())
}

/// The opened masking data of one proof, as both sides hold it: the g group's layout, the G values by sumcheck,
/// the opened round messages by sumcheck, rho.
#[derive(Clone, Debug)]
pub struct MaskZ<const E: usize> {
    pub gm: GMask,
    pub g: BTreeMap<String, [u64; E]>,
    pub msgs: BTreeMap<String, Vec<Vec<[u64; E]>>>,
    pub rho: [u64; E],
}

impl<const E: usize> MaskZ<E> {
    /// The G values in spec order, flat (the transcript's and the wire's form).
    pub fn g_flat(&self) -> Vec<u64> {
        self.gm.specs.iter().flat_map(|(nm, _, _)| self.g[nm].iter().copied()).collect()
    }

    /// The verifier's side before the schedule: absorb the g roots and G, draw rho.
    pub fn from_wire(gm: GMask, g_roots: &[Hash], gflat: &[u64], tr: &mut Transcript) -> Self {
        let g = gm.specs.iter().enumerate().map(|(i, (nm, _, _))| (nm.clone(), std::array::from_fn(|k| gflat[E * i + k]))).collect();
        absorb_g(tr, g_roots, gflat);
        let rho = ext::chal1::<E>(tr);
        MaskZ { gm, g, msgs: BTreeMap::new(), rho }
    }

    /// The per-sumcheck constraints (cosnark_zk.constraints sumcheck_mask): G = the sum of g over the cube; claim + rho
    /// G = s_0(0) + s_0(1) when the claim is hidden (`first` emits the claim's form); final + rho g(r) = s_l(r_l).
    pub(crate) fn sumcheck(
        &self,
        em: &mut EEm<E>,
        name: &str,
        rs: &[[u64; E]],
        first: Option<&dyn Fn(&mut EEm<E>)>,
        fin: &dyn Fn(&mut EEm<E>),
    ) {
        let (msgs, g) = (&self.msgs[name], self.g[name]);
        self.gm.lin_form(em, name, &self.gm.g_coef::<E>(name), ext::one());
        em.done(&format!("sumcheck {name}: G = the sum of g over the cube"), g);
        if let Some(f) = first {
            f(em);
            em.done(&format!("sumcheck {name}: claim + rho G = first round sum"), ext::sub(ext::add(msgs[0][0], msgs[0][1]), ext::mul(self.rho, g)));
        }
        fin(em);
        self.gm.lin_form(em, name, &self.gm.at_coef(name, rs), self.rho);
        em.done(&format!("sumcheck {name}: final + rho g(r) = last round at r"), ext::interp_at(msgs.last().unwrap(), *rs.last().unwrap()));
    }
}

pub fn absorb_g(tr: &mut Transcript, g_roots: &[Hash], gflat: &[u64]) {
    tr.absorb(|h| {
        h.s("zkg").list_hx(g_roots);
    });
    tr.absorb(|h| {
        h.s("G").list(gflat);
    });
}

/// The opened sum of every party's element shares (every custodian broadcasts its shares).
fn open_all<const E: usize>(net: &mut dyn Net, mine: Vec<u64>) -> Vec<[u64; E]> {
    let all = net.all_gather(mine);
    let m = all[0].len() / E;
    (0..m).map(|x| std::array::from_fn(|k| all.iter().fold(0, |a, v| field::add(a, v[x * E + k])))).collect()
}

/// The prover's side (cosnark_zk.prove_zk pre / GMask.commit): this party draws its g shares from its own Ligero
/// stream, adds the rows, commits them as one group; the G values are opened and absorbed and rho drawn. `bump`:
/// the ATTACK rows' G (this party's G share of that sumcheck + 1). Returns (the opened data, this party's g shares,
/// the g roots).
pub fn commit<const E: usize>(
    gm: GMask,
    lg: &mut LigParty,
    net: &mut dyn Net,
    tr: &mut Transcript,
    bump: Option<&str>,
) -> (MaskZ<E>, Vec<u64>, Vec<Hash>) {
    let gsh = lg.draw(gm.ncells);
    for r in 0..gm.nrows {
        lg.add_row(&gsh[r * gm.kl..((r + 1) * gm.kl).min(gm.ncells)]);
    }
    let g_roots = lg.commit(net);
    let mut mine = Vec::with_capacity(E * gm.specs.len());
    for (nm, _, _) in &gm.specs {
        let mut v = gm.share_val(&gsh, nm, &gm.g_coef::<E>(nm));
        if bump == Some(nm.as_str()) {
            v = ext::add(v, ext::one());
        }
        mine.extend(v);
    }
    let gv = open_all::<E>(net, mine);
    let g: BTreeMap<String, [u64; E]> = gm.specs.iter().zip(gv).map(|((nm, _, _), v)| (nm.clone(), v)).collect();
    let mut mz = MaskZ { gm, g, msgs: BTreeMap::new(), rho: ext::zero() };
    absorb_g(tr, &g_roots, &mz.g_flat());
    mz.rho = ext::chal1::<E>(tr);
    (mz, gsh, g_roots)
}

/// cosnark_zk open_round: every custodian broadcasts its share of s_rnd = f part + rho g part, for each of several
/// sumchecks of one round (the middle's lockstep linear sumchecks: one broadcast for all). vals[s][t]: this party's
/// f-part shares of sumcheck names[s] at X = t; pts: the round's challenges so far. `bump`: the ATTACK row (this
/// party's share of (sumcheck, X = t) + 1). Returns the opened messages, in names' order.
pub fn open_round<const E: usize>(
    mz: &MaskZ<E>,
    gsh: &[u64],
    net: &mut dyn Net,
    names: &[&str],
    rnd: usize,
    pts: &[[u64; E]],
    vals: &[Vec<[u64; E]>],
    bump: Option<(&str, usize)>,
) -> Vec<Vec<[u64; E]>> {
    let mut mine = Vec::new();
    for (s, nm) in names.iter().enumerate() {
        for (t, &v) in vals[s].iter().enumerate() {
            let cf = mz.gm.round_coef(nm, rnd, t, pts);
            let mut x = ext::add(v, ext::mul(mz.rho, mz.gm.share_val(gsh, nm, &cf)));
            if bump == Some((*nm, t)) {
                x = ext::add(x, ext::one());
            }
            mine.extend(x);
        }
    }
    let plain = open_all::<E>(net, mine);
    let mut out = Vec::with_capacity(names.len());
    let mut o = 0;
    for v in vals {
        out.push(plain[o..o + v.len()].to_vec());
        o += v.len();
    }
    out
}
