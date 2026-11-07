//! The harness's test instances, draw for draw (run_zkpopk_ligero.sk_batch, and tests/py/zkpopk_vectors.py's pk
//! batch and key statement), for the bit-exact checks and the attack table.

use crate::canon::Json;
use crate::gen::{encrypt_pk, encrypt_sk, keygen};
use crate::proof::Witness;
use crate::statement::{ntt_primes, Kind, Statement};
use pycompat::PyRandom;
use std::sync::Arc;

pub fn ctx() -> Json {
    Json::list(vec![
        Json::s("mind-0"),
        Json::i(0),
        Json::i(7),
        Json::s("matvec-fwd-0"),
        Json::s("custodian-1"),
        Json::list(vec![Json::s("custodian-0"), Json::s("custodian-2")]),
    ])
}

pub fn params(n: usize, l: usize) -> (Vec<u64>, u64) {
    let pr = ntt_primes(61, l + 1, 2 * n as u64);
    (pr[..l].to_vec(), pr[l])
}

/// run_zkpopk_ligero.sk_batch + the vectors script's pk batch and key statement, draw for draw.
pub fn instances(n: usize, l: usize, m: usize) -> Vec<(&'static str, Statement, Witness)> {
    let (qp, t) = params(n, l);
    let mut rng = PyRandom::from_u64((n * 1000 + m) as u64);
    let (reg, s, epk) = keygen(n, &qp, t, "registry-seed-0", "custodian-1", &mut rng);
    let reg = Arc::new(reg);
    let dc = 64.min(n / 2);
    let (mut cts, mut ws, mut slots) = (vec![], vec![], vec![]);
    for j in 0..m {
        let sl: Vec<usize> = if j == m - 1 && m > 1 { (0..n).step_by((n / dc).max(1)).take(dc).collect() } else { (0..dc).collect() };
        let mut pm = vec![0u64; n];
        for &k in &sl {
            pm[k] = rng.randrange_u64(t);
        }
        let (ct, w) = encrypt_sk(&reg, &s, &pm, &sl, &mut rng, None);
        cts.push(ct);
        ws.push(w);
        slots.push(sl);
    }
    let st_sk = Statement::new(reg.clone(), Kind::Sk, cts, slots, ctx()).unwrap();
    let (regj, _, _) = keygen(n, &qp, t, "joint-seed-0", "joint", &mut rng);
    let regj = Arc::new(regj);
    let (mut pcts, mut pws, mut psl) = (vec![], vec![], vec![]);
    for _ in 0..(m.saturating_sub(1)).max(1) {
        let sx: Vec<usize> = (0..n.min(8)).collect();
        let mut pm = vec![0u64; n];
        for &k in &sx {
            pm[k] = rng.randrange_u64(t);
        }
        let (ct, w) = encrypt_pk(&regj, &pm, &sx, &mut rng, None);
        pcts.push(ct);
        pws.push(w);
        psl.push(sx);
    }
    let st_pk = Statement::new(regj, Kind::Pk, pcts, psl, ctx()).unwrap();
    let key_ctx = Json::list(vec![Json::s("dl-keygen-key"), Json::i(1), Json::i(1), Json::s("vectors")]);
    let st_key = Statement::new(reg, Kind::Key, vec![], vec![], key_ctx).unwrap();
    vec![
        ("sk", st_sk, Witness::Sk { s: s.clone(), e_pk: epk.clone(), cts: ws }),
        ("pk", st_pk, Witness::Pk { cts: pws }),
        ("key", st_key, Witness::Sk { s, e_pk: epk, cts: vec![] }),
    ]
}

