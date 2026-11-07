//! §19 lives_falsifier natively: a hiding commitment opened in a third proof reveals its data; the honest life
//! counter refuses that opening.
use darkproof::field;
use darkproof::pcs::PcsParty;
use darkproof::poly::lagrange_basis;
use darkproof::rng::Det;
use darkproof::transcript::Transcript;
use darkproof::Profile;
use pycompat::PyRandom;
use std::collections::BTreeMap;

fn openings(coms: &mut [PcsParty], lives: usize, pr: &Profile) -> Result<BTreeMap<usize, Vec<u64>>, String> {
    let mut pts = BTreeMap::new();
    for life in 0..lives {
        let mut tr = Transcript::new(&format!("proof-{life}"));
        for c in coms.iter_mut() {
            c.shape.base = if life == 0 { 0 } else { c.shape.block };
            c.take_life("W1n", pr.lives).map_err(|e| e.0)?;
        }
        for j in tr.distinct_cols(pr.t_cols, coms[0].shape.npts) {
            let mut s = vec![0u64; coms[0].shape.rd];
            for c in coms.iter() {
                for (a, b) in s.iter_mut().zip(c.open(j).0) {
                    *a = field::add(*a, b);
                }
            }
            pts.insert(j + 1, s);
        }
    }
    Ok(pts)
}

#[test]
fn lives_falsifier() {
    let pr = Profile::demo();
    let mut rng = PyRandom::from_u64(7);
    let d = 4;
    let secret: Vec<u64> = (0..d * d).map(|_| field::from_i64(rng.randint_i64(-7, 7))).collect();
    let mut sh: Vec<Vec<u64>> = (0..2).map(|_| secret.iter().map(|_| rng.randrange_u64(field::p())).collect()).collect();
    sh.push(secret.iter().enumerate().map(|(k, &v)| field::sub(field::sub(v, sh[0][k]), sh[1][k])).collect());
    let det = Det(None);
    let mut honest: Vec<PcsParty> = (0..3).map(|i| PcsParty::commit(&pr, &sh[i], "W1n", i, &det)).collect();
    let r = openings(&mut honest, 3, &pr);
    assert!(r.as_ref().unwrap_err().contains("already opened in 2 proofs"), "honest third opening must be refused: {r:?}");
    let mut forced: Vec<PcsParty> = (0..3).map(|i| PcsParty::commit(&pr, &sh[i], "W1n", i, &det)).collect();
    for c in forced.iter_mut() {
        c.max_lives = 99;
    }
    let pts = openings(&mut forced, 3, &pr).unwrap();
    let s = &forced[0].shape;
    assert!(pts.len() >= s.w, "{} distinct points for rows of degree < {}", pts.len(), s.w);
    let xs: Vec<u64> = pts.keys().take(s.w).map(|&x| x as u64).collect();
    let basis = lagrange_basis(&xs);
    let mut rec = Vec::new();
    for r in 0..s.rd {
        let ys: Vec<u64> = xs.iter().map(|&x| pts[&(x as usize)][r]).collect();
        let coeffs = darkproof::poly::combine(&ys, &basis, s.w);
        rec.extend_from_slice(&coeffs[..s.c]);
    }
    assert_eq!(rec, secret, "a forced third opening must leak the committed data (else the counter is moot)");
    // and two lives do not determine it (negative control on the same machinery)
    let mut two: Vec<PcsParty> = (0..3).map(|i| PcsParty::commit(&pr, &sh[i], "W1n", i, &det)).collect();
    let pts2 = openings(&mut two, 2, &pr).unwrap();
    assert!(pts2.len() < s.w, "two lives open {} < {} points", pts2.len(), s.w);
}
