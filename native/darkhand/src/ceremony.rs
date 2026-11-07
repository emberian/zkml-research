//! The new committee's key ceremony (keygen_ceremony.run_ceremony over the new committee's own mesh, at the new
//! epoch): darkstep::gate::ceremony with the epoch as a parameter (gate pins EPOCH = 1 for the first committee).
//! Each new custodian's key s is drawn from OS coins; the ceremony's transcript, seed and every key proof are checked.
use darkstep::net::{self, Net};
use dzkpopk::ceremony::{Ceremony, Custodian};
use dzkpopk::BigPoly;

fn poly_bytes(p: &BigPoly) -> Vec<u8> {
    let mut v = vec![p.nl() as u64];
    v.extend_from_slice(p.data());
    net::u64s_to_bytes(&v)
}

fn poly_parse(b: &[u8]) -> Result<BigPoly, String> {
    let v = net::bytes_to_u64s(b);
    if v.is_empty() {
        return Err("empty key".into());
    }
    BigPoly::from_limbs(v[0] as usize, v[1..].to_vec())
}

/// Returns (my custodian with its secret key, the ceremony with every key registered).
pub fn run(net: &Net, me: usize, ring_n: usize, primes: &[u64], t: u64, tcols: usize, epoch: i64) -> Result<(Custodian, Ceremony), String> {
    let mut cust = Custodian::new(me);
    let mut cer = Ceremony::new(epoch, net.n, ring_n, primes, t, tcols);
    let mine = cust.commitment(epoch);
    let coms = net.exchange_bytes(net::CTRL, mine.as_bytes());
    for (i, c) in coms.iter().enumerate() {
        let c = String::from_utf8(c.clone()).map_err(|_| "commitment: not text")?;
        cer.commit(i, &c).map_err(|e| e.0)?;
    }
    let rev = net.exchange_bytes(net::CTRL, format!("{}|{}", cust.r, cust.salt).as_bytes());
    for (i, b) in rev.iter().enumerate() {
        let s = String::from_utf8(b.clone()).map_err(|_| "reveal: not text")?;
        let (r, salt) = s.split_once('|').ok_or("reveal: shape")?;
        cer.reveal(i, r, salt).map_err(|e| e.0)?;
    }
    let (b, proof) = cust.make_key(&cer)?;
    let mut msg = poly_bytes(&b);
    let blen = msg.len() as u64;
    let mut m = blen.to_le_bytes().to_vec();
    m.append(&mut msg);
    m.extend_from_slice(&proof);
    let keys = net.exchange_bytes(net::CTRL, &m);
    for (i, m) in keys.iter().enumerate() {
        if m.len() < 8 {
            return Err(format!("custodian {i}'s key message: shape"));
        }
        let bl = u64::from_le_bytes(m[..8].try_into().unwrap()) as usize;
        if m.len() < 8 + bl {
            return Err(format!("custodian {i}'s key message: shape"));
        }
        let bi = poly_parse(&m[8..8 + bl])?;
        cer.register(i, bi, &m[8 + bl..]).map_err(|e| e.0)?;
    }
    Ok((cust, cer))
}
