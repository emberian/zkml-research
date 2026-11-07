//! dl-owner: the data owner's process. The three custodians (`darkstep serve`) dial it over mutual TLS (pinned
//! certificates); per step it takes each custodian's owner message, forms the step's input masks r, and sends every
//! custodian the broadcasts c = v - r (mod t) of the step's values v.
//!
//!   dl-owner --listen HOST:PORT --tls TLSDIR --t T --d D (--test-public DIR | --train CFG.json)
//!   - TLSDIR: tls_owner.key, cert_owner.der, cert_{0,1,2}.der
//!   - --test-public DIR: TEST: serve DIR/public_step<k>.bin (the public-seed test dealer's broadcasts as is)
//!   - --train CFG.json (darktrain's Cfg, its "data" the MNIST directory, "seed_order" the owner's private order):
//!     values from darktrain (genesis W1, W2 = darktrain::init at step 0, then the encoded example of each step),
//!     masks from the custodians' input-tuple shares (darkprep owner: r = a of each checked triple)
use std::net::TcpListener;

fn flag(a: &[String], n: &str) -> Option<String> {
    a.iter().position(|x| x == n).and_then(|k| a.get(k + 1).cloned())
}

enum Values {
    Test(std::path::PathBuf),
    Train { c: darktrain::Cfg, m: darktrain::data::Mnist, ord: Vec<usize> },
}

/// A custodian's owner message (darkprep's DLOMSG1: magic, u64 count, count x (a_i, b_i, c_i) u64 LE).
fn owner_message(b: &[u8]) -> Result<Vec<[u64; 3]>, String> {
    if b.len() < 16 || &b[..8] != b"DLOMSG1\n" {
        return Err("owner message: not DLOMSG1".into());
    }
    let n = u64::from_le_bytes(b[8..16].try_into().unwrap()) as usize;
    if b.len() != 16 + 24 * n {
        return Err("owner message: wrong length".into());
    }
    let v = darkstep::net::bytes_to_u64s(&b[16..]);
    Ok(v.chunks(3).map(|c| [c[0], c[1], c[2]]).collect())
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let tls = std::path::PathBuf::from(flag(&a, "--tls").expect("--tls"));
    let t: u64 = flag(&a, "--t").expect("--t").parse().unwrap();
    let d: usize = flag(&a, "--d").expect("--d").parse().unwrap();
    let id = darkstep::tls::Identity {
        key_der: std::fs::read(tls.join("tls_owner.key")).expect("owner key"),
        cert_der: std::fs::read(tls.join("cert_owner.der")).expect("owner cert"),
    };
    let certs: Vec<Vec<u8>> = (0..3).map(|j| std::fs::read(tls.join(format!("cert_{j}.der"))).unwrap()).collect();
    let vals = if let Some(dir) = flag(&a, "--test-public") {
        Values::Test(dir.into())
    } else {
        let cfg = std::fs::read_to_string(flag(&a, "--train").expect("--test-public or --train")).unwrap();
        let c: darktrain::Cfg = serde_json::from_str(&cfg).expect("cfg");
        c.validate().unwrap();
        assert_eq!(c.d, d);
        let m = darktrain::data::load(std::path::Path::new(&c.data)).unwrap();
        let c = c.with_means(&m);
        let ord = darktrain::order(c.seed_order, m.train.n);
        Values::Train { c, m, ord }
    };
    let l = TcpListener::bind(flag(&a, "--listen").expect("--listen")).unwrap();
    let fp = darkprep::field::Fp::new(t);
    let res = darkstep::serve::owner_serve(l, &id, &certs, |k, msgs| match &vals {
        Values::Test(dir) => std::fs::read(dir.join(format!("public_step{k}.bin"))).map(|b| darkstep::net::bytes_to_u64s(&b)).map_err(|e| e.to_string()),
        Values::Train { c, m, ord } => {
            let mut v: Vec<i64> = Vec::new();
            if k == 0 {
                let (w1, w2) = darktrain::init(c);
                v.extend(w1);
                v.extend(w2);
            }
            let ex = ord[k % m.train.n];
            let (x, y) = darktrain::encode(c, m.train.image(ex), m.train.lab[ex]);
            v.extend(x);
            v.extend(y);
            let msgs: Vec<Vec<[u64; 3]>> = msgs.iter().map(|r| owner_message(r)).collect::<Result<_, _>>()?;
            let rs = darkprep::owner::owner_masks(fp, &msgs)?;
            if rs.len() != v.len() {
                return Err(format!("step {k}: {} masks for {} inputs", rs.len(), v.len()));
            }
            Ok(v.iter().zip(&rs).map(|(&x, &r)| darkstep::arith::submod(darkstep::arith::from_i64(x, t), r, t)).collect())
        }
    });
    if let Err(e) = res {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
