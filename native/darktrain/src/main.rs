//! darktrain run '<cfg json>'   : integer training, one JSON line per eval point, then a summary line
//! darktrain float '<cfg json>' : the float baseline of the same architecture
//! darktrain feed '<cfg json>' START COUNT : the data owner's step inputs, one JSON line per step {t, k, x, y}
//! darktrain shadow '<cfg json>' STEPS N_EVAL : the plaintext shadow of a custody run: train STEPS steps, then the
//!     custodians' evaluation (the count of strictly correct predictions on test examples 0..N_EVAL) and the weight
//!     digest sha256(repr((W1, W2))) the custody run's revealed weights must equal (tests only: custody never reveals)
use darktrain::*;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let c: Cfg = serde_json::from_str(a.get(2).map(|s| s.as_str()).unwrap_or("{}")).expect("cfg json");
    c.validate().unwrap();
    let m = data::load(std::path::Path::new(&c.data)).unwrap();
    let c = c.with_means(&m);
    match a[1].as_str() {
        "run" => {
            let (pts, _, _) = train(&c, &m, |p| println!("{}", serde_json::to_string(p).unwrap()));
            let last = pts.last().unwrap();
            println!("{}", serde_json::json!({"summary": true, "cfg": c, "final_acc_o": last.eval.acc_o, "final_acc_z2": last.eval.acc_z2,
                "violations_train": last.train_bounds.violations(), "violations_eval": last.eval.bounds.violations(), "secs": last.secs}));
        }
        "float" => {
            let out = train_float(&c, &m, |s, acc, t| println!("{}", serde_json::json!({"step": s, "acc": acc, "secs": t})));
            println!("{}", serde_json::json!({"summary": true, "float": true, "cfg": c, "final_acc": out.last().unwrap().1}));
        }
        "feed" => {
            let (s0, n): (usize, usize) = (a[3].parse().unwrap(), a[4].parse().unwrap());
            let ord = order(c.seed_order, m.train.n);
            for t in s0..s0 + n {
                let k = ord[t % m.train.n];
                let (x, y) = encode(&c, m.train.image(k), m.train.lab[k]);
                println!("{}", serde_json::json!({"t": t, "k": k, "x": x, "y": y}));
            }
        }
        "shadow" => {
            let (steps, ne): (usize, usize) = (a[3].parse().unwrap(), a[4].parse().unwrap());
            let mut c2 = c.clone();
            c2.steps = steps;
            c2.evals = vec![];
            c2.eval_n = ne;
            let (pts, w1, w2) = train(&c2, &m, |_| {});
            let ev = &pts.last().unwrap().eval;
            println!("{}", serde_json::json!({"steps": steps, "n_eval": ne, "correct": (ev.acc_o * ne as f64).round() as u64,
                "acc": ev.acc_o, "violations": pts.last().unwrap().train_bounds.violations() + ev.bounds.violations(),
                "weights_sha256": weights_digest(c.d, &w1, &w2)}));
        }
        x => panic!("unknown command {x}"),
    }
}
