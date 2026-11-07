//! A production party process draws its HE coins from the OS, not from the harness's public reference streams.
//! Two runs of the real `darkstep party` binary (three processes each) on the same reference tapes and inputs:
//! - the public transcript differs from the reference's and between the runs: it holds every party's broadcast
//!   share, which carries the masks, and the Fiat-Shamir coins drawn from it,
//! - the share digests differ from the reference's and between the two runs (a public-seed coin stream would make
//!   them equal to the reference: vs_reference shows that the in-process harness, which uses those streams, does),
//! - the revealed weights refine the spec in both runs.
use darkstep::node::{prof, reveal_check, DEALER_SEED, OWNER_SEED};
use darkstep::party::Sh;
use darkstep::step::inputs;
use std::process::Command;

fn reference(name: &str) -> serde_json::Value {
    let path = format!("{}/../../research/dark_learning_2026_11_06/native_ref_results/{name}", env!("CARGO_MANIFEST_DIR"));
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn run(dir: &std::path::Path, extra: &[&str]) -> (Vec<serde_json::Value>, bool) {
    let a = ["4096", "3", "118", "64"].map(String::from);
    let pf = prof(&a);
    let addrs: Vec<String> = (0..3).map(|_| format!("127.0.0.1:{}", free_port())).collect();
    let kids: Vec<_> = (0..3)
        .map(|i| {
            Command::new(env!("CARGO_BIN_EXE_darkstep"))
                .args(["party", &i.to_string()])
                .args(&a)
                .arg(dir)
                .args(&addrs)
                .args(extra)
                .env("DS_THREADS", "4")
                .spawn()
                .unwrap()
        })
        .collect();
    for mut k in kids {
        assert!(k.wait().unwrap().success());
    }
    let res: Vec<serde_json::Value> = (0..3)
        .map(|i| serde_json::from_str(&std::fs::read_to_string(dir.join(format!("result_{i}.json"))).unwrap()).unwrap())
        .collect();
    let d = pf.d;
    let shares: Vec<(Vec<Vec<Sh>>, Vec<Vec<Sh>>)> = (0..3)
        .map(|i| {
            let v = darkstep::net::bytes_to_u64s(&std::fs::read(dir.join(format!("shares_{i}.bin"))).unwrap());
            let sh: Vec<Sh> = v.chunks(2).map(|c| Sh { s: c[0], m: c[1] }).collect();
            let rows: Vec<Vec<Sh>> = sh.chunks(d).map(|r| r.to_vec()).collect();
            (rows[..d].to_vec(), rows[d..].to_vec())
        })
        .collect();
    (res, reveal_check(&pf, &shares))
}

#[test]
fn production_party_coins_are_not_the_reference_streams() {
    check(&[], "native_ref_N4096_L3_F118_d64.json");
}

#[test]
fn production_party_coins_gated() {
    check(&["--gate", "309"], "native_ref_gated_N4096_L3_F118_d64_T309.json");
}

fn check(extra: &[&str], refname: &str) {
    let r = reference(refname);
    // the in-process harness (reference coins, full ciphertexts) for the wire comparison
    let mut pfh = prof(&["4096", "3", "118", "64"].map(String::from));
    pfh.gate = extra.get(1).map(|t| t.parse().unwrap());
    let (harness, _) = darkstep::node::run_local(&pfh, None);
    let he_ct_ref = harness["detail"][0]["bytes_sent"]["he_ct"].as_u64().unwrap();
    let a = ["4096", "3", "118", "64"].map(String::from);
    let pf = prof(&a);
    let base = std::env::temp_dir().join(format!("darkstep-party-coins-{}-{}", std::process::id(), extra.len()));
    let plain = inputs(pf.d);
    let (tapes, cs) = darkstep::tape::deal_step(pf.t, pf.d, DEALER_SEED, OWNER_SEED, &plain.flat_mod(pf.t));
    let mut runs = Vec::new();
    for run_k in 0..2 {
        let dir = base.join(format!("run{run_k}"));
        std::fs::create_dir_all(&dir).unwrap();
        for (i, tp) in tapes.iter().enumerate() {
            tp.write_to(&mut std::io::BufWriter::new(std::fs::File::create(dir.join(format!("tape_{i}.bin"))).unwrap())).unwrap();
        }
        std::fs::write(dir.join("public.bin"), darkstep::net::u64s_to_bytes(&cs)).unwrap();
        let (res, refines) = run(&dir, extra);
        for v in &res {
            assert_eq!(v["verdict"], "ACCEPT");
            assert_ne!(v["transcript"], r["transcript"], "broadcast shares carry fresh masks");
            assert_eq!(v["transcript"], res[0]["transcript"], "the three custodians agree on the transcript");
        }
        assert!(refines, "run {run_k}: the revealed weights refine step_spec");
        // seeded ciphertexts: c0 and a 32-byte seed instead of (c0, c1)
        let he_ct = res[0]["bytes_sent"]["he_ct"].as_u64().unwrap();
        let proof = res[0]["gate"]["proof_bytes_sent"].as_u64().unwrap_or(0);
        let ratio = (he_ct - proof) as f64 / (he_ct_ref - proof) as f64;
        assert!((0.49..0.51).contains(&ratio), "seeded ciphertexts halve HE_CT: {ratio}");
        let mut row: Vec<String> = res.iter().map(|v| v["digest"].as_str().unwrap().to_string()).collect();
        row.push(res[0]["transcript"].as_str().unwrap().to_string());
        runs.push(row);
    }
    for i in 0..3 {
        let refd = r["parties"][i.to_string()].as_str().unwrap();
        assert_ne!(runs[0][i], refd, "party {i}: share digest must not be the reference's (public coin stream)");
        assert_ne!(runs[1][i], refd, "party {i}: share digest must not be the reference's (public coin stream)");
        assert_ne!(runs[0][i], runs[1][i], "party {i}: two production runs must draw different coins");
    }
    assert_ne!(runs[0][3], runs[1][3], "two production runs: different transcripts");
    std::fs::remove_dir_all(&base).ok();
}
