use std::{fs, process::ExitCode, time::Instant};
use ring_browser_verifier::{MAX_BUNDLE_BYTES, verify_core};

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: ring-verify STATEMENT.bin PROOF.bin");
        return ExitCode::from(2);
    }
    let run = (|| -> Result<_, Box<dyn std::error::Error>> {
        let load_started = Instant::now();
        for path in &args[1..] {
            if fs::metadata(path)?.len() > MAX_BUNDLE_BYTES as u64 { return Err("bundle size cap".into()); }
        }
        let statement = fs::read(&args[1])?;
        let proof = fs::read(&args[2])?;
        let load_ms = load_started.elapsed().as_secs_f64() * 1000.0;
        let verify_started = Instant::now();
        let result = verify_core(&statement, &proof);
        let verify_ms = verify_started.elapsed().as_secs_f64() * 1000.0;
        Ok((result, load_ms, verify_ms))
    })();
    match run {
        Ok((result, load_ms, verify_ms)) => {
            println!("{}", serde_json::json!({"result":result,"loadMs":load_ms,"verifyMs":verify_ms}));
            if result.verified { ExitCode::SUCCESS } else { ExitCode::from(1) }
        }
        Err(error) => { eprintln!("{error}"); ExitCode::from(2) }
    }
}

