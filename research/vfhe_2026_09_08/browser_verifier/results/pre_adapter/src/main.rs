use std::{fs, process::ExitCode};
use vfhe_browser_verifier::verify_core;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 5 {
        eprintln!("usage: vfhe-verify TEMPLATE.json PUBLIC_ROWS.json PROOF.bin EXPECTED_TEMPLATE_SHA256");
        return ExitCode::from(2);
    }
    let result = (|| -> Result<_, Box<dyn std::error::Error>> {
        Ok(verify_core(&fs::read_to_string(&args[1])?, &fs::read_to_string(&args[2])?, &fs::read(&args[3])?, &args[4]))
    })();
    match result {
        Ok(outcome) => {
            println!("{}", serde_json::to_string(&outcome).unwrap());
            if outcome.verified { ExitCode::SUCCESS } else { ExitCode::from(1) }
        }
        Err(error) => { eprintln!("{error}"); ExitCode::from(2) }
    }
}

