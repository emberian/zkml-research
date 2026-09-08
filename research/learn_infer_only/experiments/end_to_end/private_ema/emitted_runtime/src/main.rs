use resident_emitted_bool_runtime::{
    ciphertext::*, Operation, PlainBoolean, Schedule, MAX_SCHEDULE_BYTES,
};
use serde_json::json;
use std::{env, path::Path, process::ExitCode, time::Instant};

fn execute(args: &[String]) -> Result<(), String> {
    let usage = "emitted-bool-runtime validate SCHEDULE | clear SCHEDULE INPUT_BOOL_ROWS_JSON | host SCHEDULE SERVER_KEY PARENT INPUT_OR_QUERY NEW_OUTPUT";
    let command = args.get(1).ok_or(usage)?;
    let expected = match command.as_str() {
        "validate" => 3,
        "clear" => 4,
        "host" => 7,
        _ => return Err(usage.into()),
    };
    if args.len() != expected {
        return Err(usage.into());
    }
    let start = Instant::now();
    // Complete descriptor validation precedes any key or ciphertext read.
    let schedule = Schedule::parse(&read_limited(Path::new(&args[2]), MAX_SCHEDULE_BYTES)?)?;
    let validation_ns = start.elapsed().as_nanos();
    match command.as_str() {
        "validate" => println!("{}", json!({"valid":true,"schedule":schedule.summary()})),
        "clear" => {
            let rows: Vec<Vec<bool>> =
                serde_json::from_slice(&read_limited(Path::new(&args[3]), 64 * 1024 * 1024)?)
                    .map_err(|e| format!("invalid public Boolean fixture JSON: {e}"))?;
            let outputs = rows
                .into_iter()
                .map(|row| schedule.evaluate(row, &mut PlainBoolean))
                .collect::<Result<Vec<_>, _>>()?;
            println!(
                "{}",
                json!({"mode":"public-plain-boolean","outputs":outputs})
            );
        }
        "host" => {
            let read_start = Instant::now();
            let key = read_server_key(Path::new(&args[3]))?;
            let mut inputs = read_bits(Path::new(&args[4]), STATE, 32)?;
            let (input_kind, input_count, output_kind) = match schedule.operation() {
                Operation::Learn => (INPUT, 10, STATE),
                Operation::Infer => (QUERY, 2, OUTPUT),
            };
            inputs.extend(read_bits(Path::new(&args[5]), input_kind, input_count)?);
            let read_ns = read_start.elapsed().as_nanos();
            let mut backend = TfheBoolean {
                key: &key,
                calls: Calls::default(),
            };
            let eval_start = Instant::now();
            let outputs = schedule.evaluate(inputs, &mut backend)?;
            require_encrypted(&outputs)?;
            let evaluate_ns = eval_start.elapsed().as_nanos();
            let write_start = Instant::now();
            let bytes = write_bits_new(Path::new(&args[6]), output_kind, &outputs)?;
            let serialize_write_ns = write_start.elapsed().as_nanos();
            println!(
                "{}",
                json!({"role":"generic-schedule-host", "operation":schedule.operation(),
                "schedule":schedule.summary(), "schedule_validation_ns":validation_ns,
                "read_ns":read_ns, "evaluate_ns":evaluate_ns, "serialize_write_ns":serialize_write_ns,
                "work_ns":start.elapsed().as_nanos(), "output_bits":outputs.len(), "serialized_bytes":bytes,
                "gate_api_calls":backend.calls, "bootstrap_count_instrumented":false,
                "client_key_read":false, "all_output_bits_encrypted":true})
            );
        }
        _ => unreachable!(),
    }
    Ok(())
}

fn main() -> ExitCode {
    match execute(&env::args().collect::<Vec<_>>()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{}", json!({"error":error}));
            ExitCode::FAILURE
        }
    }
}
