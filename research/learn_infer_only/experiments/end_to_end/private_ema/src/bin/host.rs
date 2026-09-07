use std::{env, fs, path::Path, time::Instant};
use tfhe::boolean::prelude::*;
use resident_private_ema::{read_bits, write_bits, learn, infer, Calls, STATE, INPUT, QUERY, OUTPUT};

fn main() {
    let args: Vec<_> = env::args().collect();
    assert_eq!(args.len(), 6, "host learn|infer SERVER_KEY PARENT INPUT_OR_QUERY OUTPUT");
    let start = Instant::now();
    let read_start = Instant::now();
    let sk: ServerKey = bincode::deserialize(&fs::read(&args[2]).unwrap()).unwrap();
    let parent = read_bits(Path::new(&args[3]), STATE, 32);
    let is_learn = match args[1].as_str() { "learn" => true, "infer" => false, _ => panic!("unknown host operation") };
    let input = read_bits(Path::new(&args[4]), if is_learn { INPUT } else { QUERY }, if is_learn { 10 } else { 2 });
    let read_ns = read_start.elapsed().as_nanos();
    let eval_start = Instant::now();
    let mut calls = Calls::default();
    let output = if is_learn { learn(&parent, &input, &sk, &mut calls) }
        else { infer(&parent, &input, &sk, &mut calls) };
    let eval_ns = eval_start.elapsed().as_nanos();
    let expected = if is_learn { Calls { and: 180, xor: 264, not: 46, mux: 32, trivial: 20 } }
        else { Calls { mux: 3, ..Calls::default() } };
    assert_eq!(calls, expected);
    let write_start = Instant::now();
    let bytes = write_bits(Path::new(&args[5]), if is_learn { STATE } else { OUTPUT }, &output);
    let write_ns = write_start.elapsed().as_nanos();
    println!("{{\"role\":\"host\",\"operation\":\"{}\",\"read_ns\":{read_ns},\"evaluate_ns\":{eval_ns},\"serialize_write_ns\":{write_ns},\"work_ns\":{},\"output_bits\":{},\"serialized_bytes\":{bytes},\"gate_api_calls\":{},\"bootstrap_count_instrumented\":false,\"client_key_read\":false}}",
        args[1], start.elapsed().as_nanos(), output.len(), calls.json());
}
