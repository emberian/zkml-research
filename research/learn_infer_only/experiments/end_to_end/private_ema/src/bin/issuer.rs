use std::{env, fs, path::Path, time::Instant};
use tfhe::boolean::prelude::*;
use resident_private_ema::{encrypt_address, encrypt_word, write_bits, STATE, INPUT, QUERY};

fn main() {
    let args: Vec<_> = env::args().collect();
    assert_eq!(args.len(), 5, "issuer init|learn|query PUBLIC_KEY PRIVATE_REQUEST OUTPUT");
    let start = Instant::now();
    let read_start = Instant::now();
    let pk: PublicKey = bincode::deserialize(&fs::read(&args[2]).unwrap()).unwrap();
    let request = fs::read_to_string(&args[3]).unwrap();
    let values: Vec<i16> = request.split_whitespace().map(|s| s.parse().unwrap()).collect();
    let read_ns = read_start.elapsed().as_nanos();
    let enc_start = Instant::now();
    let (kind, bits) = match args[1].as_str() {
        "init" => {
            assert!(values.is_empty());
            (STATE, (0..4).flat_map(|_| encrypt_word(0, &pk)).collect::<Vec<_>>())
        },
        "learn" => {
            assert_eq!(values.len(), 2);
            assert!((0..4).contains(&values[0]));
            assert!(values[1] == -120 || values[1] == 120);
            let mut bits = encrypt_address(values[0] as u8, &pk);
            bits.extend(encrypt_word(values[1] as i8, &pk));
            (INPUT, bits)
        },
        "query" => {
            assert_eq!(values.len(), 1);
            assert!((0..4).contains(&values[0]));
            (QUERY, encrypt_address(values[0] as u8, &pk))
        },
        _ => panic!("unknown issuer operation"),
    };
    let enc_ns = enc_start.elapsed().as_nanos();
    let write_start = Instant::now();
    let bytes = write_bits(Path::new(&args[4]), kind, &bits);
    let write_ns = write_start.elapsed().as_nanos();
    println!("{{\"role\":\"issuer\",\"operation\":\"{}\",\"read_ns\":{read_ns},\"encrypt_ns\":{enc_ns},\"serialize_write_ns\":{write_ns},\"work_ns\":{},\"ciphertext_bits\":{},\"serialized_bytes\":{bytes}}}",
        args[1], start.elapsed().as_nanos(), bits.len());
}
