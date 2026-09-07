use std::{env, fs, os::unix::fs::PermissionsExt, path::Path, time::Instant};
use tfhe::boolean::prelude::*;
use resident_private_ema::{read_bits, STATE, OUTPUT};

fn main() {
    let args: Vec<_> = env::args().collect();
    assert_eq!(args.len(), 5, "reader state|output CLIENT_KEY CIPHERTEXT PRIVATE_AUDIT_FILE");
    let start = Instant::now();
    let ck: ClientKey = bincode::deserialize(&fs::read(&args[2]).unwrap()).unwrap();
    let (kind, count) = match args[1].as_str() { "state" => (STATE, 32), "output" => (OUTPUT, 1), _ => panic!("unknown reader operation") };
    let bits = read_bits(Path::new(&args[3]), kind, count);
    let decrypt_start = Instant::now();
    let opened: Vec<bool> = bits.iter().map(|bit| ck.decrypt(bit)).collect();
    let decrypt_ns = decrypt_start.elapsed().as_nanos();
    let text = if kind == STATE {
        let values: Vec<String> = opened.chunks(8).map(|chunk| {
            let word = chunk.iter().enumerate().fold(0u8, |word, (i, bit)| word | (u8::from(*bit) << i));
            (word as i8).to_string()
        }).collect();
        format!("{{\"state\":[{}]}}\n", values.join(","))
    } else { format!("{{\"negative\":{}}}\n", opened[0]) };
    fs::write(&args[4], text).unwrap();
    fs::set_permissions(&args[4], fs::Permissions::from_mode(0o600)).unwrap();
    println!("{{\"role\":\"reader\",\"operation\":\"{}\",\"decrypt_ns\":{decrypt_ns},\"work_ns\":{},\"decrypted_bits\":{count},\"plaintext_report_private\":true,\"read_all_client_key_retained\":true}}",
        args[1], start.elapsed().as_nanos());
}
