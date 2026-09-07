use std::{env, fs, os::unix::fs::PermissionsExt, path::Path, time::Instant};
use tfhe::boolean::{prelude::*, parameters::PARAMETERS_ERROR_PROB_2_POW_MINUS_165};

fn main() {
    let args: Vec<_> = env::args().collect();
    assert_eq!(args.len(), 3, "setup PUBLIC_KEY_DIR PRIVATE_READER_DIR");
    let start = Instant::now();
    let public = Path::new(&args[1]);
    let private = Path::new(&args[2]);
    fs::create_dir_all(public).unwrap();
    fs::create_dir_all(private).unwrap();
    fs::set_permissions(private, fs::Permissions::from_mode(0o700)).unwrap();
    let key_start = Instant::now();
    let params = PARAMETERS_ERROR_PROB_2_POW_MINUS_165;
    let ck = ClientKey::new(&params);
    let pk = PublicKey::new(&ck);
    let sk = ServerKey::new(&ck);
    let key_ns = key_start.elapsed().as_nanos();
    let write_start = Instant::now();
    let ck_bytes = bincode::serialize(&ck).unwrap();
    let pk_bytes = bincode::serialize(&pk).unwrap();
    let sk_bytes = bincode::serialize(&sk).unwrap();
    let client_path = private.join("client_key.bin");
    fs::write(&client_path, &ck_bytes).unwrap();
    fs::set_permissions(client_path, fs::Permissions::from_mode(0o600)).unwrap();
    fs::write(public.join("public_key.bin"), &pk_bytes).unwrap();
    fs::write(public.join("server_key.bin"), &sk_bytes).unwrap();
    let write_ns = write_start.elapsed().as_nanos();
    println!("{{\"role\":\"setup\",\"keygen_ns\":{key_ns},\"serialize_write_ns\":{write_ns},\"work_ns\":{},\"public_key_bytes\":{},\"server_key_bytes\":{},\"client_key_bytes\":{},\"read_all_client_key_retained\":true,\"parameter_name\":\"PARAMETERS_ERROR_PROB_2_POW_MINUS_165\",\"parameter_debug\":\"{params:?}\"}}",
        start.elapsed().as_nanos(), pk_bytes.len(), sk_bytes.len(), ck_bytes.len());
}
