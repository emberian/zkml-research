//! darkhand::vault: sealed files open only under their own key, name and role; any changed byte is refused. On
//! Linux the file key survives the process in the persistent keyring (another process loads it, as `serve --resume`
//! would) and is gone, for every process, once destroyed.
use darkhand::vault::{key_name, present, Vault};

#[test]
fn seal_open_and_refusals() {
    let v = Vault::create("dl-vault:test:0:1:aaaa", false).unwrap();
    let plain = b"checkpoint bytes, 0123456789".to_vec();
    let blob = v.seal("ckpt", plain.clone());
    assert_eq!(v.open("ckpt", blob.clone()).unwrap(), plain);
    assert!(v.open("carry", blob.clone()).is_err(), "another role");
    let mut flip = blob.clone();
    flip[30] ^= 1;
    assert!(v.open("ckpt", flip).is_err(), "a flipped byte");
    let other = Vault::with_key("dl-vault:test:0:1:aaaa", [7u8; 32]);
    assert!(other.open("ckpt", blob.clone()).is_err(), "another key");
    let renamed = Vault::with_key("dl-vault:test:1:1:aaaa", *v.key_bytes());
    assert!(renamed.open("ckpt", blob.clone()).is_err(), "the same key under another seat's name");
    assert!(Vault::with_key("x", [0u8; 32]).open("ckpt", blob).is_err(), "the zero key");
    // the file form
    let dir = std::env::temp_dir().join(format!("dlv-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let f = dir.join("ckpt_P0.bin");
    v.seal_to(&f, "ckpt", plain.clone()).unwrap();
    assert!(!std::fs::read(&f).unwrap().windows(10).any(|w| w == &plain[..10]), "no plaintext on disk");
    assert_eq!(v.open_file(&f, "ckpt").unwrap(), plain);
    std::fs::remove_dir_all(&dir).unwrap();
    assert_eq!(key_name("m", 2, 5, "0123456789abcdef0123"), "dl-vault:m:2:5:0123456789abcdef");
}

#[cfg(target_os = "linux")]
#[test]
fn keyring_survives_the_process_and_destroy_erases_it() {
    if let Ok(name) = std::env::var("DLV_CHILD") {
        // the child: a later process of the same uid
        let v = Vault::load(&name).expect("the file key is in the persistent keyring");
        let blob = std::fs::read(std::env::var("DLV_FILE").unwrap()).unwrap();
        assert_eq!(v.open("tls", blob).unwrap(), b"secret");
        return;
    }
    let mut fp = [0u8; 8];
    getrandom::getrandom(&mut fp).unwrap();
    let name = key_name("test", 0, 1, &pycompat::repr::hex(&fp));
    let v = Vault::create(&name, true).unwrap();
    assert!(Vault::create(&name, true).is_err(), "one key per name");
    let f = std::env::temp_dir().join(format!("dlv-k-{}", std::process::id()));
    v.seal_to(&f, "tls", b"secret".to_vec()).unwrap();
    let child = |want: bool| {
        let ok = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "keyring_survives_the_process_and_destroy_erases_it", "--test-threads", "1"])
            .env("DLV_CHILD", &name)
            .env("DLV_FILE", &f)
            .status()
            .unwrap()
            .success();
        assert_eq!(ok, want);
    };
    child(true);
    let rep = v.destroy();
    assert_eq!(rep["in_keyring"], true);
    assert!(rep["invalidate_error"].is_null());
    assert_eq!(rep["key_in_keyring_after"], false);
    assert!(!present(&name));
    assert!(Vault::load(&name).is_err());
    child(false);
    std::fs::remove_file(&f).unwrap();
}
