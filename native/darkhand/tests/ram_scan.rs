//! The disk scan follows a symlink into a RAM filesystem (prep's MP-SPDZ Player-Data in /dev/shm) and counts what it
//! finds there apart from persistent storage; a persistent file in the same scan is counted as before. Linux only.
#[cfg(target_os = "linux")]
#[test]
fn ram_symlinks_are_scanned_and_counted_apart() {
    use darkhand::scan::Canaries;
    let shm = std::path::PathBuf::from(format!("/dev/shm/dlh-ram-test-{}", std::process::id()));
    let disk = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("dlh-ram-test-{}", std::process::id())); // persistent (bb2's /tmp is a tmpfs)
    std::fs::create_dir_all(&shm).unwrap();
    std::fs::create_dir_all(&disk).unwrap();
    let mut can = Canaries::bounded(1 << 61);
    let secret: Vec<u64> = (0..64).map(|k| 0x1234_5678_9abc + 977 * k).collect();
    can.add_words("secret", &secret, 64);
    let bytes: Vec<u8> = secret.iter().flat_map(|w| w.to_le_bytes()).collect();
    std::fs::write(shm.join("Player-MAC-Keys"), &bytes).unwrap();
    std::fs::write(disk.join("ckpt.bin"), &bytes).unwrap();
    std::os::unix::fs::symlink(&shm, disk.join("Player-Data")).unwrap();
    let r = can.scan_paths(&[disk.clone()]);
    println!("persistent {} files {} hits; RAM {} files {} hits, mounts {:?}, swap {:?} kB", r.files, r.hits, r.ram_files, r.ram_hits, r.ram_mounts, r.swap_total_kb);
    assert_eq!((r.files, r.ram_files), (1, 1));
    assert_eq!(r.hits, 64, "the persistent copy is found");
    assert_eq!(r.ram_hits, 64, "the RAM copy is found through the symlink and counted apart");
    assert!(r.ram_mounts.iter().any(|(_, f, _)| f == "tmpfs"));
    // erase both: nothing left either way
    std::fs::remove_file(shm.join("Player-MAC-Keys")).unwrap();
    std::fs::remove_file(disk.join("ckpt.bin")).unwrap();
    let r = can.scan_paths(&[disk.clone()]);
    assert_eq!((r.hits, r.ram_hits), (0, 0));
    std::fs::remove_dir_all(&shm).unwrap();
    std::fs::remove_dir_all(&disk).unwrap();
}
