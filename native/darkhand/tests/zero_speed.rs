//! zero_raw: the bytes are zero afterwards, and it runs at memset speed (compared with a plain write_bytes).
//!   cargo test --release -p darkhand --test zero_speed -- --nocapture
#[test]
fn zero_raw_zeroes_at_memset_speed() {
    let n = 256 << 20;
    let mut v = vec![0xA5u8; n];
    let t = std::time::Instant::now();
    for _ in 0..8 {
        unsafe { darkhand::erase::zero_raw(v.as_mut_ptr(), n) };
        v[n / 3] = 1;
    }
    let ours = t.elapsed().as_secs_f64() / 8.0;
    unsafe { darkhand::erase::zero_raw(v.as_mut_ptr().add(1), n - 3) };
    assert!(v[1..n - 2].iter().all(|&b| b == 0), "zero_raw left nonzero bytes");
    let mut w = vec![0xA5u8; n];
    let t = std::time::Instant::now();
    for _ in 0..8 {
        unsafe { std::ptr::write_bytes(w.as_mut_ptr(), 0, n) };
        w[n / 3] = 1;
        std::hint::black_box(&mut w);
    }
    let memset = t.elapsed().as_secs_f64() / 8.0;
    println!("256 MiB: zero_raw {:.1} ms ({:.1} GB/s), write_bytes {:.1} ms", ours * 1e3, n as f64 / ours / 1e9, memset * 1e3);
    assert!(ours < 2.0 * memset + 0.005, "zero_raw is much slower than memset");
}
