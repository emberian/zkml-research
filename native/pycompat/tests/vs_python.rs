use pycompat::{PyRandom, ReprHasher};
use std::process::Command;

fn py(code: &str) -> String {
    let out = Command::new("python3").arg("-c").arg(code).output().expect("python3");
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

#[test]
fn int_seed_randrange_matches() {
    let p: u64 = 2305843009213554689; // a 61-bit value; any n works
    let want = py(&format!("import random\nr=random.Random(5)\nprint(' '.join(str(r.randrange({p})) for _ in range(2000)))"));
    let mut r = PyRandom::from_u64(5);
    let got: Vec<String> = (0..2000).map(|_| r.randrange_u64(p).to_string()).collect();
    assert_eq!(got.join(" "), want);
}

#[test]
fn big_seed_and_wide_draws_match() {
    let want = py("import random,hashlib\nh=hashlib.sha256(b'x').hexdigest()\nr=random.Random(int(h,16))\nQ=(1<<244)-12345\nF=1<<175\nprint(' '.join([str(r.randrange(Q)) for _ in range(50)]+[str(r.randint(-F,F)) for _ in range(50)]+[str(r.choice((-1,0,1))) for _ in range(50)]+[str(r.randint(-8,8)) for _ in range(50)]))");
    let h = pycompat::repr::sha256_hex(b"x");
    let mut r = PyRandom::from_hex_int(&h);
    let q = num_bigint::BigUint::from(1u32) << 244usize;
    let q = q - num_bigint::BigUint::from(12345u32);
    let mut got: Vec<String> = (0..50).map(|_| r.randbelow_big(&q).to_string()).collect();
    for _ in 0..50 {
        let (neg, mag) = r.randint_sym_pow2(175);
        let v = num_bigint::BigUint::from_slice(&pycompat::random::to_u32s(&mag));
        got.push(if neg && v != num_bigint::BigUint::from(0u32) { format!("-{v}") } else { v.to_string() });
    }
    for _ in 0..50 {
        got.push(r.ternary().to_string());
    }
    for _ in 0..50 {
        got.push(r.randint_i64(-8, 8).to_string());
    }
    assert_eq!(got.join(" "), want);
}

#[test]
fn str_seed_matches() {
    let want = py("import random\nr=random.Random('hm|11|1|False|0|1|3')\nprint(' '.join(str(r.getrandbits(k)) for k in (1,7,32,33,61,64,100)))");
    let mut r = PyRandom::from_str_seed("hm|11|1|False|0|1|3");
    let mut got: Vec<String> = Vec::new();
    for k in [1u32, 7, 32, 33, 61, 64] {
        got.push(r.getrandbits_u64(k).to_string());
    }
    let l = r.getrandbits_limbs(100);
    got.push(num_bigint::BigUint::from_slice(&pycompat::random::to_u32s(&l)).to_string());
    assert_eq!(got.join(" "), want);
}

#[test]
fn repr_hash_matches() {
    let want = py("import hashlib\nt=[('input', {}, 5), ('mul', {0: 1, 1: 2, 2: 3}, 6), ('he_outer_commit', {0: 'ab', 1: 'cd', 2: 'ef'}, 0)]\nprint(hashlib.sha256(repr(('freivalds', ('model', 0, 0), 1, 64, False, t)).encode()).hexdigest())");
    let mut h = ReprHasher::new();
    h.raw(b"('freivalds', ('model', 0, 0), 1, 64, False, [('input', {}, 5), ('mul', {0: 1, 1: 2, 2: 3}, 6), ('he_outer_commit', {0: 'ab', 1: 'cd', 2: 'ef'}, 0)])");
    assert_eq!(h.finish_hex(), want);
}

#[test]
fn repr_hash_any_buffer_capacity() {
    // a list of 3000 61-bit ints (over 64 KiB of repr), fed int by int, as a streamed Merkle leaf is
    let want = py("import hashlib,random\nr=random.Random(9)\nv=[r.randrange(2**61) for _ in range(3000)]\nprint(hashlib.sha256(repr(('leaf', v)).encode()).hexdigest())");
    let mut r = PyRandom::from_u64(9);
    let v: Vec<u64> = (0..3000).map(|_| r.randrange_u64(1 << 61)).collect();
    for cap in [None, Some(0), Some(1), Some(7), Some(256)] {
        let mut h = cap.map_or_else(ReprHasher::new, ReprHasher::with_capacity);
        h.raw(b"('leaf', [");
        for (k, &x) in v.iter().enumerate() {
            if k > 0 {
                h.raw(b", ");
            }
            h.u64(x);
        }
        h.raw(b"])");
        assert_eq!(h.finish_hex(), want, "capacity {cap:?}");
    }
}

#[test]
fn from_state_continues_the_stream() {
    let want = py("import random\nr=random.Random(5)\nfor _ in range(1000): r.randrange(2**61)\nst=r.getstate()[1]\nprint(' '.join(map(str,st)))\nprint(' '.join(str(r.randrange(2305843009212399617)) for _ in range(1500)))");
    let mut lines = want.lines();
    let st: Vec<u64> = lines.next().unwrap().split(' ').map(|x| x.parse().unwrap()).collect();
    let mut r = PyRandom::from_state(&st);
    assert_eq!(r.state(), st);
    let got: Vec<String> = (0..1500).map(|_| r.randrange_u64(2305843009212399617).to_string()).collect();
    assert_eq!(got.join(" "), lines.next().unwrap());
    let mut a = PyRandom::from_u64(5);
    for _ in 0..1000 {
        a.randrange_u64(1 << 61);
    }
    assert_eq!(a.state(), st, "state() after the same draws");
}

#[test]
fn fixed_width_draws_equal_vec_draws() {
    // the allocation-free variants must consume the same stream and return the same values
    let mut a = PyRandom::from_str_seed("fixed");
    let mut b = PyRandom::from_str_seed("fixed");
    let q: [u64; 5] = [12345, 0, 0, u64::MAX >> 12, 0];
    for _ in 0..500 {
        let (n1, m1) = a.randint_sym_pow2(175);
        let (n2, m2) = b.randint_sym_pow2_arr::<4>(175);
        assert_eq!((n1, &m1[..]), (n2, &m2[..m1.len()]));
        let u1 = a.randbelow_limbs(&q[..4]);
        let u2 = b.randbelow_arr::<5>(&q);
        assert_eq!(&u1[..], &u2[..u1.len()]);
    }
    assert_ne!(a.genrand_u32(), PyRandom::from_str_seed("fixed").genrand_u32());
}
