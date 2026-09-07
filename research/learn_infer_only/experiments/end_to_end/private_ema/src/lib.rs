//! Small honest-input Boolean EMA probe. The reader retains a read-all client key.
use std::{fs, path::Path};
use tfhe::boolean::prelude::*;

pub const STATE: u8 = 1;
pub const INPUT: u8 = 2;
pub const QUERY: u8 = 3;
pub const OUTPUT: u8 = 4;
const MAGIC: &[u8; 8] = b"PEMA0001";

#[derive(Default, Debug, PartialEq, Eq)]
pub struct Calls {
    pub and: usize,
    pub xor: usize,
    pub not: usize,
    pub mux: usize,
    pub trivial: usize,
}

impl Calls {
    pub fn json(&self) -> String {
        format!("{{\"and\":{},\"xor\":{},\"not\":{},\"mux\":{},\"trivial_encrypt\":{}}}",
            self.and, self.xor, self.not, self.mux, self.trivial)
    }
}

pub fn read_bits(path: &Path, kind: u8, count: usize) -> Vec<Ciphertext> {
    let bytes = fs::read(path).expect("read ciphertext envelope");
    assert!(bytes.len() >= 17);
    assert_eq!(&bytes[..8], MAGIC);
    assert_eq!(bytes[8], kind);
    let payload_len = u64::from_le_bytes(bytes[9..17].try_into().unwrap()) as usize;
    assert_eq!(bytes.len(), 17 + payload_len);
    let bits: Vec<Ciphertext> = bincode::deserialize(&bytes[17..]).expect("decode bit vector");
    assert_eq!(bits.len(), count);
    assert_eq!(bincode::serialize(&bits).unwrap(), bytes[17..]);
    assert!(bits.iter().all(|b| matches!(b, Ciphertext::Encrypted(_))),
            "artifact data bits must use real encryption");
    bits
}

pub fn write_bits(path: &Path, kind: u8, bits: &[Ciphertext]) -> usize {
    assert!(bits.iter().all(|b| matches!(b, Ciphertext::Encrypted(_))));
    let payload = bincode::serialize(bits).unwrap();
    let mut bytes = Vec::with_capacity(17 + payload.len());
    bytes.extend_from_slice(MAGIC);
    bytes.push(kind);
    bytes.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    bytes.extend(payload);
    fs::write(path, &bytes).expect("write ciphertext envelope");
    bytes.len()
}

pub fn encrypt_word(value: i8, pk: &PublicKey) -> Vec<Ciphertext> {
    let word = value as u8;
    (0..8).map(|i| pk.encrypt(((word >> i) & 1) != 0)).collect()
}

pub fn encrypt_address(value: u8, pk: &PublicKey) -> Vec<Ciphertext> {
    assert!(value < 4);
    (0..2).map(|i| pk.encrypt(((value >> i) & 1) != 0)).collect()
}

fn add(a: &[Ciphertext], b: &[Ciphertext], cin: bool,
       sk: &ServerKey, calls: &mut Calls) -> Vec<Ciphertext> {
    assert_eq!(a.len(), b.len());
    let mut carry = sk.trivial_encrypt(cin);
    calls.trivial += 1;
    let mut out = Vec::with_capacity(a.len());
    for (x, y) in a.iter().zip(b) {
        let p = sk.xor(x, y);
        out.push(sk.xor(&p, &carry));
        let xy = sk.and(x, y);
        let pc = sk.and(&p, &carry);
        carry = sk.xor(&xy, &pc);
        calls.and += 2;
        calls.xor += 3;
    }
    out
}

fn candidate(s: &[Ciphertext], u: &[Ciphertext], sk: &ServerKey,
             calls: &mut Calls) -> Vec<Ciphertext> {
    assert_eq!(s.len(), 8);
    assert_eq!(u.len(), 8);
    let mut s11 = s.to_vec();
    let mut u11 = u.to_vec();
    s11.extend((0..3).map(|_| s[7].clone()));
    u11.extend((0..3).map(|_| u[7].clone()));
    let mut eight_s: Vec<_> = (0..3).map(|_| sk.trivial_encrypt(false)).collect();
    calls.trivial += 3;
    eight_s.extend_from_slice(s);
    let not_s: Vec<_> = s11.iter().map(|b| sk.not(b)).collect();
    calls.not += 11;
    let seven_s = add(&eight_s, &not_s, true, sk, calls);
    let numerator = add(&seven_s, &u11, false, sk, calls);
    numerator[3..].to_vec()
}

pub fn learn(state: &[Ciphertext], input: &[Ciphertext], sk: &ServerKey,
             calls: &mut Calls) -> Vec<Ciphertext> {
    assert_eq!(state.len(), 32);
    assert_eq!(input.len(), 10);
    let not_b0 = sk.not(&input[0]);
    let not_b1 = sk.not(&input[1]);
    calls.not += 2;
    let mut output = Vec::with_capacity(32);
    for j in 0..4 {
        let b0 = if j & 1 != 0 { &input[0] } else { &not_b0 };
        let b1 = if j & 2 != 0 { &input[1] } else { &not_b1 };
        let select = sk.and(b0, b1);
        calls.and += 1;
        let old = &state[8*j..8*(j+1)];
        let updated = candidate(old, &input[2..], sk, calls);
        for (new_bit, old_bit) in updated.iter().zip(old) {
            output.push(sk.mux(&select, new_bit, old_bit));
            calls.mux += 1;
        }
    }
    output
}

pub fn infer(state: &[Ciphertext], query: &[Ciphertext], sk: &ServerKey,
             calls: &mut Calls) -> Vec<Ciphertext> {
    assert_eq!(state.len(), 32);
    assert_eq!(query.len(), 2);
    let low = sk.mux(&query[0], &state[15], &state[7]);
    let high = sk.mux(&query[0], &state[31], &state[23]);
    let answer = sk.mux(&query[1], &high, &low);
    calls.mux += 3;
    vec![answer]
}
