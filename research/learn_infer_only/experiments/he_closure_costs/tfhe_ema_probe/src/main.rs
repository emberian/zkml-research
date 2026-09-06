//! Real Boolean FHE arithmetic only. Test reader retains a read-all key.
use tfhe::boolean::prelude::*;
use tfhe::boolean::parameters::PARAMETERS_ERROR_PROB_2_POW_MINUS_165;

#[derive(Default, Debug)]
struct Calls { and: usize, xor: usize, not: usize }

fn add(a: &[Ciphertext], b: &[Ciphertext], cin: bool,
       sk: &ServerKey, n: &mut Calls) -> Vec<Ciphertext> {
    assert_eq!(a.len(), b.len());
    let mut carry = sk.trivial_encrypt(cin);
    let mut out = Vec::with_capacity(a.len());
    for (x, y) in a.iter().zip(b) {
        let p = sk.xor(x, y);
        out.push(sk.xor(&p, &carry));
        let xy = sk.and(x, y);
        let pc = sk.and(&p, &carry);
        carry = sk.xor(&xy, &pc);
        n.and += 2;
        n.xor += 3;
    }
    out
}

fn encrypt(x: i16, pk: &PublicKey) -> Vec<Ciphertext> {
    (0..8).map(|i| pk.encrypt(((x >> i) & 1) != 0)).collect()
}

fn read(x: &[Ciphertext], ck: &ClientKey) -> i16 {
    let word: u8 = x.iter().enumerate()
        .map(|(i, c)| u8::from(ck.decrypt(c)) << i).fold(0, |a,b|a|b);
    word as i8 as i16
}

fn learn(c: &[Ciphertext], u: &[Ciphertext], sk: &ServerKey,
         n: &mut Calls) -> Vec<Ciphertext> {
    assert_eq!(c.len(),8); assert_eq!(u.len(),8);
    let mut c11 = c.to_vec();
    let mut u11 = u.to_vec();
    c11.extend((0..3).map(|_| c[7].clone()));
    u11.extend((0..3).map(|_| u[7].clone()));
    let mut eight_c: Vec<_> = (0..3).map(|_|sk.trivial_encrypt(false)).collect();
    eight_c.extend_from_slice(c);
    let not_c: Vec<_> = c11.iter().map(|b|sk.not(b)).collect();
    n.not +=11;
    let seven_c = add(&eight_c, &not_c, true, sk, n);
    let numerator = add(&seven_c, &u11, false, sk, n);
    numerator[3..].to_vec()
}

fn main() {
    println!("STATUS real_TFHE_Boolean_EMA no_no_master_read_claim no_latency_benchmark");
    let params=PARAMETERS_ERROR_PROB_2_POW_MINUS_165;
    println!("PARAMETERS source_name=PARAMETERS_ERROR_PROB_2_POW_MINUS_165 source_claim_not_reestimated=true {params:?}");
    let ck=ClientKey::new(&params);
    let sk=ServerKey::new(&ck);
    let pk=PublicKey::new(&ck);
    println!("KEY_SERIALIZED_BYTES public_key={} server_key={} read_all_client_key_retained=true",
             bincode::serialized_size(&pk).unwrap(), bincode::serialized_size(&sk).unwrap());
    let mut calls=Calls::default();
    for (history,want) in [([120i16,-120i16],-2i16), ([-120i16,120i16],1i16)] {
        let mut c=encrypt(0,&pk);
        for value in history {
            let input=encrypt(value,&pk);
            c=learn(&c,&input,&sk,&mut calls);
            // No intermediate client read or reencryption of resident state.
        }
        let got=read(&c,&ck);
        assert_eq!(got,want);
        println!("ENCRYPTED_ORDER_WITNESS history={history:?} expected={want} observed={got} state_bits={} serialized_state_bytes={}",
                 c.len(), bincode::serialized_size(&c).unwrap());
    }
    assert_eq!((calls.and,calls.xor,calls.not),(176,264,44));
    println!("GATE_API_CALLS {calls:?} bootstrap_count_not_instrumented=true");
    println!("PASS public-key ingress, four encrypted stateful EMA updates, order-sensitive final outputs; test reader retains master key");
}
