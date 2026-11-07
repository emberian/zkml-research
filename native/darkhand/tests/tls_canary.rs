//! The TLS key's canary forms are the ones the process actually holds: ring's parsed key pair (what rustls signs
//! with) contains the scalar's Montgomery limbs, and the DER holds its big-endian bytes. Negative control: another
//! key's forms are not found.
use darkhand::side::{p256_scalar, p256_scalar_words};

fn words_of<T>(x: &T) -> Vec<u64> {
    let n = std::mem::size_of::<T>() / 8;
    let p = x as *const T as *const u64;
    (0..n).map(|i| unsafe { p.add(i).read_unaligned() }).collect()
}

fn keypair(der: &[u8]) -> ring::signature::EcdsaKeyPair {
    let rng = ring::rand::SystemRandom::new();
    ring::signature::EcdsaKeyPair::from_pkcs8(&ring::signature::ECDSA_P256_SHA256_ASN1_SIGNING, der, &rng).unwrap()
}

fn contains(hay: &[u64], needle: &[u64]) -> bool {
    hay.windows(needle.len()).any(|w| w == needle)
}

#[test]
fn ring_holds_the_montgomery_limbs_and_the_der_the_bytes() {
    let id = darkstep::tls::generate(0);
    let other = darkstep::tls::generate(1);
    let d = p256_scalar(&id.key_der).expect("a P-256 scalar in the PKCS#8 DER");
    let d2 = p256_scalar(&other.key_der).unwrap();
    assert_ne!(d, d2);
    let kp = keypair(&id.key_der);
    let kw = words_of(&kp);
    let [be, limbs, mont] = p256_scalar_words(&d);
    let [_, _, mont2] = p256_scalar_words(&d2);
    assert!(contains(&kw, &mont.1), "ring's EcdsaKeyPair holds d 2^256 mod n as limbs");
    assert!(!contains(&kw, &mont2.1), "negative control: another key's limbs are not in it");
    assert!(!contains(&kw, &limbs.1), "ring does not keep the plain limbs (the Montgomery form is the one)");
    // the DER's scalar bytes, read as LE words at their own offset
    let at = id.key_der.windows(32).position(|w| w == d).unwrap();
    let dw: Vec<u64> = id.key_der[at..at + 32].chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
    assert_eq!(dw, be.1);
    assert_eq!(be.0, "TLS private scalar (big-endian bytes)");
}

#[test]
fn not_a_p256_key() {
    assert!(p256_scalar(b"not a key at all, 02 01 01 04 20").is_none());
    let id = darkstep::tls::generate(2);
    assert!(p256_scalar(&id.cert_der).is_none(), "the certificate carries no private scalar");
}

#[test]
fn the_der_canary_words_are_private_only() {
    // the words of the DER that the canary keeps (those overlapping the scalar) occur nowhere in the certificate,
    // while some other DER words (the public key) can: the reason they are left out
    for i in 0..32 {
        let id = darkstep::tls::generate(i);
        let d = p256_scalar(&id.key_der).unwrap();
        let a = id.key_der.windows(32).position(|w| w == d).unwrap();
        let cert = &id.cert_der;
        for (k, c) in id.key_der.chunks_exact(8).enumerate() {
            if 8 * k + 8 > a && 8 * k < a + 32 {
                assert!(!cert.windows(8).any(|w| w == c), "a scalar word of the DER is in the certificate");
            }
        }
        let pubk = &id.key_der[id.key_der.len() - 65..];
        assert!(cert.windows(65).any(|w| w == pubk), "the DER's public key is the certificate's");
    }
}

#[test]
fn der_words_aligned_in_the_certificate() {
    // how many of the DER's aligned words a certificate buffer holds at aligned offsets (what a heap scan sees)
    for i in 0..3 {
        let id = darkstep::tls::generate(i);
        let cw: Vec<&[u8]> = id.cert_der.chunks_exact(8).collect();
        let n = id.key_der.chunks_exact(8).filter(|w| cw.contains(w)).count();
        println!("custodian {i}: {n} of {} DER words at aligned offsets of the certificate", id.key_der.len() / 8);
        // reh (2026-11-07): exactly these 8 words were the after-erasure hits on every seat: the public certificate
        assert_eq!(n, 8);
    }
}
