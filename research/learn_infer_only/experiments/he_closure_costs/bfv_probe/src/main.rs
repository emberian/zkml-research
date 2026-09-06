//! Real BFV arithmetic controls on synthetic public test messages and RNG seeds.
//! No latency benchmark; no protected learner, release security, or PQ claim.
use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{DeserializeParametrized, FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let params = BfvParameters::default_parameters_128(20)?.nth(2).unwrap();
    println!("STATUS real_BFV_arithmetic_only no_PQ_bits_claim no_private_release no_latency");
    println!("MODULI {:?}", params.moduli());
    let modulus = params.plaintext();
    assert_eq!(modulus, 1032193u64);
    println!("PARAMETERS N={} t={modulus} noise_sampler=CBD20_variance10 coefficient_encoding=true", params.degree());
    for seed in [7u8, 19u8, 43u8, 101u8] {
        let mut rng = ChaCha20Rng::from_seed([seed; 32]);
        let sk = SecretKey::random(&params, &mut rng);
        let pk = PublicKey::new(&sk, &mut rng);
        let one = Plaintext::try_encode(&[1u64], Encoding::poly(), &params)?;
        let ct: Ciphertext = pk.try_encrypt(&one, &mut rng)?;
        let decode = |c: &Ciphertext| -> Result<u64, Box<dyn Error>> {
            Ok(Vec::<u64>::try_decode(&sk.try_decrypt(c)?, Encoding::poly())?[0])
        };
        assert_eq!(decode(&ct)?, 1);

        // Entry (0,0) of a 2x2 rank-one matrix; other entries identically zero.
        // Update W <- W + W stays rank one, uses no ct-ct multiplication,
        // and has no cryptographic operation capable of refreshing old noise.
        let mut current = ct.clone();
        let mut expected = 1u64;
        let mut failure = None;
        for step in 1..=128 {
            let previous = current.clone();
            current += &previous;
            expected = (2 * expected) % modulus;
            let observed = decode(&current)?;
            if observed != expected {
                println!("RANK_ONE_FIRST_SELECTED_COEFFICIENT_FAILURE seed={seed} additions={step} expected={expected} observed={observed}");
                failure = Some(step);
                break;
            }
            // Safe only because these are public deterministic test fixtures.
            // measure_noise decrypts internally; never report it to a real host.
            if [1, 16, 32, 48, 64].contains(&step) {
                println!("RANK_ONE_CORRECT seed={seed} additions={step} library_noise_bits={}",
                    unsafe { sk.measure_noise(&current)? });
            }
        }
        assert!(failure.is_some(), "expected bounded-modulus failure within 128 doublings");

        // Integer floor cannot be replaced by a prime-field modular inverse.
        let inverse8 = Plaintext::try_encode(&[903169u64], Encoding::poly(), &params)?;
        let bad_round = &ct * &inverse8;
        assert_eq!(decode(&bad_round)?, 903169);
        assert_ne!(decode(&bad_round)?, 1u64 / 8);
        let sixteen = Plaintext::try_encode(&[16u64], Encoding::poly(), &params)?;
        let ct16: Ciphertext = pk.try_encrypt(&sixteen, &mut rng)?;
        assert_eq!(decode(&(&ct16 * &inverse8))?, 2);
        println!("ROUNDING_CONTROL seed={seed} Enc(1)*inverse8=903169 floor(1/8)=0 Enc(16)*inverse8=2");

        // Genuine fresh-input addition loop. Readout is decrypted by the test
        // harness; this is an explicit read-all custodian, not tier A/B.
        let mut sum = ct.clone();
        for _ in 0..128 {
            let fresh: Ciphertext = pk.try_encrypt(&one, &mut rng)?;
            sum += &fresh;
        }
        assert_eq!(decode(&sum)?, 129);
        println!("FRESH_INPUT_POSITIVE seed={seed} input_encryptions=129 additions=128 output=129");

        // Sixteen packed private additive coefficients; 64 authenticated-input
        // steps are a chosen arithmetic horizon (authentication is NOT built).
        // Public input fixtures make this reproducible, not secret from readers.
        let mut reference = [0i64; 16];
        let zero = Plaintext::try_encode(&[0u64; 16], Encoding::poly(), &params)?;
        let mut resident: Ciphertext = pk.try_encrypt(&zero, &mut rng)?;
        let initial_ct_bytes = resident.to_bytes().len();
        let mut input_ct_bytes = 0usize;
        for step in 0..64usize {
            let update: Vec<u64> = (0..16).map(|i| {
                let u = ((step * (i + 1) + seed as usize) % 3) as i64 - 1;
                reference[i] += u;
                u.rem_euclid(modulus as i64) as u64
            }).collect();
            let pt = Plaintext::try_encode(&update, Encoding::poly(), &params)?;
            let encrypted_update: Ciphertext = pk.try_encrypt(&pt, &mut rng)?;
            input_ct_bytes += encrypted_update.to_bytes().len();
            resident += &encrypted_update;
            // Output only encrypted state between steps; no intermediate decrypt.
        }
        let resident_bytes = resident.to_bytes();
        resident = Ciphertext::from_bytes(&resident_bytes, &params)?;
        let question: Vec<u64> = (0..16).map(|i| u64::from(i % 3 == 0)).collect();
        let reversed: Vec<u64> = question.iter().rev().copied().collect();
        let pt_question = Plaintext::try_encode(&reversed, Encoding::poly(), &params)?;
        let encrypted_polynomial_answer = &resident * &pt_question;
        let decoded = Vec::<u64>::try_decode(
            &sk.try_decrypt(&encrypted_polynomial_answer)?, Encoding::poly())?;
        let want = reference.iter().zip(&question)
            .map(|(w, q)| *w * *q as i64).sum::<i64>();
        assert_eq!(decoded[15], want.rem_euclid(modulus as i64) as u64);
        assert!(reference.iter().all(|w| w.abs() <= 64));
        println!("PACKED_FINITE_LEARN_INFER seed={seed} dimension=16 steps=64 input_encryptions=65 ct_add=64 readout_ct_pt_mul=1 expected_signed_score={want} observed_residue={} private_state_ct=1 read_all_test_key_retained=true", decoded[15]);
        println!("PACKED_SERIALIZED_BYTES seed={seed} initial_ct={initial_ct_bytes} total_64_input_ct={input_ct_bytes} state_ct={} readout_ct={} public_key={} ciphertext_components={} raw_RNS_u64_state_bytes={} state_codec_roundtrip=true",
            resident_bytes.len(), encrypted_polynomial_answer.to_bytes().len(), pk.to_bytes().len(), resident.len(), resident.len()*params.degree()*params.moduli().len()*8);
    }
    println!("PASS four seeds: genuine BFV bounded addition positive, rank-one no-refresh falsifier, modular-rounding falsifier");
    Ok(())
}
