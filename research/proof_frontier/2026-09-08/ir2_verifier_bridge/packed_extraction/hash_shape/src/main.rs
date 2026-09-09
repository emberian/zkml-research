//! One deterministic public cross-shape alias for the deployed leaf hasher.
//! No key, proof, MMCS opening, verifier, transcript or private data is generated.
use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_symmetric::{CryptographicHasher, PaddingFreeSponge, Permutation};
use serde_json::json;
fn words(a: &[BabyBear]) -> Vec<u32> { a.iter().map(|x| x.as_canonical_u32()).collect() }
fn main() {
    let perm = default_babybear_poseidon2_16();
    let hash = PaddingFreeSponge::<_, 16, 8, 8>::new(perm.clone());
    let short: Vec<BabyBear> = (1..=20).map(BabyBear::from_u32).collect();
    let mut state = [BabyBear::ZERO; 16];
    for block in short[..16].chunks_exact(8) {
        state[..8].copy_from_slice(block);
        perm.permute_mut(&mut state);
    }
    let mut long = short.clone();
    long.extend_from_slice(&state[4..8]);
    let h20 = hash.hash_iter(short.iter().copied());
    let h24 = hash.hash_iter(long.iter().copied());
    assert_eq!(short.len(), 20);
    assert_eq!(long.len(), 24);
    assert_ne!(short, long);
    assert_eq!(h20, h24);
    assert!(words(&long).iter().all(|&x| x < 2013265921));
    println!("{}", serde_json::to_string_pretty(&json!({
        "claim": "EXECUTED one low-level cross-shape leaf collision; no forged accepted proof",
        "p3_revision": "82cfad73cd734d37a0d51953094f970c531817ec",
        "hasher": "PaddingFreeSponge<default_babybear_poseidon2_16,16,8,8>",
        "canonical_babybear_payload20": words(&short),
        "canonical_babybear_payload24": words(&long),
        "state_after_first16": words(&state),
        "appended_state_words4_to8": words(&state[4..8]),
        "actual_hash20": words(&h20), "actual_hash24": words(&h24),
        "distinct_payloads": true, "equal_actual_hashes": true,
        "same_first16_data_words": short[..16] == long[..16],
        "forged_proof_constructed": false,
        "profile_shape_admission": "separate source-derived analysis in README.md"
    })).unwrap());
}
