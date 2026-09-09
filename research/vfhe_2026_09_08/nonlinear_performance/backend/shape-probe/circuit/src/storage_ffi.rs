//! FFI symbols the Lean-compiled storage logic (`Dregg2.Storage.Deployed`) calls back into for its
//! hot Poseidon2 hashing — the "Lean is the runtime" split: verified content-root LOGIC in Lean,
//! fast crypto PRIMITIVE in Rust. Resolved at final link (dregg-lean-ffi depends on circuit).

use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2::hash_2_to_1;

/// Lean's `@[extern "dregg_poseidon2_2to1"]` — the REAL Poseidon2 2-to-1 compress over BabyBear,
/// exposed to the Lean-compiled storage content-root logic. Native-scalar ABI (`u64` canonical field
/// values `< 2^31`). No toy hash: this is the deployed Poseidon2 the circuit proves.
#[unsafe(no_mangle)]
pub extern "C" fn dregg_poseidon2_2to1(a: u64, b: u64) -> u64 {
    let fa = BabyBear::new((a % BABYBEAR_P as u64) as u32);
    let fb = BabyBear::new((b % BABYBEAR_P as u64) as u32);
    u64::from(hash_2_to_1(fa, fb).canonical_val())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poseidon2_2to1_is_a_real_order_sensitive_compress() {
        let h = dregg_poseidon2_2to1(7, 11);
        assert_eq!(h, dregg_poseidon2_2to1(7, 11), "deterministic");
        assert_ne!(
            h,
            dregg_poseidon2_2to1(11, 7),
            "order-sensitive — a real compress, not addition"
        );
        assert!(h < BABYBEAR_P as u64, "canonical field element out");
        // The FFI symbol IS circuit::poseidon2::hash_2_to_1 — no toy, the deployed primitive.
        let direct = u64::from(hash_2_to_1(BabyBear::new(7), BabyBear::new(11)).canonical_val());
        assert_eq!(
            h, direct,
            "the extern symbol is the real deployed Poseidon2 compress"
        );
    }
}
