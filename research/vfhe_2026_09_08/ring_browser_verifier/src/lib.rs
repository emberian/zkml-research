//! Fixed degree-4096 public-bundle consumer. All proof decoding and verification
//! comes from the saved matvec source; no protocol equation is reimplemented.
use matvec::{
    arith::field::Field64_2,
    protocol::{
        pcs::whir::Whir,
        public_wire::{decode_proof, decode_statement, same_outputs},
        verifier::Verifier,
    },
};
use serde::Serialize;

pub const DEGREE: usize = 4096;
pub const MAX_BUNDLE_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug, Serialize)]
pub struct Verification {
    pub verified: bool,
    pub stage: &'static str,
    pub verifier_ran: bool,
    pub expected_output_matched: bool,
    pub degree: usize,
    pub matrix_rows: usize,
    pub matrix_columns: usize,
    pub statement_bytes: usize,
    pub proof_bytes: usize,
    pub statement_blake3: String,
    pub proof_blake3: String,
    pub whir_configured_security_level: usize,
    pub whir_soundness_type: String,
    pub security_scope: &'static str,
    pub error: Option<String>,
}

/// Verify against the caller-selected matrix, ciphertext input and expected
/// output contained in statement_bytes. RNG/transcript state is never imported.
pub fn verify_core(statement_bytes: &[u8], proof_bytes: &[u8]) -> Verification {
    let mut result = Verification {
        verified: false, stage: "size", verifier_ran: false,
        expected_output_matched: false, degree: DEGREE,
        matrix_rows: 0, matrix_columns: 0,
        statement_bytes: statement_bytes.len(), proof_bytes: proof_bytes.len(),
        statement_blake3: String::new(), proof_blake3: String::new(),
        whir_configured_security_level: Whir::<Field64_2>::SECURITY_LEVEL,
        whir_soundness_type: format!("{:?}", Whir::<Field64_2>::SOUNDNESS_TYPE),
        security_scope: "Upstream ConjectureList model; configured WHIR level is not a certified security-bit claim.",
        error: None,
    };
    let checked = (|| -> Result<(), String> {
        if statement_bytes.len() > MAX_BUNDLE_BYTES || proof_bytes.len() > MAX_BUNDLE_BYTES {
            return Err("either public bundle exceeds 64 MiB".into());
        }
        result.statement_blake3 = blake3::hash(statement_bytes).to_hex().to_string();
        result.proof_blake3 = blake3::hash(proof_bytes).to_hex().to_string();
        result.stage = "decode_statement";
        let (matrix, input, expected_output) = decode_statement::<DEGREE>(statement_bytes)?;
        result.matrix_rows = matrix.height();
        result.matrix_columns = matrix.width();
        result.stage = "decode_proof";
        let proof = decode_proof::<DEGREE>(proof_bytes, matrix.width(), matrix.height())?;
        result.stage = "expected_output";
        if !same_outputs(&proof.y, &expected_output) {
            return Err("proof output differs from caller-selected expected output".into());
        }
        result.expected_output_matched = true;
        result.stage = "verification";
        let (ring_matrix, num_vars, mut transcript) = Verifier::<DEGREE, Field64_2>::preprocess(&matrix);
        result.verifier_ran = true;
        Verifier::<DEGREE, Field64_2>::verify(&ring_matrix, num_vars, &mut transcript, &input, &proof)
            .map_err(|_| "existing ring-matvec verifier rejected the proof".to_string())?;
        Ok(())
    })();
    match checked {
        Ok(()) => { result.verified = true; result.stage = "accepted"; }
        Err(error) => result.error = Some(error),
    }
    result
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen::prelude::wasm_bindgen]
pub fn verify_bundle(statement: &[u8], proof: &[u8]) -> String {
    serde_json::to_string(&verify_core(statement, proof)).expect("fixed result serializes")
}

