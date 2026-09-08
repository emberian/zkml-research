//! Thin consumer of the existing DescriptorIR-v2 HidingFRI verifier with the
//! prover lane's shared public-only deterministic preprocessing adapter.
//! No arithmetic constraints, witness generation, prover, or FHE code is added.
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2, TableSem};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofVerifier, DescriptorStatement,
};
use dregg_circuit::field::BABYBEAR_P;
use serde::Serialize;
use sha2::{Digest, Sha256};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing;

type Proof = <FixedPublicPreprocessing as DescriptorProofVerifier>::Proof;
pub const PUBLIC_TABLE_ID: usize = 11;
pub const MAX_TEMPLATE_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_ROWS_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_PROOF_BYTES: usize = 64 * 1024 * 1024;

#[derive(Debug, Serialize)]
pub struct Verification {
    pub verified: bool,
    pub backend: &'static str,
    pub public_rows: usize,
    pub public_width: usize,
    pub proof_bytes: usize,
    pub template_sha256: String,
    pub error: Option<String>,
}

/// Check a proof against caller-selected public rows and an independently pinned
/// template. The expected hash is a transport/provenance pin, not a replacement
/// for the backend's typed relation identity. Never take it from an untrusted
/// proof envelope without comparing it to the application's approved pin.
pub fn verify_core(
    template_json: &str,
    public_rows_json: &str,
    proof_bytes: &[u8],
    expected_template_sha256: &str,
) -> Verification {
    let mut outcome = Verification {
        verified: false,
        backend: FixedPublicPreprocessing::BACKEND_ID,
        public_rows: 0,
        public_width: 0,
        proof_bytes: proof_bytes.len(),
        template_sha256: String::new(),
        error: None,
    };
    let checked = (|| -> Result<(), String> {
        if template_json.len() > MAX_TEMPLATE_BYTES || public_rows_json.len() > MAX_ROWS_BYTES
            || proof_bytes.len() > MAX_PROOF_BYTES {
            return Err("input exceeds this consumer's size limit".into());
        }
        if expected_template_sha256.len() != 64
            || !expected_template_sha256.bytes().all(|x| x.is_ascii_digit() || (b'a'..=b'f').contains(&x)) {
            return Err("expected template SHA256 must be 64 lowercase hexadecimal characters".into());
        }
        outcome.template_sha256 = format!("{:x}", Sha256::digest(template_json.as_bytes()));
        if outcome.template_sha256 != expected_template_sha256 {
            return Err("template bytes do not match the application's expected SHA256".into());
        }
        let rows: Vec<Vec<u32>> = serde_json::from_str(public_rows_json)
            .map_err(|e| format!("invalid public rows JSON: {e}"))?;
        outcome.public_rows = rows.len();
        outcome.public_width = rows.first().map_or(0, Vec::len);
        if rows.is_empty() || rows.len() > 65_536 || outcome.public_width == 0 || outcome.public_width > 256 {
            return Err("public table dimensions exceed this consumer's supported limits".into());
        }
        if rows.iter().any(|r| r.len() != outcome.public_width || r.iter().any(|x| *x >= BABYBEAR_P)) {
            return Err("public rows must be rectangular canonical BabyBear values".into());
        }
        let mut descriptor = parse_vm_descriptor2(template_json)
            .map_err(|e| format!("descriptor parse failed: {e}"))?;
        if descriptor.public_input_count != 0 {
            return Err("this consumer requires all public values in exact-public table 11".into());
        }
        if descriptor.tables.iter().filter(|t| t.id == PUBLIC_TABLE_ID).count() != 1 {
            return Err("descriptor must contain exactly one table with id 11".into());
        }
        let table = descriptor.tables.iter_mut().find(|t| t.id == PUBLIC_TABLE_ID).unwrap();
        if table.arity != outcome.public_width || !matches!(table.sem, TableSem::ExactPublicRows { .. }) {
            return Err("table 11 must be ExactPublicRows of the supplied width".into());
        }
        table.sem = TableSem::ExactPublicRows { rows };
        let statement = DescriptorStatement::try_new(descriptor, vec![])?;
        // take_from_bytes makes the no-trailing-data requirement explicit.
        let (proof, trailing): (Proof, &[u8]) = postcard::take_from_bytes(proof_bytes)
            .map_err(|e| format!("invalid postcard proof: {e}"))?;
        if !trailing.is_empty() {
            return Err("trailing bytes after proof".into());
        }
        FixedPublicPreprocessing::verify(&statement, &proof)
            .map_err(|e| format!("proof rejected: {e}"))?;
        Ok(())
    })();
    match checked {
        Ok(()) => outcome.verified = true,
        Err(error) => outcome.error = Some(error),
    }
    outcome
}

/// JSON-in/bytes-in/JSON-out ABI; web/verifier.js gives this a small object API.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen::prelude::wasm_bindgen]
pub fn verify_receipt(template_json: &str, public_rows_json: &str, proof: &[u8], expected_template_sha256: &str) -> String {
    serde_json::to_string(&verify_core(template_json, public_rows_json, proof, expected_template_sha256))
        .expect("fixed verification result is JSON serializable")
}
