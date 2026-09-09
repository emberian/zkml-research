//! Public BFV parsing and complete linear-plan row reconstruction.
//!
//! [SOURCE] Adapted from continuing_system/linear/native/src/main.rs. The
//! consumer performs public encoding, permutation, residue lifting and NTTs;
//! it does not evaluate ciphertext rotations or read a secret key. Rows contain
//! canonical residues, not the predecessor's nine-bit limbs or carry witnesses.
use fhe::bfv::{
    BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, EvaluationKey, Plaintext,
};
use fhe_math::rq::{Poly, Representation, traits::TryConvertFrom};
use fhe_traits::{DeserializeParametrized, FheEncoder, Serialize as FheSerialize};
use ndarray::Array2;
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{error::Error, fs, io::Read, path::Path, sync::Arc, time::Instant};

pub type Result<T> = std::result::Result<T, Box<dyn Error>>;
pub const N: usize = 8192;
pub const STAGES: usize = 11;
pub const Q: [u64; 4] = [
    1125899906826241,
    1125899906629633,
    1125899905744897,
    1125899905351681,
];
const T: u64 = 4294475777;
const SHIFTS: [usize; 9] = [8, 16, 32, 64, 128, 256, 512, 1024, 2048];
const EXPONENTS: [usize; 10] = [
    6561, 5953, 16001, 15617, 14849, 13313, 10241, 4097, 8193, 16383,
];
const MAX_PLAN: usize = 4 << 20;
const MAX_CT: usize = 2 << 20;
const MAX_QUERY: usize = 1 << 20;
const MAX_KEY: usize = 16 << 20;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Binding {
    pub linear_plan_sha256: String,
    pub model_ciphertext_sha256: String,
    pub query_sha256: String,
    pub evaluation_key_sha256: String,
    pub dot_ciphertext_sha256: String,
}

impl Binding {
    pub fn validate(&self) -> Result<()> {
        for digest in [
            &self.linear_plan_sha256,
            &self.model_ciphertext_sha256,
            &self.query_sha256,
            &self.evaluation_key_sha256,
            &self.dot_ciphertext_sha256,
        ] {
            require(
                digest.len() == 64
                    && digest
                        .bytes()
                        .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)),
                "binding digests must be lowercase SHA-256 hex",
            )?;
        }
        Ok(())
    }
}

pub struct PublicCase {
    pub binding: Binding,
    /// Exactly 44 groups indexed by stage * 4 + prime, each with N rows.
    /// Tuple order: d[0..4], k0[0..4], k1[0..4], add0, add1, out0, out1.
    pub rows: Vec<Vec<[u64; 16]>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpdateBinding {
    pub acc_sha256: String,
    pub fresh_sha256: String,
    pub old_sha256: String,
    pub out_sha256: String,
}

pub struct PublicUpdate {
    pub binding: UpdateBinding,
    /// Four prime groups of N canonical MAC tuples, with no limb encoding.
    pub rows: Vec<Vec<[u64; 16]>>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct LinearStage {
    index: usize,
    exponent: usize,
    permutation: Vec<usize>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct LinearPlan {
    schema: String,
    degree: usize,
    primes: Vec<u64>,
    stages: Vec<LinearStage>,
}

fn require(condition: bool, message: &str) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(message.into())
    }
}

fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn read(path: &Path, max: usize) -> Result<Vec<u8>> {
    let resolved = fs::canonicalize(path)?;
    require(
        !resolved
            .components()
            .any(|part| part.as_os_str() == ".private"),
        "private paths are outside this public interface",
    )?;
    let file = fs::File::open(resolved)?;
    require(file.metadata()?.is_file(), "expected a regular input file")?;
    require(
        file.metadata()?.len() <= max as u64,
        "input exceeds size limit",
    )?;
    let mut bytes = Vec::new();
    file.take(max as u64 + 1).read_to_end(&mut bytes)?;
    require(bytes.len() <= max, "input exceeds size limit")?;
    Ok(bytes)
}

fn reverse_index(index: usize) -> usize {
    index.reverse_bits() >> (usize::BITS - 13)
}

fn permutation(exponent: usize, index: usize) -> usize {
    // [SOURCE] full_bfv_infer_composition/Compiler/BfvInferLinear.lean:39-46;
    // fhe-math 0.1.1 src/rq/mod.rs:57-68,338-344. The direct input storage
    // coordinate is rev13(((e-1)/2 + e*rev13(output)) mod 8192).
    reverse_index(((exponent - 1) / 2 + exponent * reverse_index(index)) % N)
}

fn parse_plan(bytes: &[u8]) -> Result<LinearPlan> {
    let plan: LinearPlan = serde_json::from_slice(bytes)?;
    require(
        plan.schema == "lean-bfv-infer-linear-plan-v1",
        "wrong linear-plan schema",
    )?;
    require(
        plan.degree == N && plan.primes == Q,
        "wrong linear-plan parameters",
    )?;
    require(
        plan.stages.len() == STAGES - 1,
        "wrong linear-plan stage count",
    )?;
    for (i, stage) in plan.stages.iter().enumerate() {
        require(
            stage.index == i + 1 && stage.exponent == EXPONENTS[i],
            "wrong linear-plan stage/exponent",
        )?;
        require(
            stage.permutation.len() == N,
            "wrong linear-plan permutation length",
        )?;
        for (j, &input) in stage.permutation.iter().enumerate() {
            require(
                input == permutation(stage.exponent, j),
                "linear-plan permutation differs from fixed exponent",
            )?;
        }
    }
    Ok(plan)
}

fn params() -> Result<Arc<BfvParameters>> {
    Ok(BfvParametersBuilder::new()
        .set_degree(N)
        .set_plaintext_modulus(T)
        .set_moduli(&Q)
        .set_variance(10)
        .build_arc()?)
}

fn check_poly(poly: &Poly, params: &Arc<BfvParameters>, allow_shoup: bool) -> Result<()> {
    require(
        params.level_of_context(poly.ctx())? == 0,
        "polynomial is not at level zero",
    )?;
    require(
        *poly.representation() == Representation::Ntt
            || (allow_shoup && *poly.representation() == Representation::NttShoup),
        "polynomial has unexpected representation",
    )?;
    let coefficients = poly.coefficients();
    require(
        coefficients.shape() == [4, N],
        "wrong polynomial dimensions",
    )?;
    for (row, q) in coefficients.outer_iter().zip(Q) {
        require(
            row.iter().all(|&x| x < q),
            "noncanonical polynomial residue",
        )?;
    }
    Ok(())
}

fn parse_ct(bytes: &[u8], params: &Arc<BfvParameters>) -> Result<Ciphertext> {
    let ct = Ciphertext::from_bytes(bytes, params)?;
    require(ct.len() == 2, "ciphertext must have exactly two components")?;
    require(
        ct.to_bytes() == bytes,
        "noncanonical ciphertext serialization",
    )?;
    for poly in ct.iter() {
        check_poly(poly, params, false)?;
    }
    Ok(ct)
}

fn canonical(ct: Ciphertext, params: &Arc<BfvParameters>) -> Result<Ciphertext> {
    let mut canonical = Ciphertext::new(ct.iter().cloned().collect(), params)?;
    for poly in canonical.iter_mut() {
        // All arithmetic here consumes caller-supplied public objects.
        unsafe {
            poly.allow_variable_time_computations();
        }
    }
    Ok(canonical)
}

fn coeff(poly: &Poly) -> Vec<Vec<u64>> {
    poly.coefficients()
        .outer_iter()
        .map(|row| row.to_vec())
        .collect()
}

fn parse_query_values(bytes: &[u8]) -> Result<Vec<i64>> {
    let values: Vec<i64> = serde_json::from_slice(bytes)?;
    require(
        values.len() == 576,
        "query must contain exactly 576 integers",
    )?;
    require(
        values.iter().all(|x| (-32..=32).contains(x)),
        "query element exceeds signed bound",
    )?;
    require(
        values.iter().map(|x| x * x).sum::<i64>() <= 20000,
        "query squared norm exceeds 20000",
    )?;
    Ok(values)
}

fn query(bytes: &[u8], params: &Arc<BfvParameters>) -> Result<(Plaintext, Poly)> {
    let values = parse_query_values(bytes)?;
    let mut slots = vec![0u64; N];
    for (i, x) in values.iter().enumerate() {
        for lane in 0..8 {
            slots[i * 8 + lane] = x.rem_euclid(T as i64) as u64;
        }
    }
    let pt = Plaintext::try_encode(&slots, Encoding::simd(), params)?;
    let mut poly = Poly::try_convert_from(
        &pt,
        params.context_at_level(0)?,
        false,
        Representation::PowerBasis,
    )?;
    poly.change_representation(Representation::Ntt);
    check_poly(&poly, params, false)?;
    Ok((pt, poly))
}

type Components = Vec<Vec<Vec<u64>>>;
struct RotationParts {
    k0: Components,
    k1: Components,
}

fn rotation_parts(key: &EvaluationKey, params: &Arc<BfvParameters>) -> Result<Vec<RotationParts>> {
    let mut parts = Vec::with_capacity(STAGES - 1);
    for i in 0..STAGES - 1 {
        let shift = SHIFTS.get(i).copied();
        let (exponent, ct_level, key_level, log_base, c0, c1) =
            key.vfhe_public_rotation_parts(shift)?;
        require(
            exponent == EXPONENTS[i],
            "evaluation key has wrong rotation exponent",
        )?;
        require(
            (ct_level, key_level, log_base) == (0, 0, 0),
            "unsupported evaluation-key decomposition",
        )?;
        require(
            (c0.len(), c1.len()) == (4, 4),
            "wrong evaluation-key component count",
        )?;
        for poly in c0.iter().chain(&c1) {
            check_poly(poly, params, true)?;
        }
        parts.push(RotationParts {
            k0: c0.iter().map(coeff).collect(),
            k1: c1.iter().map(coeff).collect(),
        });
    }
    Ok(parts)
}

/// Reconstruct every public row from public input bytes, independently of any
/// producer-exported rows, operation metadata, proof manifest or self-check.
pub fn reconstruct(plan_path: &Path, case: &Path) -> Result<PublicCase> {
    let plan_bytes = read(plan_path, MAX_PLAN)?;
    let plan = parse_plan(&plan_bytes)?;
    let model_bytes = read(&case.join("model.ct"), MAX_CT)?;
    let query_bytes = read(&case.join("query.json"), MAX_QUERY)?;
    let key_bytes = read(&case.join("evaluation.key"), MAX_KEY)?;
    let dot_bytes = read(&case.join("expected_dot.ct"), MAX_CT)?;
    let params = params()?;
    let model = parse_ct(&model_bytes, &params)?;
    let (_, query_poly) = query(&query_bytes, &params)?;
    let key = EvaluationKey::from_bytes(&key_bytes, &params)?;
    // The underlying evaluation-key encoder iterates a HashMap, so byte
    // reserialization is not canonical. Approval binds the original raw bytes;
    // every used key branch and expanded residue is checked above/below.
    let keys = rotation_parts(&key, &params)?;
    let mut steps = Vec::with_capacity(STAGES);
    for stage in 0..STAGES {
        let bytes = read(&case.join(format!("steps/{stage:02}.ct")), MAX_CT)?;
        if stage == STAGES - 1 {
            require(
                bytes == dot_bytes,
                "final step differs from bound dot ciphertext",
            )?;
        }
        let ct = parse_ct(&bytes, &params)?;
        steps.push([coeff(&ct[0]), coeff(&ct[1])]);
    }
    let binding = Binding {
        linear_plan_sha256: hash(&plan_bytes),
        model_ciphertext_sha256: hash(&model_bytes),
        query_sha256: hash(&query_bytes),
        evaluation_key_sha256: hash(&key_bytes),
        dot_ciphertext_sha256: hash(&dot_bytes),
    };
    let query_coeff = coeff(&query_poly);
    let model_coeff = [coeff(&model[0]), coeff(&model[1])];
    let mut rows = Vec::with_capacity(STAGES * 4);
    for stage in 0..STAGES {
        let mut digits: Components = Vec::new();
        if stage != 0 {
            let perm = &plan.stages[stage - 1].permutation;
            let prev = &steps[stage - 1];
            let permuted: Vec<u64> = prev[1]
                .iter()
                .flat_map(|r| perm.iter().map(|&j| r[j]))
                .collect();
            let ctx = params.context_at_level(0)?;
            let mut sub1 = Poly::try_convert_from(
                Array2::from_shape_vec((4, N), permuted)?,
                ctx,
                true,
                Representation::Ntt,
            )?;
            sub1.change_representation(Representation::PowerBasis);
            let power = coeff(&sub1);
            for residue in &power {
                let values: Vec<u64> = Q
                    .iter()
                    .flat_map(|q| residue.iter().map(move |x| x % q))
                    .collect();
                let mut lift = Poly::try_convert_from(
                    Array2::from_shape_vec((4, N), values)?,
                    ctx,
                    true,
                    Representation::PowerBasis,
                )?;
                lift.change_representation(Representation::Ntt);
                check_poly(&lift, &params, false)?;
                digits.push(coeff(&lift));
            }
        }
        for (prime, &q) in Q.iter().enumerate() {
            let mut group = Vec::with_capacity(N);
            for k in 0..N {
                let mut row = [0u64; 16];
                if stage == 0 {
                    row[0] = query_coeff[prime][k];
                    row[4] = model_coeff[0][prime][k];
                    row[8] = model_coeff[1][prime][k];
                } else {
                    let prev = &steps[stage - 1];
                    let key = &keys[stage - 1];
                    for digit in 0..4 {
                        row[digit] = digits[digit][prime][k];
                        row[4 + digit] = key.k0[digit][prime][k];
                        row[8 + digit] = key.k1[digit][prime][k];
                    }
                    let j = plan.stages[stage - 1].permutation[k];
                    row[12] = ((prev[0][prime][k] as u128 + prev[0][prime][j] as u128) % q as u128)
                        as u64;
                    row[13] = prev[1][prime][k];
                }
                row[14] = steps[stage][0][prime][k];
                row[15] = steps[stage][1][prime][k];
                require(
                    row.iter().all(|&x| x < q),
                    "public row has noncanonical residue",
                )?;
                group.push(row);
            }
            rows.push(group);
        }
    }
    Ok(PublicCase { binding, rows })
}

/// Produce the eleven trace ciphertexts from caller-selected public inputs.
/// This performs no proof generation, secret-key operation or decryption.
pub fn import(
    plan_path: &Path,
    model_path: &Path,
    query_path: &Path,
    key_path: &Path,
    out: &Path,
) -> Result<()> {
    let timer = Instant::now();
    let plan_bytes = read(plan_path, MAX_PLAN)?;
    parse_plan(&plan_bytes)?;
    let model_bytes = read(model_path, MAX_CT)?;
    let query_bytes = read(query_path, MAX_QUERY)?;
    let key_bytes = read(key_path, MAX_KEY)?;
    let params = params()?;
    let model = parse_ct(&model_bytes, &params)?;
    let (pt, _) = query(&query_bytes, &params)?;
    let key = EvaluationKey::from_bytes(&key_bytes, &params)?;
    rotation_parts(&key, &params)?;
    fs::create_dir(out)?;
    fs::create_dir(out.join("steps"))?;
    for (name, bytes) in [
        ("model.ct", &model_bytes),
        ("query.json", &query_bytes),
        ("evaluation.key", &key_bytes),
    ] {
        fs::write(out.join(name), bytes)?;
    }
    let mut current = canonical(&model * &pt, &params)?;
    fs::write(out.join("steps/00.ct"), current.to_bytes())?;
    for stage in 1..STAGES {
        let rotated = if let Some(&shift) = SHIFTS.get(stage - 1) {
            key.rotates_columns_by(&current, shift)?
        } else {
            key.rotates_rows(&current)?
        };
        current += &rotated;
        current = canonical(current, &params)?;
        for poly in current.iter() {
            check_poly(poly, &params, false)?;
        }
        fs::write(out.join(format!("steps/{stage:02}.ct")), current.to_bytes())?;
    }
    let dot_bytes = current.to_bytes();
    fs::write(out.join("expected_dot.ct"), &dot_bytes)?;
    let binding = Binding {
        linear_plan_sha256: hash(&plan_bytes),
        model_ciphertext_sha256: hash(&model_bytes),
        query_sha256: hash(&query_bytes),
        evaluation_key_sha256: hash(&key_bytes),
        dot_ciphertext_sha256: hash(&dot_bytes),
    };
    let report = json!({
        "claim": "[EXECUTED] imported caller-selected complete packed linear trace",
        "schema": "matched-field-linear-case-v1", "binding": binding,
        "degree": N, "primes": Q, "stages": STAGES, "groups": STAGES * 4,
        "public_arity": 16, "mac_tuple_rows": STAGES * 4 * N,
        "private_files_read": 0, "proofs_generated": 0,
        "final_step_dot_bytes_equal": true, "elapsed_ns": timer.elapsed().as_nanos()
    });
    fs::write(
        out.join("operation.json"),
        serde_json::to_vec_pretty(&report)?,
    )?;
    Ok(())
}

/// Independently reconstruct out = acc + fresh - old using the same two-output
/// MAC relation as linear inference. This consumer parses all four public
/// ciphertexts once; it does not recompute an output and substitute it for the
/// claimed output being proved.
pub fn reconstruct_update(case: &Path) -> Result<PublicUpdate> {
    let params = params()?;
    let mut bytes = Vec::with_capacity(4);
    let mut ciphertexts = Vec::with_capacity(4);
    for name in ["acc", "fresh", "old", "out"] {
        let encoded = read(&case.join(format!("{name}.ct")), MAX_CT)?;
        let ct = parse_ct(&encoded, &params)?;
        ciphertexts.push([coeff(&ct[0]), coeff(&ct[1])]);
        bytes.push(encoded);
    }
    let binding = UpdateBinding {
        acc_sha256: hash(&bytes[0]),
        fresh_sha256: hash(&bytes[1]),
        old_sha256: hash(&bytes[2]),
        out_sha256: hash(&bytes[3]),
    };
    let mut rows = Vec::with_capacity(4);
    for (prime, q) in Q.into_iter().enumerate() {
        let mut group = Vec::with_capacity(N);
        for k in 0..N {
            let get = |ct: usize, component: usize| ciphertexts[ct][component][prime][k];
            // [SOURCE] nonlinear_performance/runtime/native/update/src/main.rs:93-95.
            // The four digits are fresh0, fresh1, old0, old1. The two
            // coefficient vectors select +fresh0-old0 and +fresh1-old1.
            group.push([
                get(1, 0),
                get(1, 1),
                get(2, 0),
                get(2, 1),
                1,
                0,
                q - 1,
                0,
                0,
                1,
                0,
                q - 1,
                get(0, 0),
                get(0, 1),
                get(3, 0),
                get(3, 1),
            ]);
        }
        rows.push(group);
    }
    Ok(PublicUpdate { binding, rows })
}

/// Produce a complete public ciphertext update from caller-selected operands.
/// No secret key, key generation, multiplication, rotation or proof is invoked.
pub fn import_update(
    acc_path: &Path,
    fresh_path: &Path,
    old_path: &Path,
    out: &Path,
) -> Result<()> {
    let timer = Instant::now();
    let acc_bytes = read(acc_path, MAX_CT)?;
    let fresh_bytes = read(fresh_path, MAX_CT)?;
    let old_bytes = read(old_path, MAX_CT)?;
    let params = params()?;
    let mut output = parse_ct(&acc_bytes, &params)?;
    let fresh = parse_ct(&fresh_bytes, &params)?;
    let old = parse_ct(&old_bytes, &params)?;
    output += &fresh;
    output -= &old;
    output = canonical(output, &params)?;
    for poly in output.iter() {
        check_poly(poly, &params, false)?;
    }
    let output_bytes = output.to_bytes();
    fs::create_dir(out)?;
    for (name, bytes) in [
        ("acc", &acc_bytes),
        ("fresh", &fresh_bytes),
        ("old", &old_bytes),
        ("out", &output_bytes),
    ] {
        fs::write(out.join(format!("{name}.ct")), bytes)?;
    }
    let binding = UpdateBinding {
        acc_sha256: hash(&acc_bytes),
        fresh_sha256: hash(&fresh_bytes),
        old_sha256: hash(&old_bytes),
        out_sha256: hash(&output_bytes),
    };
    let report = json!({
        "claim": "[EXECUTED] imported caller-selected complete public ciphertext update",
        "schema": "matched-field-update-case-v1", "operation": "out=acc+fresh-old", "binding": binding,
        "degree": N, "primes": Q, "groups": 4, "public_arity": 16,
        "mac_tuple_rows": 4 * N, "private_files_read": 0, "proofs_generated": 0,
        "elapsed_ns": timer.elapsed().as_nanos()
    });
    fs::write(
        out.join("operation.json"),
        serde_json::to_vec_pretty(&report)?,
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plan_value() -> serde_json::Value {
        json!({"schema":"lean-bfv-infer-linear-plan-v1", "degree":N, "primes":Q,
            "stages": EXPONENTS.iter().enumerate().map(|(i,&e)| json!({
                "index":i+1,"exponent":e,"permutation":(0..N).map(|j|permutation(e,j)).collect::<Vec<_>>()
            })).collect::<Vec<_>>()})
    }

    #[test]
    fn fixed_plan_accepts_and_rejects_permutation_mutations() {
        let mut value = plan_value();
        assert!(parse_plan(&serde_json::to_vec(&value).unwrap()).is_ok());
        let first = value["stages"][0]["permutation"][0].clone();
        value["stages"][0]["permutation"][0] = value["stages"][0]["permutation"][1].clone();
        value["stages"][0]["permutation"][1] = first;
        assert!(parse_plan(&serde_json::to_vec(&value).unwrap()).is_err());
        value = plan_value();
        value["stages"][0]["extra"] = json!(0);
        assert!(parse_plan(&serde_json::to_vec(&value).unwrap()).is_err());
        value = plan_value();
        value["stages"][0]["exponent"] = json!(3);
        assert!(parse_plan(&serde_json::to_vec(&value).unwrap()).is_err());
    }

    #[test]
    fn permutation_matches_library_storage_assignment() {
        for exponent in EXPONENTS {
            let mut library_map = vec![0usize; N];
            let mut power = (exponent - 1) / 2;
            for index in 0..N {
                library_map[reverse_index(index)] = reverse_index(power & (N - 1));
                power += exponent;
            }
            assert!((0..N).all(|j| permutation(exponent, j) == library_map[j]));
            library_map.sort_unstable();
            assert_eq!(library_map, (0..N).collect::<Vec<_>>());
        }
    }

    #[test]
    fn query_rejects_wrong_shape_range_norm_and_nonintegers() {
        assert!(parse_query_values(&serde_json::to_vec(&vec![0i64; 576]).unwrap()).is_ok());
        for values in [
            vec![0i64; 575],
            vec![33; 576],
            vec![32; 576],
            vec![i64::MIN; 576],
        ] {
            assert!(parse_query_values(&serde_json::to_vec(&values).unwrap()).is_err());
        }
        assert!(parse_query_values(b"[0.5]").is_err());
    }
}
