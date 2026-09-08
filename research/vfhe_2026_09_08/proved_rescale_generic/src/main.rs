//! Public real-operator capture reader and a generic generated-relation proof call.
//! No rescale equations or witness arithmetic are written in Rust.
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, TableSem, UMemBoundaryWitness, parse_vm_descriptor2,
};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriWitness,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use fhe::bfv::{BfvParametersBuilder, Ciphertext};
use fhe_math::rq::Representation;
use fhe_traits::{DeserializeParametrized, Serialize};
use serde::{Deserialize, Serialize as SerdeSerialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeSet, error::Error, fs, path::Path, time::Instant};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;

type Result<T> = std::result::Result<T, Box<dyn Error>>;
type Proof = <Backend as DescriptorProofVerifier>::Proof;
const WIDTH: usize = 88;
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Capture {
    #[serde(rename = "N")]
    degree: usize,
    t: u64,
    base: Vec<u64>,
    extended_base: Vec<u64>,
    components: usize,
    input_dot_sha256: String,
    output_sha256: String,
    native_multiplicator_bytes_equal: bool,
    output_power_basis: Vec<Vec<Vec<u64>>>,
    product_extended_power_basis: Vec<Vec<Vec<u64>>>,
    rounding: String,
}
#[derive(Clone, Deserialize, SerdeSerialize)]
#[serde(deny_unknown_fields)]
struct Position {
    component: usize,
    coefficient: usize,
}
fn hash(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn write_json(p: &Path, v: &Value) -> Result<()> {
    fs::write(p, serde_json::to_vec(v)?)?;
    Ok(())
}
fn capped(p: &Path, max: usize) -> Result<Vec<u8>> {
    let b = fs::read(p)?;
    if b.len() > max {
        return Err("public artifact exceeds cap".into());
    }
    Ok(b)
}
fn read_case(case: &Path) -> Result<(Capture, Vec<Position>)> {
    let trace_bytes = capped(&case.join("basic.json"), 32 * 1024 * 1024)?;
    let capture: Capture = serde_json::from_slice(&trace_bytes)?;
    let d: Value = serde_json::from_slice(&capped(&case.join("source_descriptor.json"), 1 << 20)?)?;
    assert_eq!(
        d["files"]["trace"]["sha256"].as_str(),
        Some(hash(&trace_bytes).as_str())
    );
    assert_eq!(capture.base.len(), 4);
    assert_eq!(capture.extended_base.len(), 9);
    assert_eq!(&capture.extended_base[..4], capture.base.as_slice());
    assert!(capture.degree.is_power_of_two() && capture.degree >= 8 && capture.degree <= 32768);
    assert!(capture.components >= 1 && capture.components <= 16);
    assert!(capture.native_multiplicator_bytes_equal);
    assert_eq!(d["N"].as_u64(), Some(capture.degree as u64));
    assert_eq!(d["t"].as_u64(), Some(capture.t));
    assert_eq!(d["base"], json!(capture.base));
    assert_eq!(d["extended_base"], json!(capture.extended_base));
    assert_eq!(d["components"].as_u64(), Some(capture.components as u64));
    let tensor_valid = |tensor: &Vec<Vec<Vec<u64>>>, moduli: &[u64]| {
        tensor.len() == capture.components
            && tensor.iter().all(|p| {
                p.len() == moduli.len()
                    && p.iter()
                        .zip(moduli)
                        .all(|(r, q)| r.len() == capture.degree && r.iter().all(|x| *x < *q))
            })
    };
    assert!(tensor_valid(
        &capture.product_extended_power_basis,
        &capture.extended_base
    ));
    assert!(tensor_valid(&capture.output_power_basis, &capture.base));
    assert!(
        capture.extended_base.iter().all(|q| *q < (1u64 << 63))
            && capture.base.iter().all(|q| *q < (1u64 << 54))
    );
    // Decode public ciphertexts under the capture's declared parameters. This
    // source-binding check is distinct from the generated rescale relation.
    let p = BfvParametersBuilder::new()
        .set_degree(capture.degree)
        .set_plaintext_modulus(capture.t)
        .set_moduli(&capture.base)
        .set_variance(10)
        .build_arc()?;
    for (name, sha, kind) in [
        ("basic.dot.ct", &capture.input_dot_sha256, "dot_ciphertext"),
        ("basic-000.ct", &capture.output_sha256, "output_ciphertext"),
    ] {
        let bytes = capped(&case.join(name), 16 * 1024 * 1024)?;
        assert_eq!(&hash(&bytes), sha);
        assert_eq!(d["files"][kind]["sha256"].as_str(), Some(sha.as_str()));
        let ct = Ciphertext::from_bytes(&bytes, &p)?;
        assert_eq!(ct.to_bytes(), bytes);
        if kind == "dot_ciphertext" {
            assert_eq!(ct.len(), 2);
        } else {
            assert_eq!(ct.len(), capture.components);
            for (i, poly) in ct.iter().enumerate() {
                let mut power = poly.clone();
                power.change_representation(Representation::PowerBasis);
                let actual: Vec<Vec<u64>> = power
                    .coefficients()
                    .outer_iter()
                    .map(|r| r.to_vec())
                    .collect();
                assert_eq!(actual, capture.output_power_basis[i]);
            }
        }
    }
    let positions: Vec<Position> =
        serde_json::from_slice(&capped(&case.join("selection.json"), 1 << 20)?)?;
    assert!(!positions.is_empty() && positions.len().is_power_of_two() && positions.len() <= 1024);
    assert!(
        positions
            .iter()
            .all(|p| p.component < capture.components && p.coefficient < capture.degree)
    );
    assert_eq!(
        positions
            .iter()
            .map(|p| (p.component, p.coefficient))
            .collect::<BTreeSet<_>>()
            .len(),
        positions.len()
    );
    Ok((capture, positions))
}
fn rows(capture: &Capture, positions: &[Position]) -> Vec<Vec<u32>> {
    positions
        .iter()
        .enumerate()
        .map(|(row_id, p)| {
            let mut row = vec![row_id as u32];
            for (tensor, limbs, digits) in [
                (&capture.product_extended_power_basis, 9, 7),
                (&capture.output_power_basis, 4, 6),
            ] {
                for limb in 0..limbs {
                    let v = tensor[p.component][limb][p.coefficient];
                    for d in 0..digits {
                        row.push(((v >> (9 * d)) & 511) as u32);
                    }
                }
            }
            assert_eq!(row.len(), WIDTH);
            row
        })
        .collect()
}
fn import(source: &Path, selection: &Path, out: &Path) -> Result<()> {
    fs::create_dir(out)?;
    let timer = Instant::now();
    for (input, output) in [
        ("descriptor.json", "source_descriptor.json"),
        ("basic.json", "basic.json"),
        ("basic.dot.ct", "basic.dot.ct"),
        ("basic-000.ct", "basic-000.ct"),
    ] {
        fs::write(
            out.join(output),
            capped(&source.join(input), 32 * 1024 * 1024)?,
        )?;
    }
    fs::write(out.join("selection.json"), capped(selection, 1 << 20)?)?;
    let (capture, positions) = read_case(out)?;
    let public_rows = rows(&capture, &positions);
    write_json(&out.join("public_rows.json"), &json!(public_rows))?;
    let report = json!({"claim":"EXECUTED exact public coefficient export from real nonlinear native rescale capture","degree":capture.degree,"plaintext_modulus":capture.t,"base_moduli":capture.base,"extended_moduli":capture.extended_base,"components":capture.components,"selected_actual_positions":positions.len(),"total_ciphertext_positions":capture.components*capture.degree,"selected_output_residue_equations":4*positions.len(),"all_captured_output_coefficients_checked_against_raw_ciphertext":4*capture.components*capture.degree,"public_tuple_width":WIDTH,"radix":512,"input_digits_per_limb":7,"output_digits_per_limb":6,"selection":positions,"source_trace_sha256":hash(&fs::read(out.join("basic.json"))?),"source_descriptor_sha256":hash(&fs::read(out.join("source_descriptor.json"))?),"public_rows_sha256":hash(&fs::read(out.join("public_rows.json"))?),"private_files_read":0,"source_rounding_description":capture.rounding,"import_ns":timer.elapsed().as_nanos(),"scope":"Bounded selected actual rescale positions; no whole-ciphertext or extension/convolution proof. Public tensor/ciphertext decode and basis conversion remain implementation assumptions."});
    write_json(&out.join("operation.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn statement(template: &Path, public_rows: Vec<Vec<u32>>) -> Result<DescriptorStatement> {
    let mut d = parse_vm_descriptor2(&fs::read_to_string(template)?)?;
    assert_eq!(d.public_input_count, 0);
    assert_eq!(d.tables.iter().filter(|t| t.id == 11).count(), 1);
    let t = d
        .tables
        .iter_mut()
        .find(|t| t.id == 11)
        .ok_or("missing exact public table")?;
    assert_eq!(t.arity, WIDTH);
    assert!(matches!(t.sem, TableSem::ExactPublicRows { .. }));
    t.sem = TableSem::ExactPublicRows { rows: public_rows };
    Ok(DescriptorStatement::try_new(d, vec![])?)
}
fn prove(template: &Path, case: &Path, trace_file: &Path, out: &Path) -> Result<()> {
    fs::create_dir(out)?;
    let (capture, positions) = read_case(case)?;
    let public_rows = rows(&capture, &positions);
    let statement = statement(template, public_rows.clone())?;
    let width = statement.descriptor().trace_width;
    assert!(width >= WIDTH);
    let encoded = fs::read(trace_file)?;
    assert_eq!(
        encoded.len(),
        positions
            .len()
            .checked_mul(width)
            .and_then(|x| x.checked_mul(4))
            .ok_or("trace length overflow")?
    );
    let raw: Vec<Vec<u32>> = encoded
        .chunks_exact(width * 4)
        .map(|r| {
            r.chunks_exact(4)
                .map(|x| u32::from_le_bytes(x.try_into().unwrap()))
                .collect()
        })
        .collect();
    assert!(
        raw.iter()
            .zip(&public_rows)
            .all(|(r, p)| &r[..WIDTH] == p.as_slice() && r.iter().all(|x| *x < BABYBEAR_P))
    );
    let trace: Vec<Vec<BabyBear>> = raw
        .into_iter()
        .map(|r| r.into_iter().map(BabyBear::new).collect())
        .collect();
    let mem = MemBoundaryWitness::default();
    let umem = UMemBoundaryWitness::default();
    let witness = Plonky3HidingFriWitness {
        base_trace: &trace,
        mem_boundary: &mem,
        map_heaps: &[],
        umem_boundary: &umem,
    };
    let timer = Instant::now();
    let proof = Backend::prove(&statement, witness)?;
    let prove_ns = timer.elapsed().as_nanos();
    let bytes = postcard::to_allocvec(&proof)?;
    fs::write(out.join("proof.bin"), &bytes)?;
    let timer = Instant::now();
    Backend::verify(&statement, &proof)?;
    let verify_ns = timer.elapsed().as_nanos();
    let report = json!({"claim":"EXECUTED generated exact rescale proof for a bounded real nonlinear batch","backend":Backend::BACKEND_ID,"selected_positions":positions.len(),"total_ciphertext_positions":capture.components*capture.degree,"output_residue_equations":4*positions.len(),"trace_width":width,"public_tuple_width":WIDTH,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"template_sha256":hash(&fs::read(template)?),"prove_ns":prove_ns,"self_verify_ns":verify_ns,"verified":true});
    write_json(&out.join("proof.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn verify(template: &Path, case: &Path, proof_file: &Path, mutate: bool) -> Result<()> {
    let (capture, positions) = read_case(case)?;
    let mut public_rows = rows(&capture, &positions);
    if mutate {
        public_rows[0][64] ^= 1;
    }
    let s = statement(template, public_rows)?;
    let bytes = fs::read(proof_file)?;
    let (proof, tail): (Proof, &[u8]) = postcard::take_from_bytes(&bytes)?;
    assert!(tail.is_empty());
    let timer = Instant::now();
    let result = Backend::verify(&s, &proof);
    let ns = timer.elapsed().as_nanos();
    if mutate {
        assert!(result.is_err(), "changed output accepted");
    } else {
        result?;
    }
    println!(
        "{}",
        json!({"claim":"EXECUTED fresh-process verification of bounded real rescale batch","verified":!mutate,"changed_output_rejected":mutate,"verify_ns":ns,"selected_positions":positions.len(),"proof_sha256":hash(&bytes)})
    );
    Ok(())
}
fn main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(String::as_str) {
        Some("import")if a.len()==5=>import(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4])),
        Some("prove")if a.len()==6=>prove(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),Path::new(&a[5])),
        Some("verify"|"verify-changed-output")if a.len()==5=>verify(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),a[1].contains("changed")),
        _=>Err("usage: import PUBLIC_SOURCE SELECTION OUT_CASE | prove TEMPLATE CASE TRACE OUT | verify[-changed-output] TEMPLATE CASE PROOF".into())
    }
}
