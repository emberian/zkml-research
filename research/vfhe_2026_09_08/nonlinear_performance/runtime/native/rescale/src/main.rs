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
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{error::Error, fs, io::Read, path::Path, time::Instant};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;

type Result<T> = std::result::Result<T, Box<dyn Error>>;
type Proof = <Backend as DescriptorProofVerifier>::Proof;
const WIDTH: usize = 88;
const DEGREE: usize = 8192;
const COMPONENTS: usize = 3;
const CHUNK_ROWS: usize = 4096;
const CHUNKS: usize = COMPONENTS * DEGREE / CHUNK_ROWS;
const BASE: [u64; 4] = [
    1125899906826241,
    1125899906629633,
    1125899905744897,
    1125899905351681,
];
const EXTENDED: [u64; 9] = [
    1125899906826241,
    1125899906629633,
    1125899905744897,
    1125899905351681,
    4611686018427322369,
    4611686018427289601,
    4611686018426454017,
    4611686018426257409,
    4611686018425815041,
];
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
fn hash(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn write_json(p: &Path, v: &Value) -> Result<()> {
    fs::write(p, serde_json::to_vec(v)?)?;
    Ok(())
}
fn capped(p: &Path, max: usize) -> Result<Vec<u8>> {
    let f = fs::File::open(p)?;
    if f.metadata()?.len() > max as u64 {
        return Err("public artifact exceeds cap".into());
    }
    let mut b = Vec::new();
    f.take((max + 1) as u64).read_to_end(&mut b)?;
    if b.len() > max {
        return Err("public artifact exceeds cap".into());
    }
    Ok(b)
}
fn read_case(case: &Path) -> Result<Capture> {
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
    assert_eq!(capture.degree, DEGREE);
    assert_eq!(capture.components, COMPONENTS);
    assert_eq!(capture.t, 4294475777);
    assert_eq!(capture.base, BASE);
    assert_eq!(capture.extended_base, EXTENDED);
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
    Ok(capture)
}

fn span(chunk: usize) -> std::ops::Range<usize> {
    assert!(chunk < CHUNKS, "chunk must be in0..6");
    chunk * CHUNK_ROWS..(chunk + 1) * CHUNK_ROWS
}
fn rows(capture: &Capture, chunk: usize) -> Vec<Vec<u32>> {
    span(chunk)
        .map(|global_id| {
            let component = global_id / DEGREE;
            let coefficient = global_id % DEGREE;
            let mut row = vec![global_id as u32];
            for (tensor, limbs, digits) in [
                (&capture.product_extended_power_basis, 9, 7),
                (&capture.output_power_basis, 4, 6),
            ] {
                for limb in 0..limbs {
                    let value = tensor[component][limb][coefficient];
                    for digit in 0..digits {
                        row.push(((value >> (9 * digit)) & 511) as u32);
                    }
                }
            }
            assert_eq!(row.len(), WIDTH);
            row
        })
        .collect()
}
fn import(source: &Path, out: &Path) -> Result<()> {
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
    let capture = read_case(out)?;
    let mut chunks = Vec::new();
    fs::create_dir(out.join("chunks"))?;
    for chunk in 0..CHUNKS {
        let public_rows = rows(&capture, chunk);
        let file = format!("chunks/{chunk:03}.json");
        write_json(&out.join(&file), &json!(public_rows))?;
        chunks.push(json!({"chunk":chunk,"rows":CHUNK_ROWS,"first_global_row":span(chunk).start,"end_global_row_exclusive":span(chunk).end,"component":span(chunk).start/DEGREE,"coefficient_start":span(chunk).start%DEGREE,"coefficient_end_exclusive":(span(chunk).end-1)%DEGREE+1,"public_rows":file,"sha256":hash(&fs::read(out.join(&file))?)}));
    }
    let report = json!({"claim":"EXECUTED full exact public9-to4 coefficient export in six deterministic chunks","degree":DEGREE,"components":COMPONENTS,"chunk_count":CHUNKS,"chunk_rows":CHUNK_ROWS,"total_positions":COMPONENTS*DEGREE,"input_residues":9*COMPONENTS*DEGREE,"output_residues":4*COMPONENTS*DEGREE,"global_row_formula":"component*8192+coefficient","exact_coverage_no_padding":true,"public_tuple_width":WIDTH,"radix":512,"plaintext_modulus":capture.t,"base_moduli":capture.base,"extended_moduli":capture.extended_base,"all_captured_output_coefficients_checked_against_raw_ciphertext":4*COMPONENTS*DEGREE,"source_trace_sha256":hash(&fs::read(out.join("basic.json"))?),"source_descriptor_sha256":hash(&fs::read(out.join("source_descriptor.json"))?),"output_ciphertext_sha256":capture.output_sha256,"source_rounding_description":capture.rounding,"chunks":chunks,"private_files_read":0,"import_ns":timer.elapsed().as_nanos(),"scope":"Complete rescale tensor only. Captured extended-product provenance, public decoding and inverse NTT remain implementation assumptions. No extension/convolution/whole ct-times-ct theorem."});
    write_json(&out.join("operation.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn statement(template: &Path, public_rows: Vec<Vec<u32>>) -> Result<DescriptorStatement> {
    let raw = capped(template, 32 * 1024 * 1024)?;
    let mut d = parse_vm_descriptor2(std::str::from_utf8(&raw)?)?;
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
fn prove(template: &Path, case: &Path, chunk: usize, trace_file: &Path, out: &Path) -> Result<()> {
    fs::create_dir(out)?;
    let capture = read_case(case)?;
    let public_rows = rows(&capture, chunk);
    let statement = statement(template, public_rows.clone())?;
    let width = statement.descriptor().trace_width;
    assert!(width >= WIDTH && width <= 100000);
    let expected = CHUNK_ROWS
        .checked_mul(width)
        .and_then(|x| x.checked_mul(4))
        .ok_or("trace length overflow")?;
    let encoded = capped(trace_file, expected)?;
    assert_eq!(encoded.len(), expected);
    let mut trace = Vec::with_capacity(CHUNK_ROWS);
    for (row, pubrow) in encoded.chunks_exact(width * 4).zip(&public_rows) {
        let row: Vec<u32> = row
            .chunks_exact(4)
            .map(|x| u32::from_le_bytes(x.try_into().unwrap()))
            .collect();
        assert_eq!(&row[..WIDTH], pubrow.as_slice());
        assert!(row.iter().all(|x| *x < BABYBEAR_P));
        trace.push(row.into_iter().map(BabyBear::new).collect::<Vec<_>>());
    }
    assert_eq!(trace.len(), CHUNK_ROWS);
    drop(encoded);
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
    let report = json!({"claim":"EXECUTED exact rescale proof for one full-coverage chunk","backend":Backend::BACKEND_ID,"chunk":chunk,"rows":CHUNK_ROWS,"first_global_row":span(chunk).start,"end_global_row_exclusive":span(chunk).end,"total_positions":COMPONENTS*DEGREE,"output_residues":4*CHUNK_ROWS,"trace_width":width,"public_tuple_width":WIDTH,"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"source_trace_sha256":hash(&fs::read(case.join("basic.json"))?),"output_ciphertext_sha256":capture.output_sha256,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"template_sha256":hash(&fs::read(template)?),"prove_ns":prove_ns,"self_verify_ns":verify_ns,"verified":true});
    write_json(&out.join("proof.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn verify(template: &Path, case: &Path, chunk: usize, proof_file: &Path) -> Result<()> {
    let capture = read_case(case)?;
    let public_rows = rows(&capture, chunk);
    let s = statement(template, public_rows.clone())?;
    let bytes = capped(proof_file, 256 * 1024 * 1024)?;
    let (proof, tail): (Proof, &[u8]) = postcard::take_from_bytes(&bytes)?;
    assert!(tail.is_empty());
    let timer = Instant::now();
    Backend::verify(&s, &proof)?;
    let verify_ns = timer.elapsed().as_nanos();
    println!(
        "{}",
        json!({"claim":"EXECUTED fresh-process exact rescale chunk verification","verified":true,"chunk":chunk,"rows":CHUNK_ROWS,"first_global_row":span(chunk).start,"end_global_row_exclusive":span(chunk).end,"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"source_trace_sha256":hash(&fs::read(case.join("basic.json"))?),"output_ciphertext_sha256":capture.output_sha256,"proof_sha256":hash(&bytes),"verify_ns":verify_ns})
    );
    Ok(())
}
fn main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(String::as_str) {
        Some("import")if a.len()==4=>import(Path::new(&a[2]),Path::new(&a[3])),
        Some("prove")if a.len()==7=>prove(Path::new(&a[2]),Path::new(&a[3]),a[4].parse()?,Path::new(&a[5]),Path::new(&a[6])),
        Some("verify")if a.len()==6=>verify(Path::new(&a[2]),Path::new(&a[3]),a[4].parse()?,Path::new(&a[5])),
        _=>Err("usage: import PUBLIC_SOURCE NEW_CASE | prove TEMPLATE CASE CHUNK TRACE NEW_PROOF | verify TEMPLATE CASE CHUNK PROOF".into())
    }
}
