//! Real BFV operation plus the existing generic DescriptorIR-v2 proof backend.
//! Arithmetic constraints and witness generation are Lean-owned artifacts.
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2, MemBoundaryWitness, TableSem, UMemBoundaryWitness};
use dregg_circuit::descriptor_proof_backend::{DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriWitness};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Plonky3HidingFriReference;
use dregg_circuit::field::{BabyBear, BABYBEAR_P};
use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_math::rq::Representation;
use fhe_traits::{DeserializeParametrized, FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{error::Error, fs, path::Path, sync::Arc, time::Instant};
mod update;

type Result<T> = std::result::Result<T, Box<dyn Error>>;
type Proof = <Plonky3HidingFriReference as DescriptorProofVerifier>::Proof;
const MODULI: [u64; 3] = [68719403009, 68719230977, 137438822401];
const PUBLIC_TABLE: usize = 11;

fn hash(bytes: &[u8]) -> String { format!("{:x}", Sha256::digest(bytes)) }
fn write_json(path: &Path, value: &Value) -> Result<()> {
    fs::write(path, serde_json::to_vec(value)?)?; Ok(())
}
fn params() -> Result<Arc<BfvParameters>> {
    let p = BfvParameters::default_parameters_128(20)?.nth(2).ok_or("missing preset")?;
    assert_eq!(p.degree(), 4096); assert_eq!(p.moduli(), MODULI); assert_eq!(p.plaintext(), 1032193);
    Ok(p)
}
fn coefficients(ct: &Ciphertext) -> Vec<Vec<Vec<u64>>> {
    ct.iter().map(|p| { let mut p = p.clone(); p.change_representation(Representation::PowerBasis);
        p.coefficients().outer_iter().map(|row| row.to_vec()).collect() }).collect()
}
fn rows_for(a: &Ciphertext, b: &Ciphertext, out: &Ciphertext, n: usize) -> Vec<Vec<u32>> {
    let cs = [coefficients(a), coefficients(b), coefficients(out)];
    assert!(cs.iter().all(|c| c.len() == 2 && c.iter().all(|p| p.len() == 3 && p.iter().all(|r| r.len() == n))));
    (0..2*n).map(|row_id| {
        let mut row = vec![row_id as u32]; let component = row_id / n; let coefficient = row_id % n;
        for source in &cs { for limb in 0..3 {
            let value = source[component][limb][coefficient]; assert!(value < MODULI[limb]);
            for digit in 0..7 { row.push(((value >> (6*digit)) & 63) as u32); }
        }}
        assert_eq!(row.len(), 64); row
    }).collect()
}
fn load_case(dir: &Path) -> Result<Vec<Vec<u32>>> {
    let p = params()?;
    let load = |name: &str| -> Result<Ciphertext> {
        let bytes=fs::read(dir.join(name))?; let ct=Ciphertext::from_bytes(&bytes,&p)?;
        assert_eq!(ct.to_bytes(),bytes); Ok(ct)
    };
    let (a,b,o) = (load("a.ct")?, load("b.ct")?, load("output.ct")?);
    Ok(rows_for(&a, &b, &o, p.degree()))
}
fn generate(dir: &Path) -> Result<()> {
    fs::create_dir(dir)?; let started = Instant::now(); let p = params()?;
    let mut rng = ChaCha20Rng::from_os_rng();
    let sk = SecretKey::random(&p, &mut rng); let pk = PublicKey::new(&sk, &mut rng);
    let t = p.plaintext() as i64;
    let av: Vec<i64> = (0..p.degree()).map(|i| (i % 11) as i64 - 5).collect();
    let bv: Vec<i64> = (0..p.degree()).map(|i| ((3*i) % 13) as i64 - 6).collect();
    let encode = |v: &[i64]| -> Result<Plaintext> { let residues: Vec<u64> = v.iter().map(|x| x.rem_euclid(t) as u64).collect(); Ok(Plaintext::try_encode(&residues, Encoding::poly(), &p)?) };
    let a: Ciphertext = pk.try_encrypt(&encode(&av)?, &mut rng)?;
    let b: Ciphertext = pk.try_encrypt(&encode(&bv)?, &mut rng)?;
    let three = Plaintext::try_encode(&[3u64], Encoding::poly(), &p)?;
    let five = Plaintext::try_encode(&[5u64], Encoding::poly(), &p)?;
    let op_start = Instant::now(); let a3 = &a * &three; let b5 = &b * &five; let output = &a3 + &b5;
    let operation_ns = op_start.elapsed().as_nanos();
    let (ca,cb,co) = (coefficients(&a), coefficients(&b), coefficients(&output));
    for c in 0..2 { for l in 0..3 { for i in 0..p.degree() {
        assert_eq!(co[c][l][i], (3*ca[c][l][i] + 5*cb[c][l][i]) % MODULI[l]);
    }}}
    let decoded = Vec::<u64>::try_decode(&sk.try_decrypt(&output)?, Encoding::poly())?;
    let expected: Vec<u64> = av.iter().zip(&bv).map(|(x,y)| (3*x + 5*y).rem_euclid(t) as u64).collect();
    assert_eq!(decoded, expected);
    let rows = rows_for(&a,&b,&output,p.degree());
    write_json(&dir.join("public_rows.json"), &json!(rows))?;
    let mut serialized = Vec::new();
    for (name, bytes) in [("a.ct",a.to_bytes()), ("b.ct",b.to_bytes()), ("output.ct",output.to_bytes()), ("public_key.bin",pk.to_bytes())] {
        serialized.push(json!({"name":name,"bytes":bytes.len(),"sha256":hash(&bytes)})); fs::write(dir.join(name),bytes)?;
    }
    let report = json!({"claim":"EXECUTED real BFV ciphertext linear combination on public synthetic messages","operation":"3*A + 5*B","degree":p.degree(),"moduli":p.moduli(),"plaintext_modulus":p.plaintext(),"ciphertext_components":output.len(),"coefficient_rows":rows.len(),"public_tuple_width":64,"residue_equations":2*p.degree()*3,"all_plaintext_coefficients_match":true,"plaintext_coefficients_checked":decoded.len(),"all_rns_coefficient_equations_match":true,"operation_ns":operation_ns,"total_ns":started.elapsed().as_nanos(),"ciphertext_files":serialized,"secret_key_saved":false,"proof_produced":false});
    write_json(&dir.join("operation.json"),&report)?; println!("{}",report); Ok(())
}
fn statement(template: &Path, rows: Vec<Vec<u32>>) -> Result<DescriptorStatement> {
    let public_width=rows.first().ok_or("empty public rows")?.len();
    let mut desc = parse_vm_descriptor2(&fs::read_to_string(template)?)?;
    assert_eq!(desc.public_input_count,0); assert_eq!(desc.tables.iter().filter(|t| t.id == PUBLIC_TABLE).count(),1);
    let table = desc.tables.iter_mut().find(|t| t.id == PUBLIC_TABLE).ok_or("missing public table")?;
    assert_eq!(table.arity,public_width); assert!(matches!(table.sem, TableSem::ExactPublicRows { .. }));
    table.sem = TableSem::ExactPublicRows { rows };
    Ok(DescriptorStatement::try_new(desc, vec![])? )
}
fn inspect(template:&Path,case:&Path,update:bool)->Result<()> {
    let rows=if update {update::rows(case)?} else {load_case(case)?};
    let row_count=rows.len(); let public_width=rows[0].len();
    let statement=statement(template,rows)?;
    println!("{}",json!({"claim":"EXECUTED strict descriptor/public ciphertext input check","rows":row_count,"public_tuple_width":public_width,"trace_width":statement.descriptor().trace_width,"constraints":statement.descriptor().constraints.len(),"template_sha256":hash(&fs::read(template)?)}));Ok(())
}
fn prove(template: &Path, case: &Path, trace_file: &Path, output: &Path, update:bool) -> Result<()> {
    fs::create_dir(output)?;
    let rows = if update {update::rows(case)?} else {load_case(case)?}; let public_width=rows[0].len();
    let statement = statement(template, rows.clone())?;
    let width=statement.descriptor().trace_width;
    let encoded_trace=fs::read(trace_file)?;
    let raw: Vec<Vec<u32>> = if trace_file.extension().is_some_and(|x| x=="json") {
        serde_json::from_slice(&encoded_trace)?
    } else {
        assert_eq!(encoded_trace.len(),rows.len().checked_mul(width).and_then(|x| x.checked_mul(4)).ok_or("trace size overflow")?);
        encoded_trace.chunks_exact(width*4).map(|r| r.chunks_exact(4).map(|v| u32::from_le_bytes(v.try_into().unwrap())).collect()).collect()
    };
    assert_eq!(raw.len(),rows.len());
    assert!(width>=public_width);
    assert!(raw.iter().zip(&rows).all(|(r,p)| r.len()==width && &r[..public_width]==p.as_slice() && r.iter().all(|v| *v<BABYBEAR_P)));
    let trace: Vec<Vec<BabyBear>> = raw.into_iter().map(|r| r.into_iter().map(BabyBear::new).collect()).collect();
    let memory=MemBoundaryWitness::default(); let umemory=UMemBoundaryWitness::default();
    let witness=Plonky3HidingFriWitness {base_trace:&trace,mem_boundary:&memory,map_heaps:&[],umem_boundary:&umemory};
    let timer=Instant::now(); let proof=Plonky3HidingFriReference::prove(&statement,witness)?; let prove_ns=timer.elapsed().as_nanos();
    let bytes=postcard::to_allocvec(&proof)?; fs::write(output.join("proof.bin"),&bytes)?;
    let timer=Instant::now(); Plonky3HidingFriReference::verify(&statement,&proof)?; let verify_ns=timer.elapsed().as_nanos();
    let report=json!({"claim":"EXECUTED proof over Lean-derived BFV relation","backend":Plonky3HidingFriReference::BACKEND_ID,"rows":trace.len(),"trace_width":width,"public_tuple_width":public_width,"public_rows_bound":rows.len(),"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"prove_ns":prove_ns,"self_verify_ns":verify_ns,"verified":true,"template_sha256":hash(&fs::read(template)?)});
    write_json(&output.join("proof.json"),&report)?; println!("{}",report); Ok(())
}
fn verify(template: &Path, case: &Path, proof_file: &Path, mutate: bool, update:bool) -> Result<()> {
    let mut rows=if update {update::rows(case)?} else {load_case(case)?};
    if mutate { rows[0][43] ^= 1; }
    let statement=statement(template,rows)?; let bytes=fs::read(proof_file)?;
    let (proof,remainder):(Proof,&[u8])=postcard::take_from_bytes(&bytes)?;
    assert!(remainder.is_empty(),"trailing proof bytes");
    let timer=Instant::now(); let result=Plonky3HidingFriReference::verify(&statement,&proof);
    if mutate { assert!(result.is_err(),"changed output claim accepted"); } else { result?; }
    println!("{}",json!({"claim":"EXECUTED fresh-process verification","verified":!mutate,"changed_output_claim_rejected":mutate,"verify_ns":timer.elapsed().as_nanos(),"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes)})); Ok(())
}
fn main() -> Result<()> {
    let a:Vec<String>=std::env::args().collect();
    match a.get(1).map(String::as_str) {
        Some("generate") if a.len()==3 => generate(Path::new(&a[2])),
        Some("import-update") if a.len()==4 => update::import(Path::new(&a[2]),Path::new(&a[3])),
        Some("export-update-ntt") if a.len()==3 => update::export_ntt(Path::new(&a[2])),
        Some("inspect"|"inspect-update") if a.len()==4 => inspect(Path::new(&a[2]),Path::new(&a[3]),a[1]=="inspect-update"),
        Some("prove"|"prove-update") if a.len()==6 => prove(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),Path::new(&a[5]),a[1]=="prove-update"),
        Some("verify"|"verify-update"|"verify-changed-output"|"verify-update-changed-output") if a.len()==5 => verify(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),a[1].contains("changed-output"),a[1].contains("update")),
        _ => Err("usage: generate DIR | import-update JOIN_DIR CASE | prove[-update] TEMPLATE CASE TRACE_JSON_OR_LE32 OUT | verify[-update][-changed-output] TEMPLATE CASE PROOF".into())
    }
}
