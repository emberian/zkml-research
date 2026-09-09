//! Public four-prime teaching reader and generic generated-relation proof calls.
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, TableSem, UMemBoundaryWitness, parse_vm_descriptor2,
};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriWitness,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use fhe::bfv::{
    BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, EvaluationKey, Plaintext,
};
use fhe_math::rq::{Poly, Representation, traits::TryConvertFrom};
use fhe_traits::{DeserializeParametrized, FheEncoder, Serialize};
use ndarray::Array2;
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{error::Error, fs, io::Read, path::Path, sync::Arc, time::Instant};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;
type Result<T> = std::result::Result<T, Box<dyn Error>>;
type Proof = <Backend as DescriptorProofVerifier>::Proof;
const N: usize = 8192;
const ROWS: usize = 4096;
const ARITY: usize = 97;
const CHUNKS: usize = 8;
const T: u64 = 4294475777;
const Q: [u64; 4] = [
    1125899906826241,
    1125899906629633,
    1125899905744897,
    1125899905351681,
];
fn hash(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn read(p: &Path, max: usize) -> Result<Vec<u8>> {
    let f = fs::File::open(p)?;
    assert!(f.metadata()?.len() <= max as u64);
    let mut b = Vec::new();
    f.take(max as u64 + 1).read_to_end(&mut b)?;
    assert!(b.len() <= max);
    Ok(b)
}
fn save(p: &Path, v: &Value) -> Result<()> {
    fs::write(p, serde_json::to_vec(v)?)?;
    Ok(())
}
fn params() -> Result<Arc<BfvParameters>> {
    Ok(BfvParametersBuilder::new()
        .set_degree(N)
        .set_plaintext_modulus(T)
        .set_moduli(&Q)
        .set_variance(10)
        .build_arc()?)
}
fn ct(path: &Path, p: &Arc<BfvParameters>) -> Result<(Vec<u8>, Ciphertext)> {
    let b = read(path, 2 << 20)?;
    let c = Ciphertext::from_bytes(&b, p)?;
    assert_eq!(c.len(), 2);
    assert_eq!(c.to_bytes(), b);
    for poly in c.iter() {
        assert_eq!(p.level_of_context(poly.ctx())?, 0);
        assert_eq!(*poly.representation(), Representation::Ntt);
        for (r, q) in poly.coefficients().outer_iter().zip(Q) {
            assert!(r.iter().all(|x| *x < q));
        }
    }
    Ok((b, c))
}
fn coeff(p: &Poly) -> Vec<Vec<u64>> {
    p.coefficients().outer_iter().map(|r| r.to_vec()).collect()
}
fn binding(case: &Path) -> Result<Value> {
    let mut result = serde_json::Map::new();
    for name in ["acc", "fresh", "old", "out"] {
        result.insert(format!("{name}_sha256"), json!(hash(&read(&case.join(format!("{name}.ct")), 2 << 20)?)));
    }
    Ok(Value::Object(result))
}
fn rows(case: &Path, index: usize) -> Result<Vec<Vec<u32>>> {
    assert!(index < CHUNKS);
    let p = params()?;
    let acc = ct(&case.join("acc.ct"), &p)?.1;
    let fresh = ct(&case.join("fresh.ct"), &p)?.1;
    let old = ct(&case.join("old.ct"), &p)?.1;
    let out = ct(&case.join("out.ct"), &p)?.1;
    let prime = index / 2;
    let q = Q[prime];
    let start = index % 2 * ROWS;
    Ok((start..start + ROWS).map(|position| {
        let get = |c: &Ciphertext, h: usize| c[h].coefficients()[[prime, position]];
        let words = [get(&fresh,0),get(&fresh,1),get(&old,0),get(&old,1),
            1,0,q-1,0,0,1,0,q-1,get(&acc,0),get(&acc,1),get(&out,0),get(&out,1)];
        let mut row=vec![(prime*N+position) as u32];
        for word in words {
            assert!(word < q);
            for d in 0..6 { row.push(((word >> (9*d)) & 511) as u32); }
        }
        assert_eq!(row.len(),ARITY);
        row
    }).collect())
}
fn export(source: &Path, out: &Path) -> Result<()> {
    fs::create_dir(out)?;
    for name in ["acc","fresh","old","out"] {
        fs::write(out.join(format!("{name}.ct")),read(&source.join(format!("{name}.ct")),2<<20)?)?;
    }
    fs::create_dir(out.join("rows"))?;
    let mut chunks=Vec::new();
    for index in 0..CHUNKS {
        let path=format!("rows/{index:03}.json");
        save(&out.join(&path),&json!(rows(out,index)?))?;
        chunks.push(json!({"index":index,"prime_index":index/2,"rows":ROWS,"first_row":index*ROWS,"end_row_exclusive":(index+1)*ROWS,"path":path,"sha256":hash(&read(&out.join(&path),32<<20)?)}));
    }
    let report=json!({"operation":"out=acc+fresh-old","binding":binding(out)?,"N":N,"q":Q,"t":T,"chunks":chunks,"public_arity":ARITY,"paired_output_residues":2*N*4,"private_files_read":0});
    save(&out.join("operation.json"),&report)?;
    println!("{report}");
    Ok(())
}
fn statement(template: &Path, public_rows: Vec<Vec<u32>>) -> Result<DescriptorStatement> {
    let raw = read(template, 32 << 20)?;
    let mut d = parse_vm_descriptor2(std::str::from_utf8(&raw)?)?;
    assert_eq!(d.public_input_count, 0);
    assert_eq!(d.tables.iter().filter(|t| t.id == 11).count(), 1);
    let t = d
        .tables
        .iter_mut()
        .find(|t| t.id == 11)
        .ok_or("missing exact public table")?;
    assert_eq!(t.arity, ARITY);
    assert!(matches!(t.sem, TableSem::ExactPublicRows { .. }));
    t.sem = TableSem::ExactPublicRows { rows: public_rows };
    Ok(DescriptorStatement::try_new(d, vec![])?)
}
fn prove(
    index: usize,
    template: &Path,
    case: &Path,
    trace_file: &Path,
    out: &Path,
) -> Result<()> {
    fs::create_dir(out)?;
    let public_rows = rows(case, index)?;
    let s = statement(template, public_rows.clone())?;
    let width = s.descriptor().trace_width;
    assert!((ARITY..=100000).contains(&width));
    let size = ROWS * width * 4;
    let encoded = read(trace_file, size)?;
    assert_eq!(encoded.len(), size);
    let mut trace = Vec::with_capacity(ROWS);
    for (row, pubrow) in encoded.chunks_exact(width * 4).zip(&public_rows) {
        let r: Vec<u32> = row
            .chunks_exact(4)
            .map(|x| u32::from_le_bytes(x.try_into().unwrap()))
            .collect();
        assert_eq!(&r[..ARITY], pubrow);
        assert!(r.iter().all(|x| *x < BABYBEAR_P));
        trace.push(r.into_iter().map(BabyBear::new).collect::<Vec<_>>());
    }
    drop(encoded);
    let mem = MemBoundaryWitness::default();
    let umem = UMemBoundaryWitness::default();
    let w = Plonky3HidingFriWitness {
        base_trace: &trace,
        mem_boundary: &mem,
        map_heaps: &[],
        umem_boundary: &umem,
    };
    let timer = Instant::now();
    let proof = Backend::prove(&s, w)?;
    let prove_ns = timer.elapsed().as_nanos();
    let bytes = postcard::to_allocvec(&proof)?;
    fs::write(out.join("proof.bin"), &bytes)?;
    let timer = Instant::now();
    Backend::verify(&s, &proof)?;
    let self_verify_ns = timer.elapsed().as_nanos();
    let report = json!({"verified":true,"index":index,"prime_index":index%8/2,"rows":ROWS,"first_row":index*ROWS,"end_row_exclusive":(index+1)*ROWS,"arity":ARITY,"width":width,"binding":binding(case)?,"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"template_sha256":hash(&read(template,32<<20)?),"backend":Backend::BACKEND_ID,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"prove_ns":prove_ns,"self_verify_ns":self_verify_ns});
    save(&out.join("proof.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn verify(
    index: usize,
    template: &Path,
    case: &Path,
    proof_file: &Path,
) -> Result<()> {
    let public_rows = rows(case, index)?;
    let s = statement(template, public_rows.clone())?;
    let bytes = read(proof_file, 256 << 20)?;
    let (proof, tail): (Proof, &[u8]) = postcard::take_from_bytes(&bytes)?;
    assert!(tail.is_empty());
    let timer = Instant::now();
    Backend::verify(&s, &proof)?;
    println!(
        "{}",
        json!({"verified":true,"index":index,"prime_index":index%8/2,"rows":ROWS,"first_row":index*ROWS,"end_row_exclusive":(index+1)*ROWS,"binding":binding(case)?,"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"template_sha256":hash(&read(template,32<<20)?),"proof_sha256":hash(&bytes),"verify_ns":timer.elapsed().as_nanos()})
    );
    Ok(())
}
fn main() -> Result<()> {
    let a:Vec<String>=std::env::args().collect();
    match a.get(1).map(String::as_str) {
        Some("export") if a.len()==4 => export(Path::new(&a[2]),Path::new(&a[3])),
        Some("prove") if a.len()==7 => prove(a[4].parse()?,Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[5]),Path::new(&a[6])),
        Some("verify") if a.len()==6 => verify(a[4].parse()?,Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[5])),
        _=>Err("usage: export SOURCE NEW_CASE | prove TEMPLATE CASE INDEX TRACE NEW_PROOF | verify TEMPLATE CASE INDEX PROOF".into())
    }
}
