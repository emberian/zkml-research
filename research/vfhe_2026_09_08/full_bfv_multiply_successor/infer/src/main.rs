//! Complete saved kernel Infer: public trace binding, generated MAC proof calls.
//! No switching/product constraints are authored in Rust.
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
const CHUNKS: usize = 88;
const T: u64 = 4294475777;
const Q: [u64; 4] = [
    1125899906826241,
    1125899906629633,
    1125899905744897,
    1125899905351681,
];
const SHIFTS: [usize; 9] = [8, 16, 32, 64, 128, 256, 512, 1024, 2048];
const EXPONENTS: [usize; 10] = [
    6561, 5953, 16001, 15617, 14849, 13313, 10241, 4097, 8193, 16383,
];
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LinearStage {
    index: usize,
    exponent: usize,
    permutation: Vec<usize>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LinearPlan {
    schema: String,
    degree: usize,
    primes: Vec<u64>,
    stages: Vec<LinearStage>,
}
fn linear_plan(path: &Path) -> Result<LinearPlan> {
    let plan: LinearPlan = serde_json::from_slice(&read(path, 4 << 20)?)?;
    assert_eq!(plan.schema, "lean-bfv-infer-linear-plan-v1");
    assert_eq!(plan.degree, N);
    assert_eq!(plan.primes, Q);
    assert_eq!(plan.stages.len(), 10);
    for (i, s) in plan.stages.iter().enumerate() {
        assert_eq!(s.index, i + 1);
        assert_eq!(s.exponent, EXPONENTS[i]);
        assert_eq!(s.permutation.len(), N);
        assert!(s.permutation.iter().all(|j| *j < N));
    }
    Ok(plan)
}
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
fn canonical(ct: Ciphertext, p: &Arc<BfvParameters>) -> Result<Ciphertext> {
    let mut c = Ciphertext::new(ct.iter().cloned().collect(), p)?;
    for poly in c.iter_mut() {
        unsafe {
            poly.allow_variable_time_computations();
        }
    }
    Ok(c)
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
fn query(path: &Path, p: &Arc<BfvParameters>) -> Result<(Vec<u8>, Plaintext, Poly)> {
    let b = read(path, 1 << 20)?;
    let v: Vec<i64> = serde_json::from_slice(&b)?;
    assert_eq!(v.len(), 576);
    assert!(v.iter().all(|x| (-32..=32).contains(x)));
    assert!(v.iter().map(|x| x * x).sum::<i64>() <= 20000);
    let mut slots = vec![0u64; N];
    for (i, x) in v.iter().enumerate() {
        for lane in 0..8 {
            slots[i * 8 + lane] = x.rem_euclid(T as i64) as u64;
        }
    }
    let pt = Plaintext::try_encode(&slots, Encoding::simd(), p)?;
    let mut poly = Poly::try_convert_from(
        &pt,
        p.context_at_level(0)?,
        false,
        Representation::PowerBasis,
    )?;
    poly.change_representation(Representation::Ntt);
    Ok((b, pt, poly))
}
fn binding(case: &Path, plan_path: &Path) -> Result<Value> {
    let model = read(&case.join("model.ct"), 2 << 20)?;
    let q = read(&case.join("query.json"), 1 << 20)?;
    let key = read(&case.join("evaluation.key"), 16 << 20)?;
    let dot = read(&case.join("expected_dot.ct"), 2 << 20)?;
    assert_eq!(read(&case.join("steps/10.ct"), 2 << 20)?, dot);
    let kernel = read(&case.join("expected_kernel.ct"), 2 << 20)?;
    Ok(
        json!({"linear_plan_sha256":hash(&read(plan_path,4<<20)?),"model_ciphertext_sha256":hash(&model),"query_sha256":hash(&q),"evaluation_key_sha256":hash(&key),"dot_ciphertext_sha256":hash(&dot),"kernel_ciphertext_sha256":hash(&kernel)}),
    )
}
fn rows(case: &Path, index: usize, plan_path: &Path) -> Result<Vec<Vec<u32>>> {
    let plan = linear_plan(plan_path)?;
    assert!(index < CHUNKS);
    let stage = index / 8;
    let prime = (index % 8) / 2;
    let half = index % 2;
    let p = params()?;
    let (_, out) = ct(&case.join(format!("steps/{stage:02}.ct")), &p)?;
    let zeros = vec![0u64; N];
    let mut d = vec![zeros.clone(); 4];
    let mut k0 = vec![zeros.clone(); 4];
    let mut k1 = vec![zeros.clone(); 4];
    let (mut add0, mut add1) = (zeros.clone(), zeros);
    if stage == 0 {
        let (_, model) = ct(&case.join("model.ct"), &p)?;
        let (_, _, pp) = query(&case.join("query.json"), &p)?;
        d[0] = coeff(&pp)[prime].clone();
        k0[0] = coeff(&model[0])[prime].clone();
        k1[0] = coeff(&model[1])[prime].clone();
    } else {
        let (_, prev) = ct(&case.join(format!("steps/{:02}.ct", stage - 1)), &p)?;
        let key = EvaluationKey::from_bytes(&read(&case.join("evaluation.key"), 16 << 20)?, &p)?;
        let shift = if stage <= 9 {
            Some(SHIFTS[stage - 1])
        } else {
            None
        };
        let (exp, ct_level, ksk_level, log_base, c0, c1) = key.vfhe_public_rotation_parts(shift)?;
        assert_eq!(exp, EXPONENTS[stage - 1]);
        assert_eq!((ct_level, ksk_level, log_base), (0, 0, 0));
        assert_eq!((c0.len(), c1.len()), (4, 4));
        let permutation = &plan.stages[stage - 1].permutation;
        assert_eq!(exp, plan.stages[stage - 1].exponent);
        let sub0 = coeff(&prev[0])
            .iter()
            .map(|r| permutation.iter().map(|j| r[*j]).collect::<Vec<u64>>())
            .collect::<Vec<_>>();
        let prior1 = coeff(&prev[1]);
        let permuted = prior1
            .iter()
            .flat_map(|r| permutation.iter().map(|j| r[*j]))
            .collect::<Vec<u64>>();
        let mut sub1 = Poly::try_convert_from(
            Array2::from_shape_vec((4, N), permuted)?,
            p.context_at_level(0)?,
            true,
            Representation::Ntt,
        )?;
        sub1.change_representation(Representation::PowerBasis);
        let power = coeff(&sub1);
        let ctx = p.context_at_level(0)?;
        for i in 0..4 {
            // Public residue selection/lift and NTT. No secret decomposition or
            // multiplication is hidden in this verifier boundary.
            let values: Vec<u64> = Q
                .iter()
                .flat_map(|q| power[i].iter().map(move |x| x % q))
                .collect();
            let a = Array2::from_shape_vec((4, N), values)?;
            let mut lift = Poly::try_convert_from(a, ctx, true, Representation::PowerBasis)?;
            lift.change_representation(Representation::Ntt);
            d[i] = coeff(&lift)[prime].clone();
            k0[i] = coeff(&c0[i])[prime].clone();
            k1[i] = coeff(&c1[i])[prime].clone();
        }
        let prior0 = coeff(&prev[0]);
        add0 = (0..N)
            .map(|k| {
                ((prior0[prime][k] as u128 + sub0[prime][k] as u128) % Q[prime] as u128) as u64
            })
            .collect();
        add1 = coeff(&prev[1])[prime].clone();
    }
    let o0 = coeff(&out[0])[prime].clone();
    let o1 = coeff(&out[1])[prime].clone();
    for word in d
        .iter()
        .chain(k0.iter())
        .chain(k1.iter())
        .chain([&add0, &add1, &o0, &o1])
    {
        assert_eq!(word.len(), N);
        assert!(word.iter().all(|x| *x < Q[prime]));
    }
    let mut result = Vec::with_capacity(ROWS);
    for k in half * ROWS..(half + 1) * ROWS {
        let mut row = vec![(stage * 4 * N + prime * N + k) as u32];
        for word in d
            .iter()
            .chain(k0.iter())
            .chain(k1.iter())
            .chain([&add0, &add1, &o0, &o1])
        {
            for digit in 0..6 {
                row.push(((word[k] >> (9 * digit)) & 511) as u32);
            }
        }
        assert_eq!(row.len(), ARITY);
        result.push(row);
    }
    Ok(result)
}
fn import(
    plan_path: &Path,
    model: &Path,
    q: &Path,
    key: &Path,
    dot: &Path,
    kernel: &Path,
    out: &Path,
) -> Result<()> {
    linear_plan(plan_path)?;
    fs::create_dir(out)?;
    fs::create_dir(out.join("steps"))?;
    fs::create_dir(out.join("rows"))?;
    let timer = Instant::now();
    for (src, name, max) in [
        (model, "model.ct", 2 << 20),
        (q, "query.json", 1 << 20),
        (key, "evaluation.key", 16 << 20),
        (dot, "expected_dot.ct", 2 << 20),
        (kernel, "expected_kernel.ct", 2 << 20),
    ] {
        fs::write(out.join(name), read(src, max)?)?;
    }
    let p = params()?;
    let (_, model) = ct(&out.join("model.ct"), &p)?;
    let (_, pt, _) = query(&out.join("query.json"), &p)?;
    let ek = EvaluationKey::from_bytes(&read(&out.join("evaluation.key"), 16 << 20)?, &p)?;
    let mut current = canonical(&model * &pt, &p)?;
    fs::write(out.join("steps/00.ct"), current.to_bytes())?;
    let mut key_meta = Vec::new();
    for i in 0..10 {
        let shift = if i < 9 { Some(SHIFTS[i]) } else { None };
        let (exp, cl, kl, lb, c0, c1) = ek.vfhe_public_rotation_parts(shift)?;
        assert_eq!(exp, EXPONENTS[i]);
        assert_eq!((cl, kl, lb), (0, 0, 0));
        assert_eq!((c0.len(), c1.len()), (4, 4));
        let rot = if let Some(s) = shift {
            ek.rotates_columns_by(&current, s)?
        } else {
            ek.rotates_rows(&current)?
        };
        current += &rot;
        current = canonical(current, &p)?;
        fs::write(
            out.join(format!("steps/{:02}.ct", i + 1)),
            current.to_bytes(),
        )?;
        key_meta.push(json!({"stage":i+1,"shift":shift,"exponent":exp,"ciphertext_level":cl,"key_level":kl,"log_base":lb,"public_polynomials_per_component":4}));
    }
    assert_eq!(
        current.to_bytes(),
        read(&out.join("expected_dot.ct"), 2 << 20)?
    );
    let mut chunks = Vec::new();
    for i in 0..CHUNKS {
        let name = format!("rows/{i:03}.json");
        let r = rows(out, i, plan_path)?;
        save(&out.join(&name), &json!(r))?;
        chunks.push(json!({"index":i,"stage":i/8,"prime_index":i%8/2,"rows":ROWS,"first_row":i*ROWS,"end_row_exclusive":(i+1)*ROWS,"path":name,"sha256":hash(&fs::read(out.join(&name))?)}));
    }
    let report = json!({"claim":"EXECUTED complete saved packed dot/reduction public export","N":N,"moduli":Q,"t":T,"stages":11,"chunks":chunks,"public_arity":ARITY,"mac_tuple_rows":11*4*N,"output_residues":2*11*4*N,"full_native_dot_bytes_match":true,"key_branches":key_meta,"binding":binding(out, plan_path)?,"private_files_read":0,"square_reexecuted":false,"elapsed_ns":timer.elapsed().as_nanos(),"verifier_tcb":"Public SIMD encoder, canonical residue selection/lift, NTT/permutation and affine additions, public key decoder/seed expansion. Generated proof enforces all products and switching sums."});
    save(&out.join("operation.json"), &report)?;
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
    plan_path: &Path,
    index: usize,
    template: &Path,
    case: &Path,
    trace_file: &Path,
    out: &Path,
) -> Result<()> {
    fs::create_dir(out)?;
    let public_rows = rows(case, index, plan_path)?;
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
    let report = json!({"verified":true,"index":index,"stage":index/8,"prime_index":index%8/2,"rows":ROWS,"first_row":index*ROWS,"end_row_exclusive":(index+1)*ROWS,"arity":ARITY,"width":width,"binding":binding(case, plan_path)?,"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"template_sha256":hash(&read(template,32<<20)?),"backend":Backend::BACKEND_ID,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"prove_ns":prove_ns,"self_verify_ns":self_verify_ns});
    save(&out.join("proof.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn verify(
    plan_path: &Path,
    index: usize,
    template: &Path,
    case: &Path,
    proof_file: &Path,
) -> Result<()> {
    let public_rows = rows(case, index, plan_path)?;
    let s = statement(template, public_rows.clone())?;
    let bytes = read(proof_file, 256 << 20)?;
    let (proof, tail): (Proof, &[u8]) = postcard::take_from_bytes(&bytes)?;
    assert!(tail.is_empty());
    let timer = Instant::now();
    Backend::verify(&s, &proof)?;
    println!(
        "{}",
        json!({"verified":true,"index":index,"stage":index/8,"prime_index":index%8/2,"rows":ROWS,"first_row":index*ROWS,"end_row_exclusive":(index+1)*ROWS,"binding":binding(case, plan_path)?,"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"template_sha256":hash(&read(template,32<<20)?),"proof_sha256":hash(&bytes),"verify_ns":timer.elapsed().as_nanos()})
    );
    Ok(())
}
fn main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(String::as_str){
 Some("import") if a.len()==9=>import(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),Path::new(&a[5]),Path::new(&a[6]),Path::new(&a[7]),Path::new(&a[8])),
 Some("prove") if a.len()==8=>prove(Path::new(&a[2]),a[3].parse()?,Path::new(&a[4]),Path::new(&a[5]),Path::new(&a[6]),Path::new(&a[7])),
 Some("verify") if a.len()==7=>verify(Path::new(&a[2]),a[3].parse()?,Path::new(&a[4]),Path::new(&a[5]),Path::new(&a[6])),
 _=>Err("usage: import LINEAR_PLAN MODEL QUERY EVALKEY DOT KERNEL NEW_CASE | prove LINEAR_PLAN INDEX TEMPLATE CASE TRACE NEW_PROOF | verify LINEAR_PLAN INDEX TEMPLATE CASE PROOF".into())}
}
