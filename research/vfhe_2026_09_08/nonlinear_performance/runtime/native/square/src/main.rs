//! Public full-square phase binding and generic generated-relation proof calls.
//! No rescale equations or witness arithmetic are written in Rust.
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, TableSem, UMemBoundaryWitness, parse_vm_descriptor2,
};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriWitness,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use fhe::bfv::{BfvParametersBuilder, Ciphertext};
use fhe_math::rq::traits::TryConvertFrom;
use fhe_math::{
    rns::{RnsContext, RnsScaler, ScalingFactor},
    rq::{Context, Poly, Representation, scaler::Scaler},
};
use fhe_traits::{DeserializeParametrized, Serialize};
use ndarray::Array2;
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{error::Error, fs, io::Read, path::Path, sync::Arc, time::Instant};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;

type Result<T> = std::result::Result<T, Box<dyn Error>>;
type Proof = <Backend as DescriptorProofVerifier>::Proof;

const DEGREE: usize = 8192;
const COMPONENTS: usize = 3;
const CHUNK_ROWS: usize = 4096;

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

type Tensor = Vec<Vec<Vec<u64>>>;
fn coefficients(p: &Poly) -> Vec<Vec<u64>> {
    p.coefficients().outer_iter().map(|r| r.to_vec()).collect()
}
fn params() -> Result<Arc<fhe::bfv::BfvParameters>> {
    Ok(BfvParametersBuilder::new()
        .set_degree(DEGREE)
        .set_plaintext_modulus(4294475777)
        .set_moduli(&BASE)
        .set_variance(10)
        .build_arc()?)
}
fn poly_from(v: &[Vec<u64>], ctx: &Arc<Context>) -> Result<Poly> {
    assert_eq!(v.len(), ctx.moduli().len());
    for (row, q) in v.iter().zip(ctx.moduli()) {
        assert_eq!(row.len(), DEGREE);
        assert!(row.iter().all(|x| x < q));
    }
    let a = Array2::from_shape_vec((v.len(), DEGREE), v.iter().flatten().copied().collect())?;
    Ok(Poly::try_convert_from(
        a,
        ctx,
        true,
        Representation::PowerBasis,
    )?)
}
fn to_ntt(t: &Tensor, ctx: &Arc<Context>) -> Result<Tensor> {
    t.iter()
        .map(|v| {
            let mut p = poly_from(v, ctx)?;
            p.change_representation(Representation::Ntt);
            Ok(coefficients(&p))
        })
        .collect()
}
struct Joint {
    capture: Capture,
    input_power: Tensor,
    extension_power: Tensor,
    extension_ntt: Tensor,
    product_ntt: Tensor,
}
fn load_joint(case: &Path) -> Result<Joint> {
    let capture = read_case(case)?;
    let p = params()?;
    let ct = Ciphertext::from_bytes(&capped(&case.join("basic.dot.ct"), 16 << 20)?, &p)?;
    assert_eq!(ct.len(), 2);
    let input_power = ct
        .iter()
        .map(|v| {
            let mut v = v.clone();
            v.change_representation(Representation::PowerBasis);
            coefficients(&v)
        })
        .collect::<Tensor>();
    let extension_power: Tensor =
        serde_json::from_slice(&capped(&case.join("extension_power.json"), 16 << 20)?)?;
    assert_eq!(extension_power.len(), 2);
    let ctx = Context::new_arc(&EXTENDED, DEGREE)?;
    let extension_ntt = to_ntt(&extension_power, &ctx)?;
    // The first four moduli are copied by the deployed is_one scaler.
    // Both equalities are explicit public verifier checks, in addition to
    // the generated extension relation's PowerBasis copy constraints.
    for component in 0..2 {
        assert_eq!(
            &extension_power[component][..4],
            input_power[component].as_slice()
        );
        assert_eq!(
            &extension_ntt[component][..4],
            coefficients(&ct[component]).as_slice()
        );
    }
    // These public linear transforms bind the tensor proof's NTT outputs to
    // exactly the PowerBasis inputs used by the existing rescale proofs.
    // No scaler or ciphertext product is executed in this verifier path.
    let product_ntt = to_ntt(&capture.product_extended_power_basis, &ctx)?;
    Ok(Joint {
        capture,
        input_power,
        extension_power,
        extension_ntt,
        product_ntt,
    })
}
#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Extension,
    Tensor,
}
impl Kind {
    fn parse(s: &str) -> Result<Self> {
        match s {
            "extension" => Ok(Self::Extension),
            "tensor" => Ok(Self::Tensor),
            _ => Err("kind must be extension or tensor".into()),
        }
    }
    fn name(self) -> &'static str {
        match self {
            Self::Extension => "extension",
            Self::Tensor => "tensor",
        }
    }
    fn arity(self) -> usize {
        match self {
            Self::Extension => 84,
            Self::Tensor => 56,
        }
    }
    fn count(self) -> usize {
        match self {
            Self::Extension => 4,
            Self::Tensor => 18,
        }
    }
}
fn digits(row: &mut Vec<u32>, x: u64, bits: usize, n: usize) {
    assert!(bits * n >= 64 || x < (1u64 << (bits * n)));
    for j in 0..n {
        let shift = j * bits;
        row.push(if shift >= 64 {
            0
        } else {
            ((x >> shift) & ((1u64 << bits) - 1)) as u32
        });
    }
}
fn rows(j: &Joint, kind: Kind, index: usize) -> Vec<Vec<u32>> {
    assert!(index < kind.count());
    (index * CHUNK_ROWS..(index + 1) * CHUNK_ROWS)
        .map(|id| {
            let mut r = vec![id as u32];
            match kind {
                Kind::Extension => {
                    let c = id / DEGREE;
                    let k = id % DEGREE;
                    for v in &j.input_power[c] {
                        digits(&mut r, v[k], 9, 6);
                    }
                    for (limb, v) in j.extension_power[c].iter().enumerate() {
                        digits(&mut r, v[k], 9, if limb < 4 { 6 } else { 7 });
                    }
                }
                Kind::Tensor => {
                    let prime = id / DEGREE;
                    let k = id % DEGREE;
                    for t in [
                        &j.extension_ntt[0],
                        &j.extension_ntt[1],
                        &j.product_ntt[0],
                        &j.product_ntt[1],
                        &j.product_ntt[2],
                    ] {
                        digits(&mut r, t[prime][k], 6, 11);
                    }
                }
            }
            assert_eq!(r.len(), kind.arity());
            r
        })
        .collect()
}
fn binding(case: &Path, j: &Joint) -> Result<Value> {
    Ok(json!({
        "input_ciphertext_sha256":j.capture.input_dot_sha256,
        "output_ciphertext_sha256":j.capture.output_sha256,
        "source_trace_sha256":hash(&capped(&case.join("basic.json"),32<<20)?),
        "extension_power_sha256":hash(&capped(&case.join("extension_power.json"),16<<20)?),
        "scope":"Exact raw-square phase binding with public parsing and linear NTT transforms in verifier TCB; no scaler/product computation in verification"
    }))
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
        fs::write(out.join(output), capped(&source.join(input), 32 << 20)?)?;
    }
    let capture = read_case(out)?;
    let p = params()?;
    let ct = Ciphertext::from_bytes(&capped(&out.join("basic.dot.ct"), 16 << 20)?, &p)?;
    let ctx = Context::new_arc(&EXTENDED, DEGREE)?;
    let extender = Scaler::new(ct[0].ctx(), &ctx, ScalingFactor::one())?;
    let extended = [ct[0].scale(&extender)?, ct[1].scale(&extender)?];
    let ext_power = extended
        .iter()
        .map(|v| {
            let mut v = v.clone();
            v.change_representation(Representation::PowerBasis);
            coefficients(&v)
        })
        .collect::<Tensor>();
    write_json(&out.join("extension_power.json"), &json!(ext_power))?;
    let j = load_joint(out)?;
    for c in 0..2 {
        assert_eq!(j.extension_ntt[c], coefficients(&extended[c]));
    }
    // One public export control against the native pointwise tensor path;
    // generated arithmetic proofs, rather than this comparison, decide the
    // verification result. The expensive existing rescale is not re-executed.
    let p0 = &extended[0] * &extended[0];
    let mut p1 = &extended[0] * &extended[1];
    p1 += &(&extended[1] * &extended[0]);
    let p2 = &extended[1] * &extended[1];
    for (c, mut product) in [p0, p1, p2].into_iter().enumerate() {
        assert_eq!(coefficients(&product), j.product_ntt[c]);
        product.change_representation(Representation::PowerBasis);
        assert_eq!(
            coefficients(&product),
            capture.product_extended_power_basis[c]
        );
    }
    let from = Arc::new(RnsContext::new(&BASE)?);
    let to = Arc::new(RnsContext::new(&EXTENDED)?);
    let native = RnsScaler::new(&from, &to, ScalingFactor::one());
    write_json(
        &out.join("native_extension_constants.json"),
        &json!({"base":BASE,"extended_base":EXTENDED,"factor":"one","native_RnsScaler_constructor_debug":format!("{native:#?}"),"secret_key_read":false,"random_sampling":false}),
    )?;
    let mut chunks = Vec::new();
    for kind in [Kind::Extension, Kind::Tensor] {
        fs::create_dir(out.join(kind.name()))?;
        for index in 0..kind.count() {
            let name = format!("{}/{index:03}.json", kind.name());
            let v = rows(&j, kind, index);
            write_json(&out.join(&name), &json!(v))?;
            chunks.push(json!({"kind":kind.name(),"index":index,"path":name,"rows":CHUNK_ROWS,"arity":kind.arity(),"first_row":index*CHUNK_ROWS,"end_row_exclusive":(index+1)*CHUNK_ROWS,"prime_index":if kind==Kind::Tensor{Some(index/2)}else{None},"sha256":hash(&fs::read(out.join(&name))?)}));
        }
    }
    let report = json!({"claim":"EXECUTED complete public export for saved ciphertext square","binding":binding(out,&j)?,"N":DEGREE,"base":BASE,"extended_base":EXTENDED,"input_components":2,"output_components":3,"extension_positions":2*DEGREE,"extension_output_residues":2*9*DEGREE,"tensor_rows":9*DEGREE,"tensor_output_residues":3*9*DEGREE,"native_tensor_and_inverse_ntt_match_captured_rescale_inputs":true,"native_extension_ntt_matches_powerbasis_forward_transform":true,"rescale_reexecuted":false,"private_files_read":0,"chunks":chunks,"elapsed_ns":timer.elapsed().as_nanos()});
    write_json(&out.join("operation.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn statement(
    template: &Path,
    public_rows: Vec<Vec<u32>>,
    arity: usize,
) -> Result<DescriptorStatement> {
    let raw = capped(template, 32 << 20)?;
    let mut d = parse_vm_descriptor2(std::str::from_utf8(&raw)?)?;
    assert_eq!(d.public_input_count, 0);
    assert_eq!(d.tables.iter().filter(|t| t.id == 11).count(), 1);
    let t = d
        .tables
        .iter_mut()
        .find(|t| t.id == 11)
        .ok_or("missing table11")?;
    assert_eq!(t.arity, arity);
    assert!(matches!(t.sem, TableSem::ExactPublicRows { .. }));
    t.sem = TableSem::ExactPublicRows { rows: public_rows };
    Ok(DescriptorStatement::try_new(d, vec![])?)
}
fn prove(
    kind: Kind,
    index: usize,
    template: &Path,
    case: &Path,
    trace_file: &Path,
    out: &Path,
) -> Result<()> {
    fs::create_dir(out)?;
    let j = load_joint(case)?;
    let public_rows = rows(&j, kind, index);
    let s = statement(template, public_rows.clone(), kind.arity())?;
    let width = s.descriptor().trace_width;
    assert!((kind.arity()..=100000).contains(&width));
    let expected = CHUNK_ROWS
        .checked_mul(width)
        .and_then(|x| x.checked_mul(4))
        .ok_or("length overflow")?;
    let encoded = capped(trace_file, expected)?;
    assert_eq!(encoded.len(), expected);
    let mut trace = Vec::with_capacity(CHUNK_ROWS);
    for (row, pubrow) in encoded.chunks_exact(width * 4).zip(&public_rows) {
        let row: Vec<u32> = row
            .chunks_exact(4)
            .map(|x| u32::from_le_bytes(x.try_into().unwrap()))
            .collect();
        assert_eq!(&row[..kind.arity()], pubrow);
        assert!(row.iter().all(|x| *x < BABYBEAR_P));
        trace.push(row.into_iter().map(BabyBear::new).collect::<Vec<_>>());
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
    let report = json!({"verified":true,"kind":kind.name(),"index":index,"rows":CHUNK_ROWS,"first_row":index*CHUNK_ROWS,"end_row_exclusive":(index+1)*CHUNK_ROWS,"arity":kind.arity(),"width":width,"binding":binding(case,&j)?,"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"template_sha256":hash(&capped(template,32<<20)?),"backend":Backend::BACKEND_ID,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"prove_ns":prove_ns,"self_verify_ns":self_verify_ns});
    write_json(&out.join("proof.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn verify(kind: Kind, index: usize, template: &Path, case: &Path, proof_file: &Path) -> Result<()> {
    let j = load_joint(case)?;
    let public_rows = rows(&j, kind, index);
    let s = statement(template, public_rows.clone(), kind.arity())?;
    let bytes = capped(proof_file, 256 << 20)?;
    let (proof, tail): (Proof, &[u8]) = postcard::take_from_bytes(&bytes)?;
    assert!(tail.is_empty());
    let timer = Instant::now();
    Backend::verify(&s, &proof)?;
    let verify_ns = timer.elapsed().as_nanos();
    println!(
        "{}",
        json!({"verified":true,"kind":kind.name(),"index":index,"rows":CHUNK_ROWS,"first_row":index*CHUNK_ROWS,"end_row_exclusive":(index+1)*CHUNK_ROWS,"binding":binding(case,&j)?,"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"template_sha256":hash(&capped(template,32<<20)?),"proof_sha256":hash(&bytes),"verify_ns":verify_ns})
    );
    Ok(())
}
fn main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(String::as_str){
        Some("import") if a.len()==4=>import(Path::new(&a[2]),Path::new(&a[3])),
        Some("prove") if a.len()==8=>prove(Kind::parse(&a[2])?,a[3].parse()?,Path::new(&a[4]),Path::new(&a[5]),Path::new(&a[6]),Path::new(&a[7])),
        Some("verify") if a.len()==7=>verify(Kind::parse(&a[2])?,a[3].parse()?,Path::new(&a[4]),Path::new(&a[5]),Path::new(&a[6])),
        _=>Err("usage: import PUBLIC_SOURCE NEW_CASE | prove KIND INDEX TEMPLATE CASE TRACE NEW_PROOF | verify KIND INDEX TEMPLATE CASE PROOF".into())
    }
}
