//! Exact public query codec/export and calls into a generated joined relation.
//! AIR and witness arithmetic belong to the Lean query_arithmetic compiler.
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, TableSem, UMemBoundaryWitness, parse_vm_descriptor2,
};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriWitness,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use fhe::bfv::{BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, Plaintext};
use fhe_math::rq::{Poly, Representation, traits::TryConvertFrom};
use fhe_traits::{DeserializeParametrized, FheEncoder, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{error::Error, fs, io::Read, path::Path, sync::Arc, time::Instant};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;
type Result<T> = std::result::Result<T, Box<dyn Error>>;
type Proof = <Backend as DescriptorProofVerifier>::Proof;
const N: usize = 4096;
const ROWS: usize = 8192;
const WIDTH: usize = 57;
const T: u64 = 4294828033;
const Q: [u64; 2] = [2199023190017, 4398046486529];
const PARAM_ID: &str = "fb16ccd74dd4b7bedb6673b369b56475af06f9415a4faf4645d411d3c7d0cda3";
fn hash(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn json_file(p: &Path, v: &Value) -> Result<()> {
    fs::write(p, serde_json::to_vec(v)?)?;
    Ok(())
}
fn capped(p: &Path, cap: usize) -> Result<Vec<u8>> {
    let f = fs::File::open(p)?;
    if f.metadata()?.len() > cap as u64 {
        return Err("file exceeds cap".into());
    }
    let mut b = Vec::new();
    f.take((cap + 1) as u64).read_to_end(&mut b)?;
    if b.len() > cap {
        return Err("file exceeds cap".into());
    }
    Ok(b)
}
fn parameters() -> Result<Arc<BfvParameters>> {
    let p = BfvParametersBuilder::new()
        .set_degree(N)
        .set_plaintext_modulus(T)
        .set_moduli(&Q)
        .set_variance(10)
        .build_arc()?;
    assert_eq!(p.moduli(), Q);
    Ok(p)
}
fn canonical(ct: Ciphertext, p: &Arc<BfvParameters>) -> Result<Ciphertext> {
    assert_eq!(ct.len(), 2);
    assert!(
        ct.iter()
            .all(|c| p.level_of_context(c.ctx()).ok() == Some(0)
                && c.representation() == &Representation::Ntt)
    );
    let mut c = Ciphertext::new(ct.iter().cloned().collect(), p)?;
    for poly in c.iter_mut() {
        unsafe {
            poly.allow_variable_time_computations();
        }
    }
    Ok(c)
}
fn ciphertext(path: &Path, p: &Arc<BfvParameters>) -> Result<(Vec<u8>, Ciphertext)> {
    let b = capped(path, 200_000)?;
    assert_eq!(b.len(), 85103);
    assert_eq!(&b[..8], b"RSBFV001");
    assert_eq!(b[8], 1);
    assert_eq!(
        b[9..41]
            .iter()
            .map(|x| format!("{x:02x}"))
            .collect::<String>(),
        PARAM_ID
    );
    assert_eq!(u64::from_le_bytes(b[73..81].try_into().unwrap()), 85022);
    let c = canonical(Ciphertext::from_bytes(&b[81..], p)?, p)?;
    assert_eq!(c.to_bytes(), b[81..]);
    Ok((b, c))
}
fn query(path: &Path) -> Result<(Vec<u8>, Vec<i64>)> {
    let b = capped(path, 20_000)?;
    let v: Value = serde_json::from_slice(&b)?;
    assert_eq!(v.as_object().ok_or("query must be object")?.len(), 3);
    assert_eq!(v["schema"], "resident-public-query-v1");
    assert_eq!(v["params_id"], PARAM_ID);
    let q = v["coefficients"]
        .as_array()
        .ok_or("query coefficients must be array")?;
    assert_eq!(q.len(), 577);
    let q = q
        .iter()
        .map(|x| {
            x.as_i64()
                .filter(|x| (-127..=127).contains(x))
                .ok_or("query coefficient must be bounded integer")
        })
        .collect::<std::result::Result<Vec<_>, _>>()?;
    assert_eq!(
        serde_json::to_vec(
            &json!({"schema":"resident-public-query-v1","params_id":PARAM_ID,"coefficients":q})
        )?,
        b
    );
    Ok((b, q))
}
fn coeff(poly: &Poly) -> Vec<Vec<u64>> {
    assert_eq!(poly.representation(), &Representation::Ntt);
    let r: Vec<Vec<u64>> = poly
        .coefficients()
        .outer_iter()
        .map(|r| r.to_vec())
        .collect();
    assert_eq!(r.len(), 2);
    assert!(
        r.iter()
            .zip(Q)
            .all(|(r, q)| r.len() == N && r.iter().all(|v| *v < q))
    );
    r
}
fn ct_coeff(c: &Ciphertext) -> Vec<Vec<Vec<u64>>> {
    c.iter().map(coeff).collect()
}
struct Case {
    p: Arc<BfvParameters>,
    acc: Ciphertext,
    out: Ciphertext,
    pp: Plaintext,
    pm: Plaintext,
    pp_poly: Poly,
    pm_poly: Poly,
    acc_bytes: Vec<u8>,
    out_bytes: Vec<u8>,
    query_bytes: Vec<u8>,
}
fn read_case(dir: &Path) -> Result<Case> {
    let p = parameters()?;
    let (ab, acc) = ciphertext(&dir.join("acc.ct"), &p)?;
    let (ob, out) = ciphertext(&dir.join("out.ct"), &p)?;
    assert_eq!(&ab[41..73], &ob[41..73]);
    let (qb, q) = query(&dir.join("query.json"))?;
    let plus: Vec<u64> = q.iter().rev().map(|x| (*x).max(0) as u64).collect();
    let minus: Vec<u64> = q.iter().rev().map(|x| (-*x).max(0) as u64).collect();
    let pp = Plaintext::try_encode(&plus, Encoding::poly(), &p)?;
    let pm = Plaintext::try_encode(&minus, Encoding::poly(), &p)?;
    // Public TryConvertFrom exports encoded coefficients. The same library NTT
    // produces the plaintext multipliers used by native MulAssign<&Plaintext>.
    let ctx = p.context_at_level(0)?;
    let mut pp_poly = Poly::try_convert_from(&pp, ctx, false, Representation::PowerBasis)?;
    pp_poly.change_representation(Representation::Ntt);
    let mut pm_poly = Poly::try_convert_from(&pm, ctx, false, Representation::PowerBasis)?;
    pm_poly.change_representation(Representation::Ntt);
    Ok(Case {
        p,
        acc,
        out,
        pp,
        pm,
        pp_poly,
        pm_poly,
        acc_bytes: ab,
        out_bytes: ob,
        query_bytes: qb,
    })
}
fn rows(c: &Case) -> Vec<Vec<u32>> {
    let a = ct_coeff(&c.acc);
    let o = ct_coeff(&c.out);
    let pp = coeff(&c.pp_poly);
    let pm = coeff(&c.pm_poly);
    (0..ROWS)
        .map(|id| {
            let mut row = vec![id as u32];
            for values in [&a[id / N], &pp, &pm, &o[id / N]] {
                for limb in 0..2 {
                    let v = values[limb][id % N];
                    for d in 0..7 {
                        row.push(((v >> (6 * d)) & 63) as u32);
                    }
                }
            }
            assert_eq!(row.len(), WIDTH);
            row
        })
        .collect()
}
fn export(acc: &Path, query: &Path, out: &Path, dest: &Path) -> Result<()> {
    fs::create_dir(dest)?;
    for (src, name) in [(acc, "acc.ct"), (query, "query.json"), (out, "out.ct")] {
        fs::write(dest.join(name), capped(src, 200_000)?)?;
    }
    let timer = Instant::now();
    let c = read_case(dest)?;
    let public_rows = rows(&c);
    json_file(&dest.join("public_rows.json"), &json!(public_rows))?;
    let plus = &c.acc * &c.pp;
    let minus = &c.acc * &c.pm;
    let replay = canonical(&plus - &minus, &c.p)?;
    assert_eq!(replay.to_bytes(), c.out.to_bytes());
    let a = ct_coeff(&c.acc);
    let pp = coeff(&c.pp_poly);
    let pm = coeff(&c.pm_poly);
    let products = [ct_coeff(&plus), ct_coeff(&minus)];
    for component in 0..2 {
        for limb in 0..2 {
            for i in 0..N {
                for sign in 0..2 {
                    let b = if sign == 0 { pp[limb][i] } else { pm[limb][i] };
                    assert_eq!(
                        (a[component][limb][i] as u128 * b as u128 % Q[limb] as u128) as u64,
                        products[sign][component][limb][i]
                    );
                }
            }
        }
    }
    json_file(
        &dest.join("actual_products.json"),
        &json!({"order":"sign(plus,minus),component,prime,NTT coefficient","values":products}),
    )?;
    fs::write(dest.join("positive.poly"), c.pp_poly.to_bytes())?;
    fs::write(dest.join("negative.poly"), c.pm_poly.to_bytes())?;
    let report = json!({"claim":"EXECUTED whole public query arithmetic export and native replay","degree":N,"components":2,"ciphertext_moduli":Q,"plaintext_modulus":T,"rows":ROWS,"public_tuple_width":WIDTH,"public_order":"rowID,accumulator2x7,positivePT2x7,negativePT2x7,finalout2x7; radix64","native_payload_replay_equal":true,"actual_product_residue_checks":32768,"final_output_residues":16384,"acc_sha256":hash(&c.acc_bytes),"query_sha256":hash(&c.query_bytes),"out_sha256":hash(&c.out_bytes),"public_rows_sha256":hash(&fs::read(dest.join("public_rows.json"))?),"private_files_read":0,"export_ns":timer.elapsed().as_nanos(),"scope":"Public query parsing, plaintext polynomial encoding and NTT are implementation TCB. Generated relation must bind both signed products and final subtraction. No reader/plaintext or authorization proof."});
    json_file(&dest.join("operation.json"), &report)?;
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
    let c = read_case(case)?;
    let public_rows = rows(&c);
    let s = statement(template, public_rows.clone())?;
    let width = s.descriptor().trace_width;
    assert!(width >= WIDTH);
    let encoded = fs::read(trace_file)?;
    assert_eq!(
        encoded.len(),
        ROWS.checked_mul(width)
            .and_then(|x| x.checked_mul(4))
            .ok_or("trace size overflow")?
    );
    let raw: Vec<Vec<u32>> = encoded
        .chunks_exact(width * 4)
        .map(|r| {
            r.chunks_exact(4)
                .map(|v| u32::from_le_bytes(v.try_into().unwrap()))
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
    let proof = Backend::prove(&s, witness)?;
    let prove_ns = timer.elapsed().as_nanos();
    let bytes = postcard::to_allocvec(&proof)?;
    fs::write(out.join("proof.bin"), &bytes)?;
    let timer = Instant::now();
    Backend::verify(&s, &proof)?;
    let verify_ns = timer.elapsed().as_nanos();
    let report = json!({"claim":"EXECUTED generated joined whole query arithmetic proof","backend":Backend::BACKEND_ID,"rows":ROWS,"trace_width":width,"public_tuple_width":WIDTH,"final_output_residues":16384,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"template_sha256":hash(&fs::read(template)?),"public_rows_sha256":hash(&serde_json::to_vec(&public_rows)?),"prove_ns":prove_ns,"self_verify_ns":verify_ns,"verified":true});
    json_file(&out.join("proof.json"), &report)?;
    println!("{report}");
    Ok(())
}
fn verify(template: &Path, case: &Path, proof_file: &Path, mutate: bool) -> Result<()> {
    let c = read_case(case)?;
    let mut public_rows = rows(&c);
    if mutate {
        public_rows[0][43] ^= 1;
    }
    let s = statement(template, public_rows)?;
    let bytes = fs::read(proof_file)?;
    let (proof, tail): (Proof, &[u8]) = postcard::take_from_bytes(&bytes)?;
    assert!(tail.is_empty());
    let timer = Instant::now();
    let result = Backend::verify(&s, &proof);
    let ns = timer.elapsed().as_nanos();
    if mutate {
        assert!(result.is_err(), "changed final output accepted");
    } else {
        result?;
    }
    println!(
        "{}",
        json!({"claim":"EXECUTED fresh-process whole query arithmetic verification","verified":!mutate,"changed_output_rejected":mutate,"verify_ns":ns,"proof_sha256":hash(&bytes),"acc_sha256":hash(&c.acc_bytes),"query_sha256":hash(&c.query_bytes),"out_sha256":hash(&c.out_bytes)})
    );
    Ok(())
}
fn main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(String::as_str){
 Some("export")if a.len()==6=>export(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),Path::new(&a[5])),
 Some("prove")if a.len()==6=>prove(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),Path::new(&a[5])),
 Some("verify"|"verify-changed-output")if a.len()==5=>verify(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),a[1].contains("changed")),
 _=>Err("usage: export ACC QUERY OUT NEW_CASE | prove TEMPLATE CASE TRACE NEW_PROOF | verify[-changed-output] TEMPLATE CASE PROOF".into())}
}
