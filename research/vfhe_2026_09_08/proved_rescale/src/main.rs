//! Actual small BFV multiplication, complete public rescale inputs, generic proof.
//! No arithmetic constraints or witness generation are authored in Rust.
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2,MemBoundaryWitness,TableSem,UMemBoundaryWitness};
use dregg_circuit::descriptor_proof_backend::{DescriptorProofProver,DescriptorProofVerifier,DescriptorStatement,Plonky3HidingFriWitness};
use dregg_circuit::field::{BabyBear,BABYBEAR_P};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;
use fhe::bfv::{BfvParameters,BfvParametersBuilder,Ciphertext,Encoding,Multiplicator,Plaintext,PublicKey,SecretKey};
use fhe_math::{rns::ScalingFactor,rq::{scaler::Scaler,Context,Poly,Representation}};
use fhe_traits::{DeserializeParametrized,DeserializeWithContext,FheEncoder,FheEncrypter,FheDecoder,FheDecrypter,Serialize};
use num_bigint::BigUint;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::{json,Value};
use sha2::{Digest,Sha256};
use std::{error::Error,fs,path::Path,sync::Arc,time::Instant};

type Result<T>=std::result::Result<T,Box<dyn Error>>;
type Proof=<Backend as DescriptorProofVerifier>::Proof;
const Q:[u64;3]=[68719403009,68719230977,137438822401];
const EXT:[u64;6]=[68719403009,68719230977,137438822401,4611686018427322369,4611686018427289601,4611686018427215873];
const N:usize=8;
const T:u64=1032193;
const PUBLIC_WIDTH:usize=88;
fn hash(b:&[u8])->String {format!("{:x}",Sha256::digest(b))}
fn write_json(p:&Path,v:&Value)->Result<()> {fs::write(p,serde_json::to_vec(v)?)?;Ok(())}
fn params()->Result<Arc<BfvParameters>> {
    let p=BfvParametersBuilder::new().set_degree(N).set_plaintext_modulus(T).set_moduli(&Q).set_variance(10).build_arc()?;
    assert_eq!(p.degree(),N);assert_eq!(p.moduli(),Q);Ok(p)
}
fn power(poly:&Poly)->Poly {let mut p=poly.clone();p.change_representation(Representation::PowerBasis);p}
fn scalar_rows(products:&[Poly],output:&Ciphertext)->Vec<Vec<u32>> {
    assert_eq!(products.len(),3);assert_eq!(output.len(),3);
    let outs:Vec<_>=output.iter().map(power).collect();
    let mut rows=Vec::new();
    for c in 0..3 {for i in 0..N {
        assert_eq!(products[c].representation(),&Representation::PowerBasis);
        let mut row=vec![(c*N+i) as u32];
        for (p,limbs,digits) in [(&products[c],6,11),(&outs[c],3,7)] {
            for l in 0..limbs {
                let value=p.coefficients()[[l,i]];assert!(value<p.ctx().moduli()[l]);
                for d in 0..digits {row.push(if 6*d>=64 {0}else{((value>>(6*d))&63) as u32});}
            }
        }
        assert_eq!(row.len(),PUBLIC_WIDTH);rows.push(row);
    }}
    // IR2 requires a power-of-two main trace. Padding repeats a real relation,
    // with distinct public rowIDs and explicitly recorded source-row aliases.
    while rows.len()<32 {let mut row=rows[23].clone();row[0]=rows.len() as u32;rows.push(row);}
    rows
}
fn load_rows(case:&Path)->Result<Vec<Vec<u32>>> {
    let p=params()?;let ctx=Context::new_arc(&EXT,N)?;
    let mut products=Vec::new();
    for c in 0..3 {
        let b=fs::read(case.join(format!("product-{c}.poly")))?;
        let poly=Poly::from_bytes(&b,&ctx)?;assert_eq!(poly.to_bytes(),b);products.push(poly);
    }
    let b=fs::read(case.join("output.ct"))?;let out=Ciphertext::from_bytes(&b,&p)?;assert_eq!(out.to_bytes(),b);
    Ok(scalar_rows(&products,&out))
}
fn generate(dir:&Path)->Result<()> {
    fs::create_dir(dir)?;let started=Instant::now();let p=params()?;
    let mut rng=ChaCha20Rng::from_os_rng();let sk=SecretKey::random(&p,&mut rng);let pk=PublicKey::new(&sk,&mut rng);
    let av:Vec<u64>=(1..=8).collect();let bv:Vec<u64>=(1..=8).rev().collect();
    let a:Ciphertext=pk.try_encrypt(&Plaintext::try_encode(&av,Encoding::poly(),&p)?,&mut rng)?;
    let b:Ciphertext=pk.try_encrypt(&Plaintext::try_encode(&bv,Encoding::poly(),&p)?,&mut rng)?;
    let q:BigUint=Q.iter().map(|&x|BigUint::from(x)).product();
    let factor=ScalingFactor::new(&BigUint::from(T),&q);
    let mul=Multiplicator::new(ScalingFactor::one(),ScalingFactor::one(),&EXT,factor.clone(),&p)?;
    let timer=Instant::now();let output=mul.multiply(&a,&b)?;let multiply_ns=timer.elapsed().as_nanos();
    assert_eq!(output.len(),3);
    // Reconstruct the exact public intermediate with the same library operators
    // as Multiplicator. Its provenance from a,b is outside the rescale proof.
    let ctx=Context::new_arc(&EXT,N)?;let up=Scaler::new(a[0].ctx(),&ctx,ScalingFactor::one())?;
    let ae=[a[0].scale(&up)?,a[1].scale(&up)?];let be=[b[0].scale(&up)?,b[1].scale(&up)?];
    let p0=&ae[0]*&be[0];let mut p1=&ae[0]*&be[1];p1+=&(&ae[1]*&be[0]);let p2=&ae[1]*&be[1];
    let products:Vec<_>=[p0,p1,p2].iter().map(power).collect();
    let down=Scaler::new(&ctx,p.context_at_level(0)?,factor)?;
    for c in 0..3 {assert_eq!(power(&products[c].scale(&down)?).coefficients(),power(&output[c]).coefficients());}
    let decoded=Vec::<u64>::try_decode(&sk.try_decrypt(&output)?,Encoding::poly())?;
    let mut expected=vec![0i64;N];
    for i in 0..N {for j in 0..N {let sign=if i+j<N {1}else{-1};expected[(i+j)%N]+=sign*(av[i]*bv[j]) as i64;}}
    let expected:Vec<u64>=expected.iter().map(|v|v.rem_euclid(T as i64) as u64).collect();assert_eq!(decoded,expected);
    let mut files=Vec::new();
    for (name,bytes) in [("a.ct",a.to_bytes()),("b.ct",b.to_bytes()),("output.ct",output.to_bytes()),("public_key.bin",pk.to_bytes())] {
        files.push(json!({"name":name,"bytes":bytes.len(),"sha256":hash(&bytes)}));fs::write(dir.join(name),bytes)?;
    }
    for (c,poly) in products.iter().enumerate() {
        let name=format!("product-{c}.poly");let bytes=poly.to_bytes();
        files.push(json!({"name":name,"bytes":bytes.len(),"sha256":hash(&bytes)}));fs::write(dir.join(name),bytes)?;
    }
    let rows=scalar_rows(&products,&output);write_json(&dir.join("public_rows.json"),&json!(rows))?;
    let report=json!({"claim":"EXECUTED actual BFV ct*ct and complete rescale data at a small arithmetic-only degree","degree":N,"base_moduli":Q,"extended_moduli":EXT,"plaintext_modulus":T,"input_components":2,"output_components":3,"actual_rescale_positions":24,"output_residue_equations":72,"proof_rows":32,"public_tuple_width":PUBLIC_WIDTH,"padding":{"rows":[24,25,26,27,28,29,30,31],"source_row":23},"relinearization":false,"modulus_switch":false,"multiply_ns":multiply_ns,"total_ns":started.elapsed().as_nanos(),"all_output_plaintext_coefficients_match":true,"expected_plaintext":expected,"public_intermediate_downscale_matches_all_output_residues":true,"files":files,"secret_key_saved":false,"scope":"Whole small rescale step. RNS extension and convolution provenance from a,b to product are executed source-based reconstruction, not covered by the rescale relation. Degree8 is not a secure FHE parameter."});
    write_json(&dir.join("operation.json"),&report)?;println!("{report}");Ok(())
}
fn statement(template:&Path,rows:Vec<Vec<u32>>)->Result<DescriptorStatement> {
    let mut d=parse_vm_descriptor2(&fs::read_to_string(template)?)?;
    assert_eq!(d.public_input_count,0);assert_eq!(d.tables.iter().filter(|t|t.id==11).count(),1);
    let t=d.tables.iter_mut().find(|t|t.id==11).ok_or("missing public table")?;
    assert_eq!(t.arity,PUBLIC_WIDTH);assert!(matches!(t.sem,TableSem::ExactPublicRows{..}));t.sem=TableSem::ExactPublicRows{rows};
    Ok(DescriptorStatement::try_new(d,vec![])? )
}
fn prove(template:&Path,case:&Path,trace_file:&Path,out:&Path)->Result<()> {
    fs::create_dir(out)?;let rows=load_rows(case)?;let statement=statement(template,rows.clone())?;
    let width=statement.descriptor().trace_width;assert!(width>=PUBLIC_WIDTH);
    let bytes=fs::read(trace_file)?;assert_eq!(bytes.len(),rows.len()*width*4);
    let raw:Vec<Vec<u32>>=bytes.chunks_exact(width*4).map(|r|r.chunks_exact(4).map(|v|u32::from_le_bytes(v.try_into().unwrap())).collect()).collect();
    assert!(raw.iter().zip(&rows).all(|(r,p)|&r[..PUBLIC_WIDTH]==p.as_slice()&&r.iter().all(|v|*v<BABYBEAR_P)));
    let trace:Vec<Vec<BabyBear>>=raw.into_iter().map(|r|r.into_iter().map(BabyBear::new).collect()).collect();
    let mem=MemBoundaryWitness::default();let umem=UMemBoundaryWitness::default();
    let w=Plonky3HidingFriWitness{base_trace:&trace,mem_boundary:&mem,map_heaps:&[],umem_boundary:&umem};
    let timer=Instant::now();let proof=Backend::prove(&statement,w)?;let prove_ns=timer.elapsed().as_nanos();
    let encoded=postcard::to_allocvec(&proof)?;fs::write(out.join("proof.bin"),&encoded)?;
    let timer=Instant::now();Backend::verify(&statement,&proof)?;let verify_ns=timer.elapsed().as_nanos();
    let report=json!({"claim":"EXECUTED complete small BFV rescale proof over Lean-generated relation","backend":Backend::BACKEND_ID,"actual_positions":24,"proof_rows":32,"trace_width":width,"public_tuple_width":PUBLIC_WIDTH,"proof_bytes":encoded.len(),"proof_sha256":hash(&encoded),"template_sha256":hash(&fs::read(template)?),"prove_ns":prove_ns,"self_verify_ns":verify_ns,"verified":true});
    write_json(&out.join("proof.json"),&report)?;println!("{report}");Ok(())
}
fn verify(template:&Path,case:&Path,proof_file:&Path,mutate:bool)->Result<()> {
    let mut rows=load_rows(case)?;if mutate {rows[0][67]^=1;}
    let s=statement(template,rows)?;let bytes=fs::read(proof_file)?;
    let (proof,tail):(Proof,&[u8])=postcard::take_from_bytes(&bytes)?;assert!(tail.is_empty());
    let timer=Instant::now();let result=Backend::verify(&s,&proof);let ns=timer.elapsed().as_nanos();
    if mutate {assert!(result.is_err(),"changed output accepted");}else{result?;}
    println!("{}",json!({"claim":"EXECUTED fresh-process verification","verified":!mutate,"changed_output_rejected":mutate,"verify_ns":ns,"proof_sha256":hash(&bytes)}));Ok(())
}
fn main()->Result<()> {
    let a:Vec<String>=std::env::args().collect();match a.get(1).map(String::as_str) {
        Some("generate")if a.len()==3=>generate(Path::new(&a[2])),
        Some("prove")if a.len()==6=>prove(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),Path::new(&a[5])),
        Some("verify"|"verify-changed-output")if a.len()==5=>verify(Path::new(&a[2]),Path::new(&a[3]),Path::new(&a[4]),a[1].contains("changed")),
        _=>Err("usage: generate DIR | prove TEMPLATE CASE TRACE OUT | verify[-changed-output] TEMPLATE CASE PROOF".into())
    }
}
