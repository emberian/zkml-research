//! Existing TFHE public integer operations and shared proof consumer only.
//! All proof constraints and auxiliary witness construction are emitted by Lean.
#[allow(dead_code)] mod prior_rotation;
use std::{fs,path::Path,time::Instant};
use bincode::Options;use serde::{Serialize,de::DeserializeOwned};use serde_json::json;
use sha2::{Digest,Sha256};use tfhe::core_crypto::prelude::*;
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2,MemBoundaryWitness,UMemBoundaryWitness,TableSem};
use dregg_circuit::descriptor_proof_backend::{DescriptorStatement,DescriptorProofProver,DescriptorProofVerifier,Plonky3HidingFriWitness};
use dregg_circuit::field::{BabyBear,BABYBEAR_P};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;
use tfhe::core_crypto::algorithms::polynomial_algorithms::{polynomial_wrapping_monic_monomial_mul,polynomial_wrapping_sub_assign};
type Result<T>=std::result::Result<T,Box<dyn std::error::Error>>;
type Proof=<Backend as DescriptorProofVerifier>::Proof;
fn hash(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn read(path:&Path,max:usize)->Result<Vec<u8>>{assert!(fs::metadata(path)?.len()<=max as u64,"file cap");Ok(fs::read(path)?)}
fn decode<T:DeserializeOwned+Serialize>(path:&Path)->Result<T>{
 let bytes=read(path,1<<20)?;let value:T=bincode::DefaultOptions::new().with_fixint_encoding().reject_trailing_bytes().deserialize(&bytes)?;
 assert_eq!(bincode::serialize(&value)?,bytes,"noncanonical ciphertext bytes");Ok(value)
}
fn proof(bytes:&[u8])->Result<Proof>{let (p,rest):(Proof,&[u8])=postcard::take_from_bytes(bytes)?;assert!(rest.is_empty());Ok(p)}
fn prepare(old:&Path,new:&Path)->Result<()> {
 fs::create_dir(new)?;let mut origins=Vec::new();
 for (src,dst) in [("fixtures/normal_001/initial_lut.ct","initial_lut.ct"),("fixtures/normal_001/body_rotated_lut.ct","body_rotated_lut.ct"),
  ("fixtures/normal_001/pbs_input.ct","pbs_input.ct"),("fixtures/normal_001/prior_rows.json","prior_rows.json"),
  ("fixtures/normal_001/prior_template.json","prior_template.json"),("fixtures/normal_001/prior_proof.bin","prior_proof.bin"),
  ("artifacts/template_ir2.json","rotation_template.json"),("results/proof001/proof.bin","rotation_proof.bin")] {
  let p=old.join(src);let bytes=read(&p,1<<24)?;fs::write(new.join(dst),&bytes)?;
  origins.push(json!({"origin":p,"file":dst,"bytes":bytes.len(),"sha256":hash(&bytes)}));
 }
 let (ct0,a,prefix)=prior_rotation::verified_prefix(new)?;
 let mut delta=ct0.clone();let now=Instant::now();
 for (src,mut dst) in ct0.as_polynomial_list().iter().zip(delta.as_mut_polynomial_list().iter_mut()) {
  polynomial_wrapping_monic_monomial_mul(&mut dst,&src,MonomialDegree(a as usize));
  polynomial_wrapping_sub_assign(&mut dst,&src);
 }
 let cmux_input_ns=now.elapsed().as_nanos();
 let decomposer=SignedDecomposer::<u32>::new(DecompositionBaseLog(10),DecompositionLevelCount(2));
 let now=Instant::now();let mut digits=Vec::new();
 for &x in delta.as_ref() {
  let terms:Vec<_>=decomposer.decompose(x).collect();assert_eq!(terms.len(),2);
  assert_eq!(terms[0].level().0,2);assert_eq!(terms[1].level().0,1);
  let d2=terms[0].value() as i32;let d1=terms[1].value() as i32;
  assert!((-512..=512).contains(&d2)&&(-512..=512).contains(&d1));
  let rounded=decomposer.closest_representable(x);assert_eq!(rounded%4096,0);
  assert_eq!(terms.iter().fold(0u32,|s,t|s.wrapping_add(t.to_recomposition_summand())),rounded);
  digits.push(vec![rounded/4096%1024,rounded/4096/1024,(d2+512) as u32,(d1+512) as u32]);
 }
 let decomposition_ns=now.elapsed().as_nanos();
 fs::write(new.join("delta.ct"),bincode::serialize(&delta)?)?;
 fs::write(new.join("digits.json"),serde_json::to_vec(&digits)?)?;
 let (input,output)=tables(&ct0,&delta,a,&digits);
 fs::write(new.join("tables.json"),serde_json::to_vec(&json!({"input_rows":input,"output_rows":output}))?)?;
 let r=json!({"claim":"EXECUTED existing TFHE integer CMUX input and SignedDecomposer on genuine saved accumulator",
  "prefix":prefix,"mask_exponent":a,"coefficients":2048,"base_log":10,"levels":2,"iteration_levels":[2,1],
  "cmux_input_ns":cmux_input_ns,"decomposition_ns":decomposition_ns,"new_keys":0,"new_encryptions":0,"fft_calls":0,
  "origins":origins,"delta_sha256":hash(&fs::read(new.join("delta.ct"))?)});
 fs::write(new.join("capture.json"),serde_json::to_vec_pretty(&r)?)?;println!("{r}");Ok(())
}
fn tables(ct0:&GlweCiphertextOwned<u32>,delta:&GlweCiphertextOwned<u32>,a:u32,digits:&[Vec<u32>])->(Vec<Vec<u32>>,Vec<Vec<u32>>){
 let input=(0..2048).map(|i|{let x=ct0.as_ref()[i];vec![(i/512) as u32,(i%512) as u32,x&65535,x>>16]}).collect();
 let output=(0..2048).map(|i|{let z=delta.as_ref()[i];let d=&digits[i];vec![i as u32,(i/512) as u32,(i%512) as u32,a,z&65535,z>>16,d[0],d[1],d[2],d[3]]}).collect();
 (input,output)
}
fn statement(template:&Path,input:Vec<Vec<u32>>,output:Vec<Vec<u32>>)->Result<DescriptorStatement>{
 let raw=read(template,1<<20)?;let mut d=parse_vm_descriptor2(std::str::from_utf8(&raw)?)?;
 assert_eq!(d.trace_width,301);assert_eq!(d.public_input_count,0);assert_eq!(d.tables.len(),3);
 for (id,arity,rows) in [(11,10,output),(12,4,input.clone()),(13,4,input)] {
  let t=d.tables.iter_mut().find(|t|t.id==id).ok_or("missing exact public table")?;
  assert_eq!(t.arity,arity);assert!(matches!(t.sem,TableSem::ExactPublicRows{..}));t.sem=TableSem::ExactPublicRows{rows};
 }Ok(DescriptorStatement::try_new(d,vec![])? )
}
fn main()->Result<()> {
 let a:Vec<String>=std::env::args().collect();
 if a.len()==4&&a[1]=="prepare"{return prepare(Path::new(&a[2]),Path::new(&a[3]));}
 if a.len()!=6{return Err("usage: prepare OLD_PACKAGE NEW_FIXTURE | prove TEMPLATE FIXTURE TRACE NEW_PROOF_DIR | verify/reject-changed TEMPLATE FIXTURE PROOF REPORT".into());}
 let dir=Path::new(&a[3]);let changed=a[1]=="reject-changed";
 let (ct0,exponent,prefix)=prior_rotation::verified_prefix(dir)?;
 let delta:GlweCiphertextOwned<u32>=decode(&dir.join("delta.ct"))?;
 assert_eq!(delta.polynomial_size().0,512);assert_eq!(delta.glwe_size().0,4);assert!(delta.ciphertext_modulus().is_native_modulus());
 let mut digits:Vec<Vec<u32>>=serde_json::from_slice(&read(&dir.join("digits.json"),1<<20)?)?;
 assert_eq!(digits.len(),2048);assert!(digits.iter().all(|d|d.len()==4&&d[0]<1024&&d[1]<1024&&d[2]<=1024&&d[3]<=1024));
 if changed {digits[1536][2]+=1;}
 let (input,output)=tables(&ct0,&delta,exponent,&digits);let st=statement(Path::new(&a[2]),input,output)?;
 let result=if a[1]=="prove" {
  let dest=Path::new(&a[5]);fs::create_dir(dest)?;let width=st.descriptor().trace_width;
  let raw=read(Path::new(&a[4]),1<<24)?;assert_eq!(raw.len(),2048*width*4);
  let parsed:Vec<Vec<u32>>=raw.chunks_exact(width*4).map(|r|r.chunks_exact(4).map(|x|u32::from_le_bytes(x.try_into().unwrap())).collect()).collect();
  assert!(parsed.iter().flatten().all(|x|*x<BABYBEAR_P));
  let trace:Vec<Vec<BabyBear>>=parsed.into_iter().map(|r|r.into_iter().map(BabyBear::new).collect()).collect();
  let mem=MemBoundaryWitness::default();let umem=UMemBoundaryWitness::default();
  let w=Plonky3HidingFriWitness{base_trace:&trace,mem_boundary:&mem,map_heaps:&[],umem_boundary:&umem};
  let t=Instant::now();let p=Backend::prove(&st,w)?;let prove_ns=t.elapsed().as_nanos();let bytes=postcard::to_allocvec(&p)?;
  fs::write(dest.join("proof.bin"),&bytes)?;let t=Instant::now();Backend::verify(&st,&p)?;
  let r=json!({"claim":"EXECUTED complete first CMUX integer input and exact signed decomposition proof","verified":true,"prefix":prefix,
   "backend":Backend::BACKEND_ID,"rows":2048,"trace_width":width,"exact_public_tables":3,
   "proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"prove_ns":prove_ns,"self_verify_ns":t.elapsed().as_nanos(),
   "template_sha256":hash(&fs::read(&a[2])?)});
  fs::write(dest.join("proof.json"),serde_json::to_vec_pretty(&r)?)?;r
 } else {
  assert!(a[1]=="verify"||changed);let bytes=read(Path::new(&a[4]),1<<24)?;let p=proof(&bytes)?;
  let t=Instant::now();let accepted=Backend::verify(&st,&p);let ns=t.elapsed().as_nanos();let error=accepted.as_ref().err().map(|e|format!("{e:?}"));
  if changed{assert!(accepted.is_err(),"changed digit accepted");}else{accepted?;}
  let r=json!({"claim":"EXECUTED fresh joined public proof verification","verified":!changed,"prefix":prefix,
   "changed_level2_digit_rejected":changed,"mutated_coefficient":if changed{Some(1536)}else{None},"verifier_ran":true,
   "verify_ns":ns,"error":error,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes)});
  fs::write(&a[5],serde_json::to_vec_pretty(&r)?)?;r
 };println!("{result}");Ok(())
}
