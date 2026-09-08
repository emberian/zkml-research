//! Public ciphertext decoder and existing proof-backend glue. No TFHE keys,
//! encryption, new native rotation or handwritten arithmetic AIR are used here.
use std::{fs,path::Path,time::Instant};
use bincode::Options;use serde::{Serialize,de::DeserializeOwned};use serde_json::{Value,json};
use sha2::{Digest,Sha256};use tfhe::core_crypto::prelude::*;
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2,MemBoundaryWitness,UMemBoundaryWitness,TableSem};
use dregg_circuit::descriptor_proof_backend::{DescriptorStatement,DescriptorProofProver,DescriptorProofVerifier,Plonky3HidingFriWitness};
use dregg_circuit::field::{BabyBear,BABYBEAR_P};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;
type Result<T>=std::result::Result<T,Box<dyn std::error::Error>>;
type Proof=<Backend as DescriptorProofVerifier>::Proof;
const PRIOR_TEMPLATE:&str="7922bc82170a30a377292326277cea85125633aae64021ec291d5603fb25eb31";
fn hash(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn read(path:&Path,max:usize)->Result<Vec<u8>>{assert!(fs::metadata(path)?.len()<=max as u64,"file cap");Ok(fs::read(path)?)}
fn decode<T:DeserializeOwned+Serialize>(path:&Path)->Result<T>{
 let bytes=read(path,1<<20)?;let value:T=bincode::DefaultOptions::new().with_fixint_encoding().reject_trailing_bytes().deserialize(&bytes)?;
 assert_eq!(bincode::serialize(&value)?,bytes,"noncanonical ciphertext bytes");Ok(value)
}
fn proof(bytes:&[u8])->Result<Proof>{let (p,rest):(Proof,&[u8])=postcard::take_from_bytes(bytes)?;assert!(rest.is_empty());Ok(p)}
struct Bundle {input:GlweCiphertextOwned<u32>,output:GlweCiphertextOwned<u32>,prior_rows:Vec<Vec<u32>>,body:Vec<u32>}
fn bundle(dir:&Path,changed:bool)->Result<Bundle>{
 let input:GlweCiphertextOwned<u32>=decode(&dir.join("initial_lut.ct"))?;
 let mut output:GlweCiphertextOwned<u32>=decode(&dir.join("body_rotated_lut.ct"))?;
 for ct in [&input,&output] {assert_eq!(ct.polynomial_size().0,512);assert_eq!(ct.glwe_size().0,4);assert!(ct.ciphertext_modulus().is_native_modulus());assert_eq!(ct.as_ref().len(),2048);}
 let precursor:LweCiphertextOwned<u32>=decode(&dir.join("pbs_input.ct"))?;
 assert_eq!(precursor.lwe_size().0,806);assert!(precursor.ciphertext_modulus().is_native_modulus());
 let prior_rows:Vec<Vec<u32>>=serde_json::from_slice(&read(&dir.join("prior_rows.json"),1<<20)?)?;
 assert_eq!(prior_rows.len(),1024);
 for (i,r) in prior_rows.iter().enumerate(){let x=precursor.as_ref()[i%806];assert_eq!(r.len(),4);assert_eq!(&r[..3],&[i as u32,x&65535,x>>16]);assert!(r[3]<1024);}
 let body=prior_rows[805].clone();assert_eq!(body[0],805);
 if changed {output.as_mut()[1536]^=1;}
 Ok(Bundle{input,output,prior_rows,body})
}
fn tables(b:&Bundle)->(Vec<Vec<u32>>,Vec<Vec<u32>>){
 let input=(0..2048).map(|i|{let x=b.input.as_ref()[i];vec![(i/512) as u32,(i%512) as u32,x&65535,x>>16]}).collect();
 let output=(0..2048).map(|i|{let z=b.output.as_ref()[i];vec![i as u32,(i/512) as u32,(i%512) as u32,b.body[3],z&65535,z>>16]}).collect();
 (input,output)
}
fn verify_prior(dir:&Path,b:&Bundle)->Result<Value>{
 let template=read(&dir.join("prior_template.json"),1<<20)?;assert_eq!(hash(&template),PRIOR_TEMPLATE);
 let mut d=parse_vm_descriptor2(std::str::from_utf8(&template)?)?;assert_eq!(d.trace_width,55);assert_eq!(d.public_input_count,0);assert_eq!(d.tables.len(),1);
 let t=&mut d.tables[0];assert_eq!(t.id,11);assert_eq!(t.arity,4);assert!(matches!(t.sem,TableSem::ExactPublicRows{..}));t.sem=TableSem::ExactPublicRows{rows:b.prior_rows.clone()};
 let st=DescriptorStatement::try_new(d,vec![])?;let bytes=read(&dir.join("prior_proof.bin"),1<<24)?;
 let p=proof(&bytes)?;let now=Instant::now();Backend::verify(&st,&p)?;
 Ok(json!({"verified":true,"verify_ns":now.elapsed().as_nanos(),"proof_sha256":hash(&bytes),"template_sha256":PRIOR_TEMPLATE,"body_row":b.body,"body_row_matches_decoded_pbs_input":true}))
}
fn statement(template:&Path,input:Vec<Vec<u32>>,output:Vec<Vec<u32>>)->Result<DescriptorStatement>{
 let raw=read(template,1<<20)?;let mut d=parse_vm_descriptor2(std::str::from_utf8(&raw)?)?;
 assert_eq!(d.trace_width,111);assert_eq!(d.public_input_count,0);assert_eq!(d.tables.len(),2);
 for (id,arity,rows) in [(11,6,output),(12,4,input)] {
  let t=d.tables.iter_mut().find(|t|t.id==id).ok_or("missing exact public table")?;
  assert_eq!(t.arity,arity);assert!(matches!(t.sem,TableSem::ExactPublicRows{..}));t.sem=TableSem::ExactPublicRows{rows};
 }Ok(DescriptorStatement::try_new(d,vec![])? )
}
fn prepare(old:&Path,new:&Path)->Result<()> {
 fs::create_dir(new)?;let mut origins=Vec::new();
 for (src,dst) in [("fixtures/normal_001/initial_lut.ct","initial_lut.ct"),("fixtures/normal_001/body_rotated_lut.ct","body_rotated_lut.ct"),
  ("fixtures/normal_001/pbs_input.ct","pbs_input.ct"),("fixtures/normal_001/public_rows.json","prior_rows.json"),
  ("artifacts/template_ir2.json","prior_template.json"),("results/proof001/proof.bin","prior_proof.bin")] {
  let p=old.join(src);let bytes=read(&p,1<<24)?;fs::write(new.join(dst),&bytes)?;
  origins.push(json!({"origin":p,"file":dst,"bytes":bytes.len(),"sha256":hash(&bytes)}));
 }
 let b=bundle(new,false)?;let (input,output)=tables(&b);
 fs::write(new.join("tables.json"),serde_json::to_vec(&json!({"input_rows":input,"output_rows":output}))?)?;
 let r=json!({"claim":"EXECUTED public-only decode/export of existing genuine TFHE fixture","body_row":b.body,
  "rotation_exponent":b.body[3],"input_coefficients":2048,"output_coefficients":2048,"polynomial_size":512,"glwe_size":4,
  "new_tfhe_operations":0,"new_keys":0,"prior_proof_verification_deferred_to_proof_consumer":true,"origins":origins});
 fs::write(new.join("join.json"),serde_json::to_vec_pretty(&r)?)?;println!("{r}");Ok(())
}
fn main()->Result<()> {
 let a:Vec<String>=std::env::args().collect();
 if a.len()==4&&a[1]=="prepare"{return prepare(Path::new(&a[2]),Path::new(&a[3]));}
 if a.len()!=6{return Err("usage: prepare OLD_PACKAGE NEW_FIXTURE | prove TEMPLATE FIXTURE TRACE NEW_PROOF_DIR | verify/reject-changed TEMPLATE FIXTURE PROOF REPORT".into());}
 let dir=Path::new(&a[3]);let changed=a[1]=="reject-changed";let b=bundle(dir,changed)?;
 let prior=verify_prior(dir,&b)?;let (input,output)=tables(&b);let st=statement(Path::new(&a[2]),input,output.clone())?;
 let result=if a[1]=="prove" {
  let dest=Path::new(&a[5]);fs::create_dir(dest)?;let width=st.descriptor().trace_width;
  let raw=read(Path::new(&a[4]),1<<24)?;assert_eq!(raw.len(),2048*width*4);
  let parsed:Vec<Vec<u32>>=raw.chunks_exact(width*4).map(|r|r.chunks_exact(4).map(|x|u32::from_le_bytes(x.try_into().unwrap())).collect()).collect();
  assert!(parsed.iter().zip(&output).all(|(r,p)|&r[..6]==p.as_slice()&&r.iter().all(|x|*x<BABYBEAR_P)));
  let trace:Vec<Vec<BabyBear>>=parsed.into_iter().map(|r|r.into_iter().map(BabyBear::new).collect()).collect();
  let mem=MemBoundaryWitness::default();let umem=UMemBoundaryWitness::default();
  let w=Plonky3HidingFriWitness{base_trace:&trace,mem_boundary:&mem,map_heaps:&[],umem_boundary:&umem};
  let t=Instant::now();let p=Backend::prove(&st,w)?;let prove_ns=t.elapsed().as_nanos();let bytes=postcard::to_allocvec(&p)?;
  fs::write(dest.join("proof.bin"),&bytes)?;let t=Instant::now();Backend::verify(&st,&p)?;
  let r=json!({"claim":"EXECUTED complete initial TFHE LUT rotation proof","verified":true,"prior_modulus_switch":prior,
   "backend":Backend::BACKEND_ID,"rows":2048,"trace_width":width,"input_table_rows":2048,"output_table_rows":2048,
   "proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"prove_ns":prove_ns,"self_verify_ns":t.elapsed().as_nanos(),
   "template_sha256":hash(&fs::read(&a[2])?)});
  fs::write(dest.join("proof.json"),serde_json::to_vec_pretty(&r)?)?;r
 } else {
  assert!(a[1]=="verify"||changed);let bytes=read(Path::new(&a[4]),1<<24)?;let p=proof(&bytes)?;
  let t=Instant::now();let accepted=Backend::verify(&st,&p);let ns=t.elapsed().as_nanos();let error=accepted.as_ref().err().map(|e|format!("{e:?}"));
  if changed{assert!(accepted.is_err(),"changed output accepted");}else{accepted?;}
  let r=json!({"claim":"EXECUTED fresh joined public proof verification","verified":!changed,"prior_modulus_switch":prior,
   "changed_output_rejected":changed,"mutated_output_coefficient":if changed{Some(1536)}else{None},"verifier_ran":true,
   "verify_ns":ns,"error":error,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes)});
  fs::write(&a[5],serde_json::to_vec_pretty(&r)?)?;r
 };println!("{result}");Ok(())
}
