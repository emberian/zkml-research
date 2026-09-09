//! Canonical public reader and existing proof backend, for the generated recurrence.
#[allow(dead_code)] mod prior_decomposition;
use std::{fs,path::Path,time::Instant};
use bincode::Options;use serde::{Serialize,de::DeserializeOwned};use serde_json::json;
use sha2::{Digest,Sha256};use tfhe::core_crypto::prelude::*;
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2,MemBoundaryWitness,UMemBoundaryWitness,TableSem};
use dregg_circuit::descriptor_proof_backend::{DescriptorStatement,DescriptorProofProver,DescriptorProofVerifier,Plonky3HidingFriWitness};
use dregg_circuit::field::{BabyBear,BABYBEAR_P};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;
type Result<T>=std::result::Result<T,Box<dyn std::error::Error>>;
type Proof=<Backend as DescriptorProofVerifier>::Proof;
const M:u32=16777216;
fn hash(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn read(p:&Path,max:u64)->Result<Vec<u8>>{assert!(fs::metadata(p)?.len()<=max);Ok(fs::read(p)?)}
fn decode<T:DeserializeOwned+Serialize>(p:&Path)->Result<T>{let b=read(p,1<<24)?;let v:T=bincode::DefaultOptions::new().with_fixint_encoding().reject_trailing_bytes().deserialize(&b)?;assert_eq!(bincode::serialize(&v)?,b);Ok(v)}
fn proof(b:&[u8])->Result<Proof>{let (p,rest):(Proof,&[u8])=postcard::take_from_bytes(b)?;assert!(rest.is_empty());Ok(p)}
fn limbs(out:&mut Vec<u32>,mut x:u32,n:usize){for _ in 0..n{out.push(x&63);x>>=6;}assert_eq!(x,0);}
fn rows(dir:&Path,changed:bool)->Result<Vec<Vec<u32>>>{
 let raw:GgswCiphertextOwned<u32>=decode(&dir.join("public_raw_ggsw.ct"))?;
 assert_eq!(raw.polynomial_size().0,512);assert_eq!(raw.glwe_size().0,4);assert_eq!(raw.decomposition_base_log().0,10);assert_eq!(raw.decomposition_level_count().0,2);assert!(raw.ciphertext_modulus().is_native_modulus());assert_eq!(raw.as_ref().len(),16384);
 let mut out:GlweCiphertextOwned<u32>=decode(&dir.join("exact_ntt_external_product.ct"))?;
 assert_eq!(out.polynomial_size().0,512);assert_eq!(out.glwe_size().0,4);assert!(out.ciphertext_modulus().is_native_modulus());
 if changed{out.as_mut()[1536]^=256;}
 // All decomp inputs are public; full cryptographic predecessor verification is done by callers.
 let digits:Vec<Vec<u32>>=serde_json::from_slice(&read(&dir.join("digits.json"),1<<20)?)?;assert_eq!(digits.len(),2048);
 for (i,d) in digits.iter().enumerate(){assert_eq!(d.len(),4);assert_eq!(d[2],512);let j=i%512;let expected=if i<1536{0}else if j<44{256}else if j<162{0}else{-256};assert_eq!(d[3] as i64-512,expected);}
 let mut rows=Vec::new();
 for c in 0..4{let k:Vec<u32>=raw.as_ref()[(28+c)*512..(29+c)*512].iter().map(|x|x&(M-1)).collect();
  let z=&out.as_ref()[c*512..(c+1)*512];assert!(z.iter().all(|x|x&255==0));let y:Vec<u32>=z.iter().map(|x|x>>8).collect();
  let mut s=vec![0u32;513];for j in 0..512{let w=if j<=350{1i64}else if j>=469{-1}else{0};s[j+1]=(s[j] as i64+w*k[j] as i64).rem_euclid(M as i64) as u32;}
  for j in 0..512{let mut r=vec![(c*512+j) as u32,c as u32,j as u32,(j==0) as u32,(j<44) as u32,(j<162) as u32,(j<=350) as u32,(j>=469) as u32];
   let prev=if j==0{(M-y[511])%M}else{y[j-1]};
   for x in [k[j],k[(j+512-44)%512],k[(j+512-162)%512],y[j],prev,s[j],s[j+1],s[512]]{limbs(&mut r,x,4);}limbs(&mut r,z[j],6);assert_eq!(r.len(),46);rows.push(r);
  }
 }Ok(rows)
}
fn statement(template:&Path,rows:Vec<Vec<u32>>)->Result<DescriptorStatement>{let b=read(template,1<<22)?;assert_eq!(hash(&b),"9a3f98d241dad5430e980941ddf4fa0a360ec11c291e51a833f280dee71101b3");let mut d=parse_vm_descriptor2(std::str::from_utf8(&b)?)?;assert_eq!(d.trace_width,279);assert_eq!(d.public_input_count,0);assert_eq!(d.tables.len(),1);let t=&mut d.tables[0];assert_eq!(t.id,11);assert_eq!(t.arity,46);assert!(matches!(t.sem,TableSem::ExactPublicRows{..}));t.sem=TableSem::ExactPublicRows{rows};Ok(DescriptorStatement::try_new(d,vec![])?) }
fn main()->Result<()>{let a:Vec<String>=std::env::args().collect();if a.len()==4&&a[1]=="rows"{let r=rows(Path::new(&a[2]),false)?;fs::write(&a[3],serde_json::to_vec(&r)?)?;println!("{}",json!({"claim":"EXECUTED canonical public reader export only","rows":r.len(),"arity":46,"predecessor_verification_deferred_to_consumer":true,"output":a[3]}));return Ok(());}
 if a.len()!=6{return Err("usage: rows FIXTURE OUTPUT_JSON | prove TEMPLATE FIXTURE TRACE NEW_PROOF_DIR | verify/reject-changed TEMPLATE FIXTURE PROOF REPORT".into());}
 let dir=Path::new(&a[3]);let changed=a[1]=="reject-changed";let (_,_,prefix)=prior_decomposition::verified_input(dir)?;let public=rows(dir,changed)?;let st=statement(Path::new(&a[2]),public.clone())?;
 let result=if a[1]=="prove"{let dest=Path::new(&a[5]);fs::create_dir(dest)?;let width=st.descriptor().trace_width;let raw=read(Path::new(&a[4]),1<<26)?;assert_eq!(raw.len(),2048*width*4);let parsed:Vec<Vec<u32>>=raw.chunks_exact(width*4).map(|r|r.chunks_exact(4).map(|x|u32::from_le_bytes(x.try_into().unwrap())).collect()).collect();assert!(parsed.iter().zip(&public).all(|(r,p)|&r[..46]==p.as_slice()&&r.iter().all(|x|*x<BABYBEAR_P)));let trace:Vec<Vec<BabyBear>>=parsed.into_iter().map(|r|r.into_iter().map(BabyBear::new).collect()).collect();let mem=MemBoundaryWitness::default();let umem=UMemBoundaryWitness::default();let w=Plonky3HidingFriWitness{base_trace:&trace,mem_boundary:&mem,map_heaps:&[],umem_boundary:&umem};let t=Instant::now();let p=Backend::prove(&st,w)?;let prove_ns=t.elapsed().as_nanos();let bytes=postcard::to_allocvec(&p)?;fs::write(dest.join("proof.bin"),&bytes)?;let t=Instant::now();Backend::verify(&st,&p)?;let r=json!({"claim":"EXECUTED generated complete anchored-recurrence proof for actual external product input","verified":true,"prefix":prefix,"backend":Backend::BACKEND_ID,"rows":2048,"trace_width":width,"public_arity":46,"prove_ns":prove_ns,"self_verify_ns":t.elapsed().as_nanos(),"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),"template_sha256":hash(&fs::read(&a[2])?)});fs::write(dest.join("proof.json"),serde_json::to_vec_pretty(&r)?)?;r}
 else{assert!(a[1]=="verify"||changed);let bytes=read(Path::new(&a[4]),1<<24)?;let p=proof(&bytes)?;let t=Instant::now();let accepted=Backend::verify(&st,&p);let ns=t.elapsed().as_nanos();let error=accepted.as_ref().err().map(|e|format!("{e:?}"));if changed{assert!(accepted.is_err());}else{accepted?;}let r=json!({"claim":"EXECUTED fresh public external-product proof consumer","verified":!changed,"changed_output_rejected":changed,"mutated_coefficient":if changed{Some(1536)}else{None},"mutation_preserves_low8_zero":changed,"verifier_ran":true,"error":error,"prefix":prefix,"verify_ns":ns,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes)});fs::write(&a[5],serde_json::to_vec_pretty(&r)?)?;r};println!("{result}");Ok(())}
