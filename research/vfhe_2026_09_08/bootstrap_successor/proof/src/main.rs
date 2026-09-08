//! Generic public-table descriptor glue. No arithmetic constraints or witness
//! equations are authored here: both arrive from the Lean compiler export.
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2,MemBoundaryWitness,TableSem,UMemBoundaryWitness};
use dregg_circuit::descriptor_proof_backend::{DescriptorProofProver,DescriptorProofVerifier,DescriptorStatement,Plonky3HidingFriWitness};
use dregg_circuit::field::{BabyBear,BABYBEAR_P};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;
use std::{fs,path::Path,time::Instant};use sha2::{Digest,Sha256};use serde_json::json;
type Result<T>=std::result::Result<T,Box<dyn std::error::Error>>;
type Proof=<Backend as DescriptorProofVerifier>::Proof;
fn hash(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn statement(template:&Path,rows:&[Vec<u32>])->Result<DescriptorStatement>{
 let mut d=parse_vm_descriptor2(&fs::read_to_string(template)?)?;
 assert_eq!(d.public_input_count,0);assert_eq!(d.trace_width,55);
 assert_eq!(d.tables.len(),1);let t=&mut d.tables[0];assert_eq!(t.id,11);assert_eq!(t.arity,4);
 assert!(matches!(t.sem,TableSem::ExactPublicRows{..}));t.sem=TableSem::ExactPublicRows{rows:rows.to_vec()};
 Ok(DescriptorStatement::try_new(d,vec![])? )
}
fn main()->Result<()>{
 let a:Vec<String>=std::env::args().collect();
 if a.len()!=6{return Err("usage: prove TEMPLATE ROWS TRACE NEW_DIR | verify TEMPLATE ROWS PROOF REPORT | reject-changed TEMPLATE ROWS PROOF REPORT".into());}
 let mut rows:Vec<Vec<u32>>=serde_json::from_slice(&fs::read(&a[3])?)?;
 assert_eq!(rows.len(),1024);assert!(rows.iter().enumerate().all(|(i,r)|r.len()==4&&r[0]==i as u32&&r.iter().all(|x|*x<BABYBEAR_P)));
 let mutation=a[1]=="reject-changed";if mutation{rows[0][3]^=1;}
 let st=statement(Path::new(&a[2]),&rows)?;
 let report=if a[1]=="prove"{
  let dir=Path::new(&a[5]);fs::create_dir(dir)?;
  let raw=fs::read(&a[4])?;let width=st.descriptor().trace_width;assert_eq!(raw.len(),rows.len()*width*4);
  let parsed:Vec<Vec<u32>>=raw.chunks_exact(width*4).map(|r|r.chunks_exact(4).map(|x|u32::from_le_bytes(x.try_into().unwrap())).collect()).collect();
  assert!(parsed.iter().zip(&rows).all(|(r,p)|&r[..4]==p.as_slice()&&r.iter().all(|x|*x<BABYBEAR_P)));
  let trace:Vec<Vec<BabyBear>>=parsed.into_iter().map(|r|r.into_iter().map(BabyBear::new).collect()).collect();
  let mem=MemBoundaryWitness::default();let umem=UMemBoundaryWitness::default();
  let witness=Plonky3HidingFriWitness{base_trace:&trace,mem_boundary:&mem,map_heaps:&[],umem_boundary:&umem};
  let t=Instant::now();let proof=Backend::prove(&st,witness)?;let prove_ns=t.elapsed().as_nanos();
  let bytes=postcard::to_allocvec(&proof)?;fs::write(dir.join("proof.bin"),&bytes)?;
  let t=Instant::now();Backend::verify(&st,&proof)?;let verify_ns=t.elapsed().as_nanos();
  let r=json!({"claim":"EXECUTED proof of compiler-generated TFHE modulus-switch relation","verified":true,
   "backend":Backend::BACKEND_ID,"rows":rows.len(),"trace_width":width,"public_tuple_width":4,
   "prove_ns":prove_ns,"self_verify_ns":verify_ns,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),
   "template_sha256":hash(&fs::read(&a[2])?),"public_rows_sha256":hash(&fs::read(&a[3])?)});
  fs::write(dir.join("proof.json"),serde_json::to_vec_pretty(&r)?)?;r
 }else{
  assert!(a[1]=="verify"||mutation);let bytes=fs::read(&a[4])?;
  let (proof,rest):(Proof,&[u8])=postcard::take_from_bytes(&bytes)?;assert!(rest.is_empty());
  let t=Instant::now();let result=Backend::verify(&st,&proof);let ns=t.elapsed().as_nanos();
  let error=result.as_ref().err().map(|e|format!("{e:?}"));
  if mutation{assert!(result.is_err(),"changed public exponent accepted");}else{result?;}
  let r=json!({"claim":"EXECUTED fresh-process proof verification","verified":!mutation,
   "changed_exponent_rejected":mutation,"verifier_ran":true,"verify_ns":ns,"error":error,
   "proof_bytes":bytes.len(),"proof_sha256":hash(&bytes)});
  fs::write(&a[5],serde_json::to_vec_pretty(&r)?)?;r
 };println!("{report}");Ok(())
}
