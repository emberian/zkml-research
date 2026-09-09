//! One terminal-row semantic control. Uses the actual native AIR/proof backend.
//! Inputs are already-public rows and their public-arithmetic witness, not FHE keys.
use dregg_circuit::descriptor_ir2::{
    ir2_eval_accepts_i64, parse_vm_descriptor2, MemBoundaryWitness, TableSem,
    UMemBoundaryWitness,
};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriWitness,
};
use dregg_circuit::field::{BabyBear, BABYBEAR_P};
use vfhe_public_preprocessing_backend::FixedPublicPreprocessing as Backend;
use serde_json::json;
use sha2::{Digest,Sha256};
use std::{fs,path::Path,time::Instant};
type Result<T> = std::result::Result<T,Box<dyn std::error::Error>>;
type Proof = <Backend as DescriptorProofVerifier>::Proof;
const ROWS:usize=8192;
const WIDTH:usize=2509;
const PUBLIC:usize=57;
const OUTPUT_COLUMN:usize=43;
fn hash(b:&[u8])->String {format!("{:x}",Sha256::digest(b))}
fn write_json(path:&Path,value:&serde_json::Value)->Result<()> {
    fs::write(path,serde_json::to_vec_pretty(value)?)?;Ok(())
}
fn statement(template:&[u8],rows:Vec<Vec<u32>>)->Result<DescriptorStatement> {
    let mut desc=parse_vm_descriptor2(std::str::from_utf8(template)?)?;
    assert_eq!(desc.trace_width,WIDTH);
    assert_eq!(desc.public_input_count,0);
    assert_eq!(desc.tables.len(),1);
    let table=&mut desc.tables[0];
    assert_eq!(table.id,11);assert_eq!(table.arity,PUBLIC);
    assert!(matches!(table.sem,TableSem::ExactPublicRows{..}));
    table.sem=TableSem::ExactPublicRows{rows};
    Ok(DescriptorStatement::try_new(desc,vec![])?)
}
fn main()->Result<()> {
    let a:Vec<String>=std::env::args().collect();
    if a.len()!=6 {return Err("usage: OLD_TEMPLATE REPAIRED_TEMPLATE PUBLIC_ROWS TRACE NEW_OUT".into())}
    let out=Path::new(&a[5]);fs::create_dir(out)?;
    let old_template=fs::read(&a[1])?;let repaired_template=fs::read(&a[2])?;
    let public_bytes=fs::read(&a[3])?;let trace_bytes=fs::read(&a[4])?;
    assert_eq!(hash(&old_template),"f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d");
    assert_eq!(trace_bytes.len(),ROWS*WIDTH*4);
    let mut public:Vec<Vec<u32>>=serde_json::from_slice(&public_bytes)?;
    assert_eq!(public.len(),ROWS);
    let mut raw:Vec<Vec<u32>>=trace_bytes.chunks_exact(WIDTH*4).map(|r|
        r.chunks_exact(4).map(|c|u32::from_le_bytes(c.try_into().unwrap())).collect()
    ).collect();
    assert!(raw.iter().zip(&public).enumerate().all(|(i,(r,p))|
        p.len()==PUBLIC && r[..PUBLIC]==p[..] && p[0]==i as u32 && r.iter().all(|x|*x<BABYBEAR_P)));
    let old_digit=raw[ROWS-1][OUTPUT_COLUMN];assert!(old_digit<64);
    let new_digit=old_digit^1;
    raw[ROWS-1][OUTPUT_COLUMN]=new_digit;
    public[ROWS-1][OUTPUT_COLUMN]=new_digit;
    let changed_public=serde_json::to_vec(&public)?;
    fs::write(out.join("changed_public_rows.json"),&changed_public)?;
    let old=statement(&old_template,public.clone())?;
    let repaired=statement(&repaired_template,public)?;
    let rows_i64:Vec<Vec<i64>>=raw.iter().map(|r|r.iter().map(|x|i64::from(*x)).collect()).collect();
    let t=Instant::now();
    let old_gates=ir2_eval_accepts_i64(old.descriptor(),&rows_i64,&[]);
    let old_gate_ns=t.elapsed().as_nanos();
    let t=Instant::now();
    let repaired_gates=ir2_eval_accepts_i64(repaired.descriptor(),&rows_i64,&[]);
    let repaired_gate_ns=t.elapsed().as_nanos();
    drop(rows_i64);
    let setup=json!({"scope":"One public raw-row terminal control, no FHE container generation or secret inputs",
        "old_template_sha256":hash(&old_template),"repaired_template_sha256":hash(&repaired_template),
        "source_public_rows_sha256":hash(&public_bytes),"source_trace_sha256":hash(&trace_bytes),
        "changed_public_rows_sha256":hash(&changed_public),"physical_row":ROWS-1,"column":OUTPUT_COLUMN,
        "old_digit":old_digit,"new_digit":new_digit,"changed_trace_cells":1,"changed_public_cells":1,
        "old_native_main_gates_accept":old_gates,"repaired_native_main_gates_accept":repaired_gates,
        "gate_oracle_excludes_lookup_bus":true,"old_gate_ns":old_gate_ns,"repaired_gate_ns":repaired_gate_ns});
    write_json(&out.join("gate_control.json"),&setup)?;
    assert!(old_gates,"old selector did not admit the isolated terminal mutation");
    assert!(!repaired_gates,"repaired all-row selector did not reject terminal mutation");
    let trace:Vec<Vec<BabyBear>>=raw.into_iter().map(|r|r.into_iter().map(BabyBear::new).collect()).collect();
    let mem=MemBoundaryWitness::default();let umem=UMemBoundaryWitness::default();
    let witness=Plonky3HidingFriWitness{base_trace:&trace,mem_boundary:&mem,map_heaps:&[],umem_boundary:&umem};
    let t=Instant::now();let proof=Backend::prove(&old,witness)?;let prove_ns=t.elapsed().as_nanos();
    let bytes=postcard::to_allocvec(&proof)?;fs::write(out.join("old_mutated_proof.bin"),&bytes)?;
    drop(proof);
    let(decoded,tail):(Proof,&[u8])=postcard::take_from_bytes(&bytes)?;assert!(tail.is_empty());
    let t=Instant::now();Backend::verify(&old,&decoded)?;let old_verify_ns=t.elapsed().as_nanos();
    let t=Instant::now();let rejection=Backend::verify(&repaired,&decoded);let repaired_verify_ns=t.elapsed().as_nanos();
    assert!(rejection.is_err(),"old malformed proof accepted under repaired statement");
    assert_eq!(fs::read(&a[1])?,old_template);assert_eq!(fs::read(&a[2])?,repaired_template);
    assert_eq!(fs::read(&a[3])?,public_bytes);assert_eq!(fs::read(&a[4])?,trace_bytes);
    let report=json!({"gate_control":setup,"backend":Backend::BACKEND_ID,"old_mutated_statement_native_verified":true,
        "old_proof_repaired_statement_rejected":true,"repaired_rejection":rejection.err(),
        "repaired_proof_generation_attempted":false,"proof_bytes":bytes.len(),"proof_sha256":hash(&bytes),
        "prove_ns_including_backend_self_verification":prove_ns,"explicit_deserialized_old_verify_ns":old_verify_ns,
        "repaired_statement_verify_ns":repaired_verify_ns,"source_input_bytes_unchanged":true,
        "scope":"Native gate-oracle contrast establishes selector effect; accepted old proof includes actual PCS, quotient and LogUp checks. Rejecting that proof under repaired statement is additional statement-binding evidence, not a substitute for the gate contrast."});
    write_json(&out.join("result.json"),&report)?;println!("{report}");Ok(())
}
