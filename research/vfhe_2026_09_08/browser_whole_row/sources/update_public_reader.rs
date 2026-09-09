//! Public ciphertext reader for the already-executed useful learner expiry.
//! No AIR or witness arithmetic is authored in this module.
use super::*;
use fhe::bfv::BfvParametersBuilder;

const Q: [u64;2]=[2199023190017,4398046486529];
const PARAM_ID: &str="fb16ccd74dd4b7bedb6673b369b56475af06f9415a4faf4645d411d3c7d0cda3";
const NAMES: [&str;4]=["acc","fresh","old","out"];
fn parameters()->Result<Arc<BfvParameters>> {
    let p=BfvParametersBuilder::new().set_degree(4096).set_plaintext_modulus(4294828033)
        .set_moduli_sizes(&[41,42]).set_variance(10).build_arc()?;
    assert_eq!(p.moduli(),Q); Ok(p)
}
fn read(dir:&Path)->Result<(Vec<Ciphertext>,Vec<Vec<u8>>)> {
    let p=parameters()?; let mut cts=Vec::new(); let mut envelopes=Vec::new();
    for name in NAMES {
        let bytes=fs::read(dir.join(format!("{name}.ct")))?;
        assert_eq!(bytes.len(),85103); assert_eq!(&bytes[..8],b"RSBFV001"); assert_eq!(bytes[8],1);
        assert_eq!(bytes[9..41].iter().map(|x|format!("{x:02x}")).collect::<String>(),PARAM_ID);
        assert_eq!(u64::from_le_bytes(bytes[73..81].try_into().unwrap()),85022);
        let ct=Ciphertext::from_bytes(&bytes[81..],&p)?;
        assert_eq!(ct.len(),2); assert!(ct.iter().all(|poly|p.level_of_context(poly.ctx()).ok()==Some(0)));
        assert_eq!(ct.to_bytes(),bytes[81..]);
        if let Some(previous)=envelopes.first() { let previous:&Vec<u8>=previous; assert_eq!(previous[41..73],bytes[41..73]); }
        cts.push(ct); envelopes.push(bytes);
    }
    Ok((cts,envelopes))
}
pub fn rows(dir:&Path)->Result<Vec<Vec<u32>>> {
    let (cts,_)=read(dir)?;
    // These are exactly the serialized polynomial's NTT slots; this path does
    // not perform an NTT/inverse NTT or introduce a basis-conversion assumption.
    let all:Vec<Vec<Vec<Vec<u64>>>>=cts.iter().map(|ct|ct.iter().map(|poly| {
        assert_eq!(poly.representation(),&Representation::Ntt);
        poly.coefficients().outer_iter().map(|r|r.to_vec()).collect()
    }).collect()).collect();
    assert!(all.iter().all(|c|c.len()==2 && c.iter().all(|p|p.len()==2 && p.iter().all(|r|r.len()==4096))));
    Ok((0..8192).map(|row_id| {
        let mut row=vec![row_id as u32];
        for ct in &all { for limb in 0..2 {
            let v=ct[row_id/4096][limb][row_id%4096]; assert!(v<Q[limb]);
            for digit in 0..7 {row.push(((v>>(6*digit))&63) as u32);}
        }}
        assert_eq!(row.len(),57); row
    }).collect())
}
pub fn export_ntt(dir:&Path)->Result<()> {
    let data=rows(dir)?;
    assert!(!dir.join("public_ntt_rows.json").exists());
    write_json(&dir.join("public_ntt_rows.json"),&json!(data))?;
    println!("{}",json!({"claim":"EXECUTED direct canonical NTT coefficient export","rows":8192,"public_tuple_width":57,"basis_conversion":false,"public_rows_sha256":hash(&fs::read(dir.join("public_ntt_rows.json"))?)}));Ok(())
}
pub fn import(source:&Path,out:&Path)->Result<()> {
    fs::create_dir(out)?;
    let (cts,envelopes)=read(&source.join("public"))?;
    let event_bytes=fs::read(source.join("event.json"))?;
    let event:Value=serde_json::from_slice(&event_bytes)?;
    for (name,bytes) in NAMES.iter().zip(&envelopes) {
        assert_eq!(event["files"][name]["sha256"].as_str(),Some(hash(bytes).as_str()));
        fs::write(out.join(format!("{name}.ct")),bytes)?;
    }
    fs::write(out.join("source_event.json"),&event_bytes)?;
    let timer=Instant::now(); let mut recomputed=&cts[0]+&cts[1]; recomputed-=&cts[2];
    let operation_ns=timer.elapsed().as_nanos();
    assert_eq!(coefficients(&recomputed),coefficients(&cts[3]));
    assert_eq!(recomputed.to_bytes(),cts[3].to_bytes());
    let public_rows=rows(out)?;
    write_json(&out.join("public_rows.json"),&json!(public_rows))?;
    let report=json!({"claim":"EXECUTED public replay/export of real useful-learner expiry","operation":"acc+fresh-old","degree":4096,"moduli":Q,"plaintext_modulus":4294828033u64,"ciphertext_components":2,"coefficient_rows":8192,"public_tuple_width":57,"residue_equations":16384,"event":event["event"],"class":event["class"],"source_event_sha256":hash(&event_bytes),"complete_payload_replay_equal":true,"operation_ns":operation_ns,"private_files_read":0,"scope":"Ciphertext relation; encoder, FIFO authorization, ciphertext-key membership and plaintext correctness are outside this proof statement."});
    write_json(&out.join("operation.json"),&report)?;println!("{report}");Ok(())
}
