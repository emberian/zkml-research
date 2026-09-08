use std::{fs,path::Path,time::Instant};
use tfhe::boolean::{prelude::*,parameters::DEFAULT_PARAMETERS};
use tfhe::core_crypto::prelude::*;
use tfhe::core_crypto::prelude::polynomial_algorithms::polynomial_wrapping_monic_monomial_div;
use serde_json::json;
use sha2::{Digest,Sha256};
type Result<T> = std::result::Result<T,Box<dyn std::error::Error>>;
fn hash(b:&[u8])->String {format!("{:x}",Sha256::digest(b))}
fn save(dir:&Path,name:&str,bytes:&[u8])->Result<serde_json::Value>{
    fs::write(dir.join(name),bytes)?;Ok(json!({"file":name,"bytes":bytes.len(),"sha256":hash(bytes)}))
}
fn main()->Result<()> {
    let args:Vec<String>=std::env::args().collect();
    if args.len()!=2 {return Err("usage: tfhe-bootstrap-entry-fixture NEW_DIRECTORY".into());}
    let dir=Path::new(&args[1]);fs::create_dir(dir)?;
    let start=Instant::now();let p=DEFAULT_PARAMETERS;
    assert_eq!(p.polynomial_size.0,512);assert_eq!(p.lwe_dimension.0,805);
    assert_eq!(p.pbs_base_log.0,10);assert_eq!(p.pbs_level.0,2);
    let key=ClientKey::new(&p);let server=ServerKey::new(&key);
    let a=key.encrypt(true);let b=key.encrypt(false);
    let operation=Instant::now();let output=server.and(&a,&b);let and_ns=operation.elapsed().as_nanos();
    assert!(!key.decrypt(&output));
    let (ca,cb)=match (&a,&b) {(Ciphertext::Encrypted(a),Ciphertext::Encrypted(b))=>(a,b),_=>unreachable!()};
    let mut precursor=LweCiphertext::new(0u32,ca.lwe_size(),ca.ciphertext_modulus());
    // Identical existing core calls and encoding used by BooleanEngine::and.
    lwe_ciphertext_add(&mut precursor,ca,cb);
    lwe_ciphertext_plaintext_add_assign(&mut precursor,Plaintext(0u32.wrapping_sub(1u32<<29)));
    let (bsk,_ksk,order)=server.into_raw_parts();
    assert_eq!(order,PBSOrder::BootstrapKeyswitch);
    assert_eq!(precursor.lwe_size(),bsk.input_lwe_dimension().to_lwe_size());
    let ms=lwe_ciphertext_modulus_switch::<u32,usize,_>(precursor.as_view(),CiphertextModulusLog(10));
    let mut degrees:Vec<usize>=ms.mask().collect();degrees.push(ms.body());
    let mut rows=Vec::new();
    for (i,(&x,&y)) in precursor.as_ref().iter().zip(&degrees).enumerate() {
        assert_eq!(y,(((x as u64+(1<<21))>>22)%1024) as usize);
        rows.push(vec![i as u32,x&65535,x>>16,y as u32]);
    }
    let actual_rows=rows.len();assert_eq!(actual_rows,806);
    while !rows.len().is_power_of_two() {let i=rows.len();let mut row=rows[i%actual_rows].clone();row[0]=i as u32;rows.push(row);}
    // Exact initial LUT construction and X^(-body) rotation from the existing PBS.
    let mut lut=GlweCiphertext::new(0u32,bsk.glwe_size(),p.polynomial_size,CiphertextModulus::new_native());
    lut.get_mut_body().as_mut().fill(1u32<<29);
    let initial=lut.clone();let degree=MonomialDegree(ms.body());
    for (mut target,source) in lut.as_mut_polynomial_list().iter_mut().zip(initial.as_polynomial_list().iter()) {
        polynomial_wrapping_monic_monomial_div(&mut target,&source,degree);
    }
    let mut refs=Vec::new();
    for (name,bytes) in [("left.ct",bincode::serialize(&a)?),("right.ct",bincode::serialize(&b)?),
      ("and_output.ct",bincode::serialize(&output)?),("pbs_input.ct",bincode::serialize(&precursor)?),
      ("initial_lut.ct",bincode::serialize(&initial)?),("body_rotated_lut.ct",bincode::serialize(&lut)?),
      ("public_rows.json",serde_json::to_vec(&rows)?),("rotation_degrees.json",serde_json::to_vec(&degrees)?)] {
        refs.push(save(dir,name,&bytes)?);
    }
    let report=json!({"claim":"EXECUTED fresh TFHE Boolean AND and exact PBS entry capture",
      "tfhe_version":"1.6.3","fft_feature":"experimental-force_fft_algo_dif4",
      "native_word_bits":32,"polynomial_size":512,"glwe_dimension":p.glwe_dimension.0,"lwe_dimension":805,
      "pbs_base_log":10,"pbs_level_count":2,"pbs_order":format!("{order:?}"),
      "operation":"AND(true,false)","decoded_output_matches":true,"and_ns":and_ns,
      "actual_modulus_switch_words":actual_rows,"proof_rows":rows.len(),"public_tuple_width":4,
      "initial_body_rotation_degree":ms.body(),"native_initial_lut_rotation_executed":true,
      "initial_rotation_covered_by_proof":false,"full_AND_covered_by_proof":false,
      "secret_key_saved":false,"public_server_key_saved":false,"total_ns":start.elapsed().as_nanos(),"files":refs});
    fs::write(dir.join("operation.json"),serde_json::to_vec_pretty(&report)?)?;
    println!("{report}");Ok(())
}
