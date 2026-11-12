//! Full native u32 PBS uses existing TFHE routines; no new PBS arithmetic loop.
//! Same-key keyswitch is a separately recorded extension after full PBS passes.
use std::{fs,path::Path,time::Instant};use serde::Serialize;use serde_json::json;use sha2::{Digest,Sha256};
use tfhe::boolean::parameters::DEFAULT_PARAMETERS;use tfhe::core_crypto::prelude::*;
use tfhe::core_crypto::algorithms::lwe_programmable_bootstrapping::karatsuba_pbs::blind_rotate_karatsuba_assign;
type Result<T>=std::result::Result<T,Box<dyn std::error::Error>>;
fn hash(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn save<T:Serialize>(dir:&Path,name:&str,v:&T)->Result<serde_json::Value>{let b=bincode::serialize(v)?;fs::write(dir.join(name),&b)?;Ok(json!({"file":name,"bytes":b.len(),"sha256":hash(&b)}))}
fn write(dir:&Path,name:&str,v:&serde_json::Value)->Result<()>{fs::write(dir.join(name),serde_json::to_vec_pretty(v)?)?;Ok(())}
fn main()->Result<()>{
 let a:Vec<String>=std::env::args().collect();if a.len()!=4{return Err("usage: NEW_RUN_DIRECTORY COMPLETED_PREDECESSOR_MANIFEST EXPECTED_MANIFEST_SHA256".into());}
 let predecessor=fs::read(&a[2])?;assert_eq!(hash(&predecessor),a[3],"predecessor must be completed/frozen before new setup");
 let dir=Path::new(&a[1]);fs::create_dir(dir)?;let start=Instant::now();let p=DEFAULT_PARAMETERS;
 assert_eq!(p.lwe_dimension.0,805);assert_eq!(p.glwe_dimension.0,3);assert_eq!(p.polynomial_size.0,512);assert_eq!(p.pbs_base_log.0,10);assert_eq!(p.pbs_level.0,2);assert_eq!(p.ks_base_log.0,3);assert_eq!(p.ks_level.0,5);
 let mut seeder=new_seeder();let mut enc=EncryptionRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed(),seeder.as_mut());let mut sg=SecretRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed());
 let lwe=allocate_and_generate_new_binary_lwe_secret_key::<u32,_>(p.lwe_dimension,&mut sg);
 let glwe=allocate_and_generate_new_binary_glwe_secret_key::<u32,_>(p.glwe_dimension,p.polynomial_size,&mut sg);
 let t=Instant::now();let bsk=allocate_and_generate_new_lwe_bootstrap_key(&lwe,&glwe,p.pbs_base_log,p.pbs_level,p.glwe_noise_distribution,CiphertextModulus::new_native(),&mut enc);let bsk_generation_ns=t.elapsed().as_nanos();
 assert_eq!(bsk.input_lwe_dimension().0,805);assert_eq!(bsk.as_ref().len(),805*2*4*4*512);
 let true_encoding=1u32<<29;let false_encoding=0u32.wrapping_sub(true_encoding);
 let left=allocate_and_encrypt_new_lwe_ciphertext(&lwe,Plaintext(true_encoding),p.lwe_noise_distribution,CiphertextModulus::new_native(),&mut enc);
 let right=allocate_and_encrypt_new_lwe_ciphertext(&lwe,Plaintext(false_encoding),p.lwe_noise_distribution,CiphertextModulus::new_native(),&mut enc);
 let mut precursor=left.clone();lwe_ciphertext_add(&mut precursor,&left,&right);lwe_ciphertext_plaintext_add_assign(&mut precursor,Plaintext(false_encoding));
 let mut lut=GlweCiphertext::new(0u32,GlweSize(4),PolynomialSize(512),CiphertextModulus::new_native());lut.get_mut_body().as_mut().fill(true_encoding);let initial=lut.clone();
 let mut files=vec![save(dir,"public_raw_bsk.ct",&bsk)?,save(dir,"left.ct",&left)?,save(dir,"right.ct",&right)?,save(dir,"and_precursor.ct",&precursor)?,save(dir,"initial_lut.ct",&initial)?];
 let t=Instant::now();let ms=lwe_ciphertext_modulus_switch::<u32,usize,_>(precursor.as_view(),CiphertextModulusLog(10));let modulus_switch_ns=t.elapsed().as_nanos();let masks:Vec<usize>=ms.mask().collect();assert_eq!(masks.len(),805);let body=ms.body();
 let t=Instant::now();blind_rotate_karatsuba_assign(&ms,&mut lut,&bsk);let full_blind_rotation_ns=t.elapsed().as_nanos();
 let mut output=LweCiphertext::new(0u32,LweDimension(1536).to_lwe_size(),CiphertextModulus::new_native());let t=Instant::now();extract_lwe_sample_from_glwe_ciphertext(&lut,&mut output,MonomialDegree(0));let sample_extract_ns=t.elapsed().as_nanos();
 files.push(save(dir,"full_rotated_lut.ct",&lut)?);files.push(save(dir,"pbs_output_lwe1536.ct",&output)?);
 fs::write(dir.join("public_rotation_degrees.json"),serde_json::to_vec(&json!({"mask":masks,"body":body}))?)?;
 let public=json!({"claim":"EXECUTED complete existing-routine u32 Karatsuba programmable bootstrap","predecessor_manifest_sha256":a[3],"operation":"Boolean AND(true,false) precursor followed by full PBS threshold LUT","scalar_bits":32,"input_lwe_dimension":805,"output_lwe_dimension":1536,"output_key_identity":"fresh flattened GLWE3x512 key; distinct from original LWE805 key","glwe_dimension":3,"polynomial_size":512,"pbs_base_log":10,"pbs_levels":2,"raw_ggsw_blocks":805,"nonzero_public_mask_iterations":masks.iter().filter(|&&x|x!=0).count(),"body_rotation":body,"bsk_generation_ns":bsk_generation_ns,"modulus_switch_ns":modulus_switch_ns,"full_blind_rotation_ns":full_blind_rotation_ns,"sample_extract_ns":sample_extract_ns,"public_phase_elapsed_ns":start.elapsed().as_nanos(),"private_evaluation_started":false,"client_material_serialized":false,"full_pbs_proof":false,"files":files});
 write(dir,"pbs_public_complete.json",&public)?;
 // Public result and its entire raw evaluation material exist before private evaluation.
 let phase=decrypt_lwe_ciphertext(&glwe.as_lwe_secret_key(),&output).0;let decoded=phase<(1u32<<31);let matched=!decoded;let error=phase.wrapping_sub(false_encoding) as i32 as i64;
 let private=json!({"claim":"REPORTED ephemeral private comparison after established public PBS outputs","public_report_sha256":hash(&fs::read(dir.join("pbs_public_complete.json"))?),"expected":false,"decoded_matches":matched,"signed_torus32_error":error,"client_material_serialized":false});write(dir,"pbs_private_comparison.json",&private)?;assert!(matched,"full PBS decoded wrong result; no keyswitch extension");
 // Root-authorized explicit same-key extension, only after full PBS has passed.
 let t=Instant::now();let ksk=allocate_and_generate_new_lwe_keyswitch_key(&glwe.as_lwe_secret_key(),&lwe,p.ks_base_log,p.ks_level,p.lwe_noise_distribution,CiphertextModulus::new_native(),&mut enc);let ksk_generation_ns=t.elapsed().as_nanos();
 assert_eq!(ksk.input_key_lwe_dimension().0,1536);assert_eq!(ksk.output_key_lwe_dimension().0,805);
 let keyref=save(dir,"public_keyswitch_1536_to_805.ct",&ksk)?;let mut same=LweCiphertext::new(0u32,p.lwe_dimension.to_lwe_size(),CiphertextModulus::new_native());let t=Instant::now();keyswitch_lwe_ciphertext(&ksk,&output,&mut same);let keyswitch_ns=t.elapsed().as_nanos();let outref=save(dir,"same_key_and_output_lwe805.ct",&same)?;
 let extension=json!({"claim":"EXECUTED separate existing-TFHE keyswitch extension after full PBS passed","input_lwe_dimension":1536,"output_lwe_dimension":805,"output_key_identity":"original fresh LWE805 key used for both AND inputs","ks_base_log":3,"ks_levels":5,"ksk_generation_ns":ksk_generation_ns,"keyswitch_ns":keyswitch_ns,"public_output_established_before_private_comparison":true,"files":[keyref,outref],"proof_claim":false});write(dir,"same_key_public_complete.json",&extension)?;
 let phase=decrypt_lwe_ciphertext(&lwe,&same).0;let matched=phase>=(1u32<<31);let error=phase.wrapping_sub(false_encoding) as i32 as i64;let private2=json!({"claim":"REPORTED ephemeral private comparison after established same-key public output","public_report_sha256":hash(&fs::read(dir.join("same_key_public_complete.json"))?),"expected":false,"decoded_matches":matched,"signed_torus32_error":error,"client_material_serialized":false});write(dir,"same_key_private_comparison.json",&private2)?;assert!(matched,"same-key decoded result wrong");
 let final_report=json!({"claim":"EXECUTED one full u32 exact Karatsuba PBS and separately recorded same-key continuation","full_pbs_passed":true,"same_key_extension_passed":true,"full_pbs_runs":1,"keyswitch_runs":1,"fresh_lwe_keys":1,"fresh_glwe_keys":1,"client_material_serialized":false,"public_before_private_phases":2,"total_ns":start.elapsed().as_nanos(),"whole_pbs_proof":false,"fft_equivalence_claim":false});write(dir,"report.json",&final_report)?;println!("{final_report}");Ok(())}
