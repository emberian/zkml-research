//! Exact integer/CRT-NTT external product, a distinct backend from TFHE's floating FFT.
//! Existing raw GGSW generation, Karatsuba reference, and Fourier comparison are reused.
#[allow(dead_code)] mod prior_decomposition;
use std::{fs,path::Path,time::Instant};
use bincode::Options;
use serde::{Serialize,de::DeserializeOwned};
use serde_json::json;
use sha2::{Digest,Sha256};
use tfhe::boolean::parameters::DEFAULT_PARAMETERS;
use tfhe::core_crypto::prelude::*;
use tfhe::core_crypto::algorithms::lwe_programmable_bootstrapping::karatsuba_pbs::{karatsuba_add_external_product_assign,karatsuba_add_external_product_assign_scratch};
type Result<T>=std::result::Result<T,Box<dyn std::error::Error>>;
const N:usize=512;const G:usize=4;const LEVELS:usize=2;
const PRIMES:[u64;2]=[2013265921,998244353];const ROOTS:[u64;2]=[31,3];
const COEFF_BOUND:i128=1i128<<52;
fn hash(b:&[u8])->String{format!("{:x}",Sha256::digest(b))}
fn read(p:&Path,max:u64)->Result<Vec<u8>>{assert!(fs::metadata(p)?.len()<=max);Ok(fs::read(p)?)}
fn decode<T:DeserializeOwned+Serialize>(p:&Path)->Result<T>{let b=read(p,1<<24)?;let v:T=bincode::DefaultOptions::new().with_fixint_encoding().reject_trailing_bytes().deserialize(&b)?;assert_eq!(bincode::serialize(&v)?,b);Ok(v)}
fn save<T:Serialize>(p:&Path,v:&T)->Result<()>{fs::write(p,bincode::serialize(v)?)?;Ok(())}
fn pow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1;while e!=0{if e&1!=0{r=r*a%p;}a=a*a%p;e>>=1;}r}
fn prime(p:u64)->bool{if p<2{return false;}let mut d=2;while d*d<=p{if p%d==0{return false;}d+=1;}true}
fn preflight()->serde_json::Value{
 let mut cert=Vec::new();
 for (p,g) in PRIMES.into_iter().zip(ROOTS){assert!(prime(p));assert_eq!((p-1)%1024,0);let psi=pow(g,(p-1)/1024,p);assert_eq!(pow(psi,512,p),p-1);assert_eq!(pow(psi,1024,p),1);cert.push(json!({"prime":p,"root_candidate":g,"psi":psi,"psi_order":1024,"prime_trial_division_pass":true}));}
 let m=PRIMES[0] as i128*PRIMES[1] as i128;assert!(2*COEFF_BOUND<m);
 json!({"primes":cert,"signed_coefficient_bound":COEFF_BOUND.to_string(),"crt_modulus":m.to_string(),"twice_bound_less_than_modulus":true,"derivation":"8*512*(512*2^31)=2^52 for centered raw-u32 coefficients and balanced signed digits"})
}
fn ntt(a:&mut[u64],p:u64,omega:u64,inverse:bool){
 let n=a.len();let mut j=0;
 for i in 1..n{let mut bit=n>>1;while j&bit!=0{j^=bit;bit>>=1;}j^=bit;if i<j{a.swap(i,j);}}
 let root=if inverse{pow(omega,p-2,p)}else{omega};let mut len=2;
 while len<=n{let step=pow(root,(n/len) as u64,p);for base in (0..n).step_by(len){let mut w=1;for k in 0..len/2{let u=a[base+k];let v=a[base+k+len/2]*w%p;a[base+k]=(u+v)%p;a[base+k+len/2]=(u+p-v)%p;w=w*step%p;}}len*=2;}
 if inverse{let inv=pow(n as u64,p-2,p);for x in a{*x=*x*inv%p;}}
}
fn forward(a:&[i64],p:u64,psi:u64)->Vec<u64>{let mut twist=1;let mut out=Vec::with_capacity(N);for &x in a{out.push(x.rem_euclid(p as i64) as u64*twist%p);twist=twist*psi%p;}ntt(&mut out,p,psi*psi%p,false);out}
fn backward(mut a:Vec<u64>,p:u64,psi:u64)->Vec<u64>{ntt(&mut a,p,psi*psi%p,true);let inv=pow(psi,p-2,p);let mut twist=1;for x in &mut a{*x=*x*twist%p;twist=twist*inv%p;}a}
struct Exact{output:Vec<u32>,signed:Vec<i128>,residues:Vec<Vec<u64>>,key_ntt:Vec<Vec<Vec<u64>>>,digits_ntt:Vec<Vec<Vec<u64>>>}
fn exact_ntt(key:&[u32],digits:&[Vec<i64>])->Exact{
 assert_eq!(key.len(),LEVELS*G*G*N);assert_eq!(digits.len(),LEVELS*G);assert!(digits.iter().flatten().all(|&x|(-512..=512).contains(&x)));
 let mut residues=Vec::new();let mut key_ntt=Vec::new();let mut digits_ntt=Vec::new();
 for (p,g) in PRIMES.into_iter().zip(ROOTS){let psi=pow(g,(p-1)/1024,p);
  let kt:Vec<Vec<u64>>=key.chunks_exact(N).map(|k|forward(&k.iter().map(|&x|x as i32 as i64).collect::<Vec<_>>(),p,psi)).collect();
  let dt:Vec<Vec<u64>>=digits.iter().map(|d|forward(d,p,psi)).collect();let mut rr=Vec::new();
  for col in 0..G{let mut acc=vec![0;N];for row in 0..LEVELS*G{for j in 0..N{acc[j]=(acc[j]+kt[row*G+col][j]*dt[row][j]%p)%p;}}rr.extend(backward(acc,p,psi));}
  residues.push(rr);key_ntt.push(kt);digits_ntt.push(dt);
 }
 let p=PRIMES[0];let q=PRIMES[1];let inverse=pow(p%q,q-2,q);let modulus=p as i128*q as i128;
 let mut signed=Vec::new();let mut output=Vec::new();
 for i in 0..G*N{let r=residues[0][i];let s=residues[1][i];let t=(s+q-r%q)%q*inverse%q;let u=r as i128+p as i128*t as i128;let x=if u>modulus/2{u-modulus}else{u};assert!(x.abs()<=COEFF_BOUND);signed.push(x);output.push(x.rem_euclid(1i128<<32) as u32);}
 Exact{output,signed,residues,key_ntt,digits_ntt}
}
fn direct(key:&[u32],digits:&[Vec<i64>])->Vec<i128>{let mut out=vec![0i128;G*N];for row in 0..LEVELS*G{for col in 0..G{let k=&key[(row*G+col)*N..(row*G+col+1)*N];for (i,&d) in digits[row].iter().enumerate(){if d==0{continue;}for (j,&x) in k.iter().enumerate(){let term=d as i128*(x as i32) as i128;let pos=i+j;if pos<N{out[col*N+pos]+=term;}else{out[col*N+pos-N]-=term;}}}}}out}
fn ordered_digits(saved:&[Vec<u32>])->Vec<Vec<i64>>{let mut out=Vec::new();for level in [2,1]{for row in 0..G{out.push(saved[row*N..(row+1)*N].iter().map(|d|d[if level==2{2}else{3}] as i64-512).collect());}}out}
fn same_profile(ct:&GlweCiphertextOwned<u32>){assert_eq!(ct.polynomial_size().0,N);assert_eq!(ct.glwe_size().0,G);assert!(ct.ciphertext_modulus().is_native_modulus());}
fn torus_diff(a:&[u32],b:&[u32])->serde_json::Value{let ds:Vec<i64>=a.iter().zip(b).map(|(&x,&y)|x.wrapping_sub(y) as i32 as i64).collect();json!({"coefficients":a.len(),"different_coefficients":ds.iter().filter(|&&x|x!=0).count(),"maximum_absolute_torus32_difference":ds.iter().map(|x|x.abs()).max().unwrap(),"byte_equal":a==b})}
fn indexed_rows(raw:&[u32],out:&[u32])->serde_json::Value{
 // Native PUBLIC data only; the separate Lean compiler owns every constraint/witness.
 let keys:Vec<Vec<u32>>=(0..G*N).map(|i|vec![(i/N) as u32,(i%N) as u32,raw[(LEVELS*G-1)*G*N+i]&0xffffff]).collect();
 let outputs:Vec<Vec<u32>>=(0..G*N).map(|i|{assert_eq!(out[i]&255,0);vec![i as u32,(i/N) as u32,(i%N) as u32,out[i]>>8]}).collect();
 json!({"active_key_rows":keys,"scaled_output_rows":outputs,"active_raw_ggsw_row":7,"output_scale":256,"modulus":16777216})
}
fn prepare(old:&Path,new:&Path)->Result<()>{
 fs::create_dir(new)?;let cert=preflight();let mut origins=Vec::new();
 for name in ["initial_lut.ct","body_rotated_lut.ct","pbs_input.ct","prior_rows.json","prior_template.json","prior_proof.bin","rotation_template.json","rotation_proof.bin","delta.ct","digits.json"]{let p=old.join("fixtures/normal_001").join(name);let b=read(&p,1<<24)?;fs::write(new.join(name),&b)?;origins.push(json!({"origin":p,"file":name,"bytes":b.len(),"sha256":hash(&b)}));}
 for (src,dst) in [("artifacts/template_ir2.json","decomposition_template.json"),("results/proof001/proof.bin","decomposition_proof.bin")]{let p=old.join(src);let b=read(&p,1<<24)?;fs::write(new.join(dst),&b)?;origins.push(json!({"origin":p,"file":dst,"bytes":b.len(),"sha256":hash(&b)}));}
 let (delta,saved,prefix)=prior_decomposition::verified_input(new)?;same_profile(&delta);let digits=ordered_digits(&saved);
 for row in 0..LEVELS*G{for j in 0..N{let expected=if row==7{if j<44{256}else if j<162{0}else{-256}}else{0};assert_eq!(digits[row][j],expected);}}
 let profile=DEFAULT_PARAMETERS;assert_eq!(profile.polynomial_size.0,N);assert_eq!(profile.glwe_dimension.to_glwe_size().0,G);assert_eq!(profile.pbs_base_log.0,10);assert_eq!(profile.pbs_level.0,LEVELS);
 let mut seeder=new_seeder();let mut enc=EncryptionRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed(),seeder.as_mut());let mut sg=SecretRandomGenerator::<DefaultRandomGenerator>::new(seeder.seed());
 let secret=allocate_and_generate_new_binary_glwe_secret_key::<u32,_>(profile.glwe_dimension,profile.polynomial_size,&mut sg);
 let mut raw=GgswCiphertext::new(0u32,GlweSize(G),PolynomialSize(N),DecompositionBaseLog(10),DecompositionLevelCount(LEVELS),CiphertextModulus::new_native());
 let t=Instant::now();encrypt_constant_ggsw_ciphertext(&secret,&mut raw,Cleartext(1u32),profile.glwe_noise_distribution,&mut enc);let generation_ns=t.elapsed().as_nanos();save(&new.join("public_raw_ggsw.ct"),&raw)?;
 let t=Instant::now();let exact=exact_ntt(raw.as_ref(),&digits);let ntt_ns=t.elapsed().as_nanos();
 let t=Instant::now();let reference=direct(raw.as_ref(),&digits);let direct_ns=t.elapsed().as_nanos();assert_eq!(exact.signed,reference);
 let mut exact_ct=delta.clone();exact_ct.as_mut().copy_from_slice(&exact.output);save(&new.join("exact_ntt_external_product.ct"),&exact_ct)?;
 let mut kara=delta.clone();kara.as_mut().fill(0);let mut buffers=ComputationBuffers::new();buffers.resize(karatsuba_add_external_product_assign_scratch::<u32>(GlweSize(G),PolynomialSize(N)).unaligned_bytes_required());
 let t=Instant::now();karatsuba_add_external_product_assign(kara.as_mut_view(),raw.as_view(),delta.as_view(),buffers.stack());let karatsuba_ns=t.elapsed().as_nanos();assert_eq!(kara.as_ref(),exact_ct.as_ref());save(&new.join("karatsuba_external_product.ct"),&kara)?;
 let mut fourier=FourierGgswCiphertext::new(GlweSize(G),PolynomialSize(N),DecompositionBaseLog(10),DecompositionLevelCount(LEVELS));
 let t=Instant::now();convert_standard_ggsw_ciphertext_to_fourier(&raw,&mut fourier);let fourier_conversion_ns=t.elapsed().as_nanos();save(&new.join("public_fourier_ggsw.ct"),&fourier)?;
 let mut fft=delta.clone();fft.as_mut().fill(0);let t=Instant::now();add_external_product_assign(&mut fft,&fourier,&delta);let fft_ns=t.elapsed().as_nanos();save(&new.join("fft_external_product.ct"),&fft)?;
 let mut plaintext=PlaintextList::new(0u32,PlaintextCount(N));decrypt_glwe_ciphertext(&secret,&exact_ct,&mut plaintext);let expected=&delta.as_ref()[(G-1)*N..];let plaintext_error=torus_diff(plaintext.as_ref(),expected);
 // Only public source/input/output and aggregate public-target comparison survive this scope.
 fs::write(new.join("ntt_public.json"),serde_json::to_vec(&json!({"key_ntt":exact.key_ntt,"digits_ntt":exact.digits_ntt,"output_residues":exact.residues,"signed_reconstructed":exact.signed.iter().map(|x|x.to_string()).collect::<Vec<_>>()}))?)?;
 fs::write(new.join("recurrence_public.json"),serde_json::to_vec(&indexed_rows(raw.as_ref(),exact_ct.as_ref()))?)?;
 let report=json!({"claim":"EXECUTED new exact CRT-NTT external-product backend on genuine saved TFHE input; separate fresh public evaluation block","prefix":prefix,"certificate":cert,"origins":origins,"public_selector":1,"new_glwe_secret_keys":1,"new_raw_ggsw_blocks":1,"new_bootstraps":0,"secret_key_or_rng_serialized":false,"profile":{"scalar":"u32","polynomial_size":N,"glwe_size":G,"base_log":10,"levels":LEVELS,"glwe_noise":"DEFAULT_PARAMETERS.glwe_noise_distribution"},"generation_ns":generation_ns,"ntt_ns":ntt_ns,"direct_reference_ns":direct_ns,"karatsuba_ns":karatsuba_ns,"fourier_conversion_ns":fourier_conversion_ns,"fft_external_product_ns":fft_ns,"crt_equals_complete_signed_reference":true,"exact_ntt_equals_existing_karatsuba":true,"fft_comparison":torus_diff(exact_ct.as_ref(),fft.as_ref()),"ephemeral_decrypt_error_against_public_delta":plaintext_error,"raw_ggsw_sha256":hash(&fs::read(new.join("public_raw_ggsw.ct"))?),"exact_output_sha256":hash(&fs::read(new.join("exact_ntt_external_product.ct"))?),"complete_proof":"pending separate generated recurrence"});
 fs::write(new.join("report.json"),serde_json::to_vec_pretty(&report)?)?;println!("{report}");Ok(())
}
fn main()->Result<()>{let args:Vec<String>=std::env::args().collect();match args.get(1).map(String::as_str){Some("preflight")=>{println!("{}",preflight());Ok(())},Some("capture") if args.len()==4=>prepare(Path::new(&args[2]),Path::new(&args[3])),_=>Err("usage: preflight | capture OLD_DECOMPOSITION_PACKAGE NEW_PUBLIC_FIXTURE".into())}}
