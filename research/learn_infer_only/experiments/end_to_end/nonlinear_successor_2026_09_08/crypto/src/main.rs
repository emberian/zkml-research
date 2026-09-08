//! Actual BFV polynomial-kernel memory: SIMD dot products followed by ct×ct square.
use fhe::bfv::{BfvParameters,BfvParametersBuilder,Ciphertext,Encoding,EvaluationKey,EvaluationKeyBuilder,Multiplicator,Plaintext,PublicKey,SecretKey};
use fhe_math::{rns::ScalingFactor,rq::{Context,Poly,Representation,scaler::Scaler},zq::primes::generate_prime};
use fhe_traits::{DeserializeParametrized,FheDecoder,FheDecrypter,FheEncoder,FheEncrypter,Serialize};
use num_bigint::BigUint;
use serde_json::{json,Value};
use sha2::{Digest,Sha256};
use std::{collections::BTreeMap,error::Error,fs,io::Write,os::unix::fs::{OpenOptionsExt,PermissionsExt},path::Path,sync::Arc,time::Instant};
type Res<T>=Result<T,Box<dyn Error>>;
const N:usize=8192;const D:usize=576;const LANES:usize=8;const NORM2:i64=20000;
fn sha(b:&[u8])->String{Sha256::digest(b).iter().map(|x|format!("{x:02x}")).collect()}
fn t()->u64{generate_prime(32,2*N as u64,1u64<<32).unwrap()}
fn params()->Res<Arc<BfvParameters>>{Ok(BfvParametersBuilder::new().set_degree(N).set_plaintext_modulus(t()).set_moduli_sizes(&[50,50,50,50]).set_variance(10).build_arc()?)}
fn desc(p:&Arc<BfvParameters>)->Value{json!({"scheme":"BFV","N":N,"t":t(),"q":p.moduli(),"q_bits":p.moduli_sizes(),"variance":10,"level":0,"input_components":2,"kernel_components":3,"dimension":D,"lanes":LANES,"norm_squared_bound":NORM2,"sum_kernel_bound":3200000000u64,"slots":"feature_index*8+memory_lane; pad to1024features","column_rotations":[8,16,32,64,128,256,512,1024,2048],"row_swap":true,"multiplication":"real extended-RNS tensor square, native Scaler t/Q, no relinearization or modulus switching"})}
fn read(path:&str)->Res<Vec<u8>>{let m=fs::metadata(path)?;if m.len()>128_000_000{return Err("input file too large".into())}Ok(fs::read(path)?)}
fn write(path:&str,b:&[u8],secret:bool)->Res<()>{let mut f=fs::OpenOptions::new().create_new(true).write(true).mode(if secret{0o600}else{0o644}).open(path)?;f.write_all(b)?;Ok(())}
fn canonical(ct:Ciphertext,p:&Arc<BfvParameters>)->Res<Ciphertext>{let mut out=Ciphertext::new(ct.iter().cloned().collect(),p)?;for c in out.iter_mut(){unsafe{c.allow_variable_time_computations()}}Ok(out)}
fn loadct(path:&str,p:&Arc<BfvParameters>,components:usize)->Res<Ciphertext>{let ct=Ciphertext::from_bytes(&read(path)?,p)?;if ct.len()!=components{return Err("wrong component count".into())}for poly in ct.iter(){if p.level_of_context(poly.ctx())?!=0{return Err("wrong level".into())}}canonical(ct,p)}
fn vecfile(path:&str)->Res<Vec<i64>>{let v:Vec<i64>=serde_json::from_slice(&read(path)?)?;if v.len()!=D||v.iter().any(|x|x.abs()>32)||v.iter().map(|x|x*x).sum::<i64>()>NORM2{return Err("expected576 integers, each[-32,32], squared norm<=20000".into())}Ok(v)}
fn residue(x:i64)->u64{x.rem_euclid(t() as i64)as u64}
fn save_ct(path:&str,ct:&Ciphertext)->Res<Value>{let b=ct.to_bytes();write(path,&b,false)?;Ok(json!({"sha256":sha(&b),"bytes":b.len(),"components":ct.len()}))}
fn dump_power(p:&Poly)->Value{assert_eq!(*p.representation(),Representation::PowerBasis);json!(p.coefficients().outer_iter().map(|r|r.to_vec()).collect::<Vec<_>>())}
fn basis(p:&Arc<BfvParameters>)->Vec<u64>{let count=(p.moduli_sizes().iter().sum::<usize>()+60).div_ceil(62);let mut b=p.moduli().to_vec();let mut upper=1u64<<62;while b.len()!=p.moduli().len()+count{upper=generate_prime(62,2*N as u64,upper).unwrap();if !b.contains(&upper){b.push(upper)}}b}
// Factored from the existing Multiplicator algorithm to capture the actual
// pre-/post-downscale PowerBasis values, before the final NTT conversion.
fn square(dot:&Ciphertext,p:&Arc<BfvParameters>,trace:bool)->Res<(Ciphertext,Option<Value>)>{
 let b=basis(p);let q:BigUint=p.moduli().iter().map(|&x|BigUint::from(x)).product();
 let extctx=Context::new_arc(&b,N)?;let ext=Scaler::new(dot[0].ctx(),&extctx,ScalingFactor::one())?;
 let down=Scaler::new(&extctx,dot[0].ctx(),ScalingFactor::new(&BigUint::from(t()),&q))?;
 let a0=dot[0].scale(&ext)?;let a1=dot[1].scale(&ext)?;
 let p0=&a0*&a0;let mut p1=&a0*&a1;p1+=&(&a1*&a0);let p2=&a1*&a1;
 let mut products=Vec::new();let mut scaled=Vec::new();let mut components=Vec::new();
 for mut product in [p0,p1,p2]{product.change_representation(Representation::PowerBasis);if trace{products.push(dump_power(&product))}
  let mut output=product.scale(&down)?;assert_eq!(*output.representation(),Representation::PowerBasis);if trace{scaled.push(dump_power(&output))}
  output.change_representation(Representation::Ntt);components.push(output);
 }
 let result=canonical(Ciphertext::new(components,p)?,p)?;
 let record=if trace{
  let native=Multiplicator::new(ScalingFactor::one(),ScalingFactor::one(),&b,ScalingFactor::new(&BigUint::from(t()),&q),p)?;
  let reference=canonical(native.multiply(dot,dot)?,p)?;if result.to_bytes()!=reference.to_bytes(){return Err("native Multiplicator comparison failed".into())}
  Some(json!({"N":N,"t":t(),"base":p.moduli(),"extended_base":b,"components":3,"product_extended_power_basis":products,"output_power_basis":scaled,"native_multiplicator_bytes_equal":true,"rounding":"actual native directed fixed-point RnsScaler; not ideal nearest-rounding oracle"}))
 }else{None};Ok((result,record))
}
fn main_run()->Res<Value>{
 let mut it=std::env::args().skip(1);let command=it.next().ok_or("command required")?;let mut a=BTreeMap::new();while let Some(k)=it.next(){let v=it.next().ok_or("missing argument")?;if a.insert(k,v).is_some(){return Err("duplicate option".into())}}
 let get=|k:&str|->Res<&str>{a.get(k).map(String::as_str).ok_or_else(||format!("missing{k}").into())};let p=params()?;let start=Instant::now();
 let mut result=match command.as_str(){
  "params"=>desc(&p),
  "keygen"=>{let dir=Path::new(get("--dir")?);let private=dir.join(".private");fs::create_dir(&private)?;fs::set_permissions(&private,fs::Permissions::from_mode(0o700))?;
   let mut rng=rand::rng();let sk=SecretKey::random(&p,&mut rng);let pk=PublicKey::new(&sk,&mut rng);let mut eb=EvaluationKeyBuilder::new(&sk)?;for shift in [8,16,32,64,128,256,512,1024,2048]{eb.enable_column_rotation(shift)?;}eb.enable_row_rotation()?;let ek=eb.build(&mut rng)?;
   write(dir.join("public.key").to_str().unwrap(),&pk.to_bytes(),false)?;write(dir.join("evaluation.key").to_str().unwrap(),&ek.to_bytes(),false)?;write(private.join("reader.key").to_str().unwrap(),&sk.to_bytes(),true)?;
   let pt=Plaintext::try_encode(&vec![0u64;N],Encoding::simd(),&p)?;let fresh=canonical(pk.try_encrypt(&pt,&mut rng)?,&p)?;let zero=canonical(&fresh-&fresh,&p)?;save_ct(dir.join("zero.ct").to_str().unwrap(),&zero)?;
   write(dir.join("parameters.json").to_str().unwrap(),&serde_json::to_vec_pretty(&desc(&p))?,false)?;json!({"parameters":desc(&p),"public_key_bytes":pk.to_bytes().len(),"evaluation_key_bytes":ek.to_bytes().len(),"full_reader_key":true})},
  "issue"=>{let dir=Path::new(get("--dir")?);let pk=PublicKey::from_bytes(&read(dir.join("public.key").to_str().unwrap())?,&p)?;let v=vecfile(get("--vector")?)?;let lane:usize=get("--lane")?.parse()?;if lane>=8{return Err("lane out of range".into())}let mut slots=vec![0u64;N];for(i,x)in v.iter().enumerate(){slots[i*8+lane]=residue(*x)}let pt=Plaintext::try_encode(&slots,Encoding::simd(),&p)?;let ct=canonical(pk.try_encrypt(&pt,&mut rand::rng())?,&p)?;save_ct(get("--out")?,&ct)?},
  "learn"=>{let mut acc=loadct(get("--acc")?,&p,2)?;let fresh=loadct(get("--fresh")?,&p,2)?;acc+=&fresh;if let Some(old)=a.get("--old"){acc-=&loadct(old,&p,2)?}let acc=canonical(acc,&p)?;save_ct(get("--out")?,&acc)?},
  "infer"=>{let dir=Path::new(get("--dir")?);let ek=EvaluationKey::from_bytes(&read(dir.join("evaluation.key").to_str().unwrap())?,&p)?;let ct=loadct(get("--acc")?,&p,2)?;let query=vecfile(get("--query")?)?;let mut slots=vec![0u64;N];for(i,x)in query.iter().enumerate(){for lane in 0..8{slots[i*8+lane]=residue(*x)}}let pt=Plaintext::try_encode(&slots,Encoding::simd(),&p)?;
   let dot_start=Instant::now();let mut dot=&ct*&pt;for shift in [8,16,32,64,128,256,512,1024,2048]{let rotated=ek.rotates_columns_by(&dot,shift)?;dot+=&rotated;}let swapped=ek.rotates_rows(&dot)?;dot+=&swapped;dot=canonical(dot,&p)?;let dot_ns=dot_start.elapsed().as_nanos();
   let trace=a.get("--trace");if let Some(prefix)=trace{save_ct(&format!("{prefix}.dot.ct"),&dot)?;}
   let mult_start=Instant::now();let(out,record)=square(&dot,&p,trace.is_some())?;let multiply_ns=mult_start.elapsed().as_nanos();let mut meta=save_ct(get("--out")?,&out)?;
   if let(Some(prefix),Some(mut rec))=(trace,record){rec["input_dot_sha256"]=json!(sha(&dot.to_bytes()));rec["output_sha256"]=json!(sha(&out.to_bytes()));write(&format!("{prefix}.json"),&serde_json::to_vec(&rec)?,false)?;}
   meta["dot_ns"]=json!(dot_ns);meta["ct_multiply_ns"]=json!(multiply_ns);meta["ct_ct_multiplications"]=json!(1);meta["rotation_count"]=json!(10);meta},
  "read"=>{let dir=Path::new(get("--dir")?);let sk=SecretKey::from_bytes(&read(dir.join(".private/reader.key").to_str().unwrap())?,&p)?;let ct=loadct(get("--ct")?,&p,3)?;let vals=Vec::<u64>::try_decode(&sk.try_decrypt(&ct)?,Encoding::simd())?;let first=vals[..8].to_vec();if first.iter().any(|x|*x>400000000)||vals.iter().enumerate().any(|(i,x)|*x!=first[i%8]){return Err("kernel value bound/repeated-lane check failed".into())}let sum:u64=first.iter().sum();if sum>3200000000{return Err("kernel sum bound failed".into())}json!({"sum_kernel":sum,"kernel_values":first,"all8192_slots_repeat8":true,"full_reader_key":true})},
  _=>return Err("unknown command".into())
 };result["elapsed_ns"]=json!(start.elapsed().as_nanos());Ok(result)
}
fn main(){match main_run(){Ok(v)=>println!("{v}"),Err(e)=>{eprintln!("{}",json!({"error":e.to_string()}));std::process::exit(2)}}}
