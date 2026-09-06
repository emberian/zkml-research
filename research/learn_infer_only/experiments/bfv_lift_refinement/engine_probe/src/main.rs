//! Full coefficient oracle for pinned fhe-dregg/fhe-math. Synthetic public fixtures only.
use fhe::bfv::{BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, Multiplicator, Plaintext, PublicKey, SecretKey};
use fhe_math::{rns::{RnsContext, RnsScaler, ScalingFactor}, rq::{scaler::Scaler, traits::TryConvertFrom, Context, Poly, Representation}, zq::primes::generate_prime};
use fhe_traits::{FheEncoder, FheEncrypter};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::{json,Value};
use std::{error::Error,sync::Arc};

fn dump_poly(p:&Poly)->Value {
    let mut p=p.clone();p.change_representation(Representation::PowerBasis);
    json!({"moduli":p.ctx().moduli(),"rows":p.coefficients().outer_iter().map(|r|r.to_vec()).collect::<Vec<_>>()})
}
fn extension_basis(par:&Arc<BfvParameters>)->Vec<u64> {
    let count=(par.moduli_sizes().iter().sum::<usize>()+60).div_ceil(62);
    let mut basis=par.moduli().to_vec();let mut upper=1u64<<62;
    while basis.len()!=par.moduli().len()+count {
        upper=generate_prime(62,2*par.degree() as u64,upper).unwrap();
        if !basis.contains(&upper) {basis.push(upper);}
    }
    basis
}
fn full_case(par:&Arc<BfvParameters>,seed:u8,label:&str)->Result<Value,Box<dyn Error>> {
    let mut rng=ChaCha20Rng::from_seed([seed;32]);let sk=SecretKey::random(par,&mut rng);let pk=PublicKey::new(&sk,&mut rng);
    let pa=Plaintext::try_encode(&[1u64,2,3],Encoding::poly(),par)?;
    let pb=Plaintext::try_encode(&[4u64,5,6],Encoding::poly(),par)?;
    let a:Ciphertext=pk.try_encrypt(&pa,&mut rng)?;let b:Ciphertext=pk.try_encrypt(&pb,&mut rng)?;
    evaluate_pair(par,&a,&b,seed,label)
}
fn evaluate_pair(par:&Arc<BfvParameters>,a:&Ciphertext,b:&Ciphertext,seed:u8,label:&str)->Result<Value,Box<dyn Error>> {
    let basis=extension_basis(par);let q:BigUint=par.moduli().iter().map(|&x|BigUint::from(x)).product();
    // Same public default basis/factors, with relinearization disabled by construction.
    let mult=Multiplicator::new(ScalingFactor::one(),ScalingFactor::one(),&basis,ScalingFactor::new(&BigUint::from(par.plaintext()),&q),par)?;
    let result=mult.multiply(&a,&b)?;assert_eq!(result.len(),3);
    let ctx=Context::new_arc(&basis,par.degree())?;
    let ext=Scaler::new(a[0].ctx(),&ctx,ScalingFactor::one())?;
    let ae=[a[0].scale(&ext)?,a[1].scale(&ext)?];let be=[b[0].scale(&ext)?,b[1].scale(&ext)?];
    let p0=&ae[0]*&be[0];let mut p1=&ae[0]*&be[1];p1+=&(&ae[1]*&be[0]);let p2=&ae[1]*&be[1];
    Ok(json!({"kind":"full_unrelinearized_tensor","label":label,"seed":seed,"N":par.degree(),"t":par.plaintext(),"base":par.moduli(),"extended_base":basis,
      "a":a.iter().map(dump_poly).collect::<Vec<_>>(),"b":b.iter().map(dump_poly).collect::<Vec<_>>(),
      "a_extended":ae.iter().map(dump_poly).collect::<Vec<_>>(),"b_extended":be.iter().map(dump_poly).collect::<Vec<_>>(),
      "product_extended":[dump_poly(&p0),dump_poly(&p1),dump_poly(&p2)],"output":result.iter().map(dump_poly).collect::<Vec<_>>() }))
}
fn inv_small(a:u64,m:u64)->u64 {
    let(mut old_r,mut r,mut old_s,mut ss)=(a as i128,m as i128,1i128,0i128);
    while r!=0 {let q=old_r/r;(old_r,r)=(r,old_r-q*r);(old_s,ss)=(ss,old_s-q*ss);}
    assert_eq!(old_r,1);old_s.rem_euclid(m as i128) as u64
}
fn tight_round_input(q:&BigUint,t:u64,offset:i64)->BigUint {
    let half=q>>1usize;let r:BigUint=if offset<0 {half-BigUint::from((-offset)as u64)}else{half+BigUint::from(offset as u64)};
    let qm=(q%t).to_u64().unwrap();let rm=(&r%t).to_u64().unwrap();
    let k=((t-rm)%t)*inv_small(qm,t)%t;
    (BigUint::from(k)*q+r)/t
}
fn structured_case(par:&Arc<BfvParameters>,x:&BigUint,label:&str)->Result<Value,Box<dyn Error>> {
    let ctx=par.context_at_level(0)?;
    let constant=|value:BigUint|->Result<Poly,Box<dyn Error>> {
        let mut p=Poly::try_convert_from(&[value],ctx,false,Representation::PowerBasis)?;
        p.change_representation(Representation::Ntt);Ok(p)
    };
    let a=Ciphertext::new(vec![constant(x.clone())?,constant(BigUint::from(0u64))?],par)?;
    let b=Ciphertext::new(vec![constant(BigUint::from(1u64))?,constant(BigUint::from(0u64))?],par)?;
    evaluate_pair(par,&a,&b,0,label)
}
fn scalar_cases(par:&Arc<BfvParameters>)->Result<Value,Box<dyn Error>> {
    let base=par.moduli();let extbase=extension_basis(par);let from=Arc::new(RnsContext::new(base)?);let extended=Arc::new(RnsContext::new(&extbase)?);
    let ext=RnsScaler::new(&from,&extended,ScalingFactor::one());
    let down=RnsScaler::new(&extended,&from,ScalingFactor::new(&BigUint::from(par.plaintext()),from.modulus()));
    let q=from.modulus();let t=BigUint::from(par.plaintext());let qhalf=q>>1;
    let mut near_half=Vec::new();
    for offset in -32i64..=32 {
        let x=if offset<0 {&qhalf-BigUint::from((-offset)as u64)}else{&qhalf+BigUint::from(offset as u64)};
        let rests=from.project(&x);let out=ext.scale_new((&rests).into(),extbase.len());
        near_half.push(json!({"x":x.to_string(),"input":rests,"output":out}));
    }
    let mut near_round=Vec::new();
    // x=floor((kQ+Q/2)/t)+offset places tx/Q close to an output rounding boundary.
    for k in [0u64,1,7,100,65535] {
        let center=(BigUint::from(k)*q+&qhalf)/&t;
        for offset in -2i64..=2 {
            let x=if offset<0 {&center-BigUint::from((-offset)as u64)}else{&center+BigUint::from(offset as u64)};
            let rests=extended.project(&x);let out=down.scale_new((&rests).into(),base.len());
            near_round.push(json!({"x":x.to_string(),"input":rests,"output":out}));
        }
    }
    for offset in -32i64..=32 {
        let x=tight_round_input(q,par.plaintext(),offset);
        let rests=extended.project(&x);let out=down.scale_new((&rests).into(),base.len());
        near_round.push(json!({"x":x.to_string(),"input":rests,"output":out,"target":"tz_mod_Q_near_half","offset":offset}));
    }
    Ok(json!({"kind":"scalar_boundary_cases","base":base,"extended_base":extbase,"t":par.plaintext(),"extension":near_half,"downscale":near_round}))
}
fn main()->Result<(),Box<dyn Error>> {
    let small=BfvParametersBuilder::new().set_degree(16).set_plaintext_modulus(17).set_moduli_sizes(&[20,20]).build_arc()?;
    let deployed=BfvParameters::default_parameters_128(20)?.nth(2).unwrap();
    println!("{}",json!({"kind":"metadata","label":"EXECUTED full public synthetic coefficient oracle; no privacy/PQ/noise claim","strategy":"Multiplicator default basis/factors, no relin, no modulus switch"}));
    for seed in [7,19,43,101] {println!("{}",full_case(&small,seed,"N16_admissible_arithmetic_only")?);}
    println!("{}",full_case(&deployed,7,"N4096_actual_parameter_shape")?);
    let q=deployed.context_at_level(0)?.modulus();
    println!("{}",structured_case(&deployed,&((q>>1usize)-BigUint::from(1u64)),"N4096_structured_extension_boundary")?);
    for offset in [-2i64,-1,0,1,2] {
        println!("{}",structured_case(&deployed,&tight_round_input(q,deployed.plaintext(),offset),&format!("N4096_structured_rounding_boundary_{offset}"))?);
    }
    println!("{}",scalar_cases(&small)?);println!("{}",scalar_cases(&deployed)?);
    Ok(())
}
