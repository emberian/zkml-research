//! Public-parameter constructor capture; no keys/ciphertexts/random sampling.
use fhe_math::rns::{RnsContext,RnsScaler,ScalingFactor};
use num_bigint::BigUint;
use serde_json::{json,Value};
use std::{fs,sync::Arc};
fn main(){let path=std::env::args().nth(1).expect("descriptor required");let d:Value=serde_json::from_slice(&fs::read(path).unwrap()).unwrap();let b:Vec<u64>=serde_json::from_value(d["base"].clone()).unwrap();let e:Vec<u64>=serde_json::from_value(d["extended_base"].clone()).unwrap();let t=d["t"].as_u64().unwrap();let from=Arc::new(RnsContext::new(&e).unwrap());let to=Arc::new(RnsContext::new(&b).unwrap());let q:BigUint=b.iter().map(|x|BigUint::from(*x)).product();let s=RnsScaler::new(&from,&to,ScalingFactor::new(&BigUint::from(t),&q));println!("{}",json!({"base":b,"extended_base":e,"t":t,"factor_numerator":t.to_string(),"factor_denominator":q.to_string(),"native_RnsScaler_constructor_debug":format!("{s:#?}"),"keys_or_ciphertexts_read":false,"cryptographic_operations":0}));}
