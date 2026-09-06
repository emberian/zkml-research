//! Actual serialization boundary controls. Test reader retains a full secret key.
use std::error::Error;
use std::panic::{catch_unwind,AssertUnwindSafe};
use fhe::bfv::{BfvParametersBuilder,Ciphertext,Encoding,Plaintext,PublicKey,SecretKey};
use fhe_traits::{DeserializeParametrized,FheDecoder,FheDecrypter,FheEncoder,FheEncrypter,Serialize};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
fn main()->Result<(),Box<dyn Error>> {
 let params=BfvParametersBuilder::new().set_degree(4096)
  .set_plaintext_modulus(4294828033).set_moduli_sizes(&[41,42]).set_variance(10).build_arc()?;
 let empty=Ciphertext::zero(&params);
 let empty_result=catch_unwind(AssertUnwindSafe(||empty.to_bytes()));
 println!("EMPTY_INITIAL_ZERO serialize_panics={} polynomial_count={}",empty_result.is_err(),empty.len());
 assert!(empty_result.is_err());
 let mut rng=ChaCha20Rng::from_seed([217;32]);
 let sk=SecretKey::random(&params,&mut rng);let pk=PublicKey::new(&sk,&mut rng);
 let pt=Plaintext::try_encode(&[5u64],Encoding::poly(),&params)?;
 let fresh:Ciphertext=pk.try_encrypt(&pt,&mut rng)?;
 let full_zero=&fresh-&fresh;
 let bytes=full_zero.to_bytes();
 let decoded=Ciphertext::from_bytes(&bytes,&params)?;
 let plain=Vec::<u64>::try_decode(&sk.try_decrypt(&decoded)?,Encoding::poly())?;
 assert!(plain.iter().all(|v|*v==0));
 println!("NONEMPTY_GROUP_ZERO serialize_ok=true polynomial_count={} serialized_bytes={} decrypts_zero=true",full_zero.len(),bytes.len());
 // Secret-key encryption supplies a seeded representation; adding a full
 // group-zero clears seed metadata while preserving exact polynomial objects.
 let seeded:Ciphertext=sk.try_encrypt(&pt,&mut rng)?;
 let expanded=&seeded+&full_zero;
 let same_polynomials=seeded.iter().zip(expanded.iter()).all(|(a,b)|a==b);
 let same_bytes=seeded.to_bytes()==expanded.to_bytes();
 let sd=Vec::<u64>::try_decode(&sk.try_decrypt(&seeded)?,Encoding::poly())?;
 let ed=Vec::<u64>::try_decode(&sk.try_decrypt(&expanded)?,Encoding::poly())?;
 assert_eq!(sd,ed);assert_eq!(sd[0],5);
 assert!(same_polynomials);assert!(!same_bytes);
 println!("SEEDED_ALIAS exact_polynomials_equal={} serialized_equal={} seeded_bytes={} expanded_bytes={} same_plaintext=true",same_polynomials,same_bytes,seeded.to_bytes().len(),expanded.to_bytes().len());
 println!("PASS serializer domain/normalization controls; no attack on PK window and no no-reader claim");
 Ok(())
}
