//! Public-seed oracle audit only; never prints secret bytes or private input.
use fhe::bfv::{BfvParametersBuilder,Ciphertext,Encoding,Plaintext,PublicKey,SecretKey};
use fhe_traits::{FheDecoder,FheDecrypter,FheEncoder,FheEncrypter,Serialize};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
fn main()->Result<(),Box<dyn std::error::Error>>{
    let p=BfvParametersBuilder::new().set_degree(4096).set_plaintext_modulus(4294828033)
        .set_moduli_sizes(&[41,42]).set_variance(10).build_arc()?;
    let mut a=ChaCha20Rng::from_seed([37;32]);let mut b=ChaCha20Rng::from_seed([37;32]);
    let ska=SecretKey::random(&p,&mut a);let skb=SecretKey::random(&p,&mut b);
    let pka=PublicKey::new(&ska,&mut a);let pkb=PublicKey::new(&skb,&mut b);
    let secret_equal=ska.to_bytes()==skb.to_bytes();assert!(secret_equal);
    let public_equal=pka.to_bytes()==pkb.to_bytes();assert!(!public_equal);
    let message=Plaintext::try_encode(&[37u64],Encoding::poly(),&p)?;
    let ct:Ciphertext=pka.try_encrypt(&message,&mut a)?;
    let decoded=Vec::<u64>::try_decode(&skb.try_decrypt(&ct)?,Encoding::poly())?;
    let cross_decryption=decoded[0]==37 && decoded[1..].iter().all(|x|*x==0);
    assert!(cross_decryption);
    println!("{}",serde_json::json!({"scope":"public-seed oracle only; no secret bytes printed",
        "caller_seed_byte":37,"raw_secret_keys_equal":secret_equal,
        "raw_secret_key_bytes":ska.to_bytes().len(),"public_keys_equal":public_equal,
        "regenerated_secret_cross_decrypts":cross_decryption,
        "conclusion":"public caller seed regenerates full secret credential despite nonreproducible public key bytes"}));
    Ok(())
}
