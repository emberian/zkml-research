//! Exact sliding-window ciphertext cancellation; no no-master-read claim.
use std::collections::VecDeque;
use std::error::Error;
use fhe::bfv::{BfvParametersBuilder, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

fn run_window(width:usize,window:usize,steps:usize,input_bound:usize,
              plaintext_bits:usize,seeds:&[u8],falsifiers:bool) -> Result<(), Box<dyn Error>> {
    let params=BfvParametersBuilder::new().set_degree(4096)
        .set_plaintext_modulus(4294828033).set_moduli_sizes(&[41,42])
        .set_variance(10).build_arc()?;
    assert_eq!(plaintext_bits,32);
    let q:u128=params.moduli().iter().map(|p|*p as u128).product();
    let q_bits=128-q.leading_zeros();
    assert!(q_bits<=83);
    assert!(params.moduli().iter().all(|p|p%8192==1));
    assert_eq!(params.plaintext()%8192,1);
    let conservative_min_q:u128=264008552994527828978432;
    assert!(q>conservative_min_q);
    println!("MODULUS total_Q={q} bitlength={q_bits} computation_primes=2 special_keyswitch_primes=0 rotations=0 relinearizations=0 conservative_min_Q_exclusive={conservative_min_q}");
    let t=params.plaintext();
    let (width,window,steps)=(width,window,steps);
    println!("STATUS real_BFV_window_arithmetic test_reader_retains_full_key=true no_PQ_bits_claim");
    println!("PARAMS N={} t={t} Q_factors={:?} width={width} window={window} steps={steps} input_bound={input_bound}",params.degree(),params.moduli());
    for &seed in seeds {
        let mut rng=ChaCha20Rng::from_seed([seed;32]);
        let sk=SecretKey::random(&params,&mut rng);
        let pk=PublicKey::new(&sk,&mut rng);
        let mut queue: VecDeque<(Ciphertext,Vec<i64>)>=VecDeque::new();
        let mut acc=Ciphertext::zero(&params);
        let mut reference=vec![0i64;width];
        let mut input_bytes=0usize;
        let mut subtraction_count=0usize;
        let mut equality_checks=0usize;
        let mut max_meter_bits=0usize;
        for step in 0..steps {
            let u:Vec<i64>=(0..width).map(|i| ((step*(i+1)+seed as usize+i*i)%(2*input_bound+1)) as i64-input_bound as i64).collect();
            let encoded: Vec<u64>=u.iter().map(|v|v.rem_euclid(t as i64) as u64).collect();
            let pt=Plaintext::try_encode(&encoded,Encoding::poly(),&params)?;
            let fresh: Ciphertext=pk.try_encrypt(&pt,&mut rng)?;
            input_bytes += fresh.to_bytes().len();
            acc += &fresh;
            for i in 0..width { reference[i]+=u[i]; }
            queue.push_back((fresh,u));
            if queue.len()>window {
                let (old,old_u)=queue.pop_front().unwrap();
                acc -= &old; // the very same ciphertext, not a reencryption
                for i in 0..width { reference[i]-=old_u[i]; }
                subtraction_count+=1;
            }
            if (step+1)%64==0 {
                let mut recomputed=Ciphertext::zero(&params);
                for (ct,_) in &queue { recomputed += ct; }
                assert_eq!(acc.to_bytes(),recomputed.to_bytes());
                let decoded=Vec::<u64>::try_decode(&sk.try_decrypt(&acc)?,Encoding::poly())?;
                for i in 0..width {
                    assert_eq!(decoded[i],reference[i].rem_euclid(t as i64) as u64);
                    assert!(reference[i].abs()<=(window*input_bound) as i64);
                }
                max_meter_bits=max_meter_bits.max(unsafe{sk.measure_noise(&acc)?});
                equality_checks+=1;
            }
        }
        let question:Vec<i64>=(0..width).map(|i|if input_bound==1 { i64::from(i%3==0) }
            else { ((i*i+seed as usize)%(2*input_bound+1)) as i64-input_bound as i64 }).collect();
        let qplus:Vec<u64>=question.iter().rev().map(|v|(*v).max(0) as u64).collect();
        let qminus:Vec<u64>=question.iter().rev().map(|v|(-*v).max(0) as u64).collect();
        let pt_question=Plaintext::try_encode(&qplus,Encoding::poly(),&params)?;
        let mut answer=&acc*&pt_question;
        let mut readout_products=1;
        if qminus.iter().any(|v|*v!=0) {
            let pt_minus=Plaintext::try_encode(&qminus,Encoding::poly(),&params)?;
            answer -= &(&acc*&pt_minus);
            readout_products+=1;
        }
        let decoded=Vec::<u64>::try_decode(&sk.try_decrypt(&answer)?,Encoding::poly())?;
        let expected:i64=reference.iter().zip(question).map(|(w,q)|w*q).sum();
        assert!(((width*window*input_bound*input_bound) as u64)<t/2);
        assert_eq!(decoded[width-1],expected.rem_euclid(t as i64) as u64);
        println!("WINDOW_POSITIVE seed={seed} ct_add={steps} ct_sub={subtraction_count} exact_queue_equalities={equality_checks} output_ct_pt_mul={readout_products} output_ct_sub={} expected_signed_score={expected} observed_residue={} max_observed_noise_bits={max_meter_bits}",readout_products-1,decoded[width-1]);
        println!("WINDOW_BYTES seed={seed} acc={} queue={} input_total={input_bytes} answer={} public_key={} live_acc_plus_queue_raw_RNS_bytes={}",acc.to_bytes().len(),queue.iter().map(|(c,_)|c.to_bytes().len()).sum::<usize>(),answer.to_bytes().len(),pk.to_bytes().len(),(window+1)*2*params.degree()*params.moduli().len()*8);
        if !falsifiers { continue; }

        // Same plaintext is insufficient for cancellation. A fresh encryption
        // of the oldest private contribution changes the retained ciphertext.
        let (old,old_u)=queue.front().unwrap();
        let enc_old:Vec<u64>=old_u.iter().map(|v|v.rem_euclid(t as i64) as u64).collect();
        let old_pt=Plaintext::try_encode(&enc_old,Encoding::poly(),&params)?;
        let old_fresh:Ciphertext=pk.try_encrypt(&old_pt,&mut rng)?;
        let exact_expiry=&acc-old;
        let wrong_expiry=&acc-&old_fresh;
        assert_ne!(exact_expiry.to_bytes(),wrong_expiry.to_bytes());
        let right=Vec::<u64>::try_decode(&sk.try_decrypt(&exact_expiry)?,Encoding::poly())?;
        let wrong=Vec::<u64>::try_decode(&sk.try_decrypt(&wrong_expiry)?,Encoding::poly())?;
        assert_eq!(&right[..width],&wrong[..width]);
        println!("FRESH_REPLACEMENT_FALSIFIER seed={seed} cancellation_identity=false same_plaintext_still_correct=true scope=identity_not_immediate_decrypt_failure");

        // Host-public rerandomization of the expired ciphertext: old+Z where
        // Z is a valid encryption of zero. Reusing it leaves debt -kZ each
        // turnover; true same-ciphertext expiration would leave no debt.
        let zero=Plaintext::try_encode(&[0u64],Encoding::poly(),&params)?;
        let mut z:Ciphertext=pk.try_encrypt(&zero,&mut rng)?;
        for _ in 0..72 { let copy=z.clone();z+=&copy; }
        let zero_decoded=Vec::<u64>::try_decode(&sk.try_decrypt(&z)?,Encoding::poly())?;
        assert!(zero_decoded.iter().all(|x|*x==0));
        let valid_replacement=old+&z;
        let replacement_decoded=Vec::<u64>::try_decode(&sk.try_decrypt(&valid_replacement)?,Encoding::poly())?;
        let old_decoded=Vec::<u64>::try_decode(&sk.try_decrypt(old)?,Encoding::poly())?;
        assert_eq!(replacement_decoded,old_decoded);
        let mut bad_acc=acc.clone();
        let mut bad_queue=queue.clone();
        let mut bad_reference=reference.clone();
        let mut fail=None;
        for step in 1..=4096usize {
            let fresh_zero:Ciphertext=pk.try_encrypt(&zero,&mut rng)?;
            let (expired,expired_u)=bad_queue.pop_front().unwrap();
            let rerandomized_expired=&expired+&z;
            bad_acc += &fresh_zero;
            bad_acc -= &rerandomized_expired;
            bad_queue.push_back((fresh_zero,vec![0i64;width]));
            for i in 0..width { bad_reference[i]-=expired_u[i]; }
            let got=Vec::<u64>::try_decode(&sk.try_decrypt(&bad_acc)?,Encoding::poly())?;
            let want0=bad_reference[0].rem_euclid(t as i64) as u64;
            if got[0]!=want0 {
                fail=Some(step);
                println!("RERANDOMIZED_EXPIRY_DEBT_FAILURE seed={seed} zero_amplification_doublings=72 replacements={step} expected_coefficient0={want0} observed_coefficient0={} initial_rerandomized_old_same_plaintext=true",got[0]);
                break;
            }
        }
        assert!(fail.is_some(),"bounded demonstration did not find debt failure");
    }
    println!("PASS exact same-ciphertext window cancellation and signed public readout at Q83; expiry falsifiers belong to separate Q109 fixture");
    Ok(())
}

fn main() -> Result<(),Box<dyn Error>> {
    run_window(577,128,1024,127,32,&[109,137],false)?;
    Ok(())
}
