//! Real BFV integration fixture. The test reader deliberately holds the full key.
use std::{collections::VecDeque, error::Error, sync::Arc, time::Instant};
use fhe::bfv::{BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

const WIDTH: usize = 577;
const CAP: usize = 32;
type Res<T> = Result<T, Box<dyn Error>>;

// The host has no reference coefficients, labels, features or secret key.
struct HostRoute { acc: Ciphertext, queue: VecDeque<Ciphertext> }
impl HostRoute {
    fn new(p: &Arc<BfvParameters>) -> Self {
        Self { acc: Ciphertext::zero(p), queue: VecDeque::new() }
    }
    fn learn(&mut self, fresh: Ciphertext) -> (u128,u128,bool) {
        let start=Instant::now();
        self.acc += &fresh;
        let add_ns=start.elapsed().as_nanos();
        self.queue.push_back(fresh);
        let mut expiry_ns=0;
        let evicted=self.queue.len()>CAP;
        if evicted {
            let start=Instant::now();
            let original=self.queue.pop_front().unwrap();
            self.acc -= &original; // Exact stored object, never reencryption.
            expiry_ns=start.elapsed().as_nanos();
        }
        (add_ns,expiry_ns,evicted)
    }
    fn infer(&self, question: &[i64], p: &Arc<BfvParameters>) -> Res<Option<(Ciphertext,u128,u128)>> {
        assert_eq!(question.len(),WIDTH);
        assert!(question.iter().all(|q|q.abs()<=127));
        if self.queue.is_empty() { return Ok(None); } // Public empty state.
        let start=Instant::now();
        let plus:Vec<u64>=question.iter().rev().map(|v|(*v).max(0) as u64).collect();
        let minus:Vec<u64>=question.iter().rev().map(|v|(-*v).max(0) as u64).collect();
        let pp=Plaintext::try_encode(&plus,Encoding::poly(),p)?;
        let pm=Plaintext::try_encode(&minus,Encoding::poly(),p)?;
        let encoding_ns=start.elapsed().as_nanos();
        let start=Instant::now();
        let mut answer=&self.acc*&pp;
        answer -= &(&self.acc*&pm);
        let host_ns=start.elapsed().as_nanos();
        Ok(Some((answer,encoding_ns,host_ns)))
    }
}

fn integers(parts: &[&str]) -> Vec<i64> { parts.iter().map(|s|s.parse().unwrap()).collect() }
fn run_history(lines: &[&str], p: &Arc<BfvParameters>) -> Res<()> {
    let h:Vec<_>=lines[0].split_whitespace().collect();
    assert_eq!(h[0],"H");
    let history:usize=h[1].parse()?; let seed:u8=h[2].parse()?;
    let start=Instant::now();
    let mut rng=ChaCha20Rng::from_seed([seed;32]);
    let sk=SecretKey::random(p,&mut rng);
    let pk=PublicKey::new(&sk,&mut rng);
    let keygen_ns=start.elapsed().as_nanos();
    let public_key_bytes=pk.to_bytes().len();
    let mut hosts=[HostRoute::new(p),HostRoute::new(p)];
    let (mut adds,mut subs,mut encrypted_queries,mut structural_queries,mut checks)=(0,0,0,0,0);
    let (mut input_bytes,mut output_bytes,mut peak_persistent_bytes)=(0,0,0);
    let (mut peak_retained_ct,mut peak_update_live_ct)=(0,0);
    let mut ciphertext_bytes=0;
    let history_start=Instant::now();
    println!("{{\"kind\":\"history\",\"history\":{history},\"rng_byte\":{seed},\"keygen_ns\":{keygen_ns},\"public_key_bytes\":{public_key_bytes}}}");
    for line in &lines[1..] {
        let x:Vec<_>=line.split_whitespace().collect();
        match x[0] {
            "L" => {
                let phase:usize=x[1].parse()?; let step:usize=x[2].parse()?;
                let route:usize=x[3].parse()?; let record:usize=x[4].parse()?;
                let contribution=integers(&x[6..]);
                assert_eq!(contribution.len(),WIDTH);
                assert!(contribution.iter().all(|z|z.abs()<=127));
                let start=Instant::now();
                let values:Vec<u64>=contribution.iter().map(|z|z.rem_euclid(p.plaintext() as i64) as u64).collect();
                let pt=Plaintext::try_encode(&values,Encoding::poly(),p)?;
                let encode_ns=start.elapsed().as_nanos();
                let start=Instant::now();
                let fresh:Ciphertext=pk.try_encrypt(&pt,&mut rng)?;
                let encrypt_ns=start.elapsed().as_nanos();
                let start=Instant::now();
                let fresh_bytes=fresh.to_bytes().len();
                let serialize_ns=start.elapsed().as_nanos();
                if ciphertext_bytes==0 {ciphertext_bytes=fresh_bytes;}
                assert_eq!(fresh_bytes,ciphertext_bytes);
                input_bytes+=fresh_bytes;
                let (add_ns,expiry_ns,evicted)=hosts[route].learn(fresh);
                adds+=1;subs+=usize::from(evicted);
                let active_acc=hosts.iter().filter(|r|!r.queue.is_empty()).count();
                let retained=hosts.iter().map(|r|r.queue.len()).sum::<usize>()+active_acc;
                peak_retained_ct=peak_retained_ct.max(retained);
                peak_update_live_ct=peak_update_live_ct.max(retained+usize::from(evicted));
                peak_persistent_bytes=peak_persistent_bytes.max(retained*ciphertext_bytes);
                println!("{{\"kind\":\"learn\",\"history\":{history},\"phase\":{phase},\"step\":{step},\"route\":{route},\"record\":{record},\"queue\":{},\"evicted\":{evicted},\"ciphertext_bytes\":{fresh_bytes},\"encode_ns\":{encode_ns},\"encrypt_ns\":{encrypt_ns},\"serialize_ns\":{serialize_ns},\"host_add_ns\":{add_ns},\"host_expiry_ns\":{expiry_ns}}}",hosts[route].queue.len());
            },
            "P" => {
                let phase:usize=x[1].parse()?;let route:usize=x[2].parse()?;
                let expected_count:usize=x[3].parse()?;let expected=integers(&x[4..]);
                let host=&hosts[route];assert_eq!(host.queue.len(),expected_count);
                let start=Instant::now();let mut serialized_bytes=0;
                if host.queue.is_empty() {
                    assert!(host.acc.is_empty());assert!(expected.iter().all(|x|*x==0));
                } else {
                    let mut sum=Ciphertext::zero(p);
                    for c in &host.queue {sum+=c;serialized_bytes+=c.to_bytes().len();}
                    let actual=host.acc.to_bytes();assert_eq!(actual,sum.to_bytes());
                    assert_eq!(actual.len(),ciphertext_bytes);serialized_bytes+=actual.len();
                    let decoded=Vec::<u64>::try_decode(&sk.try_decrypt(&host.acc)?,Encoding::poly())?;
                    assert_eq!(decoded.len(),p.degree());
                    for (i,&v) in decoded.iter().enumerate() {
                        let want=if i<WIDTH {expected[i]} else {0};
                        assert_eq!(v,want.rem_euclid(p.plaintext() as i64) as u64,"accumulator mismatch");
                    }
                }
                checks+=1;let diagnostic_ns=start.elapsed().as_nanos();
                println!("{{\"kind\":\"checkpoint\",\"history\":{history},\"phase\":{phase},\"route\":{route},\"queue\":{expected_count},\"empty\":{},\"serialized_queue_and_acc_bytes\":{serialized_bytes},\"exact_queue\":true,\"all_coefficients_equal\":true,\"diagnostic_ns\":{diagnostic_ns}}}",host.queue.is_empty());
            },
            "Q" => {
                let phase:usize=x[1].parse()?;let record:usize=x[2].parse()?;let route:usize=x[3].parse()?;
                let expected:i64=x[4].parse()?;let target:i64=x[5].parse()?;let question=integers(&x[6..]);
                let answer=hosts[route].infer(&question,p)?;
                let (got,encoded,host_ns,reader_ns,serialize_ns,answer_bytes,is_encrypted)=match answer {
                    None => {structural_queries+=1;(0,0,0,0,0,0,false)},
                    Some((ct,encoded,host_ns)) => {
                        encrypted_queries+=1;
                        let start=Instant::now();let answer_bytes=ct.to_bytes().len();
                        let serialize_ns=start.elapsed().as_nanos();output_bytes+=answer_bytes;
                        assert_eq!(answer_bytes,ciphertext_bytes);
                        let start=Instant::now();
                        let decoded=Vec::<u64>::try_decode(&sk.try_decrypt(&ct)?,Encoding::poly())?;
                        assert_eq!(decoded.len(),p.degree());
                        let r=decoded[WIDTH-1];let t=p.plaintext();
                        let got=if r>t/2 {r as i64-t as i64} else {r as i64};
                        let reader_ns=start.elapsed().as_nanos();
                        (got,encoded,host_ns,reader_ns,serialize_ns,answer_bytes,true)
                    }
                };
                assert_eq!(got,expected,"declared query {record} phase {phase} history {history}");
                let predicted=if got>=0 {1} else {-1};
                println!("{{\"kind\":\"query\",\"history\":{history},\"phase\":{phase},\"record\":{record},\"route\":{route},\"expected\":{expected},\"decrypted_signed\":{got},\"target\":{target},\"prediction\":{predicted},\"encrypted\":{is_encrypted},\"exact\":true,\"encode_ns\":{encoded},\"host_ns\":{host_ns},\"reader_ns\":{reader_ns},\"serialize_ns\":{serialize_ns},\"answer_bytes\":{answer_bytes}}}");
            },
            _ => panic!("unknown fixture record")
        }
    }
    assert_eq!((adds,subs,encrypted_queries,structural_queries,checks),(192,128,40,8,6));
    let elapsed_ns=history_start.elapsed().as_nanos();
    println!("{{\"kind\":\"summary\",\"history\":{history},\"learn_adds\":{adds},\"learn_expiry_subs\":{subs},\"encrypted_queries\":{encrypted_queries},\"structural_queries\":{structural_queries},\"query_ct_pt_products\":{},\"query_ct_subtractions\":{encrypted_queries},\"checkpoint_routes\":{checks},\"input_bytes\":{input_bytes},\"output_bytes\":{output_bytes},\"ciphertext_bytes\":{ciphertext_bytes},\"peak_persistent_ciphertexts\":{peak_retained_ct},\"peak_update_live_ciphertexts\":{peak_update_live_ct},\"peak_persistent_serialized_bytes\":{peak_persistent_bytes},\"elapsed_ns\":{elapsed_ns},\"pass\":true}}",encrypted_queries*2);
    Ok(())
}

fn main() -> Res<()> {
    let path=std::env::args().nth(1).expect("fixture.txt path required");
    let data=std::fs::read_to_string(path)?;
    let mut iter=data.lines();assert_eq!(iter.next(),Some("Q83_WINDOW_V1 577 32 2"));
    let start=Instant::now();
    let p=BfvParametersBuilder::new().set_degree(4096).set_plaintext_modulus(4294828033)
        .set_moduli_sizes(&[41,42]).set_variance(10).build_arc()?;
    assert_eq!(p.moduli(),&[2199023190017,4398046486529]);
    assert!(((WIDTH*CAP*127*127) as u64)<p.plaintext()/2);
    assert!(2*(WIDTH-1)<p.degree());
    let params_ns=start.elapsed().as_nanos();
    println!("{{\"kind\":\"parameters\",\"degree\":4096,\"plaintext_modulus\":4294828033,\"q_factors\":[2199023190017,4398046486529],\"width\":577,\"route_capacity\":32,\"variance\":10,\"params_ns\":{params_ns},\"whole_polynomial_test_decryption\":true,\"full_key_retained\":true,\"public_test_rng\":true}}");
    let mut lines=Vec::new();let mut histories=0;
    for line in iter {
        if line=="END" {run_history(&lines,&p)?;histories+=1;lines.clear();}
        else {lines.push(line);}
    }
    assert!(lines.is_empty());assert_eq!(histories,2);
    println!("{{\"kind\":\"complete\",\"histories\":2,\"pass\":true}}");
    Ok(())
}
