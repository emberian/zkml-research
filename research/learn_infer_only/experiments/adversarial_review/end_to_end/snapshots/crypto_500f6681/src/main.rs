//! Research benchmark R: keyless public BFV arithmetic; explicitly trusted reader.
use std::{collections::BTreeMap, error::Error, fs::{self,OpenOptions}, io::{Read,Write},
    os::unix::fs::OpenOptionsExt, sync::Arc, time::Instant};
use fhe::bfv::{BfvParameters,BfvParametersBuilder,Ciphertext,Encoding,Plaintext,PublicKey,SecretKey};
use fhe_traits::{DeserializeParametrized,FheDecoder,FheDecrypter,FheEncoder,FheEncrypter,Serialize};
use prost::Message;
use rand::{CryptoRng,Rng,RngCore,SeedableRng};
use rand_chacha::ChaCha20Rng;
use serde_json::{json,Value};
use sha2::{Digest,Sha256};

type Res<T> = Result<T,Box<dyn Error>>;
const WIDTH:usize=577;
const CAP:usize=32;
const T:u64=4_294_828_033;
const SCORE_BOUND:i64=(WIDTH*CAP*127*127) as i64;
const MAGIC:&[u8;8]=b"RSBFV001";
const HEADER:usize=81;
const CT:u8=1; const PK:u8=2; const SK:u8=3;
const MAX_FILE:usize=200_000;
const PROGRAM:&str="resident-crypto-v1;BFV-poly-N4096-t4294828033-q2199023190017,4398046486529-CBDvariance10-level0-two-components;canonical-full-ct;learn=acc+fresh-exact_original_old;W32-per-public-route;two-routes;577-signed-int8-coordinates-bound127;infer=acc*reverse(max(q,0))-acc*reverse(max(-q,0));read=coefficient576-centered-mod-t-bound297805856-sign-ge0";

fn err(s:impl Into<String>)->Box<dyn Error>{s.into().into()}
fn digest(b:&[u8])->[u8;32]{Sha256::digest(b).into()}
fn hex(b:&[u8])->String{b.iter().map(|v|format!("{v:02x}")).collect()}
fn program_id()->String{hex(&digest(PROGRAM.as_bytes()))}
fn description()->Value{json!({"schema":"resident-crypto-parameters-v1","degree":4096,
    "plaintext_modulus":T,"ciphertext_moduli":[2199023190017u64,4398046486529u64],
    "variance":10,"level":0,"components":2,"width":WIDTH,"capacity_per_route":CAP,"routes":2,
    "input_coefficient_bound":127,"query_coefficient_bound":127,"signed_score_bound":SCORE_BOUND,
    "output_coefficient":576,"encoding":"polynomial;reversed-positive-minus-negative-query",
    "codec":"RSBFV001-kind-params32-key32-lengthLE64-canonicalpayload","program_id":program_id()})}
fn params_digest()->[u8;32]{digest(&serde_json::to_vec(&description()).unwrap())}
fn params_id()->String{hex(&params_digest())}
fn params()->Res<Arc<BfvParameters>>{
    let p=BfvParametersBuilder::new().set_degree(4096).set_plaintext_modulus(T)
        .set_moduli_sizes(&[41,42]).set_variance(10).build_arc()?;
    if p.moduli()!=[2199023190017,4398046486529] {return Err(err("parameter construction mismatch"));}
    Ok(p)
}

struct Args{command:String, values:BTreeMap<String,String>}
impl Args{
    fn parse()->Res<Self>{
        let mut it=std::env::args().skip(1);
        let command=it.next().ok_or_else(||err("command required"))?;
        let mut values=BTreeMap::new();
        while let Some(k)=it.next(){
            if !k.starts_with("--"){return Err(err("expected --name value"));}
            let v=it.next().ok_or_else(||err("missing argument value"))?;
            if values.insert(k,v).is_some(){return Err(err("duplicate argument"));}
        }
        Ok(Self{command,values})
    }
    fn get(&self,k:&str)->Res<&str>{self.values.get(k).map(String::as_str).ok_or_else(||err(format!("missing {k}")))}
    fn allow(&self,allowed:&[&str])->Res<()>{
        if self.values.keys().any(|k|!allowed.contains(&k.as_str())){return Err(err("unexpected argument for role"));} Ok(())
    }
}

// Read at most cap+1 bytes, even if the file grows after metadata inspection.
fn read_capped(path:&str,cap:usize)->Res<Vec<u8>>{
    let f=fs::File::open(path)?;
    if f.metadata()?.len()>cap as u64{return Err(err("file exceeds fixed byte cap"));}
    let mut out=Vec::new();f.take((cap+1) as u64).read_to_end(&mut out)?;
    if out.len()>cap{return Err(err("file exceeds fixed byte cap"));} Ok(out)
}
fn save(path:&str,bytes:&[u8],secret:bool)->Res<()>{
    let mut o=OpenOptions::new();o.write(true).create_new(true).mode(if secret{0o600}else{0o644});
    match o.open(path){
        Ok(mut f)=>{f.write_all(bytes)?;f.sync_all()?;Ok(())},
        Err(e) if e.kind()==std::io::ErrorKind::AlreadyExists=>{
            if read_capped(path,MAX_FILE)?==bytes{Ok(())}else{Err(err("output exists with different bytes"))}
        },Err(e)=>Err(e.into())
    }
}
fn wrap(kind:u8,key:&[u8;32],payload:&[u8])->Vec<u8>{
    let mut out=Vec::with_capacity(HEADER+payload.len());out.extend(MAGIC);out.push(kind);
    out.extend(params_digest());out.extend(key);out.extend((payload.len() as u64).to_le_bytes());
    out.extend(payload);out
}
struct Blob{bytes:Vec<u8>,payload:Vec<u8>,key:[u8;32]}
fn read_blob(path:&str,kind:u8)->Res<Blob>{
    let b=read_capped(path,MAX_FILE)?;
    if b.len()<HEADER || &b[..8]!=MAGIC || b[8]!=kind{return Err(err("wrong object magic/version/kind"));}
    if b[9..41]!=params_digest(){return Err(err("wrong fixed params identity"));}
    let length=u64::from_le_bytes(b[73..81].try_into().unwrap());
    if length>MAX_FILE as u64 || length as usize!=b.len()-HEADER{return Err(err("wrong payload length/trailing bytes"));}
    Ok(Blob{key:b[41..73].try_into().unwrap(),payload:b[81..].to_vec(),bytes:b})
}
fn meta(kind:&str,key:&[u8;32],bytes:&[u8])->Value{json!({"schema":"resident-crypto-result-v1",
    "kind":kind,"params_id":params_id(),"program_id":program_id(),"key_id":hex(key),
    "key_id_scope":"declared metadata; no proof ciphertext belongs to this key",
    "sha256":hex(&digest(bytes)),"bytes":bytes.len(),"payload_bytes":bytes.len()-HEADER,
    "canonical":true,"degree":4096,"level":0,"components":2})}

fn shape(proto:&fhe::proto::bfv::Ciphertext,allow_seed:bool)->Res<()>{
    if proto.level!=0{return Err(err("only ciphertext level 0 is allowed"));}
    let full=proto.seed.is_empty() && proto.c.len()==2;
    let seeded=allow_seed && proto.seed.len()==32 && proto.c.len()==1;
    if !full && !seeded{return Err(err("expected two full polynomials or allowed seeded equivalent"));}
    if proto.c.iter().any(|c|c.is_empty() || c.len()>60_000){return Err(err("polynomial byte shape rejected"));}
    Ok(())
}
fn canonical(ct:Ciphertext,p:&Arc<BfvParameters>)->Res<Ciphertext>{
    if ct.len()!=2{return Err(err("expected two ciphertext components"));}
    if ct.iter().any(|c|p.level_of_context(c.ctx()).ok()!=Some(0)){
        return Err(err("wrong ciphertext context/level"));
    }
    // Existing library constructor retains exactly the decoded NTT polynomials,
    // checks contexts/representations, and clears seeded serialization metadata.
    let mut ct=Ciphertext::new(ct.iter().cloned().collect(),p)?;
    // These polynomial coefficients are public ciphertext data. Canonical wire
    // encoding fixes this public-operation flag as well as the seeded/full mode.
    for polynomial in ct.iter_mut(){unsafe{polynomial.allow_variable_time_computations();}}
    Ok(ct)
}
fn decode_ct_payload(payload:&[u8],p:&Arc<BfvParameters>,allow_seed:bool)->Res<Ciphertext>{
    let proto=fhe::proto::bfv::Ciphertext::decode(payload)?;shape(&proto,allow_seed)?;
    let decoded=Ciphertext::from_bytes(payload,p)?;
    // Poly's decoder can pad a shorter serialized degree into this context.
    // Exact polynomial roundtrip forbids that (also unknown/duplicate fields),
    // including in the explicitly permitted precommit seeded normalization path.
    for (poly,wire) in decoded.iter().zip(proto.c.iter()){
        if poly.to_bytes()!=*wire{return Err(err("noncanonical polynomial degree/encoding"));}
    }
    canonical(decoded,p)
}
fn load_ct(path:&str,p:&Arc<BfvParameters>,strict:bool)->Res<(Blob,Ciphertext)>{
    let b=read_blob(path,CT)?;
    let ct=decode_ct_payload(&b.payload,p,!strict)?;
    let payload=ct.to_bytes();
    if payload.len()!=85_022{return Err(err("unexpected fixed ciphertext payload size"));}
    if strict && payload!=b.payload{return Err(err("noncanonical ciphertext payload"));}
    Ok((b,ct))
}
fn load_pk(path:&str,p:&Arc<BfvParameters>)->Res<(Blob,PublicKey)>{
    let b=read_blob(path,PK)?;
    if b.key!=digest(&b.payload){return Err(err("public-key identifier mismatch"));}
    let proto=fhe::proto::bfv::PublicKey::decode(b.payload.as_slice())?;
    let inner=proto.c.as_ref().ok_or_else(||err("missing public-key ciphertext"))?;
    decode_ct_payload(&inner.encode_to_vec(),p,true)?;
    let pk=PublicKey::from_bytes(&b.payload,p)?;
    if pk.to_bytes()!=b.payload{return Err(err("noncanonical public key"));}
    Ok((b,pk))
}
fn vector(bytes:&[u8])->Res<Vec<i64>>{
    let v:Value=serde_json::from_slice(bytes)?;
    let a=v.as_array().ok_or_else(||err("vector must be a JSON array"))?;
    if a.len()!=WIDTH{return Err(err("expected exactly 577 coefficients"));}
    a.iter().map(|x|{
        let n=x.as_i64().ok_or_else(||err("coefficient must be an integer, not boolean/float/overflow"))?;
        if !(-127..=127).contains(&n){return Err(err("coefficient outside [-127,127]"));} Ok(n)
    }).collect()
}
fn query_bytes(v:&[i64])->Vec<u8>{serde_json::to_vec(&json!({"schema":"resident-public-query-v1",
    "params_id":params_id(),"coefficients":v})).unwrap()}
fn load_query(path:&str)->Res<(Vec<u8>,Vec<i64>)>{
    let bytes=read_capped(path,20_000)?;let v:Value=serde_json::from_slice(&bytes)?;
    let obj=v.as_object().ok_or_else(||err("query must be object"))?;
    if obj.len()!=3 || v["schema"]!="resident-public-query-v1" || v["params_id"]!=params_id(){
        return Err(err("wrong query schema/params/fields"));
    }
    let q=vector(&serde_json::to_vec(&v["coefficients"])?)?;
    if query_bytes(&q)!=bytes{return Err(err("query encoding is not canonical; use encode-query before commitment"));}
    Ok((bytes,q))
}
fn issue<R:RngCore+CryptoRng>(pk:&PublicKey,v:&[i64],p:&Arc<BfvParameters>,rng:&mut R)->Res<Ciphertext>{
    let encoded:Vec<u64>=v.iter().map(|z|z.rem_euclid(T as i64) as u64).collect();
    let pt=Plaintext::try_encode(&encoded,Encoding::poly(),p)?;
    canonical(pk.try_encrypt(&pt,rng)?,p)
}
fn keygen<R:RngCore+CryptoRng>(a:&Args,p:&Arc<BfvParameters>,rng:&mut R,mode:&str)->Res<Value>{
    let sk=SecretKey::random(p,rng);let pk=PublicKey::new(&sk,rng);let raw=pk.to_bytes();let key=digest(&raw);
    let public=wrap(PK,&key,&raw);let secret=wrap(SK,&key,&sk.to_bytes());
    let fresh=issue(&pk,&vec![0;WIDTH],p,rng)?;
    let zero=canonical(&fresh-&fresh,p)?;let zero=wrap(CT,&key,&zero.to_bytes());
    save(a.get("--pk")?,&public,false)?;save(a.get("--sk")?,&secret,true)?;save(a.get("--zero")?,&zero,false)?;
    Ok(json!({"kind":"keygen","params_id":params_id(),"program_id":program_id(),"key_id":hex(&key),
        "rng":mode,"public_key":meta("public_key",&key,&public),"zero":meta("ciphertext",&key,&zero),
        "secret_key_bytes":secret.len(),"reader_trust":"benchmark R; single full-key reader; no no-master-read claim"}))
}
fn encrypt<R:RngCore+CryptoRng>(a:&Args,p:&Arc<BfvParameters>,rng:&mut R,mode:&str)->Res<Value>{
    let (pkb,pk)=load_pk(a.get("--pk")?,p)?;
    let v=vector(&read_capped(a.get("--vector")?,20_000)?)?;
    let ct=issue(&pk,&v,p,rng)?;let out=wrap(CT,&pkb.key,&ct.to_bytes());
    save(a.get("--out")?,&out,false)?;let mut m=meta("ciphertext",&pkb.key,&out);m["rng"]=json!(mode);Ok(m)
}

fn run()->Res<Value>{
    let a=Args::parse()?;let start=Instant::now();
    if a.command=="params"{
        a.allow(&[])?;return Ok(json!({"params_id":params_id(),"program_id":program_id(),"parameters":description(),
            "source_sha256":hex(&digest(include_bytes!("main.rs"))),"program_spec":PROGRAM}));
    }
    if a.command=="encode-query"{
        a.allow(&["--vector","--out"])?;let v=vector(&read_capped(a.get("--vector")?,20_000)?)?;
        let b=query_bytes(&v);save(a.get("--out")?,&b,false)?;
        return Ok(json!({"kind":"public_query","params_id":params_id(),"program_id":program_id(),
            "sha256":hex(&digest(&b)),"bytes":b.len(),"canonical":true,"width":WIDTH}));
    }
    if a.command=="issuer-private-vector"{
        a.allow(&["--out"])?;let mut rng=rand::rng();
        let v:Vec<i64>=(0..WIDTH).map(|_|rng.random_range(-127..=127)).collect();
        save(a.get("--out")?,&serde_json::to_vec(&v)?,true)?;
        return Ok(json!({"kind":"private_issuer_vector_created","width":WIDTH,"coefficient_bound":127,
            "rng":"rand::rng OS-seeded ThreadRng; no public seed","private_file_mode":"0600",
            "scope":"synthetic private ingress; no utility claim; values omitted from stdout"}));
    }
    let p=params()?;
    let mut result=match a.command.as_str(){
        "keygen"=>{a.allow(&["--pk","--sk","--zero"])?;
            keygen(&a,&p,&mut rand::rng(),"rand::rng OS-seeded ThreadRng; no public seed")?},
        "oracle-keygen"=>{a.allow(&["--pk","--sk","--zero","--seed"])?;
            let seed:u8=a.get("--seed")?.parse()?;keygen(&a,&p,&mut ChaCha20Rng::from_seed([seed;32]),"ORACLE ONLY: public deterministic ChaCha20 seed byte")?},
        "issuer-encrypt"=>{a.allow(&["--pk","--vector","--out"])?;
            encrypt(&a,&p,&mut rand::rng(),"rand::rng OS-seeded ThreadRng; no public seed")?},
        "oracle-issuer-encrypt"=>{a.allow(&["--pk","--vector","--out","--seed"])?;
            let seed:u8=a.get("--seed")?.parse()?;encrypt(&a,&p,&mut ChaCha20Rng::from_seed([seed;32]),"ORACLE ONLY: public deterministic ChaCha20 seed byte")?},
        "inspect"=>{a.allow(&["--ct"])?;let (b,_)=load_ct(a.get("--ct")?,&p,true)?;meta("ciphertext",&b.key,&b.bytes)},
        "normalize"=>{a.allow(&["--ct","--out"])?;let (b,ct)=load_ct(a.get("--ct")?,&p,false)?;
            let out=wrap(CT,&b.key,&ct.to_bytes());save(a.get("--out")?,&out,false)?;meta("ciphertext",&b.key,&out)},
        "host-learn"=>{
            a.allow(&["--acc","--fresh","--old","--out"])?;
            let (ab,mut acc)=load_ct(a.get("--acc")?,&p,true)?;
            let (fb,fresh)=load_ct(a.get("--fresh")?,&p,true)?;
            if ab.key!=fb.key{return Err(err("declared key mismatch"));}
            let old=if let Some(path)=a.values.get("--old"){
                let (b,c)=load_ct(path,&p,true)?;if b.key!=ab.key{return Err(err("declared old key mismatch"));} Some((b,c))
            }else{None};
            let arithmetic=Instant::now();acc+=&fresh;if let Some((_,c))=&old{acc-=c;}
            let arithmetic_ns=arithmetic.elapsed().as_nanos();let acc=canonical(acc,&p)?;
            let out=wrap(CT,&ab.key,&acc.to_bytes());save(a.get("--out")?,&out,false)?;
            let mut m=meta("learn_result",&ab.key,&out);m["arithmetic_ns"]=json!(arithmetic_ns);
            m["acc_sha256"]=json!(hex(&digest(&ab.bytes)));m["fresh_sha256"]=json!(hex(&digest(&fb.bytes)));
            m["old_sha256"]=json!(old.as_ref().map(|(b,_)|hex(&digest(&b.bytes))));m
        },
        "host-infer"=>{
            a.allow(&["--acc","--query","--out"])?;
            let (b,acc)=load_ct(a.get("--acc")?,&p,true)?;let (qb,q)=load_query(a.get("--query")?)?;
            let encode=Instant::now();
            let plus:Vec<u64>=q.iter().rev().map(|x|(*x).max(0) as u64).collect();
            let minus:Vec<u64>=q.iter().rev().map(|x|(-*x).max(0) as u64).collect();
            let pp=Plaintext::try_encode(&plus,Encoding::poly(),&p)?;let pm=Plaintext::try_encode(&minus,Encoding::poly(),&p)?;
            let encoding_ns=encode.elapsed().as_nanos();let arithmetic=Instant::now();
            let answer=canonical(&(&acc*&pp)-&(&acc*&pm),&p)?;let arithmetic_ns=arithmetic.elapsed().as_nanos();
            let out=wrap(CT,&b.key,&answer.to_bytes());save(a.get("--out")?,&out,false)?;
            let mut m=meta("infer_result",&b.key,&out);m["acc_sha256"]=json!(hex(&digest(&b.bytes)));
            m["query_sha256"]=json!(hex(&digest(&qb)));m["encoding_ns"]=json!(encoding_ns);
            m["arithmetic_ns"]=json!(arithmetic_ns);m["output_coefficient"]=json!(576);m
        },
        "reader-decrypt"|"oracle-decrypt-polynomial"=>{
            a.allow(&["--sk","--ct"])?;
            let sb=read_blob(a.get("--sk")?,SK)?;let (b,ct)=load_ct(a.get("--ct")?,&p,true)?;
            if sb.key!=b.key{return Err(err("reader/ciphertext declared key mismatch"));}
            let proto=fhe::proto::bfv::SecretKey::decode(sb.payload.as_slice())?;
            if proto.coeffs.len()!=4096 || proto.coeffs.iter().any(|c|!(-20..=20).contains(c)){
                return Err(err("secret key outside generated degree/CBD support"));
            }
            let sk=SecretKey::from_bytes(&sb.payload,&p)?;
            if sk.to_bytes()!=sb.payload{return Err(err("noncanonical secret key"));}
            let decoded=Vec::<u64>::try_decode(&sk.try_decrypt(&ct)?,Encoding::poly())?;
            if decoded.len()!=4096{return Err(err("wrong decoded degree"));}
            if a.command=="oracle-decrypt-polynomial"{
                json!({"kind":"ORACLE_FULL_POLYNOMIAL","coefficients":decoded,"full_key_reader":true})
            }else{
                let r=decoded[576];let score=if r>T/2{r as i64-T as i64}else{r as i64};
                if !(-SCORE_BOUND..=SCORE_BOUND).contains(&score){return Err(err("decoded score outside declared honest-domain bound"));}
                json!({"kind":"trusted_reader_score","params_id":params_id(),"program_id":program_id(),
                    "key_id":hex(&b.key),"ciphertext_sha256":hex(&digest(&b.bytes)),"coefficient":576,
                    "signed_score":score,"sign":if score>=0{1}else{-1},"full_key_reader":true,
                    "scope":"benchmark R; finalization/policy gate is external; full polynomial decrypted internally"})
            }
        },_=>return Err(err("unknown command"))
    };
    result["process_work_ns"]=json!(start.elapsed().as_nanos());Ok(result)
}
fn main(){match run(){Ok(v)=>println!("{}",v),Err(e)=>{eprintln!("{}",json!({"error":e.to_string()}));std::process::exit(2)}}}
