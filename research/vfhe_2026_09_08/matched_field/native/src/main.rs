//! Complete caller-selected public linear BFV producer and independent consumer.
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::{Read, Write},
    path::Path,
    time::Instant,
};
use vfhe_matched_field::{
    linear::{self, Binding, N, Q, STAGES},
    proof::{self, PROFILE, ROWS, Timing},
};
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const CHUNKS: usize = STAGES * 4 * (N / ROWS);
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Linear,
    Update,
}
impl Kind {
    fn name(self) -> &'static str {
        match self {
            Self::Linear => "linear",
            Self::Update => "update",
        }
    }
    fn groups(self) -> usize {
        match self {
            Self::Linear => 44,
            Self::Update => 4,
        }
    }
    fn chunks(self) -> usize {
        self.groups() * 8
    }
    fn complete_key(self) -> &'static str {
        match self {
            Self::Linear => "complete_linear_verified",
            Self::Update => "complete_update_verified",
        }
    }
    fn schema(self) -> String {
        format!("matched-field-complete-{}-v1", self.name())
    }
}
struct PublicCase {
    kind: Kind,
    binding: serde_json::Value,
    rows: Vec<Vec<[u64; 16]>>,
}

fn read(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let resolved = fs::canonicalize(path)?;
    if resolved.components().any(|part| part.as_os_str() == ".private") {
        return Err("private paths are outside this public interface".into());
    }
    let f = fs::File::open(path)?;
    if f.metadata()?.len() > limit as u64 {
        return Err("file exceeds byte cap".into());
    }
    let mut b = vec![];
    f.take(limit as u64 + 1).read_to_end(&mut b)?;
    if b.len() > limit {
        return Err("file exceeds byte cap".into());
    }
    Ok(b)
}
fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut f = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    f.write_all(bytes)?;
    f.sync_all()?;
    Ok(())
}
fn save<T: Serialize>(path: &Path, value: &T) -> Result<()> {
    write_new(path, &serde_json::to_vec_pretty(value)?)
}
fn sha(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn hex(b: &[u8]) -> String {
    b.iter().map(|v| format!("{v:02x}")).collect()
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Expected {
    model_ciphertext_sha256: String,
    query_sha256: String,
    evaluation_key_sha256: String,
    #[serde(default)]
    dot_ciphertext_sha256: Option<String>,
}
fn expectation(path: &Path, case: &PublicCase) -> Result<()> {
    if case.kind == Kind::Update {
        return update_expectation(path, &case.binding);
    }
    let b: Binding = serde_json::from_value(case.binding.clone())?;
    let e: Expected = serde_json::from_slice(&read(path, 4096)?)?;
    for v in [
        &e.model_ciphertext_sha256,
        &e.query_sha256,
        &e.evaluation_key_sha256,
    ]
    .into_iter()
    .chain(e.dot_ciphertext_sha256.iter())
    {
        if v.len() != 64
            || !v
                .bytes()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
        {
            return Err("expectation must be lowercase SHA-256".into());
        }
    }
    if e.model_ciphertext_sha256 != b.model_ciphertext_sha256
        || e.query_sha256 != b.query_sha256
        || e.evaluation_key_sha256 != b.evaluation_key_sha256
        || e.dot_ciphertext_sha256
            .is_some_and(|v| v != b.dot_ciphertext_sha256)
    {
        return Err("caller expectation mismatch".into());
    }
    Ok(())
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct UpdateExpected {
    acc_sha256: String,
    fresh_sha256: String,
    old_sha256: String,
    #[serde(default)]
    out_sha256: Option<String>,
}
fn update_expectation(path: &Path, b: &serde_json::Value) -> Result<()> {
    let e: UpdateExpected = serde_json::from_slice(&read(path, 4096)?)?;
    for (k, v) in [
        ("acc_sha256", &e.acc_sha256),
        ("fresh_sha256", &e.fresh_sha256),
        ("old_sha256", &e.old_sha256),
    ]
    .into_iter()
    .chain(e.out_sha256.as_ref().map(|v| ("out_sha256", v)))
    {
        if v.len() != 64
            || !v
                .bytes()
                .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
            || b.get(k).and_then(|x| x.as_str()) != Some(v.as_str())
        {
            return Err(format!("update caller expectation mismatch: {k}").into());
        }
    }
    Ok(())
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Chunk {
    index: usize,
    stage: usize,
    prime_index: usize,
    modulus: u64,
    first_coefficient: usize,
    rows: usize,
    public_rows_sha256: String,
    context_sha256: String,
    file: String,
    proof_sha256: String,
    timing: Timing,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Bundle {
    schema: String,
    profile: String,
    binding: serde_json::Value,
    chunks: Vec<Chunk>,
}

fn rows(case: &PublicCase, index: usize) -> Result<&[[u64; 16]]> {
    if index >= case.kind.chunks() {
        return Err("chunk index out of range".into());
    }
    if case.rows.len() != case.kind.groups() || case.rows.iter().any(|r| r.len() != N) {
        return Err("incomplete public row reconstruction".into());
    }
    let group = index / 8;
    let start = (index % 8) * ROWS;
    Ok(&case.rows[group][start..start + ROWS])
}
fn row_hash(index: usize, rows: &[[u64; 16]]) -> String {
    let mut h = Sha256::new();
    h.update(b"vfhe-matched-canonical-rows-v1");
    h.update((index as u64).to_le_bytes());
    h.update((rows.len() as u64).to_le_bytes());
    for x in rows.iter().flatten() {
        h.update(x.to_le_bytes());
    }
    format!("{:x}", h.finalize())
}
fn context(case: &PublicCase, index: usize) -> Result<([u8; 32], String)> {
    let row_hash = row_hash(index, rows(case, index)?);
    let bytes = serde_json::to_vec(
        &json!({"profile":PROFILE,"kind":case.kind.name(),"binding":case.binding,"index":index,"modulus":Q[(index/8)%4],"public_rows_sha256":row_hash}),
    )?;
    Ok((Sha256::digest(bytes).into(), row_hash))
}

macro_rules! dispatch {
    ($prime:expr,$func:ident,$($arg:expr),*) => {match $prime {
        0=>proof::$func::<1125899906826241>($($arg),*),
        1=>proof::$func::<1125899906629633>($($arg),*),
        2=>proof::$func::<1125899905744897>($($arg),*),
        3=>proof::$func::<1125899905351681>($($arg),*),
        _=>Err("unsupported prime index".into()),
    }};
}
fn prove_one(case: &PublicCase, index: usize, out: &Path) -> Result<Chunk> {
    let (ctx, rowhash) = context(case, index)?;
    let group = index / 8;
    let prime = group % 4;
    let (bytes, timing) = dispatch!(prime, prove_chunk, rows(case, index)?, &ctx)?;
    write_new(out, &bytes)?;
    Ok(Chunk {
        index,
        stage: group / 4,
        prime_index: prime,
        modulus: Q[prime],
        first_coefficient: (index % 8) * ROWS,
        rows: ROWS,
        public_rows_sha256: rowhash,
        context_sha256: hex(&ctx),
        file: out
            .file_name()
            .ok_or("invalid proof path")?
            .to_str()
            .ok_or("invalid proof filename")?
            .into(),
        proof_sha256: sha(&bytes),
        timing,
    })
}
fn verify_one(
    case: &PublicCase,
    index: usize,
    path: &Path,
    expected_record: Option<&Chunk>,
) -> Result<Chunk> {
    let (ctx, rowhash) = context(case, index)?;
    let group = index / 8;
    let prime = group % 4;
    let bytes = read(path, 8 << 20)?;
    let proof_hash = sha(&bytes);
    if let Some(r) = expected_record {
        if r.index != index
            || r.stage != group / 4
            || r.prime_index != prime
            || r.modulus != Q[prime]
            || r.rows != ROWS
            || r.first_coefficient != (index % 8) * ROWS
            || r.public_rows_sha256 != rowhash
            || r.context_sha256 != hex(&ctx)
            || r.file != format!("chunk{index:03}.bin")
            || r.proof_sha256 != proof_hash
            || r.timing.proof_bytes != bytes.len()
        {
            return Err(format!("chunk {index} metadata mismatch").into());
        }
    }
    let timing = dispatch!(prime, verify_chunk, rows(case, index)?, &ctx, &bytes)?;
    Ok(Chunk {
        index,
        stage: group / 4,
        prime_index: prime,
        modulus: Q[prime],
        first_coefficient: (index % 8) * ROWS,
        rows: ROWS,
        public_rows_sha256: rowhash,
        context_sha256: hex(&ctx),
        file: format!("chunk{index:03}.bin"),
        proof_sha256: proof_hash,
        timing,
    })
}
fn reconstruct(kind: Kind, plan: Option<&Path>, case: &Path) -> Result<(PublicCase, u128)> {
    let t = Instant::now();
    let c = match kind {
        Kind::Linear => {
            let c = linear::reconstruct(plan.ok_or("missing linear plan")?, case)?;
            PublicCase {
                kind,
                binding: serde_json::to_value(c.binding)?,
                rows: c.rows,
            }
        }
        Kind::Update => {
            let c = linear::reconstruct_update(case)?;
            PublicCase {
                kind,
                binding: serde_json::to_value(c.binding)?,
                rows: c.rows,
            }
        }
    };
    Ok((c, t.elapsed().as_nanos()))
}
fn produce(kind: Kind, plan: Option<&Path>, case_path: &Path, out: &Path) -> Result<()> {
    fs::create_dir(out)?;
    let wall = Instant::now();
    let (case, reconstruction_ns) = reconstruct(kind, plan, case_path)?;
    let chunks = kind.chunks();
    let t = Instant::now();
    for (i, group) in case.rows.iter().enumerate() {
        proof::check_rows(Q[i % 4], group)?;
    }
    let direct_mac_check_ns = t.elapsed().as_nanos();
    let mut records = Vec::with_capacity(chunks);
    for i in 0..chunks {
        let record = prove_one(&case, i, &out.join(format!("chunk{i:03}.bin")))?;
        eprintln!(
            "proved chunk {i}/{chunks}, {} bytes",
            record.timing.proof_bytes
        );
        records.push(record);
    }
    let bundle = Bundle {
        schema: kind.schema(),
        profile: PROFILE.into(),
        binding: case.binding.clone(),
        chunks: records,
    };
    save(&out.join("bundle.json"), &bundle)?;
    let result = json!({(kind.complete_key()):true,"self_verification_only":true,"fresh_proofs":chunks,"profile":PROFILE,"binding":case.binding,"chunks":chunks,
        "proof_bytes":bundle.chunks.iter().map(|c|c.timing.proof_bytes).sum::<usize>(),"total_prove_ns":bundle.chunks.iter().map(|c|c.timing.proof_ns).sum::<u128>(),
        "total_preprocessing_ns":bundle.chunks.iter().map(|c|c.timing.preprocessing_ns).sum::<u128>(),"total_self_verify_ns":bundle.chunks.iter().map(|c|c.timing.verify_ns).sum::<u128>(),
        "public_reconstruction_ns":reconstruction_ns,"direct_mac_check_ns":direct_mac_check_ns,"wall_ns":wall.elapsed().as_nanos(),"private_files_read":0,"numerical_soundness_bits":null,"zero_knowledge":false,"chunk_records":bundle.chunks});
    save(&out.join("result.json"), &result)?;
    println!(
        "{}",
        json!({"result":out.join("result.json"),"chunks":chunks,(kind.complete_key()):true,"self_verification_only":true})
    );
    Ok(())
}
fn consume(
    kind: Kind,
    plan: Option<&Path>,
    expected: &Path,
    case_path: &Path,
    proofs: &Path,
    out: &Path,
) -> Result<()> {
    if out.exists() {
        return Err("report path already exists".into());
    }
    let wall = Instant::now();
    let (case, reconstruction_ns) = reconstruct(kind, plan, case_path)?;
    let chunks = kind.chunks();
    expectation(expected, &case)?;
    let manifest = read(&proofs.join("bundle.json"), 2 << 20)?;
    let bundle: Bundle = serde_json::from_slice(&manifest)?;
    if bundle.schema != kind.schema()
        || bundle.profile != PROFILE
        || bundle.binding != case.binding
        || bundle.chunks.len() != chunks
    {
        return Err("bundle identity/coverage mismatch".into());
    }
    let mut records = Vec::with_capacity(chunks);
    for i in 0..chunks {
        records.push(verify_one(
            &case,
            i,
            &proofs.join(format!("chunk{i:03}.bin")),
            Some(&bundle.chunks[i]),
        )?);
        eprintln!("verified chunk {i}/{chunks}");
    }
    let result = json!({(kind.complete_key()):true,"independent_consumer":true,"profile":PROFILE,"binding":case.binding,"chunks":chunks,
        "proof_bytes":records.iter().map(|c|c.timing.proof_bytes).sum::<usize>(),"total_verify_ns":records.iter().map(|c|c.timing.verify_ns).sum::<u128>(),
        "total_preprocessing_ns":records.iter().map(|c|c.timing.preprocessing_ns).sum::<u128>(),"public_reconstruction_ns":reconstruction_ns,"wall_ns":wall.elapsed().as_nanos(),
        "private_files_read":0,"numerical_soundness_bits":null,"zero_knowledge":false,"bound_output_path":case_path.join(if kind==Kind::Linear {"expected_dot.ct"}else{"out.ct"}),"bundle_sha256":sha(&manifest),"chunk_records":records});
    save(out, &result)?;
    println!(
        "{}",
        json!({"result":out,"chunks":chunks,(kind.complete_key()):true,"independent_consumer":true})
    );
    Ok(())
}
fn main() -> Result<()> {
    let a: Vec<String> = std::env::args().collect();
    let p = |i: usize| Path::new(&a[i]);
    match a.get(1).map(String::as_str) {
        Some("import") if a.len()==7=>linear::import(p(2),p(3),p(4),p(5),p(6)),
        Some("import-update") if a.len()==6=>linear::import_update(p(2),p(3),p(4),p(5)),
        Some("prove-update") if a.len()==4=>produce(Kind::Update,None,p(2),p(3)),
        Some("verify-update") if a.len()==6=>consume(Kind::Update,None,p(2),p(3),p(4),p(5)),
        Some("prove-linear") if a.len()==5=>produce(Kind::Linear,Some(p(2)),p(3),p(4)),
        Some("verify-linear") if a.len()==7=>consume(Kind::Linear,Some(p(2)),p(3),p(4),p(5),p(6)),
        Some("prove-chunk") if a.len()==6=>{let (case,_)=reconstruct(Kind::Linear,Some(p(2)),p(3))?;let record=prove_one(&case,a[4].parse()?,p(5))?;println!("{}",serde_json::to_string(&record)?);Ok(())},
        Some("verify-chunk") if a.len()==8=>{let (case,ns)=reconstruct(Kind::Linear,Some(p(2)),p(4))?;expectation(p(3),&case)?;let record=verify_one(&case,a[5].parse()?,p(6),None)?;save(p(7),&json!({"verified":true,"complete_linear_verified":false,"public_reconstruction_ns":ns,"record":record}))},
        Some("check-case") if a.len()==5=>{let (case,ns)=reconstruct(Kind::Linear,Some(p(2)),p(3))?;let t=Instant::now();for (i,g) in case.rows.iter().enumerate(){proof::check_rows(Q[i%4],g)?;}save(p(4),&json!({"direct_mac_check_passed":true,"proof_verified":false,"public_reconstruction_ns":ns,"direct_mac_check_ns":t.elapsed().as_nanos(),"rows":STAGES*4*N,"binding":case.binding}))},
        Some("profile") if a.len()==2=>{println!("{}",json!({"profile":PROFILE,"primes":Q,"rows":ROWS,"chunks":CHUNKS,"update_chunks":32,"public_preprocessing_width":16,"main_width":1,"whole_row_constraints":3,"private_files_read":0,"numerical_soundness_bits":null}));Ok(())},
        _=>Err("usage: import-update ACC FRESH OLD NEW_CASE | prove-update CASE NEW_PROOFS | verify-update EXPECTED CASE PROOFS NEW_REPORT | import PLAN MODEL QUERY EVALKEY NEW_CASE | prove-linear PLAN CASE NEW_PROOFS | verify-linear PLAN EXPECTED CASE PROOFS NEW_REPORT | prove-chunk PLAN CASE INDEX NEW_PROOF | verify-chunk PLAN EXPECTED CASE INDEX PROOF NEW_REPORT | check-case PLAN CASE NEW_REPORT | profile".into())
    }
}
