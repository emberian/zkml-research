//! mir-stream: one pass over a GGUF checkpoint -> FlashProve's committed integers (docs/model.md section 11),
//! their sums file wsums.txt (byte for byte as weight_sums/ writes it), per-file and per-tensor SHA-256 (the GGUF
//! "v1" manifest), and the registry v2 cSHAKE256 roots (ROOTS-V2.md) over the integers.
//!
//! usage:
//!   mir-stream local  --eres N --out DIR [--threads T] SHARD...
//!   mir-stream remote --eres N --out DIR [--threads T] [--parallel K] --base URL [--expect SHA256SUMS] NAME...
//!   mir-stream sample --manifest DIR/manifest-v2.json --base URL --count C --seed S [--threads T]
//! The shard holding the metadata comes first. remote reads URL/NAME. Nothing is written but DIR's files.

mod conv;
mod gguf;
mod tree;

use conv::*;
use gguf::*;
use rayon::prelude::*;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};
use std::io::{Cursor, Read};
use std::sync::mpsc::sync_channel;
use std::sync::Arc;
use tree::{hex, D};

#[derive(Clone)]
enum Source {
    Local(String),
    Remote(String),
}

impl Source {
    fn label(&self) -> String {
        match self {
            Source::Local(p) => p.rsplit('/').next().unwrap().to_string(),
            Source::Remote(u) => u.rsplit('/').next().unwrap().to_string(),
        }
    }
    fn range(&self, off: u64, len: u64) -> Vec<u8> {
        match self {
            Source::Local(p) => {
                use std::io::{Seek, SeekFrom};
                let mut f = std::fs::File::open(p).unwrap_or_else(|e| die(&format!("open {p}: {e}")));
                f.seek(SeekFrom::Start(off)).unwrap();
                let mut v = vec![0u8; len as usize];
                let mut got = 0;
                while got < v.len() {
                    let n = f.read(&mut v[got..]).unwrap();
                    if n == 0 {
                        break;
                    }
                    got += n;
                }
                v.truncate(got);
                v
            }
            Source::Remote(u) => {
                for attempt in 0..6 {
                    let r = ureq::get(u).set("Range", &format!("bytes={}-{}", off, off + len - 1)).call();
                    match r {
                        Ok(resp) => {
                            if resp.status() != 206 {
                                die(&format!("{u}: range request answered {}", resp.status()));
                            }
                            let mut v = Vec::with_capacity(len as usize);
                            if resp.into_reader().take(len).read_to_end(&mut v).is_ok() && v.len() as u64 == len {
                                return v;
                            }
                        }
                        Err(e) => eprintln!("range {u} attempt {attempt}: {e}"),
                    }
                    std::thread::sleep(std::time::Duration::from_secs(2 << attempt));
                }
                die(&format!("{u}: range {off}+{len} failed"))
            }
        }
    }
    fn stream(&self) -> Box<dyn Read + Send> {
        match self {
            Source::Local(p) => Box::new(std::io::BufReader::with_capacity(
                16 << 20,
                std::fs::File::open(p).unwrap_or_else(|e| die(&format!("open {p}: {e}"))),
            )),
            Source::Remote(u) => {
                let resp = ureq::get(u).call().unwrap_or_else(|e| die(&format!("GET {u}: {e}")));
                Box::new(std::io::BufReader::with_capacity(16 << 20, resp.into_reader()))
            }
        }
    }
}

fn die(m: &str) -> ! {
    eprintln!("mir-stream: {m}");
    std::process::exit(1)
}

fn header_of(src: &Source) -> Header {
    let mut len: u64 = 64 << 20;
    loop {
        let bytes = src.range(0, len);
        let short = (bytes.len() as u64) < len;
        let mut c = Counting { inner: Cursor::new(bytes), pos: 0 };
        match parse(&mut c) {
            Ok(h) => return h,
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof && !short => len *= 4,
            Err(e) => die(&format!("{}: {e}", src.label())),
        }
    }
}

struct Committed {
    shard: usize,
    info: TensorInfo,
    usage: Use,
}

struct Plan {
    shards: Vec<Source>,
    headers: Vec<Header>,
    committed: Vec<Committed>,
    /// norm name -> (shard, info, decoded gains, raw bytes)
    norms: HashMap<String, (usize, TensorInfo, Vec<f32>, Vec<u8>)>,
    eres: i32,
}

fn plan(shards: Vec<Source>, eres: i32) -> Plan {
    let headers: Vec<Header> = shards.iter().map(header_of).collect();
    let h0 = &headers[0];
    if h0.embedding_length != Some(WIDTH) {
        die(&format!("the first shard's embedding_length is {:?}, the rule needs {WIDTH}", h0.embedding_length));
    }
    if h0.key_length.unwrap_or(HEAD_DIMENSION) != HEAD_DIMENSION {
        die("the head dimension is not 128");
    }
    let layers = h0.block_count.unwrap_or_else(|| die("no block_count"));
    let mut committed = vec![];
    let mut norm_infos = vec![];
    let mut names = std::collections::HashSet::new();
    for (s, h) in headers.iter().enumerate() {
        for t in &h.tensors {
            if !names.insert(t.name.clone()) {
                die(&format!("repeated tensor name {}", t.name));
            }
            let Some(u) = classify(&t.name) else { continue };
            if let Some((l, _)) = layer_kind(&t.name) {
                if l >= layers {
                    die(&format!("{}: layer number not below block_count", t.name));
                }
            }
            match u.role {
                Role::Norm => norm_infos.push((s, t.clone())),
                _ => committed.push(Committed { shard: s, info: t.clone(), usage: u }),
            }
        }
    }
    let mut norms = HashMap::new();
    for (s, t) in norm_infos {
        if t.ggml_type != F32 || t.elements != WIDTH {
            die(&format!("norm {} is not F32 of {WIDTH} elements", t.name));
        }
        let raw = shards[s].range(headers[s].data_start + t.rel_offset, t.n_bytes.unwrap());
        let mut g = vec![0f32; WIDTH as usize];
        decode(F32, &raw, &mut g);
        norms.insert(t.name.clone(), (s, t, g, raw));
    }
    for c in &committed {
        let t = &c.info;
        let Some((be, _)) = block_shape(t.ggml_type) else {
            die(&format!("{} has storage type {}, outside the seven", t.name, t.ggml_type))
        };
        if t.elements == 0 {
            die(&format!("{} has no elements", t.name));
        }
        if t.dims[0] % be != 0 {
            die(&format!("{}: rows are not whole blocks", t.name));
        }
        if let Some((n, _)) = &c.usage.norm {
            if !norms.contains_key(n) {
                die(&format!("{} needs {n}, absent", t.name));
            }
            if t.dims[0] != WIDTH {
                die(&format!("{} reads a norm but its first dimension is not {WIDTH}", t.name));
            }
        }
    }
    Plan { shards, headers, committed, norms, eres }
}

#[derive(Clone)]
struct Result1 {
    name: String,
    line: String,
    e: i32,
    bits: u32,
    int_sha: String,
    raw_sha: String,
    ggml_type: u32,
    dims: Vec<u64>,
    elements: u64,
    slice_roots: Vec<D>,
    root: D,
}

fn gamma_of(p: &Plan, u: &Use) -> Option<Vec<f32>> {
    let (n, c) = u.norm.as_ref()?;
    let g = &p.norms[n].2;
    let gamma: Vec<f32> = g.iter().map(|x| *x * *c).collect();
    for x in &gamma {
        if !x.is_finite() {
            die(&format!("a gain of {n} times the constant is not finite"));
        }
        if *x != 0.0 && x.abs() < 2f32.powi(-100) {
            die(&format!("a gain of {n} times the constant is below 2^-100"));
        }
    }
    Some(gamma)
}

/// The rule on one tensor's bytes.
fn convert(name: &str, info: &TensorInfo, usage: &Use, gamma: Option<&[f32]>, eres: i32, raw: &[u8]) -> Result1 {
    let t = info.ggml_type;
    let d0 = info.dims[0] as usize;
    let rows = (info.elements / info.dims[0]) as usize;
    let rb = raw.len() / rows;
    assert_eq!(rb * rows, raw.len());
    let embedding = usage.role == Role::Embedding;
    let raw_sha = hex(&Sha256::digest(raw));
    // pass 1: the largest |p|
    let (e, width) = if embedding {
        (eres, 4u8)
    } else {
        let largest = raw
            .par_chunks(rb * 64)
            .map(|chunk| {
                let mut v = vec![0f32; d0];
                let mut m = 0f32;
                for row in chunk.chunks(rb) {
                    decode(t, row, &mut v);
                    products(&mut v, gamma);
                    for x in &v {
                        if !x.is_finite() {
                            die(&format!("{name}: a product or a decoded value is not finite"));
                        }
                        let a = x.abs();
                        if a > m {
                            m = a;
                        }
                    }
                }
                m
            })
            .reduce(|| 0f32, f32::max);
        if largest == 0.0 {
            die(&format!("every product of {name} is 0"));
        }
        let e = exponent_of(largest);
        if !(-100..=100).contains(&e) {
            die(&format!("the exponent of {name} is outside -100..100"));
        }
        (e, 2u8)
    };
    let scale = pow2(e);
    // pass 2: integers, their SHA-256 in file order, one leaf per row
    let mut sha = Sha256::new();
    let mut leaves: Vec<D> = Vec::with_capacity(rows);
    let (mut lo, mut hi) = (0i64, 0i64);
    let chunk_rows = 2048usize;
    for chunk in raw.chunks(rb * chunk_rows) {
        let out: Vec<(Vec<u8>, D, i64, i64)> = chunk
            .par_chunks(rb)
            .map(|row| {
                let mut v = vec![0f32; d0];
                decode(t, row, &mut v);
                if !embedding {
                    products(&mut v, gamma);
                }
                let mut bytes = Vec::with_capacity(d0 * width as usize);
                let (mut l, mut h) = (0i64, 0i64);
                for x in &v {
                    if !x.is_finite() {
                        die(&format!("{name}: a decoded value is not finite"));
                    }
                    let w = integer(*x, scale);
                    l = l.min(w);
                    h = h.max(w);
                    if width == 2 {
                        bytes.extend_from_slice(&(w as i16).to_le_bytes());
                    } else {
                        bytes.extend_from_slice(&(w as i32).to_le_bytes());
                    }
                }
                let lf = tree::leaf(&bytes);
                (bytes, lf, l, h)
            })
            .collect();
        for (b, lf, l, h) in out {
            sha.update(&b);
            leaves.push(lf);
            lo = lo.min(l);
            hi = hi.max(h);
        }
    }
    if embedding && (-lo).max(hi) >= EMBEDDING_BOUND {
        die(&format!("an integer of {name} is 2^30 or more"));
    }
    if !embedding && (-lo).max(hi) > LARGEST_MATRIX_INTEGER {
        die(&format!("an integer of {name} exceeds 4095"));
    }
    let mut bits = 1u32;
    while !(-(1i64 << (bits - 1)) <= lo && hi < (1i64 << (bits - 1))) {
        bits += 1;
    }
    let int_sha = hex(&sha.finalize());
    let line = format!("{} {} {} {} {}\n", name, info.elements, e, bits, int_sha);
    let nslices = if info.dims.len() >= 3 { info.dims[2..].iter().product::<u64>() as usize } else { 1 };
    let per = rows / nslices;
    let slice_roots: Vec<D> =
        (0..nslices).map(|s| tree::slice_root(per as u64, d0 as u64, &leaves[s * per..(s + 1) * per])).collect();
    let root = tree::tensor_root(name, &info.dims, e, width, &slice_roots);
    Result1 {
        name: name.to_string(),
        line,
        e,
        bits,
        int_sha,
        raw_sha,
        ggml_type: t,
        dims: info.dims.clone(),
        elements: info.elements,
        slice_roots,
        root,
    }
}

struct FileOut {
    label: String,
    sha256: String,
    length: u64,
}

struct Tee<R: Read> {
    inner: R,
    sha: Sha256,
    pos: u64,
}
impl<R: Read> Tee<R> {
    fn take_exact(&mut self, n: u64) -> Vec<u8> {
        let mut v = vec![0u8; n as usize];
        self.inner.read_exact(&mut v).unwrap_or_else(|e| die(&format!("stream ended early at {}: {e}", self.pos)));
        self.sha.update(&v);
        self.pos += n;
        v
    }
    fn skip_to(&mut self, at: u64) {
        if at < self.pos {
            die("tensors overlap or are out of order");
        }
        let mut left = at - self.pos;
        let mut buf = vec![0u8; 1 << 20];
        while left > 0 {
            let k = left.min(buf.len() as u64) as usize;
            self.inner.read_exact(&mut buf[..k]).unwrap_or_else(|e| die(&format!("stream: {e}")));
            self.sha.update(&buf[..k]);
            left -= k as u64;
            self.pos += k as u64;
        }
    }
    fn drain(&mut self) {
        let mut buf = vec![0u8; 1 << 20];
        loop {
            let n = self.inner.read(&mut buf).unwrap_or_else(|e| die(&format!("stream: {e}")));
            if n == 0 {
                break;
            }
            self.sha.update(&buf[..n]);
            self.pos += n as u64;
        }
    }
}

fn run_shard(p: &Plan, s: usize, log: &(dyn Fn(String) + Sync)) -> (FileOut, Vec<Result1>) {
    let src = &p.shards[s];
    let h = &p.headers[s];
    let mut todo: Vec<(TensorInfo, Option<&Committed>)> = h
        .tensors
        .iter()
        .filter(|t| t.n_bytes.is_some())
        .map(|t| (t.clone(), p.committed.iter().find(|c| c.shard == s && c.info.name == t.name)))
        .collect();
    todo.sort_by_key(|(t, _)| t.rel_offset);
    let (tx, rx) = sync_channel::<(TensorInfo, Option<&Committed>, Vec<u8>)>(1);
    let mut results = vec![];
    let mut fo = FileOut { label: src.label(), sha256: String::new(), length: 0 };
    std::thread::scope(|sc| {
        let reader = sc.spawn(move || {
            let mut tee = Tee { inner: src.stream(), sha: Sha256::new(), pos: 0 };
            for (t, c) in todo {
                tee.skip_to(h.data_start + t.rel_offset);
                let bytes = tee.take_exact(t.n_bytes.unwrap());
                if c.is_some() || p.norms.contains_key(&t.name) {
                    tx.send((t, c, bytes)).unwrap();
                }
            }
            drop(tx);
            tee.drain();
            (hex(&tee.sha.clone().finalize()), tee.pos)
        });
        for (t, c, bytes) in rx {
            if let Some((_, _, _, raw)) = p.norms.get(&t.name) {
                if *raw != bytes {
                    die(&format!("{}: streamed norm differs from its range fetch", t.name));
                }
                continue;
            }
            let c = c.unwrap();
            let gamma = gamma_of(p, &c.usage);
            let r = convert(&t.name, &t, &c.usage, gamma.as_deref(), p.eres, &bytes);
            log(format!("{} {} e={} bits={} {}", fo.label, r.name, r.e, r.bits, &r.int_sha[..16]));
            results.push(r);
        }
        let (sha, len) = reader.join().unwrap();
        fo.sha256 = sha;
        fo.length = len;
    });
    (fo, results)
}

fn arg(args: &[String], k: &str) -> Option<String> {
    args.iter().position(|a| a == k).map(|i| args[i + 1].clone())
}

fn positional(args: &[String]) -> Vec<String> {
    let mut out = vec![];
    let mut i = 2;
    while i < args.len() {
        if args[i].starts_with("--") {
            i += 2;
        } else {
            out.push(args[i].clone());
            i += 1;
        }
    }
    out
}

fn rootset(results: &BTreeMap<Vec<u8>, Result1>, experts: &BTreeMap<(u32, u32), D>) -> D {
    let mut pre = vec![];
    pre.extend_from_slice(&(results.len() as u64).to_le_bytes());
    for (name, r) in results {
        pre.extend_from_slice(&(name.len() as u32).to_le_bytes());
        pre.extend_from_slice(name);
        pre.extend_from_slice(&r.root);
    }
    pre.extend_from_slice(&(experts.len() as u64).to_le_bytes());
    for ((l, e), d) in experts {
        pre.extend_from_slice(&l.to_le_bytes());
        pre.extend_from_slice(&e.to_le_bytes());
        pre.extend_from_slice(d);
    }
    tree::h("rootset", &[&pre])
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        die("usage: see the head of src/main.rs");
    }
    if let Some(t) = arg(&args, "--threads") {
        rayon::ThreadPoolBuilder::new().num_threads(t.parse().unwrap()).build_global().unwrap();
    }
    let cmd = args[1].as_str();
    if cmd == "sample" {
        return sample(&args);
    }
    let eres: i32 = arg(&args, "--eres").unwrap_or_else(|| "11".into()).parse().unwrap();
    let out = arg(&args, "--out").unwrap_or_else(|| die("--out DIR is required"));
    let parallel: usize = arg(&args, "--parallel").unwrap_or_else(|| "1".into()).parse().unwrap();
    let names = positional(&args);
    let shards: Vec<Source> = match cmd {
        "local" => names.iter().map(|n| Source::Local(n.clone())).collect(),
        "remote" => {
            let base = arg(&args, "--base").unwrap_or_else(|| die("--base URL is required"));
            names.iter().map(|n| Source::Remote(format!("{base}/{n}"))).collect()
        }
        _ => die("unknown command"),
    };
    std::fs::create_dir_all(&out).unwrap();
    let began = std::time::Instant::now();
    let p = Arc::new(plan(shards, eres));
    eprintln!(
        "plan: {} shards, {} committed tensors, {} norms, {:.1}s",
        p.shards.len(),
        p.committed.len(),
        p.norms.len(),
        began.elapsed().as_secs_f64()
    );
    let logf = std::sync::Mutex::new(std::fs::File::create(format!("{out}/progress.log")).unwrap());
    let log = |m: String| {
        use std::io::Write;
        let line = format!("{:.0}s {m}\n", began.elapsed().as_secs_f64());
        let _ = logf.lock().unwrap().write_all(line.as_bytes());
    };
    let pool = rayon::ThreadPoolBuilder::new().num_threads(parallel).build().unwrap();
    let per: Vec<(FileOut, Vec<Result1>)> =
        pool.install(|| (0..p.shards.len()).into_par_iter().map(|s| run_shard(&p, s, &log)).collect());
    let mut files = vec![];
    let mut results: BTreeMap<Vec<u8>, Result1> = BTreeMap::new();
    for (f, rs) in per {
        files.push(f);
        for r in rs {
            results.insert(r.name.as_bytes().to_vec(), r);
        }
    }
    if results.len() != p.committed.len() {
        die("not every committed tensor was converted");
    }
    // wsums.txt, sorted by name as bytes, then END <n>
    let mut wsums = String::new();
    for r in results.values() {
        wsums.push_str(&r.line);
    }
    wsums.push_str(&format!("END {}\n", results.len()));
    std::fs::write(format!("{out}/wsums.txt"), &wsums).unwrap();
    let wsums_sha = hex(&Sha256::digest(wsums.as_bytes()));
    // per-expert roots
    let mut experts: BTreeMap<(u32, u32), D> = BTreeMap::new();
    let mut layers_with_experts = std::collections::BTreeSet::new();
    for r in results.values() {
        if let Some((l, k)) = layer_kind(&r.name) {
            if k == "ffn_gate_exps" {
                layers_with_experts.insert(l as u32);
            }
        }
    }
    let mut skipped: Vec<u32> = vec![];
    for l in &layers_with_experts {
        let get = |k: &str| {
            results.get(format!("blk.{l}.{k}.weight").as_bytes()).unwrap_or_else(|| die(&format!("layer {l} lacks {k}")))
        };
        let (g, u, d) = (get("ffn_gate_exps"), get("ffn_up_exps"), get("ffn_down_exps"));
        let n = g.slice_roots.len();
        if u.slice_roots.len() != n || d.slice_roots.len() != n {
            eprintln!("layer {l}: expert counts differ ({n}, {}, {}); no expert roots for it", u.slice_roots.len(), d.slice_roots.len());
            skipped.push(*l);
            continue;
        }
        for e in 0..n {
            let parts = [(g.e, g.slice_roots[e]), (u.e, u.slice_roots[e]), (d.e, d.slice_roots[e])];
            experts.insert((*l, e as u32), tree::expert_root(*l, e as u32, &parts));
        }
    }
    let rs = rootset(&results, &experts);
    let mut sums = String::new();
    for f in &files {
        sums.push_str(&format!("{}  {}\n", f.sha256, f.label));
    }
    std::fs::write(format!("{out}/files.sha256"), &sums).unwrap();
    let mut expect_ok = Value::Null;
    if let Some(ex) = arg(&args, "--expect") {
        let want = std::fs::read_to_string(&ex).unwrap();
        let ok = files.iter().all(|f| want.lines().any(|l| l == format!("{}  {}", f.sha256, f.label)));
        expect_ok = json!(ok);
        if !ok {
            eprintln!("FILE DIGESTS DIFFER from {ex}");
        }
    }
    let tensors: Vec<Value> = results
        .values()
        .map(|r| {
            json!({"name": r.name, "storage": type_name(r.ggml_type), "dims": r.dims, "elements": r.elements,
               "exponent": r.e, "bits": r.bits, "int_sha256": r.int_sha, "raw_sha256": r.raw_sha,
               "root": hex(&r.root), "slices": r.slice_roots.len(),
               "slice_roots": if r.slice_roots.len() > 1 { json!(r.slice_roots.iter().map(|d| hex(d)).collect::<Vec<_>>()) } else { Value::Null }})
        })
        .collect();
    let experts_json: Vec<Value> =
        experts.iter().map(|((l, e), d)| json!({"layer": l, "expert": e, "root": hex(d)})).collect();
    let manifest = json!({
        "format": "mir13/registry-v2/1",
        "hash": "cSHAKE256(X, 256, N=\"\", S=\"mir13/v2/<kind>\")",
        "eres": eres,
        "files": files.iter().map(|f| json!({"name": f.label, "sha256": f.sha256, "length": f.length})).collect::<Vec<_>>(),
        "files_match_expected": expect_ok,
        "wsums_sha256": wsums_sha,
        "rootset": hex(&rs),
        "tensors": tensors,
        "experts": experts_json,
        "expert_layers_skipped": skipped,
        "seconds": began.elapsed().as_secs_f64(),
    });
    std::fs::write(format!("{out}/manifest-v2.json"), serde_json::to_string_pretty(&manifest).unwrap()).unwrap();
    println!("wsums_sha256 {wsums_sha}");
    println!("rootset {}", hex(&rs));
    println!("tensors {} experts {} seconds {:.1}", results.len(), experts.len(), began.elapsed().as_secs_f64());
}

/// G11: re-fetch a seeded random sample of committed tensors by range request and recompute integers,
/// int_sha256, raw_sha256 and root; all must equal the manifest's.
fn sample(args: &[String]) {
    let m: Value = serde_json::from_str(
        &std::fs::read_to_string(arg(args, "--manifest").unwrap_or_else(|| die("--manifest"))).unwrap(),
    )
    .unwrap();
    let base = arg(args, "--base").unwrap_or_else(|| die("--base"));
    let count: usize = arg(args, "--count").unwrap_or_else(|| "4".into()).parse().unwrap();
    let mut seed: u64 = arg(args, "--seed").unwrap_or_else(|| "1".into()).parse().unwrap();
    let eres = m["eres"].as_i64().unwrap() as i32;
    let shards: Vec<Source> =
        m["files"].as_array().unwrap().iter().map(|f| Source::Remote(format!("{base}/{}", f["name"].as_str().unwrap()))).collect();
    let p = plan(shards, eres);
    let tensors = m["tensors"].as_array().unwrap();
    let mut bad = 0;
    for _ in 0..count {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let want = &tensors[(seed % tensors.len() as u64) as usize];
        let name = want["name"].as_str().unwrap();
        let c = p.committed.iter().find(|c| c.info.name == name).unwrap_or_else(|| die("tensor missing"));
        let raw = p.shards[c.shard].range(p.headers[c.shard].data_start + c.info.rel_offset, c.info.n_bytes.unwrap());
        let gamma = gamma_of(&p, &c.usage);
        let r = convert(name, &c.info, &c.usage, gamma.as_deref(), eres, &raw);
        let ok = r.int_sha == want["int_sha256"].as_str().unwrap()
            && r.raw_sha == want["raw_sha256"].as_str().unwrap()
            && hex(&r.root) == want["root"].as_str().unwrap()
            && r.e as i64 == want["exponent"].as_i64().unwrap();
        println!("{} {} ({} bytes)", if ok { "SAME" } else { "DIFFERS" }, name, raw.len());
        if !ok {
            bad += 1;
        }
    }
    println!("sample: {count} tensors, {bad} differ");
    std::process::exit(if bad == 0 { 0 } else { 1 });
}
