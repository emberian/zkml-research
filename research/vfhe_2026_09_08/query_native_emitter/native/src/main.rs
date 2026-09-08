//! Untrusted witness execution. All instructions are emitted by Lean, and the
//! template is copied byte-for-byte; this program does not construct any AIR.
use serde_json::{json, Value};
use std::{error::Error, fs, io::{BufWriter, Write}, path::Path, time::Instant};
type Result<T> = std::result::Result<T, Box<dyn Error>>;
#[derive(Clone,Copy)]
enum Arg { Lit(i128), Reg(usize) }
impl Arg { fn get(self, r:&[i128])->i128 { match self { Self::Lit(x)=>x, Self::Reg(i)=>r[i] } } }
struct Instruction { dst:usize, op:u8, a:Arg, b:Arg }
fn nat(v:&Value)->Result<usize> { Ok(usize::try_from(v.as_u64().ok_or("expected natural integer")?)?) }
fn arg(mode:&Value,value:&Value,regs:usize)->Result<Arg> {
    match nat(mode)? {
        0=>Ok(Arg::Lit(value.as_i64().ok_or("literal exceeds i64")? as i128)),
        1=>{let n=nat(value)?;if n>=regs{return Err("register outside program".into())}Ok(Arg::Reg(n))},
        _=>Err("unknown operand mode".into())
    }
}
fn run()->Result<()> {
    let argv:Vec<String>=std::env::args().collect();
    if argv.len()!=5{return Err("usage: lean-query-witness PLAN TEMPLATE PUBLIC_ROWS NEW_OUT_DIR".into())}
    let started=Instant::now();
    let plan:Value=serde_json::from_slice(&fs::read(&argv[1])?)?;
    if plan["schema"]!="lean-bfv-query-witness-plan-v1"{return Err("wrong plan schema".into())}
    let width=nat(&plan["trace_width"])?;let arity=nat(&plan["input_arity"])?;
    let nregs=nat(&plan["register_count"])?;let modulus=nat(&plan["field_modulus"])? as i128;
    if width==0||nregs<width||nregs>1_000_000||arity<1||modulus<=1||modulus>u32::MAX as i128{return Err("invalid plan dimensions".into())}
    let mut code=Vec::new();
    for ins in plan["instructions"].as_array().ok_or("missing instructions")? {
        let t=ins.as_array().ok_or("bad instruction")?;
        if t.len()!=6{return Err("instruction must have six entries".into())}
        let dst=nat(&t[0])?;let op=nat(&t[1])?;
        if dst>=nregs||op>8{return Err("invalid instruction".into())}
        code.push(Instruction{dst,op:op as u8,a:arg(&t[2],&t[3],nregs)?,b:arg(&t[4],&t[5],nregs)?});
    }
    let template=fs::read(&argv[2])?;
    let template_value:Value=serde_json::from_slice(&template)?;
    if nat(&template_value["trace_width"])?!=width{return Err("plan/template width mismatch".into())}
    let rows:Vec<Vec<u64>>=serde_json::from_slice(&fs::read(&argv[3])?)?;
    if rows.is_empty(){return Err("empty rows".into())}
    for (i,row) in rows.iter().enumerate() {
        if row.len()!=arity||row[0]!=i as u64||row[1..].iter().any(|v|*v>=64){return Err(format!("invalid public row {i}").into())}
    }
    let out=Path::new(&argv[4]);
    if out.exists(){return Err("output directory must be new".into())}
    fs::create_dir_all(out)?;
    fs::write(out.join("template_ir2.json"),&template)?;
    let setup_ns=started.elapsed().as_nanos();let execute=Instant::now();
    let mut writer=BufWriter::with_capacity(1<<20,fs::File::create(out.join("trace.leu32"))?);
    let mut r=vec![0i128;nregs];let mut bytes=Vec::with_capacity(width*4);
    for row in &rows {
        r.fill(0);
        for ins in &code {
            let a=ins.a.get(&r);let b=ins.b.get(&r);
            r[ins.dst]=match ins.op {
                0=>a,
                1=>a.checked_add(b).ok_or("i128 add overflow")?,
                2=>a.checked_mul(b).ok_or("i128 mul overflow")?,
                3=>a.checked_sub(b).ok_or("i128 subtraction overflow")?.max(0),
                4=>a.checked_sub(b).ok_or("i128 subtraction overflow")?,
                5=>a.checked_div_euclid(b).ok_or("invalid division")?,
                6=>a.checked_rem_euclid(b).ok_or("invalid remainder")?,
                7=>a.max(0),
                8=>*row.get(usize::try_from(a)?).ok_or("input index outside row")? as i128,
                _=>unreachable!()
            };
        }
        bytes.clear();
        for value in &r[..width] { bytes.extend_from_slice(&((*value).rem_euclid(modulus) as u32).to_le_bytes()); }
        writer.write_all(&bytes)?;
    }
    writer.flush()?;
    let execute_ns=execute.elapsed().as_nanos();
    let result=json!({"producer":"Lean-generated witness instructions; native untrusted executor", "rows":rows.len(),"trace_width":width,"trace_bytes":rows.len()*width*4,"registers":nregs,"instructions":code.len(),"setup_ns":setup_ns,"execute_and_write_ns":execute_ns,"total_ns":started.elapsed().as_nanos(),"crypto_run":false});
    fs::write(out.join("emission.json"),serde_json::to_vec_pretty(&result)?)?;
    println!("{result}");Ok(())
}
fn main(){if let Err(e)=run(){eprintln!("{e}");std::process::exit(1)}}
