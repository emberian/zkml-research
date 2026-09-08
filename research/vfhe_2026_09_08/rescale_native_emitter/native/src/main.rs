//! Untrusted execution of Lean-emitted arithmetic instructions. This executable
//! copies the frozen template and never constructs or evaluates AIR constraints.
use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_traits::ToPrimitive;
use serde_json::{json, Value};
use std::{error::Error, fs, io::{BufWriter, Write}, path::Path, time::Instant};
type Result<T> = std::result::Result<T, Box<dyn Error>>;

// Small arithmetic dominates radix bits and carries. Promotion is exact and
// automatic; the large signed source masses never pass through a fixed word.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Number { Small(i128), Big(BigInt) }
impl Number {
    fn big(x: BigInt) -> Self { x.to_i128().map(Self::Small).unwrap_or(Self::Big(x)) }
    fn as_big(&self) -> BigInt { match self { Self::Small(x) => BigInt::from(*x), Self::Big(x) => x.clone() } }
    fn positive(&self) -> bool { match self { Self::Small(x) => *x > 0, Self::Big(x) => x.sign() == Sign::Plus } }
    fn index(&self) -> Result<usize> { match self {
        Self::Small(x) => Ok(usize::try_from(*x)?),
        Self::Big(x) => x.to_usize().ok_or_else(|| "index outside usize".into())
    } }
    fn binary(op: u8, a: Self, b: Self) -> Result<Self> {
        if op == 0 { return Ok(a) }
        if op == 7 { return Ok(if a.positive() { a } else { Self::Small(0) }) }
        if op == 9 { return if a == b { Ok(a) } else { Err("public alias mismatch".into()) } }
        if (op == 5 || op == 6) && !b.positive() { return Err("division requires positive denominator".into()) }
        if let (Self::Small(x), Self::Small(y)) = (&a, &b) {
            let fast = match op {
                1 => x.checked_add(*y), 2 => x.checked_mul(*y),
                3 => x.checked_sub(*y).map(|z| z.max(0)), 4 => x.checked_sub(*y),
                5 => x.checked_div_euclid(*y), 6 => x.checked_rem_euclid(*y),
                _ => return Err("unknown arithmetic opcode".into())
            };
            if let Some(z) = fast { return Ok(Self::Small(z)) }
        }
        let x = a.as_big(); let y = b.as_big();
        Ok(Self::big(match op {
            1 => x+y, 2 => x*y, 3 => (x-y).max(BigInt::from(0)),
            4 => x-y, 5 => x.div_floor(&y), 6 => x.mod_floor(&y),
            _ => return Err("unknown arithmetic opcode".into())
        }))
    }
}
#[derive(Clone)]
enum Arg { Lit(Number), Reg(usize) }
impl Arg { fn get(&self, r: &[Number]) -> Number { match self { Self::Lit(x) => x.clone(), Self::Reg(i) => r[*i].clone() } } }
struct Instruction { dst: usize, op: u8, a: Arg, b: Arg }
fn nat(v: &Value) -> Result<usize> { Ok(usize::try_from(v.as_u64().ok_or("expected natural integer")?)?) }
fn arg(mode: &Value, value: &Value, regs: usize) -> Result<Arg> {
    match nat(mode)? {
        0 => Ok(Arg::Lit(Number::big(value.as_str().ok_or("literal must be decimal string")?.parse()?))),
        1 => { let i = nat(value)?; if i >= regs { return Err("operand outside registers".into()) } Ok(Arg::Reg(i)) },
        _ => Err("unknown operand mode".into())
    }
}
fn run() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 5 { return Err("usage: lean-bigint-witness PLAN TEMPLATE PUBLIC_ROWS NEW_OUT_DIR".into()) }
    let started = Instant::now();
    let plan: Value = serde_json::from_slice(&fs::read(&args[1])?)?;
    if plan["schema"] != "lean-bigint-witness-plan-v1" { return Err("wrong plan schema".into()) }
    let width = nat(&plan["trace_width"])?;
    let arity = nat(&plan["input_arity"])?;
    let regs = nat(&plan["register_count"])?;
    let modulus = nat(&plan["field_modulus"])?;
    let radix = nat(&plan["input_digit_radix"])?;
    if width == 0 || arity == 0 || arity > width || regs < width || regs > 1_000_000 || modulus <= 1 || modulus > u32::MAX as usize || radix < 2 {
        return Err("invalid plan dimensions".into())
    }
    let mut code = Vec::new();
    for ins in plan["instructions"].as_array().ok_or("missing instructions")? {
        let t = ins.as_array().ok_or("bad instruction")?;
        if t.len() != 6 { return Err("instruction must have six entries".into()) }
        let dst = nat(&t[0])?; let op = nat(&t[1])?;
        if dst >= regs || op > 9 { return Err("invalid instruction".into()) }
        code.push(Instruction { dst, op: op as u8, a: arg(&t[2], &t[3], regs)?, b: arg(&t[4], &t[5], regs)? });
    }
    let template = fs::read(&args[2])?;
    // The proof backend owns descriptor parsing and width validation. Carry the
    // caller's pinned template as opaque bytes, including deep expression trees.
    let rows: Vec<Vec<u64>> = serde_json::from_slice(&fs::read(&args[3])?)?;
    if rows.is_empty() { return Err("empty input".into()) }
    for (i,row) in rows.iter().enumerate() {
        if row.len() != arity || row[0] >= modulus as u64 || row[1..].iter().any(|x| *x >= radix as u64) {
            return Err(format!("invalid public row {i}").into())
        }
    }
    let out = Path::new(&args[4]);
    if out.exists() { return Err("output directory must be new".into()) }
    fs::create_dir_all(out)?;
    fs::write(out.join("template_ir2.json"), &template)?;
    let setup_ns = started.elapsed().as_nanos(); let execute = Instant::now();
    let mut writer = BufWriter::with_capacity(1<<20, fs::File::create(out.join("trace.leu32"))?);
    let mut r = vec![Number::Small(0); regs]; let mut bytes = Vec::with_capacity(width*4);
    for (i,row) in rows.iter().enumerate() {
        r.fill(Number::Small(0));
        for ins in &code {
            let a = ins.a.get(&r); let b = ins.b.get(&r);
            r[ins.dst] = if ins.op == 8 {
                Number::Small(*row.get(a.index()?).ok_or("input index outside row")? as i128)
            } else { Number::binary(ins.op, a, b).map_err(|e| format!("row {i}, destination {}: {e}",ins.dst))? };
        }
        // Public binding belongs to the caller's existing ExactPublicRows table.
        for j in 0..arity { if r[j] != Number::Small(row[j] as i128) { return Err("producer changed public prefix".into()) } }
        bytes.clear();
        for value in &r[..width] {
            let word = Number::binary(6, value.clone(), Number::Small(modulus as i128))?.index()?;
            bytes.extend_from_slice(&(word as u32).to_le_bytes());
        }
        writer.write_all(&bytes)?;
    }
    writer.flush()?;
    let result = json!({"producer":"Lean source-row elimination and sparse carry instructions; untrusted exact BigInt executor",
        "rows":rows.len(),"trace_width":width,"trace_bytes":rows.len()*width*4,
        "registers":regs,"instructions":code.len(),"setup_ns":setup_ns,
        "execute_and_write_ns":execute.elapsed().as_nanos(),"total_ns":started.elapsed().as_nanos(),
        "public_prefix_preserved":true,"crypto_run":false,"air_constructed_or_evaluated":false});
    fs::write(out.join("emission.json"), serde_json::to_vec_pretty(&result)?)?;
    println!("{result}"); Ok(())
}
fn main() { if let Err(e) = run() { eprintln!("{e}"); std::process::exit(1) } }
