"""Op and byte counts from the PRE-optimization StableHLO of a JAX program (platform independent; runs on the
Mac). This is the input to the bound: work the program asks for, before any compiler decision.

    counts(fn, *ShapeDtypeStructs) -> dict

MXU work: every stablehlo.dot_general, MACs = |out| * |contracting|, binned by operand dtype.
VPU work: elementwise arithmetic/logic/compare/select/convert and reduce inputs, in elements, binned by bit
width. Data movement (broadcast, reshape, transpose, slice, concat, pad, gather) is counted separately and
not charged to any unit: the compiler fuses most of it; the HLO inspector judges what survives.
Compulsory HBM bytes: entry arguments read once plus results written once.
Calls into private funcs are counted with multiplicity. A while loop is a hard error: kernels counted here
must be loop-free at the JAX level (use a grid in Pallas or vectorize), so counts are exact.
"""
import re
from collections import Counter, defaultdict

import jax

DT_BITS = {"i1": 1, "i8": 8, "ui8": 8, "i16": 16, "ui16": 16, "bf16": 16, "f16": 16, "i32": 32, "ui32": 32,
           "f32": 32, "i64": 64, "ui64": 64, "f64": 64, "i4": 4, "ui4": 4}
VPU_OPS = {"add", "subtract", "multiply", "and", "or", "xor", "not", "negate", "abs", "shift_left",
           "shift_right_logical", "shift_right_arithmetic", "compare", "select", "convert", "maximum", "minimum",
           "clamp", "remainder", "divide", "sign", "popcnt", "count_leading_zeros", "exponential", "log", "rsqrt",
           "sqrt", "tanh", "logistic", "power", "floor", "ceil", "round_nearest_even"}
EXPENSIVE = {"remainder", "divide", "power", "exponential", "log", "rsqrt", "sqrt", "tanh", "logistic"}
MOVE_OPS = {"broadcast_in_dim", "reshape", "transpose", "slice", "concatenate", "pad", "gather", "dynamic_slice",
            "dynamic_update_slice", "reverse", "iota", "bitcast_convert", "scatter"}
TENSOR = re.compile(r"tensor<([^>]*)>")


def _ceil(x, m):
    return -(-x // m) * m


def parse_tensor(t):
    parts = t.split("x")
    dt = parts[-1]
    dims = [int(p) for p in parts[:-1]] if len(parts) > 1 else []
    n = 1
    for d in dims:
        n *= d
    return dims, dt, n


def nbytes(t):
    dims, dt, n = parse_tensor(t)
    return n * max(DT_BITS.get(dt, 32), 8) // 8


def _funcs(text):
    funcs, cur, body = {}, None, []
    for line in text.splitlines():
        m = re.match(r"\s*func\.func (?:public |private )?@([\w.$-]+)\((.*)", line)
        if m:
            cur, body = m.group(1), [line]
            funcs[cur] = body
        elif cur:
            body.append(line)
    return funcs


def _count_func(name, funcs, memo):
    if name in memo:
        return memo[name]
    c = dict(mxu=Counter(), vpu=Counter(), vpu_by_op=Counter(), move=0, flags=set())
    for line in funcs[name][1:]:
        s = line.strip()
        m = re.match(r"(?:%[\w#:, ]+= )?\"?stablehlo\.(\w+)\"?", s)
        call = re.search(r"call @([\w.$-]+)\(", s)
        if call and call.group(1) in funcs:
            sub = _count_func(call.group(1), funcs, memo)
            for k in ("mxu", "vpu", "vpu_by_op"):
                c[k].update(sub[k])
            c["move"] += sub["move"]
            c["flags"] |= sub["flags"]
            continue
        if not m:
            continue
        op = m.group(1)
        ts = TENSOR.findall(s)
        if op == "while":
            raise ValueError("while loop in counted program: counts would not be exact; vectorize or use a Pallas grid")
        if op == "dot_general":
            (ldims, ldt, _), (rdims, rdt, _), (odims, odt, on) = (parse_tensor(t) for t in ts[-3:])
            cd = re.search(r"contracting_dims = \[([\d, ]*)\] x", s).group(1)
            k = 1
            for i in [int(x) for x in cd.split(",") if x.strip()]:
                k *= ldims[i]
            unit = {"i8": "mxu_int8", "ui8": "mxu_uint8", "bf16": "mxu_bf16", "f32": "mxu_f32"}.get(ldt, "dot_" + ldt)
            if ldt != rdt:
                unit += "x" + rdt
            c["mxu"][unit] += on * k
            # MXU-granular work: K and the output minor (lane) dim padded to 128 (the v5e edge; on v6e, edge 256,
            # this undercounts). The leading output dims are streamed rows and are not padded.
            c["mxu"][unit + "@pad"] += (on // max(odims[-1], 1)) * _ceil(odims[-1], 128) * _ceil(k, 128)
            if unit not in ("mxu_int8", "mxu_bf16"):
                c["flags"].add(f"dot with operands {ldt}x{rdt}: not a native MXU dtype on v5e (int8/bf16)")
        elif op in VPU_OPS or op == "reduce":
            if not ts:
                continue
            t = ts[0] if op == "reduce" else ts[-1]
            dims, dt, n = parse_tensor(t)
            if op in ("compare", "convert") and len(ts) > 1:
                dims, dt, n = parse_tensor(ts[0])  # charge at the operand width
            bits = DT_BITS.get(dt, 32)
            key = f"{'64' if bits == 64 else '32'}"
            c["vpu"][key] += n
            c["vpu_by_op"][f"{op}:{dt}"] += n
            if bits == 64:
                c["flags"].add(f"64-bit {op} ({dt}): emulated on TPU, illegal in Pallas/Mosaic")
            if op in EXPENSIVE:
                c["flags"].add(f"{op} on {dt}: multi-instruction on the VPU")
        elif op in MOVE_OPS and ts:
            c["move"] += parse_tensor(ts[-1])[2]
    memo[name] = c
    return c


def counts_from_text(text):
    funcs = _funcs(text)
    main = "main" if "main" in funcs else next(iter(funcs))
    c = _count_func(main, funcs, {})
    sig = funcs[main][0]
    args_part, _, res_part = sig.partition(") -> ")
    in_bytes = sum(nbytes(t) for t in TENSOR.findall(args_part))
    out_bytes = sum(nbytes(t) for t in TENSOR.findall(res_part))
    return dict(mxu_macs=dict(c["mxu"]), vpu_elems=dict(c["vpu"]), vpu_by_op=dict(c["vpu_by_op"].most_common(12)),
                move_elems=c["move"], hbm_in=in_bytes, hbm_out=out_bytes, flags=sorted(c["flags"]))


def counts(fn, *args):
    return counts_from_text(jax.jit(fn).lower(*args).as_text())


def bound(cnt, gen, vpu_ops=None):
    """Best achievable time on `gen` and the binding unit. Each unit's time is its work over its peak; the bound
    is the max (perfect overlap), which is what a well-pipelined kernel can approach."""
    from .hw import GEN
    g = GEN[gen]
    t = {}
    m = cnt["mxu_macs"]
    t["mxu"] = 2 * m.get("mxu_int8@pad", 0) / g["int8"] + 2 * m.get("mxu_bf16@pad", 0) / g["bf16"]
    ideal_mxu = 2 * m.get("mxu_int8", 0) / g["int8"] + 2 * m.get("mxu_bf16", 0) / g["bf16"]
    other = {k: v for k, v in m.items() if k not in ("mxu_int8", "mxu_bf16") and not k.endswith("@pad")}
    if other:
        t["mxu_nonnative"] = sum(2 * v for v in other.values()) / (g["bf16"] / 6)  # [INFERRED] f32-like multipass
    vp = vpu_ops or g["vpu_ops"]
    if vp:
        v = cnt["vpu_elems"]
        t["vpu"] = (v.get("32", 0) + 4 * v.get("64", 0)) / vp  # 64-bit charged 4x [INFERRED]
    t["hbm"] = (cnt["hbm_in"] + cnt["hbm_out"]) / g["hbm_bw"]
    unit = max(t, key=t.get)
    out = dict(bound_s=t[unit], unit=unit, per_unit_s=t, vpu_peak=vp, vpu_src=g.get("vpu_src"),
               mxu_ideal_unpadded_s=ideal_mxu)
    if not vp and sum(cnt["vpu_elems"].values()):
        out["caveat"] = "VPU peak unknown for this generation: the bound omits VPU work and is a lower bound only"
    return out


# ---------------------------------------------------------------------------------------------------------
# jaxpr counter: counts what the KERNEL as written does, including inside Pallas bodies (x grid steps). This
# is the VPU model for Pallas kernels; the StableHLO counter above counts an XLA formulation of the algorithm.
# ---------------------------------------------------------------------------------------------------------
JAXPR_VPU = {"add", "sub", "mul", "and", "or", "xor", "not", "neg", "shift_left", "shift_right_arithmetic",
             "shift_right_logical", "lt", "le", "gt", "ge", "eq", "ne", "select_n", "convert_element_type", "max",
             "min", "floor", "abs", "sign", "rem", "div", "reduce_sum", "reduce_max", "bitcast_convert_type"}


def _np_size(shape):
    n = 1
    for d in shape:
        n *= int(d)
    return n


def _walk_counts(jaxpr, mult, c):
    import numpy as np
    for e in jaxpr.eqns:
        name = e.primitive.name
        if name == "pallas_call":
            gm = e.params["grid_mapping"]
            steps = _np_size(gm.grid) if gm.grid else 1
            _walk_counts(e.params["jaxpr"], mult * steps, c)
            continue
        if name == "dot_general":
            (lc, rc), _ = e.params["dimension_numbers"]
            ls = e.invars[0].aval.shape
            K = _np_size([ls[i] for i in lc])
            out = e.outvars[0].aval.shape
            dt = str(e.invars[0].aval.dtype)
            unit = {"int8": "mxu_int8", "bfloat16": "mxu_bf16"}.get(dt, "dot_" + dt)
            c["mxu"][unit] += mult * _np_size(out) * K
            c["mxu"][unit + "@pad"] += mult * (_np_size(out) // max(out[-1], 1)) * _ceil(out[-1], 128) * _ceil(K, 128)
            continue
        subs = [v for v in e.params.values() if hasattr(v, "eqns") or hasattr(getattr(v, "jaxpr", None), "eqns")]
        if subs and name not in JAXPR_VPU:
            for v in subs:
                _walk_counts(v if hasattr(v, "eqns") else v.jaxpr, mult, c)
            continue
        if name in JAXPR_VPU:
            av = e.invars[0].aval if name.startswith("reduce") else e.outvars[0].aval
            dt = str(av.dtype)
            c["vpu_by_op"][f"{name}:{dt}"] += mult * _np_size(av.shape)
            bits = np.dtype(av.dtype).itemsize * 8
            c["vpu"]["64" if bits == 64 else "32"] += mult * _np_size(av.shape)


def counts_jaxpr(fn, *args):
    import jax
    from collections import Counter
    j = jax.make_jaxpr(fn)(*args)
    c = dict(mxu=Counter(), vpu=Counter(), vpu_by_op=Counter())
    _walk_counts(j.jaxpr, 1, c)
    nb = lambda a: _np_size(a.shape) * a.dtype.itemsize
    out_avals = [v.aval for v in j.jaxpr.outvars]
    return dict(mxu_macs=dict(c["mxu"]), vpu_elems=dict(c["vpu"]), vpu_by_op=dict(c["vpu_by_op"]),
                move_elems=0, hbm_in=sum(nb(a) for a in args), hbm_out=sum(nb(a) for a in out_avals), flags=[])


def vpu_time(cnt, op_rates, default_rate):
    """Per-op VPU model: sum over (op, dtype) of elements / measured rate for that op (default otherwise)."""
    t = 0.0
    for k, n in cnt["vpu_by_op"].items():
        op = k.split(":")[0]
        t += n / op_rates.get(op, default_rate)
    return t
