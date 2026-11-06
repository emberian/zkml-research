#!/usr/bin/env python3
"""sassbound: static per-pipe throughput bound for NVIDIA SASS (an llvm-mca-style port-pressure count, no scheduler).

usage: sassbound.py <file.sass> [--arch sm_75] [--kernel substr] [--clock-ghz F] [--sms N] [--json]

For every kernel in a `cuobjdump -sass` listing it finds the loops (a backward branch to a label), and for each
innermost loop body (and for the straight-line kernel when it has no loop) counts warp-instructions per pipe and
divides by that pipe's per-SM rate. The bound per loop iteration per warp, at the SM level, is

    cycles = max(issue = n_instr / 4,  max over pipes p of  sum_i 32 / rate_p(arch, i))

because an SM issues at most one warp-instruction per sub-partition per clock (4 per SM since Volta) and pipe p
retires rate_p lanes per clock per SM. That is a THROUGHPUT bound: it assumes enough warps (or ILP) to hide every
latency, no bank conflicts, no memory stalls. It is to a GPU what port pressure in llvm-mca / uiCA is to a CPU; the
classic static analytical GPU models (Hong and Kim's MWP-CWP, ISCA'09) add the latency/occupancy side, which this
tool reports only as inputs (registers, spills, occupancy from ptxas) and does not model.

Rates: CUDA C++ Best Practices Guide 13.5, Table 5 ("Throughput of Native Arithmetic Instructions", results per
clock per SM) [READ 2026-11-06], mapped to SASS opcodes below. Tensor rates: dense datasheet peak / (SMs * boost),
per SM per clock. LSU: 128 B/clk/SM for shared memory; global/local through L1 at 64 B/clk (sm_75) or 128 B/clk
(sm_80+) [A, Jia et al. 2019 / 2018 microbenchmarks; not re-measured].
"""
import argparse
import json
import re
import sys
from collections import Counter, defaultdict

ARCHS = ["sm_75", "sm_80", "sm_86", "sm_89", "sm_90", "sm_100", "sm_103", "sm_120"]


def cc_key(arch):
    a = arch.replace("sm_", "").rstrip("af")
    return {"75": "7.5", "80": "8.0", "86": "8.6", "87": "8.6", "89": "8.6", "90": "9.0", "100": "10.0",
            "101": "10.0", "103": "10.3", "110": "10.0", "120": "12.0", "121": "12.0"}[a]


# Table 5, results per clock per SM, by compute capability column (7.5, 8.0, 8.6/8.9, 9.0, 10.0, 10.3, 12.x).
T5 = {
    #               7.5   8.0   8.6   9.0   10.0  10.3  12.0
    "fp32":       (64,   64,   128,  128,  128,  128,  128),
    "fp64":       (2,    32,   2,    64,   64,   2,    2),
    "hf2":        (64,   128,  64,   128,  64,   64,   64),
    "iadd":       (128,  128,  128,  128,  128,  128,  128),   # add.s32
    "iadd3":      (64,   64,   64,   64,   64,   64,   64),    # 3-operand / extended add
    "imad":       (64,   64,   64,   64,   64,   64,   64),    # mad.lo.s32
    "imad_ext":   (32,   32,   32,   32,   32,   32,   32),    # footnote 6: extended-precision (hi, wide, .X)
    "shift":      (64,   64,   64,   64,   64,   64,   64),
    "logic":      (64,   64,   64,   64,   64,   64,   64),    # and/or/xor (LOP3)
    "minmax":     (64,   64,   64,   128,  128,  128,  128),
    "popc":       (16,   16,   16,   16,   16,   16,   16),    # popc, clz (FLO), brev
    "shfl":       (16,   32,   32,   32,   32,   32,   32),
    "vote":       (64,   64,   64,   64,   64,   64,   128),
    "mufu":       (16,   16,   16,   16,   16,   16,   16),    # table says 16 (165 footnote is a reference mark)
    "cvt_i2f":    (16,   16,   64,   64,   64,   64,   64),    # s32 -> f32
    "cvt_f2i":    (16,   16,   16,   16,   16,   2,    2),     # f32 -> s32, footnote 11
    "cvt_f64":    (2,    16,   2,    16,   16,   2,    2),
    "cvt_small":  (64,   64,   64,   64,   64,   64,   64),
}
COLS = ["7.5", "8.0", "8.6", "9.0", "10.0", "10.3", "12.0"]

# Dense tensor MACs per clock per SM by operand kind [READ datasheets; b1 on sm_75 MEASURED as ~8x u8 on T4].
TC = {
    "7.5": {"f16": 512, "s8": 1024, "s4": 2048, "b1": 8192},
    "8.0": {"f16": 1024, "s8": 2048, "s4": 4096, "b1": 16384, "f64": 32, "tf32": 512},
    "8.6": {"f16": 512, "s8": 1024, "s4": 2048, "b1": 8192, "e4m3": 1024},       # GA10x/AD10x consumer-class
    "9.0": {"f16": 2048, "s8": 4096, "e4m3": 4096, "f64": 64, "tf32": 1024, "b1": None},   # wgmma; mma.sync ~0.65x
    "10.0": {"f16": 4096, "s8": 8192, "e4m3": 8192, "e2m1": 16384, "f64": 64, "b1": None},
    "10.3": {"f16": 4096, "s8": 256, "e4m3": 8192, "e2m1": 24576, "f64": 2, "b1": None},
    "12.0": {"f16": 512, "s8": 1024, "e4m3": 1024, "e2m1": 2048, "b1": None},
}

ISSUE_PER_SM = 4  # one warp-instruction per sub-partition per clock

NOPIPE = {"BRA", "EXIT", "NOP", "BAR", "BSSY", "BSYNC", "WARPSYNC", "YIELD", "DEPBAR", "S2R", "CS2R", "S2UR",
          "RET", "CALL", "BPT", "MEMBAR", "ERRBAR", "CCTL", "JMP", "BREAK", "KILL", "NANOSLEEP", "WARPGROUP",
          "ELECT", "ENDCOLLECTIVE", "ACQBULK", "FENCE", "SYNCS", "ARRIVES", "R2UR", "REDUX", "VOTEU", "B2R"}


def classify(op, mods, operands):
    """Return (pipe, rate_key or None, lanes_bytes) for one SASS instruction."""
    if op.startswith("U") and op not in ("UTMALDG", "UTMASTG", "UBLKCP") and not op.startswith("UTC"):
        return ("uniform", None, 0)
    if op in NOPIPE:
        return ("issue", None, 0)
    if op in ("FFMA", "FADD", "FMUL", "FFMA2", "FADD2", "FMUL2", "FSWZADD", "FMNMX", "FSEL", "FSETP", "FSET",
              "FCHK"):
        return ("fma", "minmax" if op == "FMNMX" else "fp32", 0)
    if op in ("HFMA2", "HADD2", "HMUL2", "HMNMX2", "HSETP2", "HSET2"):
        return ("fma", "hf2", 0)
    if op in ("DFMA", "DADD", "DMUL", "DSETP", "DMNMX"):
        return ("fp64", "fp64", 0)
    if op == "IMAD":
        # [A] half rate for HI / WIDE (Table 5 footnote 6, "extended precision"); .X treated alike, unmeasured.
        if any(m in mods for m in ("HI", "WIDE", "X")):
            return ("fma", "imad_ext", 0)
        if "MOV" in mods or "SHL" in mods or "IADD" in mods:
            return ("fma", "imad", 0)
        return ("fma", "imad", 0)
    if op in ("IMUL", "IMADSP", "IDP", "IDP4A", "IDP2A"):
        return ("fma", "imad", 0)
    if op == "IADD3" or op == "IADD":
        # [A] Table 5 "3-operand addition" = 64. A forum microbenchmark on sm_89 (unverified here) reads IADD3 at
        # about twice the LOP3 issue rate; if so this row overstates ALU pressure for add-heavy code.
        return ("alu", "iadd3", 0)
    if op in ("LOP3", "LOP", "PLOP3", "SEL", "PRMT", "MOV", "P2R", "R2P", "BMSK", "SGXT", "LEA", "ISETP", "ICMP",
              "VABSDIFF", "VABSDIFF4", "IABS", "F2FP", "PSETP", "CSET", "CSETP", "FMNMX3"):
        return ("alu", "logic", 0)
    if op in ("SHF", "SHL", "SHR"):
        return ("alu", "shift", 0)
    if op in ("IMNMX", "VIMNMX", "VIMNMX3"):
        return ("alu", "minmax", 0)
    if op in ("FLO", "POPC", "BREV"):
        return ("xu", "popc", 0)
    if op in ("SHFL",):
        return ("lsu_shfl", "shfl", 0)
    if op in ("VOTE", "MATCH"):
        return ("alu", "vote", 0)
    if op == "MUFU":
        return ("xu", "mufu", 0)
    if op in ("I2F", "F2I", "I2FP", "F2IP", "FRND"):
        if "F64" in mods:
            return ("fp64", "cvt_f64", 0)
        return ("xu", "cvt_f2i" if op in ("F2I", "F2IP") else "cvt_i2f", 0)
    if op in ("F2F",):
        if "F64" in mods:
            return ("fp64", "cvt_f64", 0)
        return ("xu", "cvt_small", 0)
    if op in ("I2I", "I2IP"):
        return ("alu", "cvt_small", 0)
    if op in ("HMMA", "IMMA", "BMMA", "DMMA", "QMMA", "OMMA", "HGMMA", "IGMMA", "BGMMA", "QGMMA") or op.startswith("UTC"):
        return ("tensor", None, 0)
    if op in ("LDS", "STS", "LDSM", "ATOMS", "STSM"):
        return ("lsu_smem", None, width_bytes(mods, op))
    if op in ("LDG", "STG", "LD", "ST", "LDL", "STL", "ATOM", "ATOMG", "RED", "LDGSTS", "LDC", "TLD", "TEX",
              "SUST", "SULD", "ULDC", "LDGDEPBAR"):
        return ("lsu_mem", None, width_bytes(mods, op))
    if op in ("UTMALDG", "UTMASTG", "UBLKCP"):
        return ("tma", None, 0)
    return ("other", None, 0)


def width_bytes(mods, op):
    for m in mods:
        if m in ("128", "U128"):
            return 16
        if m in ("64", "U64", "S64"):
            return 8
        if m in ("U8", "S8"):
            return 1
        if m in ("U16", "S16"):
            return 2
    if op == "LDSM":
        n = 1
        for m in mods:
            if m.startswith("M88."):
                n = int(m.split(".")[1])
        return 0  # handled in tensor_macs-like path below
    return 4


SHAPE_RE = re.compile(r"^(\d+)(\d)(\d+)$")


def tensor_macs(op, mods):
    """MACs (bit-MACs for BMMA) per warp-level instruction, and the operand kind, from the SASS shape suffix."""
    kind = {"HMMA": "f16", "IMMA": "s8", "BMMA": "b1", "DMMA": "f64", "QMMA": "e4m3", "OMMA": "e2m1",
            "HGMMA": "f16", "IGMMA": "s8", "BGMMA": "b1", "QGMMA": "e4m3"}.get(op)
    shape = None
    for m in mods:
        if "x" in m and op.endswith("GMMA"):           # e.g. 64x128x32
            parts = m.split("x")
            if all(p.isdigit() for p in parts) and len(parts) == 3:
                shape = tuple(int(p) for p in parts)
        elif m.isdigit() and len(m) >= 3 and shape is None:
            # 1688 -> 16,8,8 ; 16816 -> 16,8,16 ; 16832 -> 16,8,32 ; 8816 -> 8,8,16 ; 88128 -> 8,8,128 ; 168256
            for mm in (16, 8):
                s = str(mm)
                if m.startswith(s):
                    rest = m[len(s):]
                    for nn in (8, 16):
                        t = str(nn)
                        if rest.startswith(t) and rest[len(t):].isdigit():
                            shape = (mm, nn, int(rest[len(t):]))
                            break
                if shape:
                    break
    if op == "IMMA" and any(m in ("U4", "S4") for m in mods):
        kind = "s4"
    if op in ("HMMA",) and "TF32" in mods:
        kind = "tf32"
    if op in ("HMMA",) and ("E4M3" in mods or "E5M2" in mods):
        kind = "f16"  # unpacked path
    macs = shape[0] * shape[1] * shape[2] if shape else None
    return kind, macs, shape


INSTR_RE = re.compile(r"/\*([0-9a-f]{4,})\*/\s+(@!?U?P[T0-9]+\s+)?([A-Z][A-Z0-9_]*)((?:\.[A-Za-z0-9_x]+)*)\s*([^;]*);")
LABEL_RE = re.compile(r"^\s*(\.L_x_\d+):")
FUNC_RE = re.compile(r"Function\s*:\s*(\S+)")
TARGET_RE = re.compile(r"`\((\.L_x_\d+)\)|(?:^|[\s,])(0x[0-9a-f]+)\s*$")


def parse(text):
    funcs = {}
    cur = None
    pending_labels = []
    for line in text.splitlines():
        m = FUNC_RE.search(line)
        if m:
            cur = m.group(1)
            funcs[cur] = {"instrs": [], "labels": {}}
            continue
        if cur is None:
            continue
        lm = LABEL_RE.match(line)
        if lm:
            pending_labels.append(lm.group(1))
            continue
        im = INSTR_RE.search(line)
        if im:
            addr = int(im.group(1), 16)
            op = im.group(3)
            mods = [x for x in im.group(4).split(".") if x]
            opnds = im.group(5)
            tm = TARGET_RE.search(opnds)
            tgt = (tm.group(1) or int(tm.group(2), 16)) if tm else None
            ins = dict(addr=addr, op=op, mods=mods, operands=opnds, target=tgt,
                       pred=(im.group(2) or "").strip())
            for lab in pending_labels:
                funcs[cur]["labels"][lab] = addr
            pending_labels = []
            funcs[cur]["instrs"].append(ins)
    return funcs


def loops(f):
    """(start_addr, end_addr) for each backward branch."""
    out = []
    for ins in f["instrs"]:
        if ins["op"] in ("BRA", "JMP") and ins["target"] is not None:
            t = ins["target"] if isinstance(ins["target"], int) else f["labels"].get(ins["target"])
            if t is None:
                continue
            if t <= ins["addr"]:
                out.append((t, ins["addr"]))
    return sorted(set(out))


def innermost(ls):
    return [l for l in ls if not any(o != l and l[0] <= o[0] and o[1] <= l[1] for o in ls)]


def bound(instrs, arch):
    cc = cc_key(arch)
    col = COLS.index(cc if cc in COLS else "9.0")
    pipe_cyc = defaultdict(float)
    mix = Counter()
    notes = Counter()
    tensor_macs_total = defaultdict(float)
    l1_bytes_per_clk = 64 if cc == "7.5" else 128
    for ins in instrs:
        pipe, key, nbytes = classify(ins["op"], ins["mods"], ins["operands"])
        mix[ins["op"] + ("." + ".".join(m for m in ins["mods"] if m in ("HI", "WIDE", "X", "U32", "64", "128"))
                         if ins["op"] in ("IMAD", "LDG", "STG", "LDS", "STS", "LDL", "STL") else "")] += 1
        if pipe in ("issue", "uniform", "other"):
            if pipe == "other":
                notes["unclassified:" + ins["op"]] += 1
            continue
        if key is not None:
            pipe_name = {"fp32": "fma", "hf2": "fma", "imad": "fma", "imad_ext": "fma", "fp64": "fp64",
                         "cvt_f64": "fp64"}.get(key, pipe)
            # Table 5 groups: integer multiply and fp32 FMA share the FMA datapath on these parts [A];
            # logic/shift/iadd3/minmax/vote/cvt_small share the ALU (INT) datapath.
            pipe_cyc[pipe_name] += 32.0 / T5[key][col]
        elif pipe == "lsu_smem":
            w = nbytes if nbytes else 4
            pipe_cyc["lsu"] += max(1.0, 32 * w / 128.0)
        elif pipe == "lsu_mem":
            w = nbytes if nbytes else 4
            pipe_cyc["lsu"] += max(1.0, 32 * w / l1_bytes_per_clk)
            if ins["op"] in ("LDL", "STL"):
                notes["local_memory_spill_or_array"] += 1
        elif pipe == "lsu_shfl":
            pipe_cyc["lsu"] += 32.0 / T5["shfl"][col]
        elif pipe == "tensor":
            kind, macs, shape = tensor_macs(ins["op"], ins["mods"])
            rate = TC.get(cc, {}).get(kind)
            if macs and rate:
                pipe_cyc["tensor"] += macs / rate
                tensor_macs_total[kind] += macs
            else:
                notes[f"tensor_unmodelled:{ins['op']}.{'.'.join(ins['mods'])}"] += 1
        elif pipe == "tma":
            notes["tma"] += 1
    n = sum(1 for i in instrs if classify(i["op"], i["mods"], i["operands"])[0] != "uniform")
    issue = n / ISSUE_PER_SM
    pipes = dict(pipe_cyc)
    pipes["issue"] = issue
    bind = max(pipes, key=pipes.get)
    return dict(n_instr=len(instrs), n_nonuniform=n, cycles=pipes[bind], bound_by=bind,
                pipes={k: round(v, 2) for k, v in sorted(pipes.items(), key=lambda kv: -kv[1])},
                mix=dict(mix.most_common(14)), notes=dict(notes), tensor_macs=dict(tensor_macs_total))


def analyse(text, arch, ksub=None):
    res = {}
    for name, f in parse(text).items():
        if ksub and ksub not in name:
            continue
        ls = loops(f)
        inn = innermost(ls)
        entry = dict(n_instr=len(f["instrs"]), loops=[(hex(a), hex(b)) for a, b in ls], bodies=[])
        for a, b in inn:
            body = [i for i in f["instrs"] if a <= i["addr"] <= b]
            r = bound(body, arch)
            r["range"] = (hex(a), hex(b))
            entry["bodies"].append(r)
        entry["whole"] = bound(f["instrs"], arch)
        res[name] = entry
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sass")
    ap.add_argument("--arch", default=None)
    ap.add_argument("--kernel", default=None)
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()
    arch = a.arch or re.search(r"sm_\d+[af]?", a.sass).group(0)
    res = analyse(open(a.sass).read(), arch, a.kernel)
    if a.json:
        print(json.dumps(res, indent=1))
        return
    for name, e in res.items():
        print(f"== {name}  ({arch}, {e['n_instr']} instr, {len(e['loops'])} loops)")
        for r in e["bodies"] or [e["whole"]]:
            print(f"   body {r.get('range', 'whole')}: {r['n_instr']} instr, bound {r['cycles']:.1f} clk/warp-iter "
                  f"by {r['bound_by']}; pipes {r['pipes']}")
            print(f"     mix {r['mix']}")
            if r["notes"]:
                print(f"     notes {r['notes']}")


if __name__ == "__main__":
    main()
