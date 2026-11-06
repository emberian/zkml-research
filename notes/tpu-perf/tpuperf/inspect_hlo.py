"""Inspector for the TPU compiler's OPTIMIZED HLO (c.as_text() of a deviceless TPU compile on hbox).

Flags, each with where it happens:
  relayout copy / transpose / pad  -- inside an MXU (convolution) fusion: done on VMEM windows on the fly
                                      (VPU/XLU work, no HBM pass); in a standalone fusion: an extra HBM pass
  non-MXU dot      -- a convolution whose operands are not s8/bf16 (s32/f32 dots are multipass or VPU)
  MXU underfill    -- contraction or output feature dim not a multiple of the MXU edge (128 v5e, 256 v6e)
  64-bit types     -- s64/u64 anywhere (emulated)
  while loops      -- serial loops the compiler did not unroll
  custom calls     -- tpu_custom_call (Pallas/Mosaic) and anything else
Also sums the compiler's per-fusion `estimated_cycles` and the scoped VMEM each fusion uses.
"""
import json
import re

INSTR = re.compile(r"^\s*(ROOT )?%([\w.\-]+) = (\(?[^ ]+(?: [^ =]+)*?\)?) ([\w\-]+)\((.*)$")


def computations(text):
    comps, cur = {}, None
    for line in text.splitlines():
        m = re.match(r"^(ENTRY )?%([\w.\-]+) .*\{\s*$", line)
        if m:
            cur = m.group(2)
            comps[cur] = {"entry": bool(m.group(1)), "lines": []}
        elif line.startswith("}"):
            cur = None
        elif cur:
            comps[cur]["lines"].append(line)
    return comps


def _shape(s):
    m = re.match(r"\(?(\w+)\[([\d,]*)\]", s)
    if not m:
        return None, []
    return m.group(1), [int(x) for x in m.group(2).split(",") if x]


BITS = {"pred": 8, "s8": 8, "u8": 8, "s16": 16, "u16": 16, "bf16": 16, "f16": 16, "s32": 32, "u32": 32, "f32": 32,
        "s64": 64, "u64": 64, "f64": 64}


def _bytes(shape_str):
    dt, dims = _shape(shape_str)
    n = 1
    for d in dims:
        n *= d
    return n * BITS.get(dt, 32) // 8


def inspect(text, mxu_edge=128):
    comps = computations(text)
    parent = {}  # computation -> (caller computation, caller fusion kind, caller is MXU fusion)
    conv_comps = set()
    for name, c in comps.items():
        for ln in c["lines"]:
            if " convolution(" in ln or " dot(" in ln:
                conv_comps.add(name)
    for name, c in comps.items():
        for ln in c["lines"]:
            m = re.search(r"calls=%([\w.\-]+)", ln)
            if m:
                k = re.search(r"kind=(k\w+)", ln)
                parent[m.group(1)] = (name, k.group(1) if k else "?")

    def in_mxu_fusion(comp):
        seen = 0
        while comp is not None and seen < 20:
            if comp in conv_comps:
                return True
            comp = parent.get(comp, (None,))[0]
            seen += 1
        return False

    findings, est_cycles, vmem, fusions, n_instr = [], 0, [], [], 0
    for name, c in comps.items():
        for ln in c["lines"]:
            n_instr += 1
            op = re.search(r"\) ([\w\-]+)\(|\} ([\w\-]+)\(|\] ([\w\-]+)\(", ln)
            opname = next((g for g in op.groups() if g), None) if op else None
            if opname in ("copy", "transpose", "pad"):
                dst = ln.split(" = ", 1)[1].split(" ")[0] if " = " in ln else ""
                if opname == "copy" and "S(1)" in dst and c["entry"]:
                    where = "prefetch HBM->VMEM"          # memory space 1 is VMEM: a DMA, not a relayout
                elif re.match(r"\w+\[\]", dst):
                    continue                                 # scalar bookkeeping copies
                else:
                    where = "in-MXU-fusion (VMEM, on the fly)" if in_mxu_fusion(name) else (
                        "ENTRY (HBM pass)" if c["entry"] else "standalone fusion (HBM pass)")
                lay = re.findall(r"\{[\d,]+:T[^}]*\}", ln)
                findings.append(dict(kind=opname, where=where, comp=name, layouts=lay[:3], bytes=_bytes(dst),
                                     line=ln.strip()[:240]))
            if opname == "convolution":
                ops = re.findall(r"(\w+)\[([\d,]*)\]\{", ln)
                dts = [o[0] for o in ops[1:3]]
                if any(d not in ("s8", "bf16", "u8") for d in dts):
                    findings.append(dict(kind="non-MXU-dtype dot", where=name, dtypes=dts, line=ln.strip()[:240]))
                dims = [[int(x) for x in o[1].split(",") if x] for o in ops[:3]]
                for d in dims:
                    if d and d[-1] % mxu_edge:
                        findings.append(dict(kind="MXU underfill", where=name,
                                             detail=f"minor dim {d[-1]} not a multiple of {mxu_edge}", line=ln.strip()[:200]))
                        break
            if re.search(r"\b[su]64\[", ln):
                findings.append(dict(kind="64-bit type", where=name, line=ln.strip()[:200]))
            if opname == "while":
                findings.append(dict(kind="while loop", where=name, line=ln.strip()[:200]))
            if opname == "custom-call":
                tgt = re.search(r'custom_call_target="([^"]+)"', ln)
                findings.append(dict(kind="custom-call", target=tgt.group(1) if tgt else "?", where=name))
            if c["entry"] and opname == "fusion":
                k = re.search(r"kind=(k\w+)", ln)
                e = re.search(r'"estimated_cycles":"(\d+)"', ln)
                fusions.append(dict(kind=k.group(1) if k else "?", est_cycles=int(e.group(1)) if e else None,
                                    calls=re.search(r"calls=%([\w.\-]+)", ln).group(1)))
            e = re.search(r'"estimated_cycles":"(\d+)"', ln)
            if e and c["entry"]:
                est_cycles += int(e.group(1))
            for mm in re.finditer(r'"used_scoped_memory_configs":\[([^\]]*)\]', ln):
                for sz in re.findall(r'"size":"(\d+)"', mm.group(1)):
                    vmem.append(int(sz))
    kinds = {}
    for f in findings:
        key = f["kind"] + (" @ " + f["where"] if f["kind"] in ("copy", "transpose", "pad") else "")
        kinds[key] = kinds.get(key, 0) + 1
        if "bytes" in f:
            kinds[key + " bytes"] = kinds.get(key + " bytes", 0) + f["bytes"]
    has_mosaic = any(f.get("target") == "tpu_custom_call" for f in findings)
    return dict(summary=kinds, compiler_estimate_covers_mosaic=not has_mosaic, findings=findings[:40], entry_fusions=fusions, est_cycles_entry=est_cycles,
                scoped_vmem_max=max(vmem) if vmem else 0, n_instructions=n_instr,
                async_prefetch=text.count("copy-start("))


if __name__ == "__main__":
    import sys
    print(json.dumps(inspect(open(sys.argv[1]).read()), indent=1))
