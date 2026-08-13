#!/usr/bin/env python3
"""catgrad-trace/v0  ->  zkml-trace/v1.

v1 is a GREENFIELD wire format designed against `Theory/ZkmlTensorOps.lean`'s
vocabulary, not inherited from catgrad's. The differences are not cosmetic; each
one is a fact v0 does not carry, and this script reports every place it had to
INVENT the missing fact rather than read it.

Run:  python3 v0_to_v1.py mnist-trace.json --lean out.lean --json out.json
"""
import json
import sys
from collections import OrderedDict

VERSION = "zkml-trace/v1"

# v0 op name -> v1 constructor, with the operand order the vocabulary expects.
DTYPE = {"f32": "Dtype.f32", "bf16": "Dtype.bf16", "f8": "Dtype.fp8"}


class Undetermined(list):
    def note(self, key, detail):
        self.append((key, detail))


def convert(v0):
    und = Undetermined()
    ops = v0["ops"]
    by_out = {}
    for o in ops:
        for w in o["out"]:
            by_out[w] = o

    consts = [o for o in ops if o["op"] == "const"]
    others = [o for o in ops if o["op"] != "const"]

    # ---- level assignment -------------------------------------------------
    level = {}
    for i, o in enumerate(consts):
        level[o["out"][0]] = i
    for j, o in enumerate(others):
        level[o["out"][0]] = len(consts) + j

    # ---- roles ------------------------------------------------------------
    # v0 gives every constant the SAME shape of record: an FNV digest and a
    # length. It cannot say whether a constant is a model weight, the inference
    # input, or a program literal, and the three have completely different
    # commitment obligations. We classify by rank as a stand-in and record it.
    inputs = []
    for o in consts:
        shp = o["out_shapes"][0]
        if len(shp) == 2:
            role, path = "param", f"weight/{o['attrs']['digest']}"
        elif len(shp) == 0:
            role, path = "literal", f"lit/{o['attrs']['digest']}"
        else:
            role, path = "input", "input/0"
        inputs.append(
            OrderedDict(role=role, dtype=o["dtype"], shape=shp, path=path)
        )
    und.note(
        "role",
        "v0 has ONE `const` op for weights, the inference input and program "
        "literals alike; roles below were assigned by tensor RANK, which is a "
        "guess. v1 makes `role` mandatory and the tracer must supply it.",
    )
    und.note(
        "path",
        "v0 identifies a constant only by an FNV digest, so the trace cannot "
        "say WHICH weight entered a wire and no weight commitment can be "
        "checked against it. v1 makes `path` mandatory (and FNV must be "
        "replaced by a collision-resistant commitment before it binds).",
    )

    # ---- ops --------------------------------------------------------------
    out_ops = []
    for o in others:
        k = o["op"]
        ins = [level[w] for w in o["in"]]
        if k == "neg":
            rec = OrderedDict(op="un", kind="neg", ins=ins)
        elif k in ("add", "sub", "mul", "div", "pow"):
            rec = OrderedDict(op="bin", kind=k, ins=ins)
        elif k == "matmul":
            rec = OrderedDict(op="matmul", ins=ins)
        elif k == "reshape":
            rec = OrderedDict(op="reshape", ins=ins, shape=o["attrs"]["to"])
        elif k == "broadcast":
            rec = OrderedDict(op="broadcast", ins=ins, shape=o["attrs"]["to"])
        elif k == "cast":
            rec = OrderedDict(op="cast", ins=ins, dtype=o["attrs"]["to"])
        elif k == "transpose":
            rec = OrderedDict(op="transpose", ins=ins)
        else:
            raise SystemExit(f"v0 op {k!r} has no v1 constructor")
        out_ops.append(rec)

    und.note(
        "dtype",
        "v0 carries one `dtype` per op with no statement of whether it is the "
        "operand or the result dtype; for `cast` the two differ by definition. "
        "v1 drops the field: an op's operand dtypes come from its operand "
        "wires and its result dtype is derived, so the two cannot disagree.",
    )
    und.note(
        "output",
        "v0 declares neither the output wire nor its type; 'the last op' is a "
        "convention. v1 requires `out` and `out_ty`, and the checker refuses a "
        "trace whose declared output type does not match the wire.",
    )
    und.note(
        "memory-order",
        "v0's `reshape` gives a target shape and no memory order, so the two "
        "row-major/column-major readings of the same record compute different "
        "functions. v1 pins ROW-MAJOR, once, at `idxEquiv`.",
    )
    und.note(
        "matmul-rank",
        "v0 gives matmul a `contract` attribute but does not say what a rank>2 "
        "operand means (batched? which axes?). v1 admits rank-2 only and the "
        "checker REFUSES anything else, rather than picking a reading.",
    )
    und.note(
        "public-inputs",
        "v0 declares no public/witness split at all. v1's `role` is that "
        "split; the emit layout consumes it.",
    )
    und.note(
        "identity-cast",
        "4 of v0's 26 ops are identity f32->f32 casts and 2 pairs of constants "
        "carry identical digests. v1 keeps them (a canonicalization pass is a "
        "separate, checkable transform) but the vocabulary makes an identity "
        "cast visibly free: `TOp.arithmetic` is true exactly when the source "
        "and target dtypes agree.",
    )

    last = others[-1]
    v1 = OrderedDict(
        version=VERSION,
        inputs=inputs,
        ops=out_ops,
        out=level[last["out"][0]],
        out_ty=OrderedDict(dtype=last["dtype"], shape=last["out_shapes"][0]),
    )
    return v1, und


LEAN_KIND = {
    "add": "Bin2.add", "sub": "Bin2.sub", "mul": "Bin2.mul",
    "div": "Bin2.div", "pow": "Bin2.pow",
}


def lean_shape(s):
    return "[" + ", ".join(str(x) for x in s) + "]"


def lean_ty(d, s):
    return f"⟨{DTYPE[d]}, {lean_shape(s)}⟩"


def to_lean(v1, name):
    lines = [f"def {name} : RawTrace where"]
    lines.append(f'  version := "{v1["version"]}"')
    lines.append("  inputs := [")
    body = []
    for i in v1["inputs"]:
        body.append(
            f'    ⟨WireRole.{i["role"]}, {lean_ty(i["dtype"], i["shape"])}, "{i["path"]}"⟩'
        )
    lines.append(",\n".join(body))
    lines.append("  ]")
    lines.append("  ops := [")
    body = []
    for o in v1["ops"]:
        k = o["op"]
        if k == "un":
            body.append(f'    RawOp.un Un1.neg {o["ins"][0]}')
        elif k == "bin":
            body.append(
                f'    RawOp.bin {LEAN_KIND[o["kind"]]} {o["ins"][0]} {o["ins"][1]}'
            )
        elif k == "matmul":
            body.append(f'    RawOp.matmul {o["ins"][0]} {o["ins"][1]}')
        elif k == "reshape":
            body.append(f'    RawOp.reshape {o["ins"][0]} {lean_shape(o["shape"])}')
        elif k == "broadcast":
            body.append(f'    RawOp.broadcast {o["ins"][0]} {lean_shape(o["shape"])}')
        elif k == "cast":
            body.append(f'    RawOp.cast {o["ins"][0]} {DTYPE[o["dtype"]]}')
        elif k == "transpose":
            body.append(f'    RawOp.transpose {o["ins"][0]}')
        else:
            raise SystemExit(k)
    lines.append(",\n".join(body))
    lines.append("  ]")
    lines.append(f'  outWire := {v1["out"]}')
    lines.append(f'  outTy := {lean_ty(v1["out_ty"]["dtype"], v1["out_ty"]["shape"])}')
    return "\n".join(lines) + "\n"


def main():
    src = sys.argv[1]
    v0 = json.load(open(src))
    v1, und = convert(v0)

    args = sys.argv[2:]
    if "--json" in args:
        p = args[args.index("--json") + 1]
        with open(p, "w") as f:
            json.dump(v1, f, indent=1)
            f.write("\n")
    if "--lean" in args:
        p = args[args.index("--lean") + 1]
        with open(p, "w") as f:
            f.write(to_lean(v1, "mnistRaw"))

    n_in = len(v1["inputs"])
    print(f"v0 ops {len(v0['ops'])} -> v1 inputs {n_in} + ops {len(v1['ops'])}")
    roles = {}
    for i in v1["inputs"]:
        roles[i["role"]] = roles.get(i["role"], 0) + 1
    print("roles:", roles)
    macs = 0
    elems = 0
    print("\nUNDER-DETERMINED IN v0 (each had to be invented here):")
    for k, d in und:
        print(f"  [{k}] {d}")


if __name__ == "__main__":
    main()
