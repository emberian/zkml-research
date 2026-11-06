#!/usr/bin/env python3
"""Does the backward activation table virtualize off the forward one? (DARK-TRAINING.md section 1)

2026-11-05. The claim: sigma' is a function of sigma's OUTPUT, so one 2^16 table serves both directions
(the backward pass reads sigma'(x) = g(sigma(x)) and never needs x). This is true over the reals for
sigmoid, tanh and ReLU (monotone or piecewise), false for GELU and SiLU (non-monotone: two inputs share an
output with different slopes). But the proved statement is over a FINITE format, where even a monotone
function collides (saturation and rounding merge many inputs into one output code). The question that
decides the design is therefore a count: over all 2^16 bf16 inputs, for how many output codes y do the
inputs mapping to y disagree on the bf16-rounded derivative? Each such y is a place where "derive sigma'
from sigma" returns a different number than the spec (sigma' evaluated at the input).

Pure Python, no deps. Semantics: exact real function of the bf16 input, rounded once to bf16
(round-to-nearest-even), which is the "exact 2^16 table" semantics the project uses for forward tables.
NaN/inf inputs excluded. Prints counts, not timings.
"""
import math
import struct

def bf16_to_float(h):
    return struct.unpack("<f", struct.pack("<I", h << 16))[0]

def float_to_bf16(x):
    if math.isnan(x):
        return 0x7FC0
    try:
        u = struct.unpack("<I", struct.pack("<f", x))[0]
    except OverflowError:
        return 0x7F80 if x > 0 else 0xFF80
    lsb = (u >> 16) & 1
    u = (u + 0x7FFF + lsb) & 0xFFFFFFFF
    return u >> 16

def sig(x):
    if x >= 0:
        return 1 / (1 + math.exp(-x))
    e = math.exp(x)
    return e / (1 + e)

def gelu(x):
    return 0.5 * x * (1 + math.erf(x / math.sqrt(2)))

def dgelu(x):
    return 0.5 * (1 + math.erf(x / math.sqrt(2))) + x * math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi)

def silu(x):
    return x * sig(x)

def dsilu(x):
    s = sig(x)
    return s * (1 + x * (1 - s))

FUNCS = {
    "relu":    (lambda x: max(x, 0.0), lambda x: 1.0 if x > 0 else 0.0),
    "sigmoid": (sig, lambda x: sig(x) * (1 - sig(x))),
    "tanh":    (math.tanh, lambda x: 1 - math.tanh(x) ** 2),
    "gelu":    (gelu, dgelu),
    "silu":    (silu, dsilu),
}

def main():
    inputs = []
    for h in range(1 << 16):
        x = bf16_to_float(h)
        if math.isnan(x) or math.isinf(x):
            continue
        inputs.append(x)
    print(f"finite bf16 inputs: {len(inputs)}")
    print(f"{'act':8} {'out codes':>9} {'colliding codes':>15} {'codes w/ >1 deriv':>17} "
          f"{'inputs affected':>15} {'max |dderiv|':>12}  note")
    for name, (f, df) in FUNCS.items():
        groups = {}
        for x in inputs:
            y = float_to_bf16(f(x))
            d = float_to_bf16(df(x))
            groups.setdefault(y, []).append((x, d))
        colliding = [g for g in groups.values() if len(g) > 1]
        bad = [g for g in colliding if len({d for _, d in g}) > 1]
        affected = sum(len(g) for g in bad)
        maxgap = 0.0
        for g in bad:
            ds = [bf16_to_float(d) for _, d in g]
            maxgap = max(maxgap, max(ds) - min(ds))
        note = ""
        if name in ("gelu", "silu"):
            note = "non-monotone: two-valued over the reals too"
        if name == "relu":
            note = "y=0 code: x<=0 has d=0; x=-0.0/+0.0 tie"
        print(f"{name:8} {len(groups):9} {len(colliding):15} {len(bad):17} {affected:15} {maxgap:12.4g}  {note}")
    print("\nReading: 'codes w/ >1 deriv' > 0 means a backward table keyed on the forward OUTPUT cannot reproduce the")
    print("spec's derivative at those codes; the repair is to key the backward lookup on the INPUT code (the forward")
    print("table's address, already committed by the forward lookup), i.e. one table with a two-column row")
    print("(x -> sigma(x), sigma'(x)), which costs one extra column, not a second table.")

if __name__ == "__main__":
    main()
