#!/usr/bin/env python3
"""
construction-search/space.py -- enumerate the proof-system construction space
with a COUNTS model and print Pareto fronts under several objectives.

2026-11-05.  Companion to docs/PROOF-SYSTEM-SPACE.md.  stdlib only.

    python3 notes/construction-search/space.py            # all fronts
    python3 notes/construction-search/space.py --point U1 # one named point, itemized
    python3 notes/construction-search/space.py --calibrate
    python3 notes/construction-search/space.py --certs [N]     # automata counts (pinned)
    python3 notes/construction-search/space.py --certs --markdown > COUNTS.md

CURRENCY.  The primary outputs are COUNTS: committed cells, field multiplications
(base-field, scalar-equivalent), hash compressions/permutations, INT8 MACs.  A
SECONDARY column converts counts to "H100-int32-op equivalents" using spec-sheet
throughputs; it is a proxy, NOT a measurement, and --calibrate shows it is ~30x
optimistic in absolute terms against SASH's measured Stwo rate.  Compare points by
the count columns; read the proxy only as a ratio between points on the same
hardware row.

Every constant carries a tag:
  [M:<src>]  measured by us (file cited)        [X:<src>] measured elsewhere (cited)
  [D]        derived in this file from cited     [A]       assumption (sensitivity
             constants                                       printed by --sensitivity)

WORKLOAD.  One token position of an 8B dense transformer (Llama-3.1-8B shape:
d=4096, d_ff=14336, L=32, context C=4096), the SASH workload, so the semantic-AIR
row can be checked against a published measurement.
"""
import argparse
import itertools
import math

# ----------------------------------------------------------------------------
# 0. Constants
# ----------------------------------------------------------------------------
# Poseidon2-16 over BabyBear: 655 mults + 1309 adds per permutation, rate 8.
#   [M: breadstuffs/docs/deos/GPU-PROVER-PROTOTYPE.md:632 via paper/scripts/boundary_exchange_rate.py]
P2_MULS, P2_ADDS, P2_RATE = 655, 1309, 8
# Blake2s compression: 10 rounds x 8 G x (6 add + 4 xor + 4 rot) + schedule ~= 1200 int32 ops,
# absorbs 64 bytes.  [A] (counted from RFC 7693 G function, schedule rounded up)
BLAKE2S_OPS, BLAKE2S_BYTES = 1200, 64
# BLAKE3: 7 rounds -> ~860 int32 ops / 64 bytes.  SHA-256: ~64 x 30 = 1950 ops / 64 bytes. [A]
BLAKE3_OPS, SHA256_OPS = 860, 1950
# In-circuit cost of one hash (cells/constraints), for recursion pricing:
#   Poseidon2 in BabyBear AIR: 352 committed felts/perm deployed, 141 narrowed
#     [M: docs/COMPOSITIONS.md C3, notes/poseidon2-virtualization.md]
#   BLAKE3 in binary-field SIMD R1CS: 14,000 constraints/compression; SHA-256 30,376
#     [X: ePrint 2026/1656 BinarySpartan Sec 4]
#   Blake2s in M31 AIR (Stwo): ~ 3,000 cells/compression [A: order-of-magnitude; Stwo's
#     Blake AIR packs 32-bit words as two 16-bit limbs; unmeasured here]
INCIRCUIT_CELLS = {"poseidon2": 352, "poseidon2-narrow": 141, "blake3-bin": 14000,
                   "sha256-bin": 30376, "blake2s-m31": 3000, "lattice-ajtai": 0}

# int32-op cost of one field multiplication on SIMT / CPU-SIMD lanes [A]:
#   31-bit Montgomery mult: mul.lo, mul.hi, mul.lo, mul.hi, sub, select = 6
#   64-bit (Goldilocks/p61) mult on 32-bit lanes: 4 partial products + reduction ~ 14
#   GF(2^128): CPU with PMULL/PCLMUL ~ 10 ops-equiv; GPU (no carryless mul) ~ 150
#     (bit-sliced / table tower mult; DATE'26 binary-tower GPU sumcheck is the
#      counter-evidence to watch -- if it reports < 40 ops/mult this row moves)
MULT_OPS = {
    "BabyBear": {"cpu": 6, "simt": 6},
    "KoalaBear": {"cpu": 6, "simt": 6},
    "M31": {"cpu": 5, "simt": 5},          # Mersenne reduction is shift+add
    "Goldilocks": {"cpu": 8, "simt": 14},  # CPU has 64-bit mul
    "p61": {"cpu": 8, "simt": 14},
    "GF2^128": {"cpu": 10, "simt": 150},
    "lattice-Rq": {"cpu": 6, "simt": 6},   # per coefficient, NTT-domain, 31-bit q [A]
}
ADD_OPS = 2
# Tensor-core INT8 MAC in int32-op equivalents.  H100 SXM dense INT8 1979 TOPS
# (= 990e12 MAC/s); INT32 SIMT 132 SM x 64 lanes x 1.98 GHz = 16.7e12 op/s.
#   [X: NVIDIA H100 datasheet; derived ratio]  -> one MAC = 16.7/990 = 0.0169 op-equiv
TC_MAC_OPEQ = 16.7e12 / 990e12
# A 31-bit field mult as a runtime x runtime 4x4 byte-limb product = 16 MACs, plus
# reduction amortized over an inner product (deferred).  [X: TensorZKP ePrint
# 2026/1250 Sec 4: BabyBear, L=4 limbs of 8 bits, reduction on SIMT].  TensorZKP
# measured 13.1x (inner product) and 36.2x (end to end) over SIMT.  The model below
# gives 6/(16*0.0169) = 22x before reduction, which sits between their two numbers.
TC_LIMBS = {"BabyBear": 4, "KoalaBear": 4, "M31": 4, "Goldilocks": 8, "p61": 8}
# GF(2^128) on the same INT8 tensor cores (initiative 14, mma_counts.py): bits as 0/1 operands, the
# .s32 register read for its parity (exact at every length: minidregg lane/mma-exact
# Theory/MmaAccumulatorExact.lean s32_parity_exact), three Karatsuba levels down to 16-bit pieces with
# lazy reduction (kar_lazy_commutes): 27 x 16 x 16 = 6,912 bit-MACs per multiply, plus ~2 x 108 SIMT
# ops to unpack bits into byte operands [D: mma_counts.kar_macs / unpack_ops].  "L*L" equivalent:
TC_GF2_MACS = {"GF2^128": 27 * 16 * 16}
TC_GF2_UNPACK_OPS = {"GF2^128": 2 * 27 * 16 / 4}
# Spec throughputs (op-equiv/s) for the proxy column [X: datasheets; A for CPU]
HW_THROUGHPUT = {"cpu": 3.4e11,   # 12 cores x 4 lanes x 3.5 GHz x ~2 IPC [A]
                 "simt": 16.7e12, "tc": 16.7e12}  # tc rows already discount MACs

# Extension degree used for challenges, and the resulting field-size wall (bits)
# [D from field sizes; LogUp wall per docs/VERDICTS.md 1: Ext4 -> 100, Ext5 -> 136]
FIELDS = {
    #  name        base bits  ext  ext_bits  logup_wall  two_adic  char2
    "BabyBear":   (31, 4, 124, 100, 27, False),
    "KoalaBear":  (31, 4, 124, 100, 24, False),
    "M31":        (31, 4, 124, 100, 31, False),   # circle domain, 2^31 [X: Stwo]
    "Goldilocks": (64, 2, 128, 104, 32, False),
    "p61":        (61, 2, 122, 98, 54, False),
    "GF2^128":    (128, 1, 128, 120, 128, True),  # additive domains, any size
    "lattice-Rq": (31, 1, 124, 100, 27, False),   # Module-SIS; bits are an [A]
}

# ----------------------------------------------------------------------------
# 1. Statement shapes: committed cells / virtualized values / lookups per position
# ----------------------------------------------------------------------------
D_MODEL, D_FF, LAYERS, CTX, HEADS = 4096, 14336, 32, 4096, 32
MACS_PER_POS = LAYERS * (4 * D_MODEL * D_MODEL + 3 * D_MODEL * D_FF)  # ~ 7.8e9 [D]
SHAPES = {
    # VM: RV64 emulation. ~6 retired instructions per int8 MAC (load, load, mul, add,
    # addr, branch, no SIMD in RV64I) [A]; ~30 committed cells per cycle for a
    # Twist/Shout-style zkVM [A, cf. FRONTIER-QUEUE Part 1: general RAM ~502 cells vs
    # read-only 6].
    "vm": dict(commit=MACS_PER_POS * 6 * 30, virt=0, lookups=MACS_PER_POS * 6),
    # interior AIR: 4 committed cells per MAC (a, b, product, accumulator)
    #   [D: paper/scripts/boundary_exchange_rate.py section 2]
    "interior-air": dict(commit=4 * MACS_PER_POS, virt=0, lookups=0),
    # semantic AIR with Freivalds matmul: SASH measured 79.0M committed cells/position
    #   at C=4096 for Llama-3.1-8B, of which 21% interaction (lookup) columns
    #   [X: aisafety.sg research note, Sep 2026]
    #   NOTE: the 79.0M already INCLUDES the interaction columns, so lookup cells are not
    #   added again (lookup_cells_included); lookups still pay their field mults.
    #   (codex 2026-11-05 caught the double count: 79.0M -> 95.6M in the first draft.)
    "semantic-air": dict(commit=79.0e6, virt=32768 * 32, lookups=0.21 * 79.0e6 / 2,
                         lookup_cells_included=True),
    # boundary-only: commit layer-boundary activations + attention scores; virtualize
    # every linear map by sumcheck; nonlinearities by one-hot (Shout) lookups.
    #   activations/layer/pos ~ 4*d + 3*d_ff = 59,392 ; scores/layer/pos = HEADS*CTX/HEADS
    #   (GQA, 32 query heads, scores over C) = 131,072 ; lookups ~ scores + d_ff
    #   [D from the shape; INFERRED, not an emitted object]
    "boundary-only": dict(commit=LAYERS * (4 * D_MODEL + 3 * D_FF + HEADS * CTX),
                          # matmul sumcheck prover work per position ~ MACs / B_EFF: the weight
                          # MLE pass amortizes over the B_EFF positions sharing it (Thaler's
                          # 1/B + 1/n overhead).  Prefill shares weights over the whole context;
                          # B_EFF = 64 is deliberately conservative [A] (FlashProve batch 24 x
                          # 1024 positions would allow far more).
                          virt=MACS_PER_POS / 64,
                          lookups=LAYERS * (HEADS * CTX + D_FF)),
}
# Weight opening: one PCS opening over all weights per request batch (Freivalds /
# sumcheck terminal claim lands on the committed weight MLE).  8.0e9 params.
PARAMS = 8.0e9
WEIGHT_BITS = {"int8": 8, "mxfp4": 4.25, "felt": None}   # mxfp4: E2M1 + E8M0/32 [X: OCP MX v1.0]

# ----------------------------------------------------------------------------
# 2. PCS cost per committed cell, verifier cost, proof bytes
# ----------------------------------------------------------------------------
def queries_for(bits, rho, regime):
    """Queries to reach `bits` from the query term alone, per regime.
    UD:   per-query error (1+rho)/2           [Selvage ProximityGapUD; BCIKS20 UD]
    JB:   per-query error sqrt(rho) (+eta)     [Johnson; 2026/532 Thm 28/29]
    CAP:  per-query error rho  -- WITHDRAWN (ethereum/soundcalc Nov 2025), never reported
    """
    per = {"UD": (1 + rho) / 2, "JB": math.sqrt(rho) * 1.05, "CAP": rho}[regime]
    return math.ceil(bits / -math.log2(per))


PCS = {
    # name: (multilinear?, encode kind, code rate choices, hash leaf, field set, regime-proved-in-lean)
    "FRI": dict(ml=False, encode="ntt", rates=[1 / 2, 1 / 4, 1 / 64], hashes=["poseidon2", "blake2s"],
                fields={"BabyBear", "KoalaBear", "M31", "Goldilocks", "p61"}),
    "WHIR": dict(ml=True, encode="ntt", rates=[1 / 2, 1 / 4, 1 / 16], hashes=["poseidon2", "blake2s"],
                 fields={"BabyBear", "KoalaBear", "M31", "Goldilocks", "p61"}),
    "BaseFold-add": dict(ml=True, encode="add-ntt", rates=[1 / 2, 1 / 4], hashes=["blake3", "sha256"],
                         fields={"GF2^128"}),
    "Ligerito": dict(ml=True, encode="add-ntt", rates=[1 / 4], hashes=["blake3", "sha256"],
                     fields={"GF2^128"}),
    "Brakedown": dict(ml=True, encode="spielman", rates=[1 / 2], hashes=["poseidon2", "blake2s"],
                      fields={"BabyBear", "KoalaBear", "Goldilocks"}),
    "Ajtai": dict(ml=True, encode="ajtai", rates=[1.0], hashes=["lattice-ajtai"],
                  fields={"lattice-Rq"}),
}


def hash_ops(h):
    return {"poseidon2": P2_MULS * 6 + P2_ADDS * ADD_OPS, "blake2s": BLAKE2S_OPS,
            "blake3": BLAKE3_OPS, "sha256": SHA256_OPS, "lattice-ajtai": 0}[h]


def hash_rate_cells(h, base_bits):
    """cells absorbed per hash invocation"""
    if h == "poseidon2":
        return P2_RATE
    if h == "lattice-ajtai":
        return 1
    return max(1, (64 * 8) // base_bits)


def pcs_prover(pcs, field, rate, h, log_h=22, width=64):
    """(field mults, hash invocations, tc-eligible mults) per committed cell.
    hash: leaves of `width` cells; sponge over row + binary tree over 1/rate * cells.
          [D: boundary_exchange_rate.per_element generalised]
    encode: ntt (h/2) log h mults per column per 1/rate; additive NTT same count in
            char 2 (no twiddle mults in half the butterflies; counted as full) [A];
            spielman ~ 20 adds/cell, linear [X: Brakedown]; ajtai: kappa=16 ring mults
            per committed coefficient at pay-per-bit 8-bit witness [A, cf. Neo].
    """
    blow = 1 / rate
    base_bits = FIELDS[field][0]
    r = hash_rate_cells(h, base_bits)
    if pcs["encode"] == "ajtai":
        return 16 * 8 / 32, 0.0, 0.0   # pay-per-bit: 8-bit witness, 16 ring rows
    hashes = blow * (1 / r + 2 / width) if h != "lattice-ajtai" else 0
    if pcs["encode"] in ("ntt", "add-ntt"):
        enc_m = (blow + 1) * log_h / 2
    else:
        enc_m = 20 * blow / 3   # spielman adds expressed in mult-equiv (add = mult/3)
    # multilinear PCS opening: one linear fold pass over the committed vector
    fold_m = 2.0 if pcs["ml"] else 1.0
    tc_eligible = enc_m if pcs["encode"] == "ntt" else (enc_m if pcs["encode"] == "spielman" else 0)
    return enc_m + fold_m, hashes, tc_eligible


def pcs_verifier(n_cells, rate, h, q, field, width=64):
    """(hash invocations, proof bytes) for one opening of n_cells committed cells."""
    if h == "lattice-ajtai":
        return 0, 0
    base_bits = FIELDS[field][0]
    digest = 32
    depth = math.log2(max(2, n_cells / width / rate))
    rounds = max(1, math.ceil(math.log2(max(2, n_cells)) / 4))   # arity-16 folding
    leaf_h = math.ceil(width / hash_rate_cells(h, base_bits))
    vh = q * (leaf_h + depth + rounds * (depth / 2))
    vb = q * (width * base_bits / 8 + depth * digest + rounds * (depth / 2) * digest)
    return vh, vb


# ----------------------------------------------------------------------------
# 3. PIOP, lookup, recursion, amortization multipliers
# ----------------------------------------------------------------------------
PIOP = {
    # sumcheck mults per virtualized value per layer: (d-1)*k*10 [D: exchange-rate script]
    # AIR cannot virtualize a linear map by itself; on boundary shapes it pays a side
    # sumcheck/Freivalds at the same rate (SASH runs 5 such reductions beside its AIR) [A].
    # (The first draft set 0 here, which made 'boundary-only AIR' look 5x cheaper than it is.)
    "AIR": dict(virt_mult=40, quotient=8, ml_only=False),         # quotient eval per cell [A]
    "Spartan/CCS": dict(virt_mult=40, quotient=3, ml_only=True),
    "HyperPlonk": dict(virt_mult=40, quotient=4, ml_only=True),
    "GKR": dict(virt_mult=40, quotient=0, ml_only=True, gkr=True),
}
LOOKUP = {
    # committed cells per lookup, field mults per lookup [A unless noted]
    "LogUp": dict(cells=2, mults=8),          # multiplicity + inverse helper (21% of SASH cells)
    "Lasso": dict(cells=3, mults=12),
    "Shout-onehot": dict(cells=1, mults=6),   # one-hot address chunks; per 2026/1390 cost is
                                              # a function of the access pattern only [X]
}
RECURSION = {
    # wrap factor: extra prover cells per leaf-verifier hash (in-circuit hash cost);
    # verifier: final proof only.  "none": verifier checks the leaf proof directly.
    "none": dict(wrap=False),
    "full-recursion": dict(wrap=True, overhead=1.0),
    "atomic-acc": dict(wrap=True, overhead=0.35),     # [A] defer PCS openings: WARP/Arc-style
    # 2026/538 over a HASH PCS (every PCS this file pairs it with): its Def 4 "accumulatable evaluation
    # proofs" fail for Merkle commitments and its own fallback (sec 1.1) verifies each child's FRI/WHIR proof
    # in-circuit; only the fixed-matrix (holographic) claims accumulate, and on today's Tower256 leaf (a bare
    # low-degree test) that share is 0 [D: notes/holography-accumulation-verdict.md, initiative 14].  So = full
    # recursion until a relation is arithmetized.  (Was 0.25 [A].)
    "holography-acc": dict(wrap=True, overhead=1.0),
    "folding": dict(wrap=True, overhead=0.0, step_rows=27.5e6),  # Nightstream recursive step,
                                                     # 27,537,894 R1CS rows [M: notes/nightstream-read.md]
}
AMORT = {"per-request": 1.0, "audit-1%": 0.01, "audit-0.1%": 0.001}

HARDWARE = ["cpu", "simt", "tc"]
# Witness / trace generation, per committed cell, in int32-op equivalents.  CALIBRATED, not
# derived: SASH reports the proof system at ~5% of GPU time, lookup-column generation 42%,
# base trace 35%, setup 12% [X].  At the SASH anchor the crypto proxy is ~3.1e7 ops per 1e6
# cells... we set WITGEN_OPS so that witgen / (witgen + crypto) = 0.95 at the anchor, and
# apply the same per-cell constant everywhere.  Tensor cores do NOT accelerate it.
WITGEN_OPS_PER_CELL = None   # filled by _calibrate_witgen() at import

# formal coverage of components, 0..3 (0 none, 1 statements w/ sorry or abstract,
# 2 proved for the component, 3 proved and composed end to end).  Source tags:
#   S = Selvage (minidregg/Selvage), A = ArkLib, F = FlashProve lean/
FORMAL = {
    "FRI": 2, "WHIR": 1, "BaseFold-add": 2, "Ligerito": 0, "Brakedown": 0, "Ajtai": 0,
    "AIR": 2, "Spartan/CCS": 1, "HyperPlonk": 0, "GKR": 0,
    "LogUp": 2, "Lasso": 0, "Shout-onehot": 0,
    "none": 3, "full-recursion": 1, "atomic-acc": 1, "holography-acc": 0, "folding": 1,
}


def compatible(field, pcs_name, piop, lookup, rec, hw, h):
    p = PCS[pcs_name]
    if field not in p["fields"] or h not in p["hashes"]:
        return False
    if PIOP[piop]["ml_only"] and not p["ml"]:
        return False
    if piop == "AIR" and p["ml"] and pcs_name not in ("WHIR",):
        return False
    if hw == "tc" and field not in TC_LIMBS and field not in TC_GF2_MACS:
        return False
    if rec == "folding" and pcs_name != "Ajtai":
        return False
    if pcs_name == "Ajtai" and rec != "folding":
        return False
    if field == "GF2^128" and lookup == "LogUp":
        return False   # LogUp needs field inverses of (X - a); in char 2 use Shout/Lasso
    return True


def evaluate(field, pcs_name, rate, h, piop, lookup, rec, hw, shape, amort,
             target_bits=100, regime="UD", weights="felt", pow_bits=0, q_fixed=None):
    base_bits, ext, ext_bits, logup_wall, two_adic, char2 = FIELDS[field]
    S = SHAPES[shape]
    commit = S["commit"] + (0 if S.get("lookup_cells_included") else
                            S["lookups"] * LOOKUP[lookup]["cells"])
    # soundness: query bits needed after grinding; field walls cap it
    q = queries_for(max(1, target_bits - pow_bits), rate, regime) if pcs_name != "Ajtai" else 0
    if q_fixed is not None:
        q = q_fixed
    m_cell, h_cell, tc_cell = pcs_prover(PCS[pcs_name], field, rate, h)
    quot = PIOP[piop]["quotient"]
    mults = commit * (m_cell + quot) + S["virt"] * PIOP[piop]["virt_mult"] \
        + S["lookups"] * LOOKUP[lookup]["mults"]
    if PIOP[piop].get("gkr"):
        # GKR commits only inputs + lookup data; activations become virtual
        # every former committed value becomes a virtual gate (~40 mults per layer), AND the
        # linear maps still pay their sumcheck (codex 2026-11-05: the first draft dropped
        # this term and flattered GKR by 8.7x)
        mults = (S["lookups"] * LOOKUP[lookup]["cells"]) * (m_cell) \
            + S["commit"] * 40 + S["virt"] * PIOP[piop]["virt_mult"] \
            + S["lookups"] * LOOKUP[lookup]["mults"]
        commit = S["lookups"] * LOOKUP[lookup]["cells"] + D_MODEL
    hashes = commit * h_cell
    # weight opening per request (batch 24, FlashProve's prefill batch [X])
    wb = WEIGHT_BITS[weights] or base_bits
    weight_elems = PARAMS * min(wb, base_bits) / base_bits if field != "GF2^128" \
        else PARAMS * wb / 128   # ring-switching packs sub-field values for free [X: DP24]
    if field != "GF2^128" and weights != "felt":
        weight_elems = PARAMS * wb / base_bits   # packed into felts, unpack costs lookups [A]
    mults += weight_elems * 2 / 24
    # recursion
    vh, vb = pcs_verifier(commit, rate, h, q, field)
    rinfo = RECURSION[rec]
    if rinfo["wrap"]:
        if rec == "folding":
            mults += rinfo["step_rows"] * 3
            vh_final, vb_final = 2e4, 6e5   # one decider (Spartan2) at session end [A]
        else:
            inc = INCIRCUIT_CELLS.get(h if h != "blake2s" else "blake2s-m31",
                                      INCIRCUIT_CELLS.get(h + "-bin", 3000))
            wrap_cells = vh * inc * rinfo["overhead"]
            mults += wrap_cells * (m_cell + quot)
            hashes += wrap_cells * h_cell
            vh_final, vb_final = 4.0e4, 1.5e5   # [A] constant-size final proof
        vh, vb = vh_final, vb_final
    # amortization: audited requests pay the commitment (hash only) always, proof w.p. p
    p = AMORT[amort]
    if p < 1:
        always = S["commit"] * hash_rate_cells(h, base_bits) ** -1   # hash-only boundary commit
        mults, hashes = mults * p, hashes * p + always
        vh, vb = vh * p + 1, vb * p + 32
    # soundness bits, regime-honest; audit points report the per-request detection
    q_bits = (q * -math.log2({"UD": (1 + rate) / 2, "JB": math.sqrt(rate) * 1.05,
                              "CAP": rate}[regime]) + pow_bits) if q else 120
    lookup_wall = logup_wall if lookup == "LogUp" else ext_bits - 4
    bits = min(q_bits, ext_bits - 4, lookup_wall)
    det_bits = bits if p == 1 else -math.log2(1 - p)
    # hardware proxy (int32-op equivalents)
    mops = MULT_OPS[field]["cpu" if hw == "cpu" else "simt"]
    if hw == "tc":
        # Eligible work and total work must use the same audit amortization.
        tc_share = min(1.0, p * (tc_cell * commit + S["virt"] * PIOP[piop]["virt_mult"]) / max(mults, 1))
        if field in TC_GF2_MACS:
            per = TC_GF2_MACS[field] * TC_MAC_OPEQ + TC_GF2_UNPACK_OPS[field]
        else:
            per = TC_LIMBS[field] ** 2 * TC_MAC_OPEQ + 0.25
        mult_cost = mults * (tc_share * per + (1 - tc_share) * mops)
    else:
        mult_cost = mults * mops
    hash_cost = hashes * hash_ops(h)
    crypto_s = (mult_cost + hash_cost) / HW_THROUGHPUT[hw]
    wg_rate = HW_THROUGHPUT["simt" if hw == "tc" else hw]
    witgen_s = (S["commit"] * (WITGEN_OPS_PER_CELL or 0) * p) / wg_rate
    proxy_s = crypto_s + witgen_s
    pq = None  # Unknown: requires a scheme, parameter set, and adversary model; field choice cannot certify PQ.
    formal = min(FORMAL[pcs_name], FORMAL[piop], FORMAL[lookup], FORMAL[rec])
    return dict(field=field, pcs=pcs_name, rate=rate, hash=h, piop=piop, lookup=lookup, rec=rec,
                hw=hw, shape=shape, amort=amort, regime=regime, weights=weights, q=q,
                commit=commit, mults=mults, hashes=hashes, v_hashes=vh, proof_bytes=vb,
                bits=bits, det_bits=det_bits, pq=pq, formal=formal, proxy_s=proxy_s,
                crypto_s=crypto_s, witgen_s=witgen_s)


def _calibrate_witgen():
    """Set WITGEN_OPS_PER_CELL so witgen is 95% of the SASH anchor's proxy [X: SASH]."""
    global WITGEN_OPS_PER_CELL
    WITGEN_OPS_PER_CELL = 0
    a = evaluate(**NAMED["SASH-anchor"])
    crypto_ops = a["crypto_s"] * HW_THROUGHPUT["simt"]
    WITGEN_OPS_PER_CELL = 19 * crypto_ops / SHAPES["semantic-air"]["commit"]


def enumerate_space(shapes=None, amorts=None, regimes=("UD",)):
    shapes = shapes or list(SHAPES)
    amorts = amorts or list(AMORT)
    out = []
    for field, pcs_name, piop, lookup, rec, hw in itertools.product(
            FIELDS, PCS, PIOP, LOOKUP, RECURSION, HARDWARE):
        for h in PCS[pcs_name]["hashes"]:
            if not compatible(field, pcs_name, piop, lookup, rec, hw, h):
                continue
            for rate in PCS[pcs_name]["rates"]:
                for shape in shapes:
                    for amort in amorts:
                        for regime in regimes:
                            out.append(evaluate(field, pcs_name, rate, h, piop, lookup, rec,
                                                hw, shape, amort, regime=regime))
    return out


def pareto(points, keys):
    """keys: list of (name, sense) with sense +1 maximize, -1 minimize"""
    front = []
    for a in points:
        dominated = False
        for b in points:
            if b is a:
                continue
            ge = all((b[k] * s) >= (a[k] * s) for k, s in keys)
            gt = any((b[k] * s) > (a[k] * s) for k, s in keys)
            if ge and gt:
                dominated = True
                break
        if not dominated:
            front.append(a)
    return front


def fmt(p):
    return (f"{p['field']:<10} {p['pcs']:<12} r={p['rate']:<7.4g} {p['hash']:<9} {p['piop']:<11} "
            f"{p['lookup']:<12} {p['rec']:<14} {p['hw']:<4} {p['shape']:<13} {p['amort']:<11} "
            f"| commit {p['commit']:.2e} mult {p['mults']:.2e} hash {p['hashes']:.2e} "
            f"| vH {p['v_hashes']:.1e} B {p['proof_bytes']:.1e} | bits {p['bits']:.0f} "
            f"det {p['det_bits']:.3g} formal {p['formal']} | proxy {p['proxy_s']:.2e}s "
            f"(crypto {p['crypto_s']:.1e})")


NAMED = {
    # the five unoccupied points of docs/PROOF-SYSTEM-SPACE.md section 4, plus anchors
    "U1": dict(field="BabyBear", pcs_name="WHIR", rate=1 / 4, h="blake2s", piop="Spartan/CCS",
               lookup="Shout-onehot", rec="none", hw="tc", shape="boundary-only",
               amort="audit-1%", weights="mxfp4"),
    "U1-poseidon2": dict(field="BabyBear", pcs_name="WHIR", rate=1 / 4, h="poseidon2",
                         piop="Spartan/CCS", lookup="Shout-onehot", rec="none", hw="tc",
                         shape="boundary-only", amort="audit-1%", weights="mxfp4"),
    "U1-felt-weights": dict(field="BabyBear", pcs_name="WHIR", rate=1 / 4, h="blake2s",
                            piop="Spartan/CCS", lookup="Shout-onehot", rec="none", hw="tc",
                            shape="boundary-only", amort="per-request", weights="felt"),
    "U1-per-request": dict(field="BabyBear", pcs_name="WHIR", rate=1 / 4, h="blake2s",
                           piop="Spartan/CCS", lookup="Shout-onehot", rec="none", hw="tc",
                           shape="boundary-only", amort="per-request", weights="mxfp4"),
    "U1-simt": dict(field="BabyBear", pcs_name="WHIR", rate=1 / 4, h="blake2s", piop="Spartan/CCS",
                    lookup="Shout-onehot", rec="none", hw="simt", shape="boundary-only",
                    amort="per-request", weights="mxfp4"),
    "U5-gkr-tc": dict(field="BabyBear", pcs_name="WHIR", rate=1 / 4, h="blake2s", piop="GKR",
                      lookup="Shout-onehot", rec="none", hw="tc", shape="boundary-only",
                      amort="per-request", weights="mxfp4"),
    "U4-fold": dict(field="lattice-Rq", pcs_name="Ajtai", rate=1.0, h="lattice-ajtai",
                    piop="Spartan/CCS", lookup="Shout-onehot", rec="folding", hw="simt",
                    shape="boundary-only", amort="per-request", weights="int8"),
    "SASH-anchor": dict(field="M31", pcs_name="FRI", rate=1 / 2, h="blake2s", piop="AIR",
                        lookup="LogUp", rec="none", hw="simt", shape="semantic-air",
                        amort="per-request", weights="int8"),
    "ours-deployed-shape": dict(field="BabyBear", pcs_name="FRI", rate=1 / 64, h="poseidon2",
                                piop="AIR", lookup="LogUp", rec="full-recursion", hw="cpu",
                                shape="interior-air", amort="per-request", weights="felt",
                                q_fixed=19, pow_bits=16),
    "ours-deployed-UD100": dict(field="BabyBear", pcs_name="FRI", rate=1 / 64, h="poseidon2",
                                piop="AIR", lookup="LogUp", rec="full-recursion", hw="cpu",
                                shape="interior-air", amort="per-request", weights="felt",
                                pow_bits=16),
    "SASH-shape-on-tc": dict(field="BabyBear", pcs_name="FRI", rate=1 / 2, h="blake2s", piop="AIR",
                             lookup="LogUp", rec="none", hw="tc", shape="semantic-air",
                             amort="per-request", weights="int8"),
    "binary-boundary": dict(field="GF2^128", pcs_name="Ligerito", rate=1 / 4, h="blake3",
                            piop="Spartan/CCS", lookup="Shout-onehot", rec="none", hw="cpu",
                            shape="boundary-only", amort="per-request", weights="mxfp4"),
}


def calibrate():
    p = evaluate(**NAMED["SASH-anchor"])
    cells = p["commit"]
    print("CALIBRATION against SASH (Stwo, M31, Blake2s, blowup 2, Llama-3.1-8B, 1 H100)")
    print(f"  model committed cells/position      : {cells:.3e}  (SASH measured 79.0e6, incl. lookup cols)")
    print(f"  model CRYPTO proxy s/position (SIMT): {p['crypto_s']:.3e}")
    print(f"  SASH measured proof-system rate     : 1.3e9 cells/s -> {cells/1.3e9:.3e} s/position")
    print(f"  => the crypto proxy is {cells/1.3e9/p['crypto_s']:.0f}x optimistic against the measured proof system")
    print(f"     (memory traffic, not arithmetic, is the gap; the proxy is spec-sheet ALU only).")
    print(f"  witness generation is CALIBRATED to 95% of the anchor (SASH: proof system ~5% of GPU time):")
    print(f"     WITGEN_OPS_PER_CELL = {WITGEN_OPS_PER_CELL:.0f} int32-op-equiv per committed cell, applied to every point.")
    print(f"  model total proxy s/position        : {p['proxy_s']:.3e}; SASH full loop at 99e6 cells/s: {cells/99e6:.3e}")
    print("  => because witgen is calibrated against the proxy, totals inherit the crypto proxy's ~30x optimism;")
    print("     ratios between points remain the only meaningful reading.  Tensor cores accelerate only crypto_s.")


def sensitivity():
    print("SENSITIVITY of U1 (audited, tensor-core) to the [A] constants")
    base = evaluate(**NAMED["U1"])["proxy_s"]
    global TC_MAC_OPEQ
    for f in (0.5, 2.0, 4.0):
        old = TC_MAC_OPEQ
        TC_MAC_OPEQ = old * f
        v = evaluate(**NAMED["U1"])["proxy_s"]
        TC_MAC_OPEQ = old
        print(f"  TC MAC cost x{f:<4}: proxy {v/base:.2f}x of base")
    for f in (0.5, 2.0):
        old = SHAPES["boundary-only"]["commit"]
        SHAPES["boundary-only"]["commit"] = old * f
        v = evaluate(**NAMED["U1"])["proxy_s"]
        SHAPES["boundary-only"]["commit"] = old
        print(f"  boundary commit x{f:<4}: proxy {v/base:.2f}x of base")


# ---------------------------------------------------------------------------
# Certificate families (breadstuffs docs/automata, 2026-11-05): committed cells per
# SYMBOL for the run, plus the content commitment once per record. Every number is
# tagged in the hub (AUTOMATA-ARITHMETIZATION-PROGRAM.md §2) and the family notes:
# [M] = a pinned #guard in metatheory, [I] = derived there.
#   commitment: hash_bytes_8 = ceil(n/8) + 2 Poseidon2 permutations for n bytes
#   (rate-4 absorb, 2 bytes per lane, 4 length lanes, one squeeze) [READ poseidon2.rs:704]
# "lookups" are per symbol; "chip" rows are Poseidon2 permutations per symbol.
CERT_FAMILIES = {
    # family:            (main cells/symbol, lookups/symbol, chip perms/symbol, binds word?)
    "dfa-table-routing":  (3,  1, 0,    False),
    "dfa-table-route8":   (20, 2, 1,    True),    # [M] RouteChain8 + exact-public table   # [M] DfaRoutingTableEmit: 3 cols, 1 table lookup
    "dfa-hash-chained":   (22, 2, 2,    True),    # [M] DfaRoutingGeneralEmit: 22 cols, 2 chip lookups
    "dfa-attested-weld8": (11, 1, 16,   False),
    "dfa-weld8-route8":   (28, 2, 17,   True),    # [M] full8 root-seeded route; binary symbols   # [M] Weld8: 11 cols, 1 map-op, 16 chip rows (binary symbols)
    "bracket-replay":     (24, 2, 4,    False),   # [M] DyckStackEmit: 24 cols, ~2 rows/token, 2 chip/row
    "nfa-subset":         (9,  6, 0,    False),   # [I] 03-nfa: 9 cols vs a 64-row determinized table
    "detokenizer":        (4,  1, 0,    True),    # [I] 06-transducers: 1 row + 1 vocab lookup/token
    "weighted":           (4,  1, 0,    False),   # [I] 08-weighted: dfa + 1 accumulator column
    "timed-window":       (5,  2, 0,    False),   # [I] 09-timed: dfa + clock; 2 range lookups/guard at 4 bits
}

def commitment_perms(n_bytes):
    """Poseidon2 permutations to commit n bytes with hash_bytes_8 (ceil(n/8) + 2)."""
    return (n_bytes + 7) // 8 + 2

def cert_cost(family, n_symbols, n_bytes=None, h="poseidon2"):
    """Committed cells for one certificate: the run plus (once) the content commitment.
    Returns (run_cells, commitment_cells, total). n_bytes defaults to n_symbols."""
    cells, _lk, chip, _bound = CERT_FAMILIES[family]
    if n_bytes is None:
        n_bytes = n_symbols
    perm = INCIRCUIT_CELLS[h]
    run = n_symbols * (cells + chip * perm)
    commit = commitment_perms(n_bytes) * perm
    return run, commit, run + commit

# ---------------------------------------------------------------------------
# Automata COUNTS, pinned (breadstuffs docs/automata/COUNTS.md is generated from here:
#     python3 notes/construction-search/space.py --certs --markdown > .../docs/automata/COUNTS.md
# ). 2026-11-06, lane C of the automata program.
#
# Separation the table keeps (codex round 3, finding 16): SEMANTIC operation counts (rows, lookups,
# degree per symbol: what the certificate checker does) are one block; the REALIZATION on a target
# (columns, constraints, tables, chip permutations, declared table rows, descriptor bytes) is
# another, and only BabyBear has one today. Tower256 has no AIR layer (LEAF-PROVER-DECISION §6 "not
# yet available"), so its realization column is empty and only its commitment term is modelled.
#
# Every realization number carries PIN = (path under breadstuffs/metatheory, line, substring that
# must occur on that line). `--check-pins` (and --markdown) re-reads each cited line and refuses to
# print if any pin has moved, so a cited file:line cannot rot silently.
BREADSTUFFS_MT_DEFAULT = "~/dev/breadstuffs/metatheory"
E = "Dregg2/Circuit/Emit/"

AUTOMATA_PINS = {
    "route-shape": (E + "RouteChain8.lean", 62, "constraints.length = d.constraints.length + 28"),
    "trb-width": (E + "DfaRoutingTableRoute8.lean", 22, ".traceWidth = 20"),
    "trb-pi": (E + "DfaRoutingTableRoute8.lean", 23, ".piCount = 11"),
    "trb-cons": (E + "DfaRoutingTableRoute8.lean", 24, ".constraints.length = 32"),
    "wbr-width": (E + "AttestedAutomatonRoute8.lean", 30, "weldBoundInstance.traceWidth = 28"),
    "wbr-cons": (E + "AttestedAutomatonRoute8.lean", 31, "weldBoundInstance.constraints.length = 50"),
    "trt-shape":   (E + "DfaRoutingTableEmit.lean", 540, "demoRoutingDesc.traceWidth == TRT_WIDTH"),
    "trt-width":   (E + "DfaRoutingTableEmit.lean", 109, "def TRT_WIDTH : Nat := 3"),
    "trt-cons":    (E + "DfaRoutingTableEmit.lean", 542, "constraints.length == 4"),
    "trt-golden":  (E + "DfaRoutingTableEmit.lean", 536, "#guard emitVmJson2 demoRoutingDesc =="),
    "lanes-cost":  (E + "TinyAutomataLanesK.lean", 784, "costOf (lanesRunIK k probeW)"),
    "lanes-area":  (E + "TinyAutomataLanesK.lean", 796, "(costOf (prodRunDesc k probeW)).area"),
    "gen-width":   (E + "DfaRoutingGeneralEmit.lean", 90, "def DFA_WIDTH : Nat := 22"),
    "tog-width":   (E + "DfaRoutingEmit.lean", 105, "def DFA_WIDTH : Nat := 8"),
    "tog-shape":   (E + "DfaRoutingEmit.lean", 277, "constraints.length == 14"),
    "tog-narrow":  (E + "DyckStackEmit.lean", 655, "poseidon2narrow.wireId == 8"),
    "gen-shape":   (E + "DfaRoutingGeneralEmit.lean", 274, "constraints.length == 14"),
    "gen-chip":    (E + "DfaRoutingGeneralEmit.lean", 275, "chipLookupTuple"),
    "w8-cost":     (E + "AttestedAutomatonWeld8.lean", 943, "#guard costOf weldInstance =="),
    "w8-carriers": (E + "AttestedAutomatonWeld8.lean", 946, "hashSites.isEmpty && weldInstance.ranges.isEmpty"),
    "w8-bytes":    (E + "AttestedAutomatonWeld8.lean", 957, "(2803, 1205)"),
    "w8-cross":    (E + "AttestedAutomatonWeld8.lean", 963, "jsonBytes (prodRunDesc 4 (wordN n))"),
    "w8-aux":      (E + "AttestedAutomatonWeld8.lean", 980, "MAP_TREE_DEPTH * n"),
    "asym":        (E + "AttestedAutomatonEmit.lean", 164, "def ASYM : Nat := 2"),
    "dyck-shape":  (E + "DyckStackEmit.lean", 645, "theorem constraint_count : dyckParseDesc.constraints.length = 85"),
    "dyck-width":  (E + "DyckStackEmit.lean", 653, "DYCK_WIDTH + 2 * (CHIP_OUT_LANES - 1) == 38"),
    "dyck-chip":   (E + "DyckStackEmit.lean", 647, "#guard (chipLookupTupleNarrow [.var RULE_ID"),
    "dyck-rows":   (E + "DyckStackReplay.lean", 963, "(decodeRun [op, cl] witTrace 5).length = 5"),
    "deriv-width": (E + "DerivationEmit.lean", 393, "DERIV_TRACE_WIDTH == 386"),
    "deriv-cons":  (E + "DerivationEmit.lean", 397, "derivationConstraints.length == 393"),
    "deriv-pi":    (E + "DerivationEmit.lean", 398, "derivationDesc.piCount == 13"),
    "dl-dom":      ("Dregg2/Datalog/FixpointCert.lean", 651, "(activeDomain tc edb).length == 6"),
    "dl-substs":   ("Dregg2/Datalog/FixpointCert.lean", 652, "(varBound rStep)).length == 216"),
    "dl-domdef":   ("Dregg2/Datalog/FixpointCert.lean", 139, "edb.flatMap (·.2) ++ P.flatMap ruleConsts"),
    "p2-wide":     (E + "Poseidon2RoundGates.lean", 121, "POSEIDON2_AUX_COLS == 352"),
}

# Per-family record. Semantic block: rows/symbol, lookups/symbol (abstract), degree.
# BabyBear block: main columns, constraints, tables, chip permutations per symbol and their width,
# declared table rows (as a function of n and of the policy), descriptor bytes, and the pins.
# `rows(n)` is the trace height for an n-symbol word before power-of-two padding.
AUTOMATA_FAMILIES = [
    dict(name="dfa-table-routing", served="dregg-dfa-routing-table::exact-public-v1",
         sym="byte", rows=lambda n: n, lookups=1, degree="1 [READ golden :536]",
         cols=3, cons=4, tables=1, chip=0, chip_w=0,
         declared=lambda n: n, declared_note="n (exact-public rows: the run itself is public)",
         bytes_note="~10 B/symbol (run shipped; w8-cross)",
         pins=["trt-width", "trt-shape", "trt-cons", "trt-golden", "lanes-cost"],
         binds_c="no (word read off the SYMBOL column)"),
    dict(name="dfa-table-route8", served="dregg-dfa-routing-table::route8-bound-v1",
         sym="byte", rows=lambda n: n, lookups="1 table + 1 chip", degree="1 main; chip S-box separate",
         cols=20, cons=32, tables=2, chip=1, chip_w=352,
         declared=lambda n: n, declared_note="n (same exact-public edge multiset; route pins order)",
         bytes_note="table-dependent; generated bound artifact",
         pins=["route-shape", "trb-width", "trb-pi", "trb-cons", "p2-wide"],
         binds_c="full8 ordered route + checked exact height; named canonical arity16 collision"),
    dict(name="dfa-product-lanes-k", served=None,
         sym="binary (pinned at NSYM = 2)", rows=lambda n: 8 * n, lookups="k", degree="1 [READ]",
         cols="2k+1", cons="4k", tables="k", chip=0, chip_w=0,
         declared=lambda n: 8 * n, declared_note="k·n_symbols (one exact-public table per lane)",
         bytes_note="672/1168/1664/2160 at k=1..4, word length 8",
         pins=["lanes-cost", "lanes-area"], binds_c="no"),
    dict(name="dfa-hash-chained-toggle", served="dfa-routing-toggle-2state::poseidon2-v1",
         sym="bit (2-state toggle)", rows=lambda n: 8 * n, lookups=2, degree="7 (chip S-box) [READ note 01 §3; unpinned]",
         cols=8, cons=14, tables=0, chip=2, chip_w=141,
         declared=lambda n: 0, declared_note="0 (transition is an interpolant gate)",
         bytes_note="byte-pinned golden (table 8 = narrow chip)",
         pins=["tog-width", "tog-shape", "tog-narrow"],
         binds_c="route commitment + explicit record length; named-chain collision theorem, scalar hash residual"),
    dict(name="dfa-hash-chained-injection", served="dfa-routing-injection-3state::poseidon2-v1",
         sym="byte", rows=lambda n: n, lookups=2, degree="7 (chip S-box) [READ note 01 §3; unpinned]",
         cols=22, cons=14, tables=0, chip=2, chip_w=352,
         declared=lambda n: 0, declared_note="0 (transition is an interpolant gate)",
         bytes_note="byte-pinned golden",
         pins=["gen-width", "gen-shape", "gen-chip", "p2-wide"],
         binds_c="route commitment + explicit record length; named-chain collision theorem, scalar hash residual"),
    dict(name="dfa-attested-weld8", served="dregg-attested-automaton::map-committed-weld8-v1",
         sym="binary (ASYM = 2: 8 rows per byte)", rows=lambda n: 8 * n, lookups="1 map-op + 2 range",
         degree="1 [READ: 0 nonlinear mults, w8-cost]",
         cols=11, cons=22, tables=3, chip=16, chip_w=352,
         declared=lambda n: 0, declared_note="0 (automaton is a 2^16-leaf map root, not rows)",
         bytes_note="2803, constant in word length and table size",
         pins=["w8-cost", "w8-carriers", "w8-bytes", "w8-aux", "asym", "p2-wide"],
         binds_c="automaton: yes (8-felt root); word: no"),
    dict(name="dfa-weld8-route8", served="dregg-attested-automaton::map-committed-weld8-bound-v1",
         sym="binary (8 rows per byte)", rows=lambda n: 8 * n,
         lookups="1 map-op + 2 range + 1 chip", degree="1 main; chip S-box separate",
         cols=28, cons=50, tables=4, chip=17, chip_w=352,
         declared=lambda n: 0, declared_note="0 (same 2^16-leaf map root)",
         bytes_note="6036, constant in word length and table size",
         pins=["wbr-width", "wbr-cons", "route-shape", "w8-aux", "asym", "p2-wide"],
         binds_c="full8 root-seeded route + checked exact height; row-specific map or route collision"),
    dict(name="dyck-bracket-replay", served="dregg-dyck-parse-v1",
         sym="bracket token", rows=None, lookups="2 chip per row", degree="8 [READ note 04; unpinned]",
         cols=24, cons=85, tables=0, chip=2, chip_w=141,
         declared=lambda n: 0, declared_note="0",
         bytes_note="-",
         pins=["dyck-width", "dyck-shape", "dyck-chip", "dyck-rows"],
         binds_c="canonical record wrapper pins route + padded row count; named scalar-chain collision"),
]

DYCK_MAX_TOKENS = 6   # depth cap k <= 3 => the deployed grammar's language is finite: [^k]^k, k <= 3


def check_automata_pins(mt=None):
    """Re-read every cited line; return a list of (key, problem). Empty = all pins hold."""
    import os
    mt = os.path.expanduser(mt or os.environ.get("BREADSTUFFS_MT", BREADSTUFFS_MT_DEFAULT))
    bad = []
    for key, (path, line, needle) in AUTOMATA_PINS.items():
        p = os.path.join(mt, path)
        try:
            lines = open(p, encoding="utf-8").read().splitlines()
        except OSError as e:
            bad.append((key, f"{path}: {e.strerror}"))
            continue
        if line > len(lines) or needle not in lines[line - 1]:
            got = lines[line - 1].strip() if line <= len(lines) else "<past EOF>"
            bad.append((key, f"{path}:{line} expected {needle!r}, found {got!r}"))
    return bad


def pin_ref(key):
    path, line, _ = AUTOMATA_PINS[key]
    return f"metatheory/{path}:{line}"


# ---- commitment term ---------------------------------------------------------------------------
KECCAK_RATE = 136          # cSHAKE256 rate in bytes (1088 bits)
MERKLE_LEAF_BYTES = 32     # [INFERRED] LEAF-PROVER-DECISION §7: leaf input 66 B unary / 37 B u32 = a 32-B payload


def keccak_sponge(n_absorbed, prefix_precomputed=True):
    """Keccak-f calls for SHAKE/cSHAKE256 over n_absorbed bytes with a 32-byte output:
    floor(n/136) + 1 including pad10*1 (FIPS 202 Alg. 8; the first 32 output bytes need no extra
    squeeze), +1 for the cSHAKE bytepad(N,S) prefix block unless its state is precomputed
    (SP 800-185 §3.3). Codex round 3, finding 15."""
    return n_absorbed // KECCAK_RATE + 1 + (0 if prefix_precomputed else 1)


def frame_len(n, codec):
    """Bytes absorbed for one framed payload of n bytes: `0 :: envelope b` (hashLeaf)."""
    return 1 + (n + 1 if codec == "unary" else 4) + n


def tower_merkle(n, codec="unary", prefix_precomputed=True):
    """cSHAKE Merkle over 32-byte leaves: leaves + internal nodes, one sponge each."""
    leaves = max(1, -(-n // MERKLE_LEAF_BYTES))
    node_in = 1 + 2 * ((32 + 1 if codec == "unary" else 4) + 32)
    return (leaves * keccak_sponge(frame_len(MERKLE_LEAF_BYTES, codec), prefix_precomputed)
            + (leaves - 1) * keccak_sponge(node_in, prefix_precomputed))


def babybear_commit_perms(n):
    return commitment_perms(n)          # ceil(n/8) + 2, hash_bytes_8 (poseidon2.rs:704)


AUTOMATA_SIZES = (256, 4096, 65536)


def automata_rows(n):
    """One dict per (family, n) with the run term and both commitment columns."""
    out = []
    for f in AUTOMATA_FAMILIES:
        if f["rows"] is None:      # Dyck: finite language
            run_rows = None if n > DYCK_MAX_TOKENS or n % 2 else 1 << (3 * (n // 2) + 2).bit_length()
        else:
            run_rows = f["rows"](n)
        if run_rows is None:
            out.append(dict(f, n=n, run_rows=None))
            continue
        cols = f["cols"] if isinstance(f["cols"], int) else None
        main = run_rows * cols if cols else None
        chip_cells = run_rows * f["chip"] * f["chip_w"]
        out.append(dict(f, n=n, run_rows=run_rows, main_cells=main, chip_perms=run_rows * f["chip"],
                        chip_cells=chip_cells, declared_rows=f["declared"](n)))
    return out


def commitment_rows(n):
    bb = babybear_commit_perms(n)
    return dict(
        n=n, bb_perms=bb, bb_cells=bb * INCIRCUIT_CELLS["poseidon2"],
        k_payload=keccak_sponge(n), k_payload_cold=keccak_sponge(n, prefix_precomputed=False),
        k_env_unary=keccak_sponge(frame_len(n, "unary")), k_env_u32=keccak_sponge(frame_len(n, "u32")),
        k_merkle_unary=tower_merkle(n, "unary"), k_merkle_u32=tower_merkle(n, "u32"),
        k_merkle_cold=tower_merkle(n, "unary", prefix_precomputed=False),
        frame_rows_unary=n + 1, frame_rows_u32=4)


def certs(n_bytes=None):
    """Plain-text bill at one record size (or all three)."""
    sizes = AUTOMATA_SIZES if not n_bytes or n_bytes < 0 else (n_bytes,)
    for n in sizes:
        c = commitment_rows(n)
        print(f"\n== n = {n} bytes")
        print(f"  commit BabyBear: {c['bb_perms']:,} Poseidon2 perms x 352 = {c['bb_cells']:,} cells")
        print(f"  commit Tower256 [INFERRED]: payload sponge {c['k_payload']:,} Keccak-f "
              f"(+1 cold prefix = {c['k_payload_cold']:,}); unary envelope {c['k_env_unary']:,} vs u32 "
              f"{c['k_env_u32']:,}; Merkle/32-B leaves {c['k_merkle_unary']:,} (cold {c['k_merkle_cold']:,})")
        print(f"  {'family':22} {'rows':>9} {'main cells':>12} {'chip perms':>11} {'chip cells':>13} {'decl rows':>9}")
        for r in automata_rows(n):
            if r["run_rows"] is None:
                print(f"  {r['name']:22} {'n/a: language finite (<= 6 tokens)':>60}")
                continue
            mc = f"{r['main_cells']:,}" if r["main_cells"] is not None else "(2k+1)·rows"
            print(f"  {r['name']:22} {r['run_rows']:9,} {mc:>12} {r['chip_perms']:11,} "
                  f"{r['chip_cells']:13,} {r['declared_rows']:9,}")


def certs_markdown():
    """COUNTS.md, generated. Refuses (exit 1) if any cited pin has moved."""
    import subprocess, sys
    bad = check_automata_pins()
    if bad:
        for k, why in bad:
            print(f"PIN MOVED {k}: {why}", file=sys.stderr)
        sys.exit(1)
    try:
        rev = subprocess.run(["git", "-C", __import__("os").path.dirname(__file__) or ".", "rev-parse", "--short", "HEAD"],
                             capture_output=True, text=True).stdout.strip()
    except OSError:
        rev = "?"
    L = []
    w = L.append
    w("# Automata counts")
    w("")
    w("<!-- GENERATED by zkml-research `notes/construction-search/space.py --certs --markdown` "
      f"(zkml-research {rev}); edit the script, not this file. -->")
    w("")
    w("2026-11-06, lane C of the automata program (`SUBSTRATE-DECISION.md` §4). Tags: [MEASURED] a pinned")
    w("named theorem or legacy `#guard` at the cited `file:line` (the generator re-reads each line and refuses if")
    w("one moved); [READ] read off an emitted golden or a note; [INFERRED] a model number. Counts, not clocks.")
    w("")
    w("Two blocks per family, kept apart on purpose (codex round 3, finding 16): the **semantic** operation")
    w("counts (what the checker does per symbol) and the **BabyBear realization** (what the served")
    w("descriptor spends). A \"lookup\" is an abstract operation; its realization cost (LogUp auxiliary")
    w("columns, table authentication) belongs to the target. This model prices the Tower256 commitment")
    w("term only; it does not yet contain a Tower256 realization column.")
    w("")
    w("## 1. Per symbol: semantics and the BabyBear realization")
    w("")
    w("| family | served descriptor | symbol | rows / symbol | lookups / symbol | degree | main cols | constraints | tables | chip perms / row (cells each) | declared table rows | descriptor bytes | binds `c`? | pins |")
    w("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for f in AUTOMATA_FAMILIES:
        rps = "nextPow2(3k+3) / 2k (canonical padding)" if f["name"] == "dyck-bracket-replay" else ("1 (8 per byte)" if "binary" in f["sym"] or f["name"] == "dfa-hash-chained-toggle" else "1")
        chip = f"{f['chip']} ({f['chip_w']})" if f["chip"] else "0"
        pins = ", ".join(f"`{pin_ref(p)}`" for p in f["pins"])
        w(f"| {f['name']} | {('`' + f['served'] + '`') if f['served'] else '-'} | {f['sym']} | {rps} | {f['lookups']} | "
          f"{f['degree']} | {f['cols']} | {f['cons']} | {f['tables']} | {chip} | {f['declared_note']} | "
          f"{f['bytes_note']} | {f['binds_c']} | {pins} |")
    w("")
    w("Notes on the rows [READ unless tagged]:")
    w("- the route8 variants add 17 columns, nine PIs, 28 constraints and one wide arity-16 permutation per row.")
    w("  Their current executable wrappers require power-of-two rows and reject padding/height mismatches;")
    w("  arbitrary-length inactive padding is not yet supplied. The legacy rows remain explicit controls.")
    w("- binary product and toggle rows also cost eight rows per byte; earlier bills incorrectly used one.")
    w("- Dyck canonical physical rows are nextPow2(3k+3), k=0..3: 4,8,16,16; two chip permutations per row.")
    w("  The minimal two-token semantic replay is five rows; it is not the padded proving height.")
    w(f"- table routing's exact-public table IS the run: unit-capacity exact-public receives pin the trace")
    w(f"  length to the declared rows (`{pin_ref('lanes-cost')}`, `forcedTraceRows := .pinned 8` at word length 8), so the")
    w("  descriptor grows with the word and the word is public. That is the served shape today; a private-word")
    w("  table routing needs a committed transition table (the weld's shape) or a LogUp table of `|Q|·|Σ|` rows.")
    w(f"- the weld is over binary symbols (`{pin_ref('asym')}`); a byte costs 8 rows, each with")
    w(f"  `MAP_TREE_DEPTH` = 16 chip permutations of map authentication (`{pin_ref('w8-aux')}`).")
    w(f"- Dyck: the deployed grammar caps nesting at k ≤ 3, so its language is `[ᵏ]ᵏ` for k ≤ 3, at most")
    w(f"  {DYCK_MAX_TOKENS} tokens; record-size rows below are n/a, not a cost.")
    w("- degree: no emitter pins a maximum constraint degree; the column says where each number was read.")
    w("- names are the descriptors' own `name` fields. The served toggle `dfa-routing-toggle-2state::poseidon2-v1`")
    w("  comes from `metatheory/Dregg2/Circuit/Emit/DfaRoutingEmit.lean` [READ `circuit/src/descriptor_by_name.rs:83`];")
    w("  the 3-state injection object now has an `EmitByName` artifact route consumed by zkOracle.")
    w("")
    w("## 2. Run term per record (BabyBear realization)")
    w("")
    w("Main cells = rows × main columns; chip cells = chip permutations × 352 (wide, "
      f"`{pin_ref('p2-wide')}`) or × 141 (narrow, hub §2 [MEASURED]). Trace height before power-of-two padding.")
    w("")
    w("| family | n bytes | rows | main cells | chip perms | chip cells | declared table rows |")
    w("|---|---:|---:|---:|---:|---:|---:|")
    for n in AUTOMATA_SIZES:
        for r in automata_rows(n):
            if r["run_rows"] is None:
                w(f"| {r['name']} | {n:,} | n/a (finite language) | | | | |")
                continue
            mc = f"{r['main_cells']:,}" if r["main_cells"] is not None else "(2k+1)·rows"
            dr = f"{r['declared_rows']:,}" if r["name"] != "dfa-product-lanes-k" else f"k·{n:,}"
            w(f"| {r['name']} | {n:,} | {r['run_rows']:,} | {mc} | {r['chip_perms']:,} | {r['chip_cells']:,} | {dr} |")
    w("")
    w("## 3. Commitment term (once per record, shared by every statement over the same `c`)")
    w("")
    w("BabyBear: `hash_bytes_8`, `⌈n/8⌉+2` Poseidon2 permutations × 352 cells [READ `circuit/src/poseidon2.rs:704`;")
    w("the +2 is the length lanes' absorb and the squeeze]. Tower256 [INFERRED, all of it]: cSHAKE256 over")
    w("byte-aligned input with a 32-byte output costs `⌊n/136⌋ + 1` Keccak-f including padding (FIPS 202")
    w("Algorithm 8; the first output block needs no extra squeeze), plus one block for the cSHAKE `bytepad(N, S)`")
    w("prefix (SP 800-185 §3.3) unless that state is precomputed (\"cold\" below counts it). The \"31 per 4 KiB\" of")
    w("LEAF-PROVER-DECISION §1 is the **payload sponge only**, not the commitment price: the leaf commits by a")
    w("Merkle root, modelled here over 32-byte leaves (§7's 66-byte unary / 37-byte u32 leaf inputs), one Keccak-f")
    w("per leaf and per node.")
    w("")
    w("| n bytes | BabyBear perms | BabyBear cells | Keccak-f payload sponge (warm / cold prefix) | Keccak-f Merkle, 32-B leaves (warm / cold) |")
    w("|---:|---:|---:|---:|---:|")
    for n in AUTOMATA_SIZES:
        c = commitment_rows(n)
        w(f"| {n:,} | {c['bb_perms']:,} | {c['bb_cells']:,} | {c['k_payload']:,} / {c['k_payload_cold']:,} | "
          f"{c['k_merkle_unary']:,} / {c['k_merkle_cold']:,} |")
    w("")
    w("Commitment sharing: one `c` serves every statement over the same record bytes under the same scheme")
    w("(the DFA, product, and padded-complement runs over one record share it). A BabyBear `c` and a Tower256")
    w("`c` are different objects; the weld's 8-felt root commits the automaton, not the record, and is a")
    w("second commitment.")
    w("")
    w("## 4. The two hot spots, with the binary length lane")
    w("")
    w("**Unary length framing** (`Tower256CshakeMerkleController.encodeLength n` = n zero bytes then 1;")
    w("`hashLeaf` absorbs `0 :: envelope b`, i.e. 2n+2 bytes for an n-byte payload) [READ minidregg")
    w("Compiler/Tower256CshakeMerkleController.lean, quoted in zkml-research LEAF-PROVER-DECISION §7].")
    w("In the run term it is one padding row per symbol wherever the byte column absorbs the framed payload;")
    w("a u32 length lane (LEAF-PROVER-DECISION §7) makes it 4 rows. In the sponge it doubles the absorbed bytes.")
    w("Inside 32-byte Merkle leaves it costs nothing (66 and 37 bytes are both one block).")
    w("")
    w("[INFERRED: the saving applies where a family's byte column absorbs the framed payload; no served descriptor does today.]")
    w("")
    w("| n bytes | framing rows unary → u32 | rows saved | table-routing main cells saved (×3) | weld8 main cells saved (×8 rows × 11) | flat-sponge Keccak-f unary → u32 | Merkle Keccak-f unary → u32 |")
    w("|---:|---:|---:|---:|---:|---:|---:|")
    for n in AUTOMATA_SIZES:
        c = commitment_rows(n)
        saved = c["frame_rows_unary"] - c["frame_rows_u32"]
        w(f"| {n:,} | {c['frame_rows_unary']:,} → {c['frame_rows_u32']} | {saved:,} | {3 * saved:,} | {88 * saved:,} | "
          f"{c['k_env_unary']:,} → {c['k_env_u32']:,} | {c['k_merkle_unary']:,} → {c['k_merkle_u32']:,} |")
    w("")
    w("**`⌈n/8⌉+2` Poseidon2 permutations** are the BabyBear commitment; they do not transfer. The same record on")
    w("Tower256 is the Merkle column of §3. In committed-bit terms the comparison is LEAF-PROVER-DECISION §1's")
    w("(Keccak-f on BabyBear is 63,192 cells; in char 2 about 51× fewer committed bits), which is why the")
    w("BabyBear Keccak path is not modelled here.")
    w("")
    w("| n bytes | BabyBear perms | BabyBear cells | Tower256 Keccak-f (Merkle, warm) |")
    w("|---:|---:|---:|---:|")
    for n in AUTOMATA_SIZES:
        c = commitment_rows(n)
        w(f"| {n:,} | {c['bb_perms']:,} | {c['bb_cells']:,} | {c['k_merkle_unary']:,} |")
    w("")
    w("## 5. Datalog: per firing, and the universal leg")
    w("")
    w(f"- One rule firing (`DerivationEmit`): 386 columns (`{pin_ref('deriv-width')}`), 393 constraints")
    w(f"  (`{pin_ref('deriv-cons')}`), 13 PIs (`{pin_ref('deriv-pi')}`); degree 8 [READ hub §2; unpinned]. Per")
    w("  firing, not per symbol.")
    w("- The closure (universal) leg of `FixpointCert.verify` enumerates, per rule r, every substitution over the")
    w("  active domain: Σ_r |dom|^varBound(r) candidates, each a body check. `activeDomain` is")
    w(f"  `edb.flatMap (·.2) ++ P.flatMap ruleConsts` (`{pin_ref('dl-domdef')}`), a LIST with duplicates, so the")
    w("  executable count is larger than the set count. Pinned on the transitive-closure example: |dom| = 6")
    w(f"  (`{pin_ref('dl-dom')}`), 6³ = 216 candidates for the 3-variable step rule (`{pin_ref('dl-substs')}`).")
    w("- Not arithmetized: the fixpoint and the closure leg have no descriptor; their cost is checker steps.")
    w("")
    return "\n".join(L) + "\n"


def main():
    _calibrate_witgen()
    ap = argparse.ArgumentParser()
    ap.add_argument("--point")
    ap.add_argument("--calibrate", action="store_true")
    ap.add_argument("--sensitivity", action="store_true")
    ap.add_argument("--top", type=int, default=12)
    ap.add_argument("--hw-axis", action="store_true",
                    help="per-SKU tensor-core table (H100/B200/B300/A100, INT8/FP8/FP4/b1, HBM term) from mma_counts.py")
    ap.add_argument("--certs", type=int, nargs="?", const=-1, metavar="N_BYTES",
                    help="automata counts at N_BYTES, or at 256/4096/65536 with no value (breadstuffs docs/automata)")
    ap.add_argument("--markdown", action="store_true",
                    help="with --certs: print breadstuffs docs/automata/COUNTS.md (pins re-read first)")
    ap.add_argument("--check-pins", action="store_true",
                    help="re-read every cited #guard line under $BREADSTUFFS_MT; exit 1 if one moved")
    a = ap.parse_args()
    if a.hw_axis:
        import importlib.util, os
        spec = importlib.util.spec_from_file_location(
            "mma_counts", os.path.join(os.path.dirname(os.path.abspath(__file__)), "mma_counts.py"))
        mc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mc)
        mc.validate()
        mc.exactness_table()
        mc.pareto_table()
        return
    if a.check_pins:
        bad = check_automata_pins()
        for k, why in bad:
            print(f"PIN MOVED {k}: {why}")
        print(f"{len(AUTOMATA_PINS) - len(bad)}/{len(AUTOMATA_PINS)} pins hold")
        raise SystemExit(1 if bad else 0)
    if a.certs is not None:
        if a.markdown:
            print(certs_markdown(), end="")
        else:
            certs(a.certs)
        return
    if a.calibrate:
        calibrate()
        return
    if a.sensitivity:
        sensitivity()
        return
    if a.point:
        p = evaluate(**NAMED[a.point])
        for k, v in p.items():
            print(f"  {k:>12}: {v:.4g}" if isinstance(v, float) else f"  {k:>12}: {v}")
        return
    pts = enumerate_space()
    print(f"enumerated {len(pts)} compatible points "
          f"({len(FIELDS)} fields x {len(PCS)} PCS x {len(PIOP)} PIOP x {len(LOOKUP)} lookups x "
          f"{len(RECURSION)} recursion x {len(HARDWARE)} hw x {len(SHAPES)} shapes x {len(AMORT)} amort)")
    objectives = {
        "A. per-request, cryptographic soundness: min prover proxy, min verifier hashes, max bits":
            ([("proxy_s", -1), ("v_hashes", -1), ("bits", 1)], lambda p: p["amort"] == "per-request"),
        "B. per-request: min proof bytes, min prover proxy, max formal":
            ([("proof_bytes", -1), ("proxy_s", -1), ("formal", 1)], lambda p: p["amort"] == "per-request"),
        "C. audited (expected-loss guarantee): min prover proxy, max formal, min verifier hashes":
            ([("proxy_s", -1), ("formal", 1), ("v_hashes", -1)], lambda p: p["amort"] != "per-request"),
        "D. formalizability-first: max formal, max bits, min prover proxy (per-request)":
            ([("formal", 1), ("bits", 1), ("proxy_s", -1)], lambda p: p["amort"] == "per-request"),
    }
    for title, (keys, filt) in objectives.items():
        sub = [p for p in pts if filt(p)]
        front = sorted(pareto(sub, keys), key=lambda p: p["proxy_s"])
        print("\n" + "=" * 100 + f"\n{title}\n  front size {len(front)} of {len(sub)}; "
              f"shown: {min(a.top, len(front))} cheapest-prover")
        for p in front[:a.top]:
            print("  " + fmt(p))
    print("\nNAMED POINTS")
    for k, kw in NAMED.items():
        print(f"  {k:<20}" + fmt(evaluate(**kw)))
    print("""
NAMED INADEQUACIES (read before quoting any number above)
 1. Witness / trace generation is CALIBRATED, not modelled: one per-cell constant set so it is
    95% of the SASH anchor (SASH: proof system ~5% of GPU time).  It scales with committed cells
    and is NOT accelerated by tensor cores, so it is the Amdahl ceiling on every tc row
    (codex 2026-11-05: infinite crypto speedup at 5% share is 1.053x).
 2. The proxy column is spec-sheet arithmetic; --calibrate shows it is ~30x optimistic in
    absolute terms.  Only same-hardware ratios are meaningful, and only as shape.
 3. 'boundary-only' and 'vm' committed-cell figures are DERIVED shapes, not emitted objects.
    'semantic-air' is the only shape anchored to a measurement (SASH 79.0M cells/position).
 4. GF(2^128) on GPU at 150 ops/mult is an assumption.  The published binary-tower GPU sumcheck
    (DATE'26 SumCATS, bit-sliced SIMT, A100) sits ~80x above mma_counts.py's HBM floor, so it does
    not pin the SIMT rate.  Binary fields DO run on integer tensor cores (parity read of the .s32
    register, Karatsuba-lazy; 2026-11-06, initiative 14); the tc row now admits GF(2^128).  The model
    still charges the boundary-only shape the same cell count in char 2, which FLATTERS the binary row.
 7. Every tc row is MAC-priced with no memory term.  mma_counts.py shows TensorZKP's own primitives
    are HBM-bound (tensor cores ~4% busy), so tc rows understate time wherever bytes bind; read
    --hw-axis for the per-SKU floors with the HBM term.
 5. Recursion overheads: atomic 0.35 is a placeholder [A] (the F4 note's single-codeword path model is
    ~0.12-0.19 of full recursion per step in Keccak-f at ell 14-22, K=2, and it carries codeword state);
    holography 1.0 is counted for hash PCS today (initiative 14); only the
    folding step (27.5M rows) and the deployed wrap identity (child verifier = wrap table) are
    measured.
 6. Soundness 'bits' is min(query term at the stated regime, field wall, LogUp wall).  It does
    not include the commit-phase epsilon_C (which at rho=1/64 over BabyBear^4 is the binding
    term at UDR -- see docs/VERDICTS.md 2).  Audited points report det_bits = -log2(1-p), the
    per-request detection probability, which is a DIFFERENT guarantee (expected loss), not bits.
""")


if __name__ == "__main__":
    main()
