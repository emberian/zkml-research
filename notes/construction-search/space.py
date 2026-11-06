#!/usr/bin/env python3
"""
construction-search/space.py -- enumerate the proof-system construction space
with a COUNTS model and print Pareto fronts under several objectives.

2026-11-05.  Companion to docs/PROOF-SYSTEM-SPACE.md.  stdlib only.

    python3 notes/construction-search/space.py            # all fronts
    python3 notes/construction-search/space.py --point U1 # one named point, itemized
    python3 notes/construction-search/space.py --calibrate

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
    "holography-acc": dict(wrap=True, overhead=0.25), # [A] 2026/538: accumulate holographic checks
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
    if hw == "tc" and field not in TC_LIMBS:
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
        L = TC_LIMBS[field]
        # Eligible work and total work must use the same audit amortization.
        tc_share = min(1.0, p * (tc_cell * commit + S["virt"] * PIOP[piop]["virt_mult"]) / max(mults, 1))
        mult_cost = mults * (tc_share * (L * L * TC_MAC_OPEQ + 0.25) + (1 - tc_share) * mops)
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


def main():
    _calibrate_witgen()
    ap = argparse.ArgumentParser()
    ap.add_argument("--point")
    ap.add_argument("--calibrate", action="store_true")
    ap.add_argument("--sensitivity", action="store_true")
    ap.add_argument("--top", type=int, default=12)
    a = ap.parse_args()
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
 4. GF(2^128) on GPU at 150 ops/mult is an assumption; a published binary-tower GPU sumcheck
    rate would replace it.  Binary fields cannot do integer matmul natively; the model charges
    the boundary-only shape the same cell count in char 2, which FLATTERS the binary row.
 5. Recursion overheads (atomic 0.35, holography 0.25) are placeholders, flagged [A]; only the
    folding step (27.5M rows) and the deployed wrap identity (child verifier = wrap table) are
    measured.
 6. Soundness 'bits' is min(query term at the stated regime, field wall, LogUp wall).  It does
    not include the commit-phase epsilon_C (which at rho=1/64 over BabyBear^4 is the binding
    term at UDR -- see docs/VERDICTS.md 2).  Audited points report det_bits = -log2(1-p), the
    per-request detection probability, which is a DIFFERENT guarantee (expected loss), not bits.
""")


if __name__ == "__main__":
    main()
