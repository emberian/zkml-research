#!/usr/bin/env python3
"""
notes/redesign/composed.py -- composed end-to-end time per (design x workload x target).

2026-11-06, redesign lane. Sibling of notes/construction-search/space.py (which prices one zkML token position in
abstract proxy units; this file prices the CERTIFICATE pipeline in seconds on named hardware). stdlib only:

    python3 -I notes/redesign/composed.py               # all tables
    python3 -I notes/redesign/composed.py --markdown    # the tables MODEL.md quotes
    python3 -I notes/redesign/composed.py --breakdown a c   # phase split for designs a and c

Every input carries a tag:
  [MEASURED:<run>]  our run (file cited)       [X:<src>]  measured by others (cited)
  [MODEL:<src>]     a predicted bound or a scaled measurement (source cited)
  [A]               assumption; --sensitivity varies it
The output tag of a row is the weakest tag of its inputs.

UNITS. Seconds. A "leaf" is one content certificate over one record (default 4 KiB, a DFA with <= 256 states).
"""
import argparse
import math

# =====================================================================================================  targets
# Rates per DEVICE (one CPU core, or one GPU/TPU chip). tag per rate.
TARGETS = {
    # Kaggle Xeon @2.0 GHz, one core: Keccak-f 536 ns, Tower256 mult (PCLMUL+Barrett) 22.9 ns
    # [MEASURED: accelerator-readiness/TOWER256.md section 3, runs/accel-tower-dryrun-04].
    "cpu1": dict(keccak=1 / 536e-9, t256=1 / 22.9e-9, t128=None, enc_ns_per_cw_byte=None,
                 tag_keccak="MEASURED:accel-tower-dryrun-04", tag_t256="MEASURED:accel-tower-dryrun-04"),
    # 64-core CPU box at 2x the Kaggle core per core (TOWER256.md section 5 comparison: "a 64-core host at about 2x
    # the Kaggle core"); leaves are embarrassingly parallel, so linear [MODEL].
    "cpu64": dict(keccak=128 / 536e-9, t256=128 / 22.9e-9, tag_keccak="MODEL:TOWER256.md s5", tag_t256="MODEL"),
    # T4: Keccak-f 4.35e8 (dryrun-04) .. 6.9e8 (tune-03) batched Merkle; Tower256 log/exp table mult 2.87e8
    # [MEASURED: TOWER256.md section 4]. Low end used.
    "T4": dict(keccak=4.35e8, t256=2.87e8, tag_keccak="MEASURED:accel-tower-dryrun-04",
               tag_t256="MEASURED:accel-tower-dryrun-04"),
    # H100/B200/B300: Keccak = SASS bound x 0.8 efficiency [MODEL: hw-optimality/predict.py section 1 bound
    # 3.6e9 H100, 3.9e9 B200, 4.2e9 B300; T4 measured 0.67-1.06 of its bound]. Tower256 table mult scaled by
    # integer SIMT lanes x clock from T4 [MODEL: TOWER256.md section 5: H100 4.1x T4; B200/B300 1.08/1.16x H100,
    # OPTIMAL.md Rule 2].
    "H100": dict(keccak=0.8 * 3.6e9, t256=2.87e8 * 4.1, tag_keccak="MODEL:predict.py", tag_t256="MODEL:TOWER256.md s5"),
    "B200": dict(keccak=0.8 * 3.9e9, t256=2.87e8 * 4.1 * 1.08, tag_keccak="MODEL:predict.py",
                 tag_t256="MODEL:OPTIMAL.md rule 2"),
    "B300": dict(keccak=0.8 * 4.2e9, t256=2.87e8 * 4.1 * 1.16, tag_keccak="MODEL:predict.py",
                 tag_t256="MODEL:OPTIMAL.md rule 2"),
    # TPU v5e, one chip: no 64-bit, no rotate, no CLMUL [READ tpu-perf/STYLE.md]. Keccak-f in 32-bit
    # bit-interleaved form ~1.0e4 VPU int32 ops [A, counted in MODEL.md section 2]; VPU int32 rate 6.1e12/s
    # [A: 8x128 lanes x 4 ALUs x 1.5 GHz, the placeholder the TPU lane has not calibrated]. Tower256 mult
    # bit-sliced on the VPU ~3,000 int32 ops amortized [A].
    # Tower256 mult on the VPU at T4's measured op-equivalents per multiply (~10,500 = 3.0e12 / 2.87e8) [A].
    "TPUv5e": dict(keccak=6.1e12 / 1.0e4, t256=6.1e12 / 1.05e4, tag_keccak="A", tag_t256="A"),
}
# Per-target extras for the designs that use them.
# Tensor GF(2) fixed-r route: per-proof arithmetic speedup on the encode+folds (ROTATION.md section 2(c), table
# "arith: table -> arith: tensor": T4 37.1/12.6, H100 9.0/2.3, B200 4.2/0.9, B300 3.9/0.86) [MODEL:ROTATION 2c].
TENSOR_ARITH_SPEEDUP = {"T4": 37.1 / 12.6, "H100": 9.0 / 2.3, "B200": 4.2 / 0.9, "B300": 3.9 / 0.86}
# Packed GF(2^16) interleaved encode, ns per CODEWORD byte (systematic rate 1/4, LCH, 4 KiB-2 MiB messages).
# Filled from notes/redesign/kernels runs; see MODEL.md section 3 for every run.
#   cpu1: Kaggle Xeon core, SSSE3 nibble tables, unblocked LCH: 9.1 at a 32 KiB codeword, 4.7-5.7 at 2-34 MiB,
#         8.6 at ell 14 [MEASURED: runs/redesign-encode-t4-01]. 5.5 used for batches, 9.1 for one 4 KiB leaf.
#   T4:   per-layer kernel 0.115-0.153 at 8-134 MiB codewords (HBM-bound: one round trip per layer), 6.1 at
#         32 KiB (launch-bound) [MEASURED: runs/redesign-encode-t4-01]; fused kernel: see FUSED below.
PACKED_ENC_NS = {
    "cpu1": (5.5, "MEASURED:redesign-encode-t4-01"),
    "cpu64": (5.5 / 128, "MODEL: cpu1 x 128"),
    # fused kernel (6 layers per shared-memory pass): 0.074-0.088 at 8-34 MiB, 0.10-0.14 at ell 14
    # [MEASURED: runs/redesign-encode-t4-02]; bank-conflicted nibble lookups, ~3x above its HBM floor.
    "T4": (0.088, "MEASURED:redesign-encode-t4-02"),
}
# PIOP extension multiplies per trace row for the packed design (zerocheck + Shout read-check + ring switching).
# Not built anywhere in our stack: [A], varied by --sensitivity.
PIOP_MULTS_PER_ROW = 16
# T4 calibration for design (a): measured batched encode+commit 0.82 ms per ell-14 word (64-word batch,
# TOWER256.md section 4) against this model's 0.55 ms -> GPU efficiency 0.67 applied to (a)/(b) GPU rows.
GPU_EFF_UNPACKED = 0.55 / 0.82
# BLAKE3 vs Keccak-f per hashed byte, internal Merkle nodes (64-byte inputs) and leaves:
#  SIMT: BLAKE3 compression ~7 rounds x 8 G x ~14 int32 ops ~= 800 ops per 64 B; Keccak-f 4,656 ops per 136 B
#  [SASS, OPTIMAL.md 3.2]. Per 64-byte NODE: 800 vs 4,656 -> 5.8x; per leaf byte: 12.5 vs 34 -> 2.7x [MODEL].
#  CPU: BLAKE3 ~0.5-1 cycle/B with SIMD vs Keccak ~8 cycles/B scalar [A] -> 3-6x per byte.
#  Binary R1CS (recursion): Keccak-f 38,400 constraints [X: ePrint 2026/1656 section 4], BLAKE3 compression ~14k
#  [X: same, as quoted in PROOF-SYSTEM-SPACE U2] -> per 64-byte node 2.7x, per byte 1.3x.
BLAKE3_SPEEDUP = {"node_simt": 5.8, "leaf_simt": 2.7, "node_cpu": 4.0, "leaf_cpu": 4.0, "node_r1cs": 2.7,
                  "leaf_r1cs": 1.3}

# =====================================================================================================  workloads
REC = 4096           # record bytes [A: the 4 KiB record of LEAF-PROVER-DECISION section 1]
Q_UD100 = 148        # queries, rate 1/4, UD-100 [READ minidregg TOWER256-FRI-PROVER-WORK.md section 2]
# Recursion: proving a verifier's Keccak-f inside a binary-field prover. BinarySpartan: 287k Keccak-f/s on 12
# M4 Max P-cores [X: ePrint 2026/1656 section 4] -> per core 2.39e4/s; the Tower256 analogue does not exist.
REC_KECCAK_PER_CORE_S = 287e3 / 12
# A GPU-hosted binary recursion prover: no published number. [A] 100 CPU cores-equivalent per GPU (the T4
# Tower256 batch measured ~57-59 Xeon cores, TOWER256.md section 4; H100 ~4x T4).
REC_GPU_CORE_EQUIV = {"cpu64": 128, "T4": 57, "H100": 230, "B200": 250, "B300": 270, "TPUv5e": 30}


# =====================================================================================================  designs
def leaf_unpacked(target, rec=REC, cols=4, ell_extra=2, tensor=False, blake_internal=False):
    """(a)/(b): today's Tower256 additive FRI, one symbol per 32-byte element, rate 1/4, UD-100.
    Counts from tower256_fri_counts.py at ell 14 (4 KiB): Merkle 65,493 Keccak-f per column-tree, encode 114,688
    mults per column, folds 32,736 [READ TOWER256-FRI-PROVER-WORK section 2]; scaled ~linearly in 2^ell.
    cols = 4 trace columns (byte, state, position, multiplicity) [A: section 3 'one column' caveat]; columns are
    batched into one level-0 leaf of 4 x 32 B (2 Keccak blocks with unary framing, LEAF-PROVER-DECISION section 7)
    and folded as one random combination. PIOP (zerocheck + lookup), not yet arithmetized: 8 Tower256 mults per
    row per column [A]."""
    t = TARGETS[target]
    rows = rec
    n = rows * (1 << ell_extra)
    s = n / (1 << 14)
    keccak_l0 = 2 * n + n                      # leaves (2 blocks) + nodes, level 0
    keccak_folds = 2 * n                       # fold oracles (one element per leaf), all levels
    keccak = keccak_l0 + keccak_folds + 7_666 * (1 if s <= 1 else 1)  # + seeds
    mults_enc = cols * 114_688 * s * (math.log2(n) - 2) / 12
    mults_fold = 32_736 * s
    mults_piop = 8 * rows * cols
    hash_s = keccak / t["keccak"]
    if blake_internal:
        k = BLAKE3_SPEEDUP["node_simt"] if not target.startswith("cpu") else BLAKE3_SPEEDUP["node_cpu"]
        hash_s = (n * 2 + 7_666) / t["keccak"] + (n + keccak_folds) / t["keccak"] / k  # content leaves stay cSHAKE
    arith = (mults_enc + mults_fold) / t["t256"]
    if not target.startswith("cpu"):
        arith /= GPU_EFF_UNPACKED
        hash_s /= GPU_EFF_UNPACKED
    if tensor and target in TENSOR_ARITH_SPEEDUP:
        arith /= TENSOR_ARITH_SPEEDUP[target]
    piop = mults_piop / t["t256"]
    ver_keccak = 53_263 * (1 + 0.1 * math.log2(s)) if s >= 1 else 53_263
    return dict(hash=hash_s, encode=arith, piop=piop, ver_keccak=ver_keccak, proof_bytes=1.46e6,
                committed_bytes=rows * cols * 32, keccak=keccak)


def leaf_packed(target, rec=REC, bits_per_row=80, blake_internal=False, ext="t256", leaf_bytes=272):
    """(c): packed binary. Trace bits per row = byte 8 + state 8 + Shout one-hot (d = 4 chunks of 16) 64 = 80 [A];
    position is virtual. Committed message = rows x bits / 8 bytes, systematic rate-1/4 additive RS over GF(2^16)
    twiddles interleaved across the packed lanes (kernels/encode.c), wide leaves of `leaf_bytes`, cSHAKE Merkle.
    The byte lane's message subtree IS the store's content tree (section 5 of MODEL.md), so no in-circuit Keccak.
    PCS folding (BaseFold/FRI-Binius over the packed word, or Ligerito): 1.3x level-0 hashing [A] and
    2 ext mults per packed 256-bit codeword word [A]. PIOP: 16 ext mults per row [A] (zerocheck with univariate
    skip, Shout read-check, ring switching). ext = 't256' (today's field) or 't128' (challenges in T_7 subset of
    Tower256: CLMUL GF(2^128) ~4x cheaper [A])."""
    t = TARGETS[target]
    rows = rec
    msg = rows * bits_per_row / 8
    cw = 4 * msg
    leaves = cw / leaf_bytes
    keccak_leaf = leaves * math.ceil((leaf_bytes + 6) / 136)
    keccak_node = leaves
    keccak = 1.3 * (keccak_leaf + keccak_node) + 400  # + transcript seeds (u32 codec, cached prefix) [A]
    hash_s = keccak / t["keccak"]
    if blake_internal:
        k_l = BLAKE3_SPEEDUP["leaf_simt"] if not target.startswith("cpu") else BLAKE3_SPEEDUP["leaf_cpu"]
        k_n = BLAKE3_SPEEDUP["node_simt"] if not target.startswith("cpu") else BLAKE3_SPEEDUP["node_cpu"]
        content = (msg / cw) * (keccak_leaf + keccak_node)            # byte-lane message subtree stays cSHAKE
        rest_l = 1.3 * keccak_leaf - (msg / cw) * keccak_leaf
        rest_n = 1.3 * keccak_node - (msg / cw) * keccak_node
        hash_s = (content + 400) / t["keccak"] + rest_l / t["keccak"] / k_l + rest_n / t["keccak"] / k_n
    enc_ns, _ = packed_enc_ns(target)
    encode = cw * enc_ns * 1e-9
    mult_rate = t["t256"] * ((4 if target.startswith("cpu") else 3) if ext == "t128" else 1)
    fold = 2 * (cw * 8 / 256) / mult_rate
    piop = PIOP_MULTS_PER_ROW * rows / mult_rate
    # verifier: q x (leaf blocks + path) at level 0 and ~log2(cw/32) BaseFold rounds of ext-element paths
    depth = math.log2(leaves)
    rounds = max(1, math.log2(cw / 32) - 4)
    ver_keccak = Q_UD100 * (math.ceil((leaf_bytes + 6) / 136) + depth + sum(max(1, depth - j) for j in range(int(rounds))) / 2)
    proof_bytes = Q_UD100 * (leaf_bytes + 32 * depth + 64 * rounds * depth / 2)
    return dict(hash=hash_s, encode=encode + fold, piop=piop, ver_keccak=ver_keccak, proof_bytes=proof_bytes,
                committed_bytes=msg, keccak=keccak)


def packed_enc_ns(target):
    v, tag = PACKED_ENC_NS.get(target, (None, None))
    if v is not None:
        return v, tag
    # [MODEL] SIMT estimate: 7.5 const-mults + 7.5 XORs per codeword element (5/4 LCH passes x ell 12 / 2),
    # 14 int32 ops per const-mult (4 nibble lookups x 4 lanes, smem) -> ~56 ops per codeword byte; scaled from
    # T4's measured int32 rate 3.0e12/s (OPTIMAL.md T4) by SIMT lanes x clock.
    # GPUs: the measured T4 fused kernel scaled by integer SIMT lanes x clock (it is LDS/ALU-bound, not HBM-bound).
    simt = {"H100": 1.67e13, "B200": 1.8e13, "B300": 1.94e13, "TPUv5e": 6.1e12}
    if simt.get(target):
        return PACKED_ENC_NS["T4"][0] * 3.0e12 / simt[target], "MODEL"
    return 5.0, "A"


def prime_brakedown(target, rec=REC):
    """(d)/(e): BabyBear felts (byte, state, LogUp inverse in x^4 ext 16 B, multiplicity) = 28 B per row [A];
    Brakedown/expander encode is O(n) and cheap; but the record's cSHAKE content root is NOT a BabyBear tree, so
    the leaf must evaluate Keccak in-circuit: 31 Keccak-f per 4 KiB x 63,192 committed cells each
    [READ LEAF-PROVER-DECISION section 1] = 1.96M BabyBear cells per record, ~8 bytes committed per cell incl.
    ext columns [A]. Prover throughput on committed cells: SASH's measured Stwo rate 1.3e9 cells/s per H100
    [X: PROOF-SYSTEM-SPACE section 3 calibration]; tensor cores buy 1.01-1.5x on that shape [MODEL: space.py]."""
    cells = rec * 7 + 31 * 63_192
    h100_cells_s = 1.3e9
    scale = {"cpu1": 1 / 400, "cpu64": 128 / 400, "T4": 1 / 5, "H100": 1, "B200": 1.3, "B300": 1.4, "TPUv5e": 1 / 3}[target]
    prove = cells / (h100_cells_s * scale)
    # recursion of a BabyBear Keccak-committed proof: its verifier hashes are Keccak (ruling), each 63,192 cells
    ver_keccak = 53_263
    return dict(hash=0.0, encode=prove, piop=0.0, ver_keccak=ver_keccak, proof_bytes=1.5e6,
                committed_bytes=cells * 4, keccak=0, rec_cells_per_keccak=63_192)


DESIGNS = {
    "a": ("Tower256 additive FRI, unpacked, cSHAKE trees (today)", lambda t: leaf_unpacked(t)),
    "b": ("(a) + tensor-core GF(2) encode + BLAKE3 internal trees", lambda t: leaf_unpacked(t, tensor=True, blake_internal=True)),
    "c": ("packed binary (GF(2^16) twiddles, Tower256 ext), wide cSHAKE leaves, content subtree", lambda t: leaf_packed(t)),
    "c128": ("(c) with challenges in T_7 = GF(2^128) inside Tower256", lambda t: leaf_packed(t, ext="t128")),
    "cB": ("(c128) + BLAKE3 for parity/fold oracles (content subtree stays cSHAKE)", lambda t: leaf_packed(t, ext="t128", blake_internal=True)),
    "d": ("BabyBear Brakedown/sumcheck on tensor cores, Keccak content binding in-circuit", lambda t: prime_brakedown(t)),
}


def leaf_time(d, target):
    r = DESIGNS[d][1](target)
    return r["hash"] + r["encode"] + r["piop"], r


def recursion_time(d, target, blake_internal=False):
    """Seconds to verify ONE leaf proof inside a binary-field recursion prover on `target` (cores or GPU)."""
    _, r = leaf_time(d, target)
    vk = r["ver_keccak"]
    if d == "d":
        # BabyBear recursion over Keccak paths: 63,192 cells per Keccak-f at 1.3e9 cells/s on an H100 [X/A]
        dev = {"cpu1": 1 / 400, "cpu64": 128 / 400, "T4": 1 / 5, "H100": 1, "B200": 1.3, "B300": 1.4, "TPUv5e": 1 / 3}[target]
        return vk * 63_192 / (1.3e9 * dev)
    if d in ("b", "cB"):
        vk = vk / BLAKE3_SPEEDUP["node_r1cs"]  # paths are 64-byte nodes
    per_s = REC_KECCAK_PER_CORE_S * (1 if target == "cpu1" else REC_GPU_CORE_EQUIV[target])
    # (M4 Max P-core ~2x the Kaggle core [A]; cpu1 is therefore generous to recursion by ~2x)
    return vk / per_s


# =====================================================================================================  composition
def composed(d, target, workload):
    """End-to-end seconds per RECORD for a workload, on one device of `target`."""
    leaf, r = leaf_time(d, target)
    if workload == "leaf":            # one certificate, proved and handed over as is
        return leaf
    if workload == "verify":          # native verification by a light client on cpu1
        return r["ver_keccak"] / TARGETS["cpu1"]["keccak"]
    if workload == "aggregate-recursive":   # every leaf proved, then verified inside a recursion step
        return leaf + recursion_time(d, target)
    if workload == "aggregate-batch":   # one proof over a batch of 1,024 records; recursion paid once per batch
        b = 1024
        big = DESIGNS[d][1]  # proved at 1,024x the rows
        if d in ("a", "b"):
            rr = leaf_unpacked(target, rec=REC * b, tensor=(d == "b"), blake_internal=(d == "b"))
        elif d == "d":
            rr = prime_brakedown(target, rec=REC * b)
        else:
            rr = leaf_packed(target, rec=REC * b, ext=("t128" if d in ("c128", "cB") else "t256"), blake_internal=(d == "cB"))
        return (rr["hash"] + rr["encode"] + rr["piop"]) / b + recursion_time(d, target) * 1.3 / b
    if workload.startswith("audit"):    # commit-then-audit: store's cSHAKE commit is paid anyway; prove w.p. p
        p = float(workload.split("@")[1])
        return p * composed(d, target, "aggregate-batch")
    if workload == "stream":           # 64 KiB windows, each a batch of 16 records, accumulated (0.3x a recursion)
        b = 16
        if d in ("a", "b"):
            rr = leaf_unpacked(target, rec=REC * b, tensor=(d == "b"), blake_internal=(d == "b"))
        elif d == "d":
            rr = prime_brakedown(target, rec=REC * b)
        else:
            rr = leaf_packed(target, rec=REC * b, ext=("t128" if d in ("c128", "cB") else "t256"), blake_internal=(d == "cB"))
        return (rr["hash"] + rr["encode"] + rr["piop"]) / b + 0.3 * recursion_time(d, target) / b
    raise ValueError(workload)


WORKLOADS = ["leaf", "aggregate-recursive", "aggregate-batch", "audit@0.01", "stream", "verify"]
TARGET_ORDER = ["cpu1", "cpu64", "T4", "H100", "B200", "B300", "TPUv5e"]


def fmt_s(x):
    if x >= 1:
        return f"{x:.2f} s"
    if x >= 1e-3:
        return f"{x * 1e3:.2f} ms"
    return f"{x * 1e6:.1f} us"


def table(md=False):
    out = []
    for w in WORKLOADS:
        tg = TARGET_ORDER if w != "verify" else ["cpu1"]
        hdr = ["design"] + tg
        rows = []
        for d in DESIGNS:
            if d == "b":
                vals = [composed(d, t, w) if t in TENSOR_ARITH_SPEEDUP or w == "verify" else None for t in tg]
            else:
                vals = [composed(d, t, w) for t in tg]
            rows.append([d] + ["-" if v is None else fmt_s(v) for v in vals])
        if md:
            out.append(f"\n**{w}** (seconds per record)\n")
            out.append("| " + " | ".join(hdr) + " |")
            out.append("|" + "---|" * len(hdr))
            for r in rows:
                out.append("| " + " | ".join(r) + " |")
        else:
            out.append(f"\n== {w} (per record)")
            out.append("".join(h.rjust(12) if i else h.ljust(6) for i, h in enumerate(hdr)))
            for r in rows:
                out.append("".join(c.rjust(12) if i else c.ljust(6) for i, c in enumerate(r)))
    return "\n".join(out)


# $/hour [READ accelerator-readiness/RUNBOOK.md section 1 for vast.ai H100 SXM 2.33, B200 7.50; tpu-perf/GCP-LEDGER.md
# v5e spot 0.36]; T4 ~0.35 (GCP on-demand class) [A]; 64-core CPU box ~1.5 [A]; B300 = B200 [A].
PRICE_H = {"cpu1": 1.5 / 64, "cpu64": 1.5, "T4": 0.35, "H100": 2.33, "B200": 7.50, "B300": 7.50, "TPUv5e": 0.36}


def dollars(md=False):
    out = ["\n== $ per million records, aggregate-batch (throughput x price; [A] prices)"]
    hdr = ["design"] + TARGET_ORDER
    rows = []
    for d in DESIGNS:
        r = [d]
        for t in TARGET_ORDER:
            if d == "b" and t not in TENSOR_ARITH_SPEEDUP:
                r.append("-"); continue
            r.append(f"{composed(d, t, 'aggregate-batch') * 1e6 / 3600 * PRICE_H[t]:.2f}")
        rows.append(r)
    if md:
        out = ["\n**$ per million records, aggregate-batch**\n", "| " + " | ".join(hdr) + " |", "|" + "---|" * len(hdr)]
        out += ["| " + " | ".join(r) + " |" for r in rows]
    else:
        out.append("".join(h.rjust(10) if i else h.ljust(6) for i, h in enumerate(hdr)))
        out += ["".join(c.rjust(10) if i else c.ljust(6) for i, c in enumerate(r)) for r in rows]
    return "\n".join(out)


def breakdown(designs, md=False):
    out = []
    for d in designs:
        out.append(f"\n{d}: {DESIGNS[d][0]}")
        for t in TARGET_ORDER:
            if d == "b" and t not in TENSOR_ARITH_SPEEDUP:
                continue
            tot, r = leaf_time(d, t)
            out.append(f"  {t:7s} leaf {fmt_s(tot):>10s} = hash {fmt_s(r['hash']):>9s} + encode/fold {fmt_s(r['encode']):>9s}"
                       f" + piop {fmt_s(r['piop']):>9s}; Keccak-f {r['keccak']:,.0f}; committed {r['committed_bytes'] / 1024:,.0f} KiB;"
                       f" verifier Keccak-f {r['ver_keccak']:,.0f}; proof {r['proof_bytes'] / 1e6:.2f} MB;"
                       f" recursion/leaf {fmt_s(recursion_time(d, t))}")
    return "\n".join(out)


def sensitivity():
    """Vary the [A] inputs of the winner by 4x either way and report whether the ranking a vs c flips."""
    out = []
    base = {t: composed("a", t, "aggregate-batch") / composed("c", t, "aggregate-batch") for t in TARGET_ORDER}
    out.append("ratio a / c, aggregate-batch: " + ", ".join(f"{t} {v:.1f}x" for t, v in base.items()))
    global PACKED_ENC_NS
    saved = dict(PACKED_ENC_NS)
    for f in (0.25, 4.0):
        for t in TARGET_ORDER:
            v, _ = packed_enc_ns(t)
            PACKED_ENC_NS[t] = (v * f, "sens")
        r = {t: composed("a", t, "aggregate-batch") / composed("c", t, "aggregate-batch") for t in TARGET_ORDER}
        out.append(f"packed encode x{f}: " + ", ".join(f"{t} {v:.1f}x" for t, v in r.items()))
        PACKED_ENC_NS = dict(saved)
    global PIOP_MULTS_PER_ROW
    for f in (0.25, 4.0):
        PIOP_MULTS_PER_ROW = 16 * f
        r = {t: composed("a", t, "aggregate-batch") / composed("c", t, "aggregate-batch") for t in TARGET_ORDER}
        out.append(f"piop mults/row {16 * f:g}: a/c " + ", ".join(f"{t} {v:.1f}x" for t, v in r.items()))
    PIOP_MULTS_PER_ROW = 16
    return "\n".join(out)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--breakdown", nargs="*")
    ap.add_argument("--sensitivity", action="store_true")
    a = ap.parse_args()
    if a.breakdown is not None:
        print(breakdown(a.breakdown or list(DESIGNS)))
    elif a.sensitivity:
        print(sensitivity())
    else:
        print(table(md=a.markdown))
        print(dollars(md=a.markdown))
