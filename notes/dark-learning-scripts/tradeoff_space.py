#!/usr/bin/env python3
"""Dark-learning construction space: enumerate, price in COUNTS, print the Pareto set.

2026-11-05. No clocks anywhere in this file. Every cost is a count derived from the
parameters below, and every constant that is not derived is named with its source tag:
  [MEASURED] a number our own harnesses produced (cited note),
  [DERIVED]  computed here from stated formulas,
  [CLAIM]    an outside number taken on trust (verify before quoting),
  [MODEL]    a modelling choice of this script (change it and say so).

Run: python3 notes/dark-learning-scripts/tradeoff_space.py [--d 4096 --L 32 --all]

Axes (the construction space):
  modulus    : RNS3-109@4096 (deployed), p61@4096 (single prime), RNS-202@8192, gold64@4096
  proof field: babybear-ext (bridged residues) | native (proof field = FHE modulus; single-prime only)
  custody    : fhe+mpc-boundary | mpc-only | tee-plaintext | fhe-bootstrap
  base       : dark (W0 encrypted) | public (public trunk, dark delta)
  update     : backprop-full | lowrank-r | append-rank1 | zo-seeded (MeZO-style on the trainable set)
  rank r     : 1, 8, 16, 64 (only for lowrank)
  audit p    : 1, 0.1, 0.01, 0.001
Objectives (all minimized):
  proof_felts   amortized committed felts per step for the sampled step proof (p * felts) + the envelope
  host_work     local modular multiplications per step (ct ops priced in NTT-equivalents, triples preprocessed)
  online_elems  field elements exchanged among the quorum per step (the quorum is online for every one)
  leak_log2     log2 of the union-bounded smudging leakage over 1e6 steps (read budget)
  undetected    expected injected displacement before first alarm, in units of the per-step cap B (=1/q)
Gates (hard filters, reported separately so a failure is visible, not silently dropped):
  pq       log2 Q <= HE-standard quantum-128 ceiling for N   [CLAIM: HE-standard 2018 Table, from memory]
  depth    depth available between crossings >= depth the update style needs
  wrap     plaintext does not wrap over the merge/refresh period (BFV cannot rescale)
"""
import argparse
import itertools
import math

# ---------------------------------------------------------------- parameters
MODULI = {
    # name: (N, log2 Q, residue limbs as bit widths, depth between crossings, single_prime)
    # depth 2 at deployed RNS3-109 is [MEASURED] (notes/kpz-noop-and-the-model-gap.md, 40/40 draws).
    # p61/gold64 depth 1 and RNS-202 depth 4 are [MODEL]: a ct x ct level costs 33-42 bits [MEASURED]
    # at the deployed ring; 61 - 20 (t) - ~4 (fresh) leaves ~37 bits = one level.
    "RNS3-109@4096": (4096, 109, (36, 36, 37), 2, False),
    "p61@4096":      (4096, 61, (61,), 1, True),
    "gold64@4096":   (4096, 64, (64,), 1, True),
    "RNS-202@8192":  (8192, 202, (34, 34, 34, 34, 33, 33), 4, False),
}
# [CLAIM] quantum-128 log2 Q ceilings (HomomorphicEncryption.org standard, ternary secret). From memory;
# deployed secret is CBD(20), MATZOV puts the classical row at ~122. Verify before quoting.
PQ_CEILING = {4096: 101, 8192: 202, 16384: 411}
T_BITS = 20                  # t = 1032193 ~ 2^20 [MEASURED deployed]
BRIDGE_BITS = 30             # 2-felt base-2^30 BabyBear bridge per residue (mle_gpu.rs:479) [READ]
LOOKUP_BITS = 16             # LogUp range-check limb width [MODEL]
EPS_CHK_LOG2 = -100          # checker soundness at an Ext4 challenge field [MODEL; VERDICTS 2: UDR is 34 bits
                             # at deployed FRI, so this is an aspiration until the PCS regime is pinned]
EPS_BIND_LOG2 = -120         # [MODEL]
BEACON_ALPHA = 0.05          # grinding share: eps_beacon <= alpha * p (audit-theorem-statement.md) [MODEL]
STEPS = 10 ** 6

def smudge_eps_log2(logq):
    # [READ notes/fhe-core-theory.md security ledger item 2]: shipped 2^-48 per party becomes 2^-32 per
    # session after the union factor; a statistical 80-bit smudge wants log q >= 138. Step function [MODEL].
    return -80 if logq >= 138 else -32

# ---------------------------------------------------------------- per-ciphertext proof cost
def felts_per_ct(mod, native):
    N, logq, limbs, _, single = MODULI[mod]
    if native and single:
        return 2 * N                                   # one residue per coefficient, proof field = Q
    return 2 * N * sum(math.ceil(b / BRIDGE_BITS) for b in limbs)   # 49,152 at deployed [MEASURED table]

def ctct_certificate_felts(mod, native):
    """Hole B closure: integer quotient-remainder certificate for round(t z / Q).
    z is the lifted integer convolution, |z| <~ N * (Q/2)^2 * 2 (c0*c1 cross terms) [DERIVED].
    Representing z needs int_limbs limbs in the proof field; s in [0,Q) and y need range checks.
    3 output polynomials (tensor c0, c1, c2) [READ VERDICTS 7.5 09-05 addendum: 3*4096*109 booleanity]."""
    N, logq, limbs, _, single = MODULI[mod]
    pbits = logq if (native and single) else 31
    zbits = math.log2(N) + 2 * logq + 1
    int_limbs = math.ceil((zbits + T_BITS) / (pbits - 1))
    range_felts = 3 * N * (math.ceil(logq / LOOKUP_BITS) + math.ceil((zbits + T_BITS - logq) / LOOKUP_BITS))
    return 3 * N * int_limbs + range_felts, int_limbs

# ---------------------------------------------------------------- per-step op counts (one d x d layer, L layers)
def step_ops(update, base, r, d, L, N):
    """Returns (ctct, ctpt, crossings, needed_depth, trainable_params, commit_felts_envelope).
    Ciphertext packing: an inner product of length N per ct x ct (coefficient encoding) [READ fhe-core-theory].
    Forward matvec with both operands encrypted: d*d/N ct x ct per layer [DERIVED]. With a public base the
    W0 v term is ct x pt (coefficient matmul, Hole B absent) [READ VERDICTS 3]."""
    per = d * d / N
    fwd_ctct = 0 if base == "public" else per
    fwd_ctpt = per if base == "public" else 0
    if update == "backprop-full":
        ctct = 2 * fwd_ctct + per + per          # forward, backward W^T delta, outer-product update
        ctpt = 2 * fwd_ctpt
        cross = 2 * d / N                        # sigma and sigma' fused in one crossing per direction
        depth, params, env = 1, d * d, 2 * d     # envelope commits the rank-1 factors (delta, x)
    elif update == "append-rank1":
        T_live = d / 4                           # mean live factors between merges, r=1, T_merge = d/2
        ctct = fwd_ctct + 2 * T_live * d / N + per + per   # fwd + adapter terms + backward + amortized merge
        ctpt = fwd_ctpt
        cross = 2 * d / N
        depth, params, env = 2, d * d, 2 * d
    elif update == "lowrank":
        ad = 2 * r * d / N
        ctct = fwd_ctct + 2 * ad + (per if base == "dark" else 0) + ad   # fwd, adapter fwd/bwd, base bwd, grad
        ctpt = fwd_ctpt + (per if base == "public" else 0)              # base backward is ct x pt when public
        cross = 2 * d / N
        depth, params, env = 1, 2 * r * d, 2 * r * d
    elif update == "zo-seeded":
        # two forward passes, no backward; update eta*c*z: encrypted scalar times public seeded vector.
        trainable = 2 * r * d if r else d * d
        ctct = 2 * fwd_ctct + 2 * (2 * r * d / N if r else 0)
        ctpt = 2 * fwd_ctpt + trainable / N
        cross = 2 * d / N
        depth, params, env = 1, trainable, 1     # one scalar + a public seed per step
    else:
        raise ValueError(update)
    return ctct * L, ctpt * L, cross * L, depth, params * L, env * L

# ZO needs more steps for the same progress: MeZO-class ~ O(effective rank) more steps. [CLAIM: Malladi et al.
# 2023 report up to 12x more steps than Adam at LLM fine-tuning; the 2610.27550 lower bound says randomized
# two-point methods are optimal at O(E T) calls.] We charge a multiplier on all per-step costs.
ZO_STEP_MULT = 12
KAPPA = 40        # triples (or proof felts) per nonlinear activation, 16-bit table/comparison [MODEL]
C_PRE = 100       # host mod-mults to preprocess one triple (HE-based LowGear-class) [MODEL]
NPARTY = 3        # quorum size [MODEL; fhegg deploys 3-of-4 per fhe-core-theory.md]

# ---------------------------------------------------------------- custody variants
def price(mod, native, custody, base, update, r, p, d, L):
    N, logq, limbs, depth_avail, single = MODULI[mod]
    if native and not single:
        return None
    ctct, ctpt, cross, depth_need, params, env = step_ops(update, base, r, d, L, N)
    mult = ZO_STEP_MULT if update == "zo-seeded" else 1
    cert, int_limbs = ctct_certificate_felts(mod, native)
    fct = felts_per_ct(mod, native)
    # Nonlinear work is paid by EVERY custody model: activations forward and derivatives backward (fused with the
    # forward table: DARK-TRAINING 1), 2*L*d per sample-step (ZO: two forwards, also 2*L*d). Each activation in
    # MPC costs KAPPA triples (comparison/lookup for a 16-bit table) [MODEL]; proving it costs KAPPA felts.
    act = 2 * L * d
    lg = math.log2(N)
    W_CTCT = 10 * N * lg * len(limbs)      # mod-mults per ct x ct incl. relin, ~10 NTT-equivalents [MODEL]
    W_CTPT = 4 * N * lg * len(limbs)       # [MODEL]
    nonlin_proof = KAPPA * act
    if custody == "fhe+mpc-boundary":
        proof = ctct * (fct + cert) + ctpt * fct + nonlin_proof
        host = ctct * W_CTCT + ctpt * W_CTPT + act * KAPPA * C_PRE
        online = 2 * NPARTY * (cross * N + act * KAPPA)
        leak = math.log2(max(cross * STEPS * mult, 1)) + smudge_eps_log2(logq)
        dep_ok = depth_avail >= depth_need
    elif custody == "fhe-bootstrap":
        # [READ VERDICTS 3] bootstrapping is dead at deployed parameters (depth 13-17 crossover vs 1-3); kept as a
        # row so its cost is visible: one bootstrap ~ 15 levels of ct x ct work per refreshed ct, and the
        # nonlinearity must be a polynomial (degree <= 2 at t = 2^20 regardless of levels [READ VERDICTS 3]) [MODEL].
        boots = cross
        proof = (ctct + 15 * boots) * (fct + cert) + ctpt * fct + nonlin_proof
        host = (ctct + 15 * boots * (1 + KAPPA)) * W_CTCT + ctpt * W_CTPT
        online = 0
        leak = -999                              # no quorum read per step; custody still tier C at genesis
        dep_ok = depth_avail >= 15 + depth_need
    elif custody == "mpc-only":
        # Weights secret-shared among NPARTY servers. ct x pt-class work (public matrix times shares) is local and
        # MAC-linear; ct x ct-class work (shared x shared) is a Beaver triple per scalar product. Public
        # auditability (BDO14-style commitments to shares) means the auditor re-does linear ops on commitments:
        # 1 felt per linear op, 3 per triple [MODEL].
        triples = ctct * N
        lin = (ctct + ctpt) * N
        proof = 3 * triples + lin + nonlin_proof
        host = lin + (triples + act * KAPPA) * C_PRE
        online = 2 * NPARTY * (triples + act * KAPPA)
        leak = -999                             # no decryption; tier C (full coalition reads)
        dep_ok = True
    elif custody == "tee-plaintext":
        proof = (ctct + ctpt) * N + nonlin_proof
        host = (ctct + ctpt) * N + act * KAPPA
        online = 0
        leak = 0                                # vendor can read: leakage 1 by construction (tier D)
        dep_ok = True
    else:
        raise ValueError(custody)
    # Precision wall [DERIVED, foundations critique F4]: BFV integer state |w| grows additively by the
    # per-step integer factor product; with factor-quantized 4-bit x 4-bit updates (|delta x| <= 2^8) and
    # 8-bit initial weights, steps before wrap of t/2: (2^19 - 2^7)/2^8 ~ 2^11. Fractional learning rates
    # wrap after ~ (19-8)/log2(den) steps. Merge/refresh period must be below the wrap bound.
    if custody in ("fhe+mpc-boundary", "fhe-bootstrap"):
        if update == "zo-seeded":
            wrap_steps = (2 ** (T_BITS - 1) - 2 ** 7) / (2 ** 4)    # 4-bit scalar c times 1-bit (sign) z [MODEL]
        else:
            wrap_steps = (2 ** (T_BITS - 1) - 2 ** 7) / (2 ** 8)
        # the requantizing crossing every step re-centres the state only if the crossing touches the WEIGHTS;
        # in these designs the crossing touches activations, so the weights accumulate until a merge/refresh.
        refresh_period = d / (2 * max(r, 1)) if update in ("append-rank1", "lowrank") else 1
        wrap_ok = wrap_steps >= refresh_period
    else:
        wrap_ok = True
    eps_chk = 2.0 ** EPS_CHK_LOG2
    q = p * (1 - eps_chk) - 2.0 ** EPS_BIND_LOG2 - BEACON_ALPHA * p
    undetected = 1 / q if q > 0 else float("inf")
    pq_ok = custody in ("mpc-only", "tee-plaintext") or logq <= PQ_CEILING[N]
    # read budget gate [MODEL threshold]: union-bounded smudging leakage over the run must be <= 2^-40
    read_ok = leak <= -40
    return dict(mod=mod, native=native, custody=custody, base=base, update=update, r=r, p=p,
                proof_felts=(p * proof + env) * mult, host_work=host * mult, online_elems=online * mult,
                leak_log2=leak, undetected=undetected, params=params, int_limbs=int_limbs,
                gates=dict(pq=pq_ok, depth=dep_ok, wrap=wrap_ok, read=read_ok),
                tier={"fhe+mpc-boundary": "C", "fhe-bootstrap": "C*", "mpc-only": "C", "tee-plaintext": "D"}[custody])

OBJ = ("proof_felts", "host_work", "online_elems", "leak_log2", "undetected")

def dominates(a, b):
    le = all(a[k] <= b[k] for k in OBJ)
    lt = any(a[k] < b[k] for k in OBJ)
    return le and lt

def pareto(rows):
    out = []
    for a in rows:
        if not any(dominates(b, a) for b in rows if b is not a):
            out.append(a)
    return out

def fmt(x):
    if x == float("inf"):
        return "inf"
    if abs(x) >= 1e4:
        return f"{x:.2e}"
    return f"{x:.4g}"

def show(rows, title):
    print(f"\n== {title} ({len(rows)} rows)")
    hdr = f"{'modulus':14} {'pf':3} {'custody':17} {'base':6} {'update':14} {'r':>3} {'p':>6} | " \
          f"{'proof_felts':>10} {'host_work':>9} {'online':>9} {'leak2':>6} {'undet':>7} | gates tier"
    print(hdr)
    for x in rows:
        g = "".join(k[0].upper() if v else "-" for k, v in x["gates"].items())
        print(f"{x['mod']:14} {('nat' if x['native'] else 'bb'):3} {x['custody']:17} {x['base']:6} "
              f"{x['update']:14} {x['r']:>3} {x['p']:>6} | {fmt(x['proof_felts']):>10} {fmt(x['host_work']):>9} "
              f"{fmt(x['online_elems']):>9} {fmt(x['leak_log2']):>6} {fmt(x['undetected']):>7} | {g} {x['tier']}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--d", type=int, default=4096)
    ap.add_argument("--L", type=int, default=32)
    ap.add_argument("--all", action="store_true", help="print every gated row, not only the Pareto set")
    a = ap.parse_args()

    # Controls first: the script refuses to print a frontier if it stops reproducing known counts.
    assert felts_per_ct("RNS3-109@4096", False) == 49152, "Layout-B felts per ct must reproduce cross-limb table"
    assert 3 * 4096 * 109 == 1339392
    print("controls: felts/ct deployed = 49,152 [MEASURED cross-limb-binding.md]; booleanity 3*4096*109 = 1,339,392")

    print("\n-- G1 experiment: Hole-B integer certificate limbs per ct x ct (proof field bits in parentheses)")
    for mod in MODULI:
        for native in (False, True):
            if native and not MODULI[mod][4]:
                continue
            cert, il = ctct_certificate_felts(mod, native)
            N, logq = MODULI[mod][0], MODULI[mod][1]
            pb = logq if native else 31
            zb = math.log2(N) + 2 * logq + 1 + T_BITS
            print(f"   {mod:14} proof field {pb:3}b: |t*z| ~ 2^{zb:.0f}, integer limbs {il}, "
                  f"certificate felts {cert:,}, ct felts {felts_per_ct(mod, native):,}, "
                  f"PQ-128 {'yes' if logq <= PQ_CEILING[N] else 'NO'}")

    rows = []
    for mod, native, custody, base, update, p in itertools.product(
            MODULI, (False, True), ("fhe+mpc-boundary", "fhe-bootstrap", "mpc-only", "tee-plaintext"),
            ("dark", "public"), ("backprop-full", "append-rank1", "lowrank", "zo-seeded"), (1, 0.1, 0.01, 0.001)):
        ranks = (8, 16, 64) if update == "lowrank" else ((0, 16) if update == "zo-seeded" else (1,))
        for r in ranks:
            if custody in ("mpc-only", "tee-plaintext") and (mod != "RNS3-109@4096" or native):
                continue                         # modulus is irrelevant without FHE: keep one copy
            x = price(mod, native, custody, base, update, r, p, a.d, a.L)
            if x is not None:
                if custody in ("mpc-only", "tee-plaintext"):
                    x["mod"] = "n/a"
                rows.append(x)
    print(f"\nenumerated {len(rows)} constructions at d={a.d}, L={a.L}")
    gated = [x for x in rows if all(x["gates"].values())]
    failed = {k: sum(1 for x in rows if not x["gates"][k]) for k in ("pq", "depth", "wrap", "read")}
    print(f"gate failures: {failed}; passing all gates: {len(gated)}")
    dark = [x for x in gated if x["tier"] in ("C", "C*")]
    front = pareto(dark)
    front.sort(key=lambda x: (x["proof_felts"], x["host_work"]))
    show(front, "PARETO SET, tier C custody (weights never in one party's clear), all gates passing")
    if a.all:
        show(sorted(gated, key=lambda x: x["proof_felts"]), "all gated rows")
    print("\n-- gate failures by custody (a row can fail several gates)")
    for c in ("fhe+mpc-boundary", "fhe-bootstrap", "mpc-only", "tee-plaintext"):
        cr = [x for x in rows if x["custody"] == c]
        print(f"   {c:17} rows {len(cr):4}  " + "  ".join(f"{k}:{sum(1 for x in cr if not x['gates'][k])}" for k in ("pq", "depth", "wrap", "read")))
    print("\n-- best gated tier-C point per update family at p=0.01 (by proof_felts), and who dominates it")
    for u in ("backprop-full", "append-rank1", "lowrank", "zo-seeded"):
        cand = [x for x in dark if x["update"] == u and x["p"] == 0.01]
        if not cand:
            why = [x for x in rows if x["update"] == u and x["tier"] in ("C", "C*") and x["p"] == 0.01]
            fails = {k: sum(1 for x in why if not x["gates"][k]) for k in ("pq", "depth", "wrap", "read")}
            print(f"   {u:14} NO gated tier-C point; failures over {len(why)} rows: {fails}")
            continue
        b = min(cand, key=lambda x: x["proof_felts"])
        dom = [y for y in dark if dominates(y, b)]
        show([b], f"{u}: best; dominated by {len(dom)} gated rows")
    print("\n-- THE WELFARE PRICE: cheapest gated tier-C point with the WHOLE model dark (base=dark), per custody, p=0.01")
    pub = min((x for x in dark if x["p"] == 0.01), key=lambda x: x["proof_felts"])
    for c in ("fhe+mpc-boundary", "mpc-only", "fhe-bootstrap"):
        cand = [x for x in dark if x["base"] == "dark" and x["custody"] == c and x["p"] == 0.01]
        if not cand:
            print(f"   {c:17} none passes the gates")
            continue
        b = min(cand, key=lambda x: x["proof_felts"])
        show([b], f"{c}: fully dark; x{b['proof_felts']/pub['proof_felts']:.1f} proof felts, "
                  f"x{b['online_elems']/max(pub['online_elems'],1):.1f} online vs best public-trunk point")
    # the deployed point, so its distance from the frontier is explicit
    dep = [x for x in rows if x["mod"] == "RNS3-109@4096" and not x["native"] and x["custody"] == "fhe+mpc-boundary"
           and x["base"] == "dark" and x["update"] == "backprop-full" and x["p"] == 0.01]
    show(dep, "DEPLOYED-PARAMETER reference point (fails PQ; shown regardless)")
    print("\n-- audit-rate knee: undetected displacement (units of B) vs amortized proof felts, p61 native, public base, lowrank r=16")
    for p in (1, 0.1, 0.01, 0.001):
        x = price("p61@4096", True, "fhe+mpc-boundary", "public", "lowrank", 16, p, a.d, a.L)
        print(f"   p={p:<6} proof_felts/step={fmt(x['proof_felts']):>10}  E[undetected]={fmt(x['undetected'])}")

if __name__ == "__main__":
    main()
