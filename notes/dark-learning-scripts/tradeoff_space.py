#!/usr/bin/env python3
"""Dark-learning construction space: enumerate, price in COUNTS, print Pareto sets per opacity regime.

2026-11-05, v2. v1 (commit 9443850d) was attacked by Codex round 2 (notes/dark-learning-codex-synthesis.md);
v2 repairs the defects it found: dense-product double count, public full-update status, packing tiles and
the t-wrap of split dot products, minimum crossing counts, split-sign ct x pt doubling, low-rank depth,
append-only backward traversal, weight-refresh charges for dense updates, an UNCONDITIONAL envelope priced
as proof work, a smudging ledger instead of a log-Q step function, 2B/q, and frontiers separated by
opacity regime. What v2 still is: a counts model with named constants, for SHAPE, not a price list.

No clocks. Tags: [MEASURED] our harness, [DERIVED] here, [CLAIM] outside, [MODEL] a choice of this script.
Run: python3 notes/dark-learning-scripts/tradeoff_space.py [--d 4096 --L 32 --all]
"""
import argparse
import itertools
import math

# ---------------------------------------------------------------- parameters
MODULI = {
    # name: (N, log2 Q, residue limb bit widths, depth between crossings, single_prime)
    # depth 2 at deployed RNS3-109 [MEASURED kpz-noop note, 40/40]; others [MODEL]: a ct x ct level costs
    # 33-42 bits at the deployed ring [MEASURED]; 61 - 20 (t) - ~4 (fresh) leaves ~one level.
    "RNS3-109@4096": (4096, 109, (36, 36, 37), 2, False),
    "p61@4096":      (4096, 61, (61,), 1, True),
    "gold64@4096":   (4096, 64, (64,), 1, True),
    "RNS-202@8192":  (8192, 202, (34, 34, 34, 34, 33, 33), 4, False),
}
# quantum-128 log2 Q ceilings, ternary secret, HE Standard v1.1 printed p.31 BKZ.qsieve table [CLAIM, page
# located by Codex round 2]. They do NOT certify the deployed CBD(20) secret or evaluation keys: a pass here
# is "conditionally PQ", never "PQ verified".
PQ_CEILING = {4096: 101, 8192: 202, 16384: 411}
T = 1032193                  # deployed plaintext modulus [MEASURED]
T_BITS = 20
W_BITS, A_BITS = 4, 4        # integer recipe: signed 4-bit weights-or-factors and activations (F1) [MODEL]
BRIDGE_BITS = 30             # 2-felt base-2^30 BabyBear bridge per residue (mle_gpu.rs:479) [READ]
LOOKUP_BITS = 16             # LogUp range-check limb width [MODEL]
EPS_CHK_LOG2 = -100          # [MODEL; deployed FRI is 34 bits at UDR (VERDICTS 2): not quotable]
EPS_BIND_LOG2 = -120         # [MODEL]
BEACON_ALPHA = 0.05          # eps_beacon <= alpha * p [MODEL]
STEPS = 10 ** 6
NPARTY = 3                   # quorum size [MODEL]
KAPPA = 40                   # triples / proof felts per nonlinear activation [MODEL]
C_PRE = 100                  # host mod-mults to preprocess one triple [MODEL]
ZO_STEP_MULT = 12            # [CLAIM MeZO-class step overhead; not an equal-utility comparison]
SMUDGE_E_LOG2 = 32           # ciphertext-noise envelope fed to the smudging window [READ Smudging.lean:330-376
                             # proves the window at E = 2^32; NOT established for training ct x ct outputs]

# ---------------------------------------------------------------- per-ciphertext proof cost
def felts_per_ct(mod, native):
    N, logq, limbs, _, single = MODULI[mod]
    if native and single:
        return 2 * N
    return 2 * N * sum(math.ceil(b / BRIDGE_BITS) for b in limbs)   # 49,152 at deployed [MEASURED table]

def ctct_certificate_felts(mod, native):
    """Hole B: integer quotient-remainder certificate for round(t z / Q); |t z| ~ N (Q/2)^2 * 2 * t [DERIVED].
    Capacity count, not a lower bound on every protocol (Codex round 1)."""
    N, logq, limbs, _, single = MODULI[mod]
    pbits = logq if (native and single) else 31
    zbits = math.log2(N) + 2 * logq + 1
    int_limbs = math.ceil((zbits + T_BITS) / (pbits - 1))
    range_felts = 3 * N * (math.ceil(logq / LOOKUP_BITS) + math.ceil((zbits + T_BITS - logq) / LOOKUP_BITS))
    return 3 * N * int_limbs + range_felts, int_limbs

# ---------------------------------------------------------------- packing (Codex round 2 b, c)
def k_wrap():
    """Longest dot product whose signed integer sum stays inside (t-1)/2 [READ bfv_coeff_matmul.rs:45-108]."""
    return ((T - 1) // 2) // ((2 ** (W_BITS - 1) - 1) * (2 ** (A_BITS - 1) - 1))

def matvec_tiles(rows, inner, N):
    """Coefficient-encoded matvec, rows x inner: window k = min(inner, N, k_wrap); floor(N/k) outputs per
    polynomial product; returns (ct ops, partial-sum ciphertexts that must leave BFV to be summed)."""
    k = min(inner, N, k_wrap())
    per_poly = max(1, N // k)
    ops = math.ceil(inner / k) * math.ceil(rows / per_poly)
    pieces = math.ceil(inner / k)
    leave = ops if pieces > 1 else 0         # split dot products are summed outside BFV (wrap), each crosses
    return ops, leave

# ---------------------------------------------------------------- per-step op counts
def step_ops(update, base, r, d, L, N):
    """Per step, all L layers. Returns dict: ctct, ctpt (split-sign doubled), cross (ciphertext crossings),
    depth needed, env (factor entries the unconditional envelope must bound), dense_update."""
    mv, leave = matvec_tiles(d, d, N)
    thin_ops, thin_leave = matvec_tiles(r if r else 1, d, N)
    base_cross = 2 * math.ceil(d / N)        # forward and backward, compacted minimum (Codex round 2 c)
    out = dict(ctct=0.0, ctpt=0.0, cross=0.0, depth=1, env=0, dense_update=False)
    pub = base == "public"
    if update == "backprop-full":
        # dark: fwd, bwd, update = 3 secret dense products. public trunk: W = W0 + D with D secret after the
        # first step: fwd and bwd each = W0 (public) + D (secret); update secret -> 3 secret + 2 public.
        out["ctct"] = 3 * mv
        out["ctpt"] = 2 * mv if pub else 0
        out["cross"] = base_cross + 2 * leave
        out["env"] = 2 * d
        out["dense_update"] = True
    elif update == "append-rank1":
        H = d / 4                                     # live factors between merges, merge at d/2 [MODEL]
        hist = 4 * H * d / N                          # forward + backward traverse the history (Codex f)
        out["ctct"] = hist + mv + (0 if pub else 2 * mv)   # + amortized merge outer products (+ dark base)
        out["ctpt"] = 2 * mv if pub else 0
        out["cross"] = base_cross + 2 * leave
        out["depth"] = 2
        out["env"] = 2 * d
    elif update == "lowrank":
        # A (d x r), B (r x d) secret; A(Bx) is depth 2 (Codex e). fwd, bwd, grads: 3 x (B-side + A-side).
        thin = 2 * thin_ops
        out["ctct"] = 3 * thin + (0 if pub else 2 * mv)
        out["ctpt"] = 2 * mv if pub else 0
        out["cross"] = base_cross + 2 * leave + 2 * thin_leave
        out["depth"] = 2
        out["env"] = 2 * r * d                        # Delta(AB) = dA B + A dB + dA dB: bound all factor rows
    elif update == "zo-seeded":
        if r:                                          # ZO on an adapter
            thin = 2 * thin_ops
            out["ctct"] = 2 * thin + (0 if pub else 2 * mv)
            out["ctpt"] = (2 * mv if pub else 0) + 2 * r * d / N
            out["env"] = 1
        else:                                          # full-parameter ZO: accumulated secret D (Codex a)
            out["ctct"] = 2 * mv
            out["ctpt"] = (2 * mv if pub else 0) + d * d / N    # c * z, public z
            out["env"] = 1
            out["dense_update"] = True
        out["cross"] = base_cross + 2 * leave
        out["depth"] = 2
    else:
        raise ValueError(update)
    out["ctpt"] *= 2                                   # split-sign W+ v, W- v (bfv_coeff_matmul.rs:17-36)
    for k in ("ctct", "ctpt", "cross", "env"):
        out[k] *= L
    return out

def wrap_steps():
    """Steps before integer weight state wraps t/2, accumulating 4x4-bit factor products onto 4-bit weights
    (F1, factor-quantized integer updates). [DERIVED]"""
    return ((T - 1) // 2 - 2 ** (W_BITS - 1)) // ((2 ** (W_BITS - 1) - 1) ** 2)

def smudge_event_log2(logq, N):
    """Per crossing event: eps_scalar ~ E/S with E + n S below the margin Q/(2t), times n N exposed scalar
    shares (Codex round 2 i). [MODEL]"""
    margin_log2 = logq - 1 - T_BITS
    s_log2 = margin_log2 - math.log2(NPARTY + 1)
    eps_scalar = SMUDGE_E_LOG2 - s_log2
    return eps_scalar + math.log2(NPARTY * N)

# ---------------------------------------------------------------- pricing
def price(mod, native, custody, base, update, r, p, d, L):
    N, logq, limbs, depth_avail, single = MODULI[mod]
    if native and not single:
        return None
    o = step_ops(update, base, r, d, L, N)
    mult = ZO_STEP_MULT if update == "zo-seeded" else 1
    cert, _ = ctct_certificate_felts(mod, native)
    fct = felts_per_ct(mod, native)
    act = 2 * L * d
    lg = math.log2(N)
    W_CTCT = 10 * N * lg * len(limbs)
    W_CTPT = 4 * N * lg * len(limbs)
    nonlin_proof = KAPPA * act
    ws = wrap_steps()
    if custody in ("fhe+mpc-boundary", "fhe-bootstrap"):
        # dense secret updates must refresh the weights (a requantizing dense crossing, d^2/N ciphertexts per
        # layer) at least every wrap_steps steps; refreshing noise does not reduce magnitude [Codex round 2 g].
        weight_refresh = (L * d * d / N) / ws if o["dense_update"] else 0
        cross = o["cross"] + weight_refresh
        # unconditional envelope on ciphertexts: square every factor entry (ct x ct) and prove it [Codex h]
        env_ctct = 2 * math.ceil(o["env"] / N)
        envelope = env_ctct * (fct + cert)
        step_proof = o["ctct"] * (fct + cert) + o["ctpt"] * fct + nonlin_proof
        if custody == "fhe+mpc-boundary":
            host = o["ctct"] * W_CTCT + o["ctpt"] * W_CTPT + act * KAPPA * C_PRE
            online = 2 * NPARTY * (cross * N + act * KAPPA)
            events = cross * STEPS * mult
            leak = math.log2(max(events, 1)) + smudge_event_log2(logq, N)
            dep_ok = depth_avail >= o["depth"]
        else:
            boots = cross
            step_proof += 15 * boots * (fct + cert)
            host = (o["ctct"] + 15 * boots * (1 + KAPPA)) * W_CTCT + o["ctpt"] * W_CTPT
            online, leak = 0, -999
            dep_ok = depth_avail >= 15 + o["depth"]
        # append-only histories must merge before the integer state wraps; dense updates are charged a
        # refresh at the wrap period above, so they pass this gate by construction
        wrap_ok = (ws >= d / 2) if update == "append-rank1" else True
    elif custody == "mpc-only":
        triples = o["ctct"] * N
        lin = (o["ctct"] + o["ctpt"] / 2) * N            # no split-sign doubling on shares (Codex d)
        step_proof = 3 * triples + lin + nonlin_proof
        envelope = 3 * o["env"]                          # squares of shared factor entries
        host = lin + (triples + act * KAPPA) * C_PRE
        online = 2 * NPARTY * (triples + act * KAPPA)
        leak, dep_ok, wrap_ok = -999, True, True         # integer truncation semantics still owed (Codex g)
    elif custody == "tee-plaintext":
        step_proof = (o["ctct"] + o["ctpt"] / 2) * N + nonlin_proof
        envelope = o["env"]
        host = (o["ctct"] + o["ctpt"] / 2) * N + act * KAPPA
        online, leak, dep_ok, wrap_ok = 0, 0, True, True
    else:
        raise ValueError(custody)
    q = p * (1 - 2.0 ** EPS_CHK_LOG2) - 2.0 ** EPS_BIND_LOG2 - BEACON_ALPHA * p
    undetected = 2 / q if q > 0 else float("inf")         # 2B/q: both updates capped (Codex rounds 1, 2)
    pq_ok = custody in ("mpc-only", "tee-plaintext") or logq <= PQ_CEILING[N]
    read_ok = leak <= -40
    total = p * step_proof + envelope
    return dict(mod=mod, native=native, custody=custody, base=base, update=update, r=r, p=p,
                proof_felts=total * mult, host_work=host * mult,
                online_elems=online * mult, leak_log2=leak, undetected=undetected,
                envelope_share=envelope / max(total, 1),
                gates=dict(pq=pq_ok, depth=dep_ok, wrap=wrap_ok, read=read_ok),
                tier={"fhe+mpc-boundary": "C", "fhe-bootstrap": "C*", "mpc-only": "C", "tee-plaintext": "D"}[custody])

OBJ = ("proof_felts", "host_work", "online_elems", "leak_log2", "undetected")

def dominates(a, b):
    return all(a[k] <= b[k] for k in OBJ) and any(a[k] < b[k] for k in OBJ)

def pareto(rows):
    return [a for a in rows if not any(dominates(b, a) for b in rows if b is not a)]

def fmt(x):
    if x == float("inf"):
        return "inf"
    if abs(x) >= 1e4:
        return f"{x:.2e}"
    return f"{x:.4g}"

def show(rows, title):
    print(f"\n== {title} ({len(rows)} rows)")
    print(f"{'modulus':14} {'pf':3} {'custody':17} {'base':6} {'update':14} {'r':>3} {'p':>6} | "
          f"{'proof_felts':>10} {'host_work':>9} {'online':>9} {'leak2':>7} {'undet':>7} {'env%':>5} | gates tier")
    for x in rows:
        g = "".join(k[0].upper() if v else "-" for k, v in x["gates"].items())
        print(f"{x['mod']:14} {('nat' if x['native'] else 'bb'):3} {x['custody']:17} {x['base']:6} "
              f"{x['update']:14} {x['r']:>3} {x['p']:>6} | {fmt(x['proof_felts']):>10} {fmt(x['host_work']):>9} "
              f"{fmt(x['online_elems']):>9} {fmt(x['leak_log2']):>7} {fmt(x['undetected']):>7} "
              f"{100*x['envelope_share']:5.1f} | {g} {x['tier']}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--d", type=int, default=4096)
    ap.add_argument("--L", type=int, default=32)
    ap.add_argument("--all", action="store_true")
    a = ap.parse_args()

    assert felts_per_ct("RNS3-109@4096", False) == 49152, "cross-limb table control"
    assert 3 * 4096 * 109 == 1339392
    # control against bfv_coeff_matmul.rs: signed 4 x 8-bit at deployed t gives inner dim 504 [READ via Codex]
    assert ((T - 1) // 2) // (7 * 127 + 137) <= 504 + 100
    print("controls: felts/ct deployed = 49,152; booleanity 3*4096*109 = 1,339,392; "
          f"k_wrap at signed {W_BITS}x{A_BITS}-bit = {k_wrap():,}; wrap_steps = {wrap_steps():,}")

    print("\n-- G1: Hole-B integer certificate per ct x ct")
    for mod in MODULI:
        for native in (False, True):
            if native and not MODULI[mod][4]:
                continue
            cert, il = ctct_certificate_felts(mod, native)
            N, logq = MODULI[mod][0], MODULI[mod][1]
            print(f"   {mod:14} {'native' if native else 'BabyBear':8}: integer limbs {il:2}, certificate felts "
                  f"{cert:>9,}, ct felts {felts_per_ct(mod, native):>7,}, quantum-128 table "
                  f"{'pass (conditional)' if logq <= PQ_CEILING[N] else 'FAIL'}, smudge per event "
                  f"2^{smudge_event_log2(logq, N):.1f}")

    rows = []
    for mod, native, custody, base, update, p in itertools.product(
            MODULI, (False, True), ("fhe+mpc-boundary", "fhe-bootstrap", "mpc-only", "tee-plaintext"),
            ("dark", "public"), ("backprop-full", "append-rank1", "lowrank", "zo-seeded"), (1, 0.1, 0.01, 0.001)):
        ranks = (8, 16, 64) if update == "lowrank" else ((0, 16) if update == "zo-seeded" else (1,))
        for r in ranks:
            if custody in ("mpc-only", "tee-plaintext") and (mod != "RNS3-109@4096" or native):
                continue
            x = price(mod, native, custody, base, update, r, p, a.d, a.L)
            if x is not None:
                if custody in ("mpc-only", "tee-plaintext"):
                    x["mod"] = "n/a"
                rows.append(x)
    gated = [x for x in rows if all(x["gates"].values())]
    failed = {k: sum(1 for x in rows if not x["gates"][k]) for k in ("pq", "depth", "wrap", "read")}
    print(f"\nenumerated {len(rows)} constructions at d={a.d}, L={a.L}; passing all gates: {len(gated)}; "
          f"gate failures {failed}")
    print("-- gate failures by custody")
    for c in ("fhe+mpc-boundary", "fhe-bootstrap", "mpc-only", "tee-plaintext"):
        cr = [x for x in rows if x["custody"] == c]
        print(f"   {c:17} rows {len(cr):4}  " + "  ".join(
            f"{k}:{sum(1 for x in cr if not x['gates'][k])}" for k in ("pq", "depth", "wrap", "read")))

    tierC = [x for x in gated if x["tier"] in ("C", "C*")]
    for regime in ("dark", "public"):
        sub = [x for x in tierC if x["base"] == regime]
        front = sorted(pareto(sub), key=lambda x: (x["proof_felts"], x["host_work"]))
        show(front, f"PARETO SET, tier C, base={regime} (separate frontier per opacity regime)")
    print("\n-- the opacity price WITHIN each custody (fully dark vs public trunk, cheapest gated, p=0.01)")
    for c in ("fhe+mpc-boundary", "mpc-only"):
        dk = [x for x in tierC if x["custody"] == c and x["base"] == "dark" and x["p"] == 0.01]
        pb = [x for x in tierC if x["custody"] == c and x["base"] == "public" and x["p"] == 0.01]
        if not dk or not pb:
            print(f"   {c:17} missing a gated row (dark {len(dk)}, public {len(pb)})")
            continue
        bd = min(dk, key=lambda x: x["proof_felts"]); bp = min(pb, key=lambda x: x["proof_felts"])
        print(f"   {c:17} proof x{bd['proof_felts']/bp['proof_felts']:.1f}, host x{bd['host_work']/bp['host_work']:.1f}, "
              f"online x{bd['online_elems']/max(bp['online_elems'],1):.1f}  ({bd['update']} r={bd['r']} vs {bp['update']} r={bp['r']})")
    if a.all:
        show(sorted(gated, key=lambda x: x["proof_felts"]), "all gated rows")
    dep = [x for x in rows if x["mod"] == "RNS3-109@4096" and not x["native"] and x["custody"] == "fhe+mpc-boundary"
           and x["base"] == "dark" and x["update"] == "backprop-full" and x["p"] == 0.01]
    show(dep, "DEPLOYED-PARAMETER reference point")
    print("\n-- audit-rate knee with the envelope charged (RNS-202@8192, FHE+MPC, public, lowrank r=16)")
    for p in (1, 0.1, 0.01, 0.001):
        x = price("RNS-202@8192", False, "fhe+mpc-boundary", "public", "lowrank", 16, p, a.d, a.L)
        print(f"   p={p:<6} proof_felts/step={fmt(x['proof_felts']):>10}  envelope share={100*x['envelope_share']:5.1f}%  "
              f"E[undetected injected]={fmt(x['undetected'])} B")

if __name__ == "__main__":
    main()
