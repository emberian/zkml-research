"""Schedule-level counts of one dark training step at any width d, both forks. Counts only.

2026-11-06. The d = 4096 step cannot be executed in pure Python (one FHE matvec is 2,048 certified ct x ct;
one MPC matvec opens 16.7 M masked values). So this file replays the step's PROTOCOL SCHEDULE and
charges each primitive its count:
  - SPDZ primitives (input, matvec, trunc, lookup, mul, outer, MAC check): exact per-call counts read off
    spdz.py;
  - the B61 ct x ct certificate and the partial-decryption proof: cert_b61.counts / e2s_proof.counts;
  - ciphertexts: 2 or 3 components of N L elements.
CONTROL: `python3 step_counts.py --validate` reproduces every count column of the EXECUTED runs exactly
(d64_results_mpc.json, d64_results_fhe.json, and the MPC fork executed at d = 16 and 32 by this file).
Exact agreement at the executed widths is the evidence that the schedule is the protocol. The FHE block
layout used above d = 64 is checked separately by executing one block of each kind at N = 8192
(`--layout-check`).

Recipe at width d (step_spec's integer learner, shifts widened so every truncation input stays in its
bit budget): |W|, |x|, |y| <= 7, S1 = ceil(log2(49 d / 128)), K1 = S1 + 8; S2 = 4, K2 = 8;
S3 = S1 + 3, K3 = K1. At d = 64 this is S1 = 5, K1 = 13, S3 = 8 (step_spec's constants).

FHE block layout (coefficient encoding): d_c = min(d, 64) columns by d_r = min(d, N / 64) rows per
ciphertext, row-major at coefficient 64 i + j. Forward: block x rev(x-block) puts row i's partial dot
product at coefficient 64 i + 63. Backward: block x colrev(e-block) puts column j at coefficient
64 (d_r - 1) + j. Homomorphic sums over the other block index precede each crossing. The update is SPDZ
outer + masked S2E (as built at d = 64); variant (b) is a homomorphic outer product plus relinearization,
priced by MODEL.
"""
import json
import math
import sys

N_PARTY = 3

def params(d):
    S1 = max(5, math.ceil(math.log2(49 * d / 128)))
    return dict(S1=S1, K1=S1 + 8, S2=4, K2=8, S3=S1 + 3, K3=S1 + 8)

class Tally:
    def __init__(self, n=N_PARTY):
        self.n = n
        self.wire = {}
        self.prep = 0          # authenticated preprocessed values (dealer.count)
        self.opens = 0         # eng.nopen

    def w(self, ph, k):
        self.wire[ph] = self.wire.get(ph, 0) + k

    def open(self, ph, k=1):
        self.opens += k
        self.w(ph, k * self.n * (self.n - 1))

    # spdz.py primitives
    def input(self, k):
        self.prep += k
        self.w("input", k * self.n)

    def matvec(self, d):
        self.prep += d * d + 2 * d
        self.open("matvec", d * d + d)

    def mul(self, k=1, ph="mul"):
        self.prep += 3 * k
        self.open(ph, 2 * k)

    def trunc(self, s, k=1):
        self.prep += (2 + s) * k
        self.open("trunc", k)
        self.mul(2 * (s - 1) * k)

    def lookup(self, k, deg=255):
        self.prep += deg * k
        self.open("lookup", k)

    def outer(self, d1, d2):
        self.prep += d1 + d2 + d1 * d2
        self.open("outer", d1 + d2)

    def auth(self, k):           # auth_plain: one prep + one broadcast round
        self.prep += k
        self.open("auth", k)

    def mac_check(self):
        self.w("mac_check", 2 * self.n * (self.n - 1))

def spdz_core(T, d, P):
    """The nonlinear middle of the step, shared by both forks (after z1 / z2 / b are shared)."""
    T.trunc(P["S1"], d)              # u1
    T.lookup(d)                      # (h, g1)
    T.trunc(P["S1"], d)              # e
    T.trunc(P["S2"], d)              # d2
    T.mul(d)                         # b * g1
    T.trunc(P["S3"], d)              # d1
    T.outer(d, d)                    # G2
    T.outer(d, d)                    # G1

def mpc_counts(d, pbits=61):
    P = params(d)
    T = Tally()
    T.input(2 * d * d + 2 * d)
    T.matvec(d)                      # z1
    T.matvec(d)                      # z2
    T.matvec(d)                      # b (transpose)
    spdz_core(T, d, P)
    T.mac_check()
    n = T.n
    view = T.prep * n * 2
    gen = 2 * d * d                                # genesis input of W1, W2 (absent in a continuing run)
    steady = dict(committed_bits=(T.prep - gen) * n * 2 * pbits, online_wire=sum(T.wire.values()) - gen * n,
                  preprocessing_elems=(T.prep - gen) * 2 * n)
    return dict(steady=steady, committed_elems=view, committed_bits=view * pbits, online_wire=sum(T.wire.values()),
                wire_by_phase=T.wire, preprocessing_auth_values=T.prep, preprocessing_elems=T.prep * 2 * n,
                openings=T.opens, crossings=0, params=P)

def fhe_layout(d, N):
    dc = min(d, 64)
    dr = min(d, N // 64)
    assert d % dc == 0 and d % dr == 0
    return dc, dr, (d // dr) * (d // dc)

def fhe_counts(d, N, Qp, Bp, E, variant="a", pbits=61):
    import cert_b61 as C
    import e2s_proof as PD
    P = params(d)
    L = len(Qp)
    n = N_PARTY
    dc, dr, nb = fhe_layout(d, N)
    T = Tally()
    pd = dict(proofs=0, elems=0, bits=0, range_lookups=0, openings=0)
    cust_wire = {}
    prep_ct = 0
    masks = dict(pairs=0, used=0)
    def e2s(values, comps, count=1):
        nonlocal prep_ct
        for _ in range(count):
            masks["pairs"] += 1
            masks["used"] += values
            T.prep += values                     # mask shares [R_k]
            prep_ct += 2 * N * L
            c = PD.counts(N, Qp, E, comps)
            for _ in range(n):
                pd["proofs"] += 1
                for k in ("elems", "bits", "range_lookups", "openings"):
                    pd[k] += c["pd_" + k]
                cust_wire["E2S"] = cust_wire.get("E2S", 0) + N * L
    def s2e(values, cts):
        nonlocal prep_ct
        masks["pairs"] += cts
        masks["used"] += values
        T.prep += values
        T.open("S2E", values)
        prep_ct += 2 * N * L * cts
    ny = math.ceil(d / N)
    two_comp = 2 * nb + d // dc + ny            # owner: W1, W2, x blocks, y
    prods = 0
    # z1 = W1 x
    prods += nb
    e2s(dr, 3, d // dr)                          # one crossing per row block, d_r values each
    e2s(dc, 2, d // dc)                          # x
    # nonlinear middle (u1, lookup) happens inside spdz_core; S2E of h in rev blocks
    s2e(d, d // dc); two_comp += d // dc
    prods += nb                                  # z2 = W2 h
    e2s(dr, 3, d // dr)
    e2s(min(d, N), 2, ny)                        # y
    if variant == "a":
        s2e(d * d, nb); two_comp += nb           # dW2 = d2 (x) h by SPDZ outer, masked S2E
    s2e(d, d // dr); two_comp += d // dr         # d2 in colrev blocks
    prods += nb                                  # b = W2^T d2
    e2s(dc, 3, d // dc)
    if variant == "a":
        s2e(d * d, nb); two_comp += nb           # dW1
    spdz_core(T, d, P)
    relin = 0
    if variant == "b":
        # homomorphic outer products: S2E of d1 (row layout) and x (column layout) blocks, nb ct x ct per
        # layer, each relinearized; the SPDZ outer products are not needed for the weights
        T.prep -= 2 * (d + d + d * d)            # remove the two SPDZ outer products ...
        T.opens -= 4 * d
        T.wire["outer"] -= 4 * d * n * (n - 1)
        s2e(d, d // dr); s2e(d, d // dc); s2e(d, d // dr); s2e(d, d // dc)
        two_comp += 2 * (d // dr + d // dc)
        prods += 2 * nb
        relin = 2 * nb
    two_comp += 2 * nb                           # new W1, W2
    T.mac_check()
    cc = C.counts(N, Qp, Bp)
    ct_elems = two_comp * 2 * N * L + prods * 3 * N * L
    view = T.prep * n * 2
    relin_elems = relin * cc["cert_elems"]       # MODEL: one key-switch certificate ~ one ct x ct certificate
    relin_bits = relin * cc["cert_bits"]
    committed = ct_elems + prods * cc["cert_elems"] + view + pd["elems"] + relin_elems
    bits = ct_elems * pbits + prods * cc["cert_bits"] + view * pbits + pd["bits"] + relin_bits
    host_wire = (2 * (d // dr) + d // dc) * 3 * N * L
    wire = dict(cust_wire)
    wire.update(T.wire)
    wire["host->custodians"] = host_wire
    digit_bits = prods * cc["range_lookups"] * 16    # certificate range digits (16-bit), not in committed_bits
    steady = dict(committed_bits=bits + digit_bits - 2 * nb * 2 * N * L * pbits, online_wire=sum(wire.values()),
                  preprocessing_elems=T.prep * 6 + prep_ct)
    pd_digits = pd["range_lookups"]
    steady["committed_bits_digits61"] = steady["committed_bits"] + 45 * (digit_bits // 16 + pd_digits)
    mk = mask_nonideal(N, L, masks["pairs"], masks["used"], n)
    nonideal = dict(committed_bits=steady["committed_bits"] + mk["committed_bits16"],
                    committed_bits_digits61=steady["committed_bits_digits61"] + mk["committed_bits61"],
                    online_wire=steady["online_wire"], offline_wire=mk["wire"],
                    preprocessing_elems=steady["preprocessing_elems"] - prep_ct + mk["prep_auth_values"] * 2 * n)
    return dict(steady=steady, nonideal_masks=nonideal, mask_pairs=masks, mask_cost=mk, certificate_digit_bits=digit_bits,
                committed_elems=committed, committed_bits=bits, online_wire=sum(wire.values()),
                wire_by_phase=wire, preprocessing_auth_values=T.prep,
                preprocessing_elems=T.prep * 6 + prep_ct, preprocessing_mask_ct_elems=prep_ct,
                openings=T.opens, ct_x_ct=prods, relinearizations=relin, pd_proofs=pd["proofs"],
                pd_elems=pd["elems"], pd_bits=pd["bits"], layout=dict(d_c=dc, d_r=dr, blocks=nb), params=P)

def mask_nonideal(N, L, pairs, used, n=N_PARTY, pbits=61):
    """MODEL: the mask pairs (Enc(R), [R_k]) generated by the custodians instead of an ideal dealer.
    Per pair, each custodian i:
      - posts Enc_pk(R_i) under the joint public key (2 N L elements), using EXACT scaling
        round(Q R_i / t) = Delta R_i + c_i, c_i = round(r R_i / t) with r = Q mod t, so the F2 fix holds
        for the sum;
      - proves it well formed: per prime the two component identities with native quotients
        (2 L (N - 1) elements) and 16-bit digits for R_i (4), c_i (4), the rounding remainder of c_i (4),
        u (1), e0 (1), e1 (1): 15 N digits; the c_i relation t c_i = r R_i + rem is checked modulo two
        auxiliary primes (counted in the digits);
      - SPDZ-inputs R_i[k] for the used coefficients (1 preprocessed mask + n broadcast elements each),
        so [R_k] = sum_i [R_i[k]];
      - links them to its committed R_i by one batched check (a sacrificed random input, 1 opening): O(1).
    The joint public key and the key commitments are long-term and excluded."""
    ct = n * 2 * N * L * pairs
    k_el = n * pairs * 2 * L * (N - 1)
    digits = n * pairs * 15 * N
    inputs = n * used
    wire = ct + inputs * n + n * pairs * n * (n - 1)
    return dict(wire=wire, posted_ct_elems=ct, proof_native_elems=k_el, proof_digits=digits,
                committed_bits16=k_el * pbits + digits * 16, committed_bits61=(k_el + digits) * pbits,
                prep_auth_values=inputs + n * pairs)

def fhe_params(N=8192):
    import fhe_fork as FF
    sch, Qp, Bp, t = FF.setup(N=N)
    E = (sch.Q // (2 * t)) // (8 * N_PARTY)
    return Qp, Bp, E

KEYS = ("committed_elems", "committed_bits", "online_wire", "preprocessing_auth_values",
        "preprocessing_elems", "openings")

def validate():
    import random
    import bfv_ref as bfv
    import spdz
    import mpc_fork as MF
    import step_spec as S
    p = bfv.ntt_primes(61, 4, 16384)[3]
    tab = MF.tables(p)
    ok = True
    for d in (16, 32):
        rng = random.Random(d)
        W1 = [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
        W2 = [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
        x = [rng.randint(-7, 7) % p for _ in range(d)]
        y = [rng.randint(-7, 7) % p for _ in range(d)]
        dealer = spdz.Dealer(p, 3, 5)
        eng = spdz.Engine(p, 3, dealer)
        MF.run_step(eng, W1, W2, x, y, tab, 9)
        eng.mac_check("v")
        got = dict(committed_elems=sum(len(s) for s in dealer.streams) * 2, online_wire=sum(eng.wire.values()),
                   preprocessing_auth_values=dealer.count, openings=eng.nopen)
        want = mpc_counts(d)
        for k, v in got.items():
            good = v == want[k]
            ok &= good
            print(f"MPC d={d:3d} {k:28s} executed {v:>12,}  schedule {want[k]:>12,}  {'=' if good else 'MISMATCH'}")
    ex = json.load(open("d64_results_mpc.json"))["mpc"]["counts"]
    want = mpc_counts(64)
    for k in KEYS:
        good = ex[k] == want[k]
        ok &= good
        print(f"MPC d= 64 {k:28s} executed {ex[k]:>12,}  schedule {want[k]:>12,}  {'=' if good else 'MISMATCH'}")
    try:
        exf = json.load(open("d64_results_fhe.json"))["fhe"]["counts"]
    except (FileNotFoundError, KeyError):
        exf = None
    if exf and "pd_proofs" in exf:
        Qp, Bp, E = fhe_params()
        want = fhe_counts(64, 8192, Qp, Bp, E)
        for k in KEYS + ("pd_proofs", "pd_elems", "preprocessing_mask_ct_elems"):
            good = exf[k] == want[k]
            ok &= good
            print(f"FHE d= 64 {k:28s} executed {exf[k]:>12,}  schedule {want[k]:>12,}  {'=' if good else 'MISMATCH'}")
        for ph, v in exf["wire_by_phase"].items():
            good = v == want["wire_by_phase"].get(ph)
            ok &= good
            print(f"FHE d= 64 wire[{ph:14s}]          executed {v:>12,}  schedule {want['wire_by_phase'].get(ph, 0):>12,}  {'=' if good else 'MISMATCH'}")
    else:
        print("FHE v2 executed counts not present yet: FHE validation skipped")
    print("VALIDATION", "PASS" if ok else "FAIL")
    return ok

def layout_check(N=8192, d=4096, seed=3):
    """Execute one block of each kind at the d = 4096 layout (d_r = 128, d_c = 64) at N = 8192, on real
    ciphertexts, and decrypt the coefficients the schedule reads."""
    import random
    import fhe_fork as FF
    import bfv_ref as bfv
    import cert_b61 as C
    sch, Qp, Bp, t = FF.setup(N=N)
    sch.keygen()
    rng = random.Random(seed)
    dc, dr, _ = fhe_layout(d, N)
    W = [[rng.randint(-7, 7) for _ in range(dc)] for _ in range(dr)]
    v = [rng.randint(-7, 7) for _ in range(dc)]
    e = [rng.randint(-7, 7) for _ in range(dr)]
    enc = lambda vals: sch.encrypt([vals.get(k, 0) % t for k in range(N)])
    cW = enc({64 * i + j: W[i][j] for i in range(dr) for j in range(dc)})
    fwd, _ = C.build(sch, Qp, Bp, cW, enc({63 - j: v[j] for j in range(dc)}))
    bwd, _ = C.build(sch, Qp, Bp, cW, enc({64 * (dr - 1 - i): e[i] for i in range(dr)}))
    outp, _ = C.build(sch, Qp, Bp, enc({64 * i: e[i] for i in range(dr)}), enc({j: v[j] for j in range(dc)}))
    c = lambda m: [x - t if x > t // 2 else x for x in m]
    mf, mb, mo = c(sch.decrypt(fwd)), c(sch.decrypt(bwd)), c(sch.decrypt(outp))
    okf = all(mf[64 * i + 63] == sum(W[i][j] * v[j] for j in range(dc)) for i in range(dr))
    okb = all(mb[64 * (dr - 1) + j] == sum(W[i][j] * e[i] for i in range(dr)) for j in range(dc))
    oko = all(mo[64 * i + j] == e[i] * v[j] for i in range(dr) for j in range(dc))
    print(f"layout d_r={dr} d_c={dc} at N={N}: forward {okf}, backward {okb}, outer (variant b) {oko}")
    return okf and okb and oko

if __name__ == "__main__":
    if "--validate" in sys.argv:
        sys.exit(0 if validate() else 1)
    if "--layout-check" in sys.argv:
        sys.exit(0 if layout_check() else 1)
    Qp, Bp, E = fhe_params()
    out = {}
    for d in (64, 256, 1024, 4096):
        out[d] = dict(mpc=mpc_counts(d), fhe_a=fhe_counts(d, 8192, Qp, Bp, E, "a"),
                      fhe_b=fhe_counts(d, 8192, Qp, Bp, E, "b"))
    print("STEADY STATE (weights already in custody: no genesis input of W; FHE bits include certificate digits)")
    hdr = f"{'d':>5} {'fork':7} {'committed bits':>18} {'online wire':>14} {'prep elems':>16} {'openings':>12} {'ct x ct':>8}"
    print(hdr)
    for d, r in out.items():
        for k, c in r.items():
            st = c["steady"]
            print(f"{d:>5} {k:7} {st['committed_bits']:>18,} {st['online_wire']:>14,} {st['preprocessing_elems']:>16,} "
                  f"{c['openings']:>12,} {c.get('ct_x_ct', 0):>8,}")
        for k in ("fhe_a", "fhe_b"):
            ni, mk = r[k]["nonideal_masks"], r[k]["mask_cost"]
            print(f"      {k} non-ideal masks: +{mk['committed_bits16']:,} committed bits (16-bit digits), "
                  f"+{mk['wire']:,} offline wire, {r[k]['mask_pairs']['pairs']} pairs; "
                  f"bits with 61-bit digits: {ni['committed_bits_digits61']:,}")
        m, a, b = r["mpc"]["steady"], r["fhe_a"]["steady"], r["fhe_b"]["steady"]
        print(f"      ratio FHE/MPC  (a) bits x{a['committed_bits'] / m['committed_bits']:.1f}  wire x{a['online_wire'] / m['online_wire']:.3f}"
              f"   (b) bits x{b['committed_bits'] / m['committed_bits']:.1f}  wire x{b['online_wire'] / m['online_wire']:.3f}")
    json.dump({str(d): r for d, r in out.items()}, open("step_counts.json", "w"), indent=1, default=str)
