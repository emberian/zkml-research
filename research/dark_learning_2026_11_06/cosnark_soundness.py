"""The collaborative proof's soundness, term by term (union bound), per step and per run (proof lane gen 5, 2026-11-07).

  python3 cosnark_soundness.py [PROFILE] [d] [steps]       (default: ledger 4096 2000; prints both EXT = 1 and 2)

Statistical (interactive) soundness of one step's bundle: the spine proof, the middle proof, and the release proof
for the run's end. |F| is the challenge field, p^EXT. Every term is the standard one:
  - sumcheck of l rounds of degree deg: l deg / |F| (Schwartz-Zippel per round, on the round message's identity);
  - a claim at a random point tau (matvec z(tau) = sum W(tau, .) v, zerocheck eq(tau, .)): l / |F| (multilinear in tau);
  - the rank-1 check W'(r) = W(r) - d(r_row) v(r_col): 2 ld / |F| (multilinear in 2 ld variables);
  - the linear batch with independent coefficients gamma: 1 / |F|;
  - Ligero (Ames, Hazay, Ishai, Venkitasubramaniam 2017) per proof: proximity n / |F| (an RS code of length n, e < d/3),
    linear and quadratic tests 1 / |F| each, and the column test (1 - delta)^T with delta = 1/4 at rate 1/4;
  - every PCS commitment opened in a proof: proximity n_c / |F| and the column test (3/4)^T_COLS.
Not in the table (stated): Merkle binding (SHA-256 collisions, computational), the MAC check (an MPC abort among the
custodians, not the verifier's soundness), Fiat-Shamir grinding (a prover with Q hash queries gains a factor of
about Q on the round-by-round terms).
"""
import math
import sys

import cosnark as CS
import cosnark_gates_zk as GZ
import cosnark_zk as ZK
import proofwire as PW

# d = 4096, GEN6 + RC + LB (darkproof counts 4096 ledger): Hadamard rows and atoms of the step and of the release at M = 64
COUNTS = {4096: dict(had=2166784, prep=3772416, rel_had=41050048, rel_prep=77343488, M=64)}

def log2(x):
    return math.log2(x) if x > 0 else float("-inf")

def terms(prof, d, ext):
    PW.set_profile(prof)
    import cosnark_ext as X
    X.EXT = ext
    if ext == 2:
        CS.NMASK = 4
    p = PW.he_field()
    F = p ** ext
    ld = d.bit_length() - 1
    c = COUNTS[d]
    out = []
    def add(where, name, prob):
        out.append((where, name, prob))
    # spine
    for nm in ("z1", "z2", "b"):
        add("spine", f"matvec {nm}: claim at tau", ld / F)
        add("spine", f"matvec {nm}: sumcheck {ld} x deg 2", 2 * ld / F)
    add("spine", "zerocheck b g1: tau", ld / F)
    add("spine", f"zerocheck b g1: {ld} x deg 3", 3 * ld / F)
    for nm in ("W1n", "W2n"):
        add("spine", f"rank-1 {nm}", 2 * ld / F)
    sh = ZK.shapes(p, d, True)
    for k, s in sorted(sh.items()):
        add("spine", f"PCS proximity {k} (n = {len(s.pts)})", len(s.pts) / F)
        add("spine", f"PCS columns {k}", 0.75 ** CS.T_COLS)
    nl = 4 * (ZK.K_L + ZK.T_HIDE)
    for nm in ("proximity", "linear", "quadratic"):
        add("spine", f"Ligero {nm}", (nl if nm == "proximity" else 1) / F)
    add("spine", "Ligero columns", 0.75 ** ZK.T_OPEN)
    # middle
    lens = dict(P=GZ.plen(c["prep"]), A=GZ.plen(c["had"]), B=GZ.plen(c["had"]), C=GZ.plen(c["had"]))
    lens.update({nm: GZ.plen(d) for nm in GZ.NAMES})
    lh = (lens["A"] - 1).bit_length()
    lmax = max((L - 1).bit_length() for L in lens.values())
    add("middle", "zerocheck A B = C: tau", lh / F)
    add("middle", f"zerocheck A B = C: {lh} x deg 3", 3 * lh / F)
    add("middle", "linear batch gamma", 1 / F)
    add("middle", f"linear sumchecks: {len(lens)} x {lmax} x deg 2", len(lens) * 2 * lmax / F)
    for k, L in sorted(lens.items()):
        s = ZK.PubShape(p, (L - 1).bit_length(), CS.HIDE, CS.NMASK, 0)
        add("middle", f"PCS proximity {k} (n = {len(s.pts)})", len(s.pts) / F)
        add("middle", f"PCS columns {k}", 0.75 ** CS.T_COLS)
    for nm in ("proximity", "linear", "quadratic"):
        add("middle", f"Ligero {nm}", (nl if nm == "proximity" else 1) / F)
    add("middle", "Ligero columns", 0.75 ** ZK.T_OPEN)
    # release (once per run)
    rl = dict(P=GZ.plen(c["rel_prep"]), A=GZ.plen(c["rel_had"]), B=GZ.plen(c["rel_had"]), C=GZ.plen(c["rel_had"]),
              W1=d * d, W2=d * d, z1=GZ.plen(d * c["M"]), h=GZ.plen(d * c["M"]))
    rlh = (rl["A"] - 1).bit_length()
    rlmax = max((L - 1).bit_length() for L in rl.values())
    add("release", "zerocheck: tau", rlh / F)
    add("release", f"zerocheck: {rlh} x deg 3", 3 * rlh / F)
    add("release", "linear batch gamma", 1 / F)
    add("release", f"linear sumchecks: {len(rl)} x {rlmax} x deg 2", len(rl) * 2 * rlmax / F)
    for k, L in sorted(rl.items()):
        s = ZK.PubShape(p, (L - 1).bit_length(), CS.HIDE, CS.NMASK, 0)
        add("release", f"PCS proximity {k} (n = {len(s.pts)})", len(s.pts) / F)
        add("release", f"PCS columns {k}", 0.75 ** CS.T_COLS)
    for nm in ("proximity", "linear", "quadratic"):
        add("release", f"Ligero {nm}", (nl if nm == "proximity" else 1) / F)
    add("release", "Ligero columns", 0.75 ** ZK.T_OPEN)
    return out

def summary(prof, d, steps, ext):
    t = terms(prof, d, ext)
    step = sum(x for w, _, x in t if w != "release")
    rel = sum(x for w, _, x in t if w == "release")
    worst = max(((x, n, w) for w, n, x in t if w != "release"))
    return dict(ext=ext, step=log2(step), run=log2(steps * step + rel), release=log2(rel),
                worst=(worst[2], worst[1], log2(worst[0])),
                by_kind={k: log2(sum(x for w, n, x in t if w != "release" and k in n))
                         for k in ("sumcheck", "tau", "rank-1", "gamma", "PCS proximity", "PCS columns", "Ligero proximity",
                                   "Ligero linear", "Ligero quadratic", "Ligero columns")})

if __name__ == "__main__":
    prof = sys.argv[1] if len(sys.argv) > 1 else "ledger"
    d = int(sys.argv[2]) if len(sys.argv) > 2 else 4096
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    for ext in (1, 2):
        s = summary(prof, d, steps, ext)
        print(f"EXT = {ext}: per step 2^{s['step']:.1f}, release 2^{s['release']:.1f}, run of {steps} steps + release "
              f"2^{s['run']:.1f}; largest single term {s['worst'][0]} {s['worst'][1]}: 2^{s['worst'][2]:.1f}")
        for k, v in s["by_kind"].items():
            print(f"    {k:18s} 2^{v:.1f}")
