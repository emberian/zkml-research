"""Regression falsifier for review3's BREAK (2026-11-06): the public SPDZ transcript was not bound into Fiat-Shamir,
so colluding custodians could commit a d1 that is NOT trunc(bg) (and the matching W1n), see the batch challenge gam,
then pick one dead opening value so the batched identity held. The ledger ACCEPTED the steered update (review3's
run of this attack against the unfixed code). Fixed: both proofs absorb the public transcript right after the
context, so changing an opening changes gam. This script mounts the same attack against the fixed code and exits
1 unless the ledger REFUSES it. Adapted from review3/forge_public.py (genesis-pinned ledger, public bound)."""
import os, random, sys, tempfile
import bfv_ref as bfv, cosnark as CS, cosnark_gates as G, cosnark_gates_zk as GZ, cosnark_zk as ZK
import mpc_fork as MF, proofwire as PW, spdz, run_proofwire as RP

d = 4
p = bfv.ntt_primes(61, 4, 16384)[3]
tab = MF.tables(p)
rng = random.Random(d)
M = lambda: [[rng.randint(-7, 7) % p for _ in range(d)] for _ in range(d)]
W1, W2 = M(), M()
x = [rng.randint(-7, 7) % p for _ in range(d)]
y = [rng.randint(-7, 7) % p for _ in range(d)]
ctx = ("mind-0", 0, 1)
DELTA = 12345

# record (cons index, transcript position) for every opening in the symbolic replay
_open = G.RecEngine.open
def rec_open(self, xv, phase="open"):
    if self.symbolic:
        self.omap = getattr(self, "omap", []) + [(len(self.cons), self.tpos)]
    return _open(self, xv, phase)
G.RecEngine.open = rec_open

dealer = spdz.Dealer(p, 3, 5)
live = G.RecEngine(p, 3, dealer)
W1n, W2n, wires = MF.run_step(live, W1, W2, x, y, tab, 9)
live.mac_check("step")
honest_d1 = [sum(v[i][0] for i in range(3)) % p for v in wires["d1"]]
# collusion: d1[0] += DELTA, and W1n row 0 consistent with the forged d1 (W1n = W1 - d1 (x) x)
wires["d1"] = list(wires["d1"]); v = dict(wires["d1"][0]); s, m = v[0]; v[0] = ((s + DELTA) % p, m); wires["d1"][0] = v
W1n = [list(r) for r in W1n]
for j in range(d):
    v = dict(W1n[0][j]); s, m = v[0]; v[0] = ((s - DELTA * x[j]) % p, m); W1n[0][j] = v
wires.update(W1n=W1n, W2n=W2n)
gen = RP.genesis_commit(p, wires)
spine, sst = ZK.prove_zk(spdz.Engine(p, 3, dealer), wires, context=ctx, carry=gen,
                         public=[v for _, _, v in live.transcript])
print("spine diagnostic (hidden witness):", sst["first_violated"])

public = [v for _, _, v in live.transcript]
sym = G.RecEngine(p, 3, None, symbolic=True, transcript=list(live.transcript))
MF.run_step(sym, None, None, [0] * d, [0] * d, tab, 9)
full_idx = {ci: tp for ci, tp in sym.omap}
mid_full = [i for i, c in enumerate(sym.cons) if c[3] in G.MIDDLE_PHASES]
# the last middle opening: the f-opening of the dead final prefix product in d1's last truncation
jstar = max(k for k, i in enumerate(mid_full) if i in full_idx and sym.cons[i][3] == "mul")
tpos = full_idx[mid_full[jstar]]
print("dead opening: middle cons", jstar, "transcript position", tpos, "of", len(public))

patch = {}
_bq = GZ.build_q
def build_q(p_, sym_, cons, had, prep, lens, gam):
    q, const = _bq(p_, sym_, cons, had, prep, lens, gam)
    sv = lambda sh: sum(sh[i][0] for i in range(3)) % p
    P = [sv(live.atom_sh[a]) for a in prep]; pos = {a: k for k, a in enumerate(prep)}
    pad = lambda xs, L: xs + [0] * (L - len(xs))
    vec = dict(P=pad(P, lens["P"]), A=pad([P[pos[a]] for a, _, _ in had], lens["A"]),
               B=pad([P[pos[b]] for _, b, _ in had], lens["B"]), C=pad([P[pos[c]] for _, _, c in had], lens["C"]))
    for nm in GZ.NAMES:
        vec[nm] = pad([sv(w) for w in wires[nm]], lens[nm])
    resid = (sum(sum(a * b for a, b in zip(q[k], vec[k])) for k in lens) + const) % p
    dval = resid * pow(gam[jstar], -1, p) % p
    patch["dval"], patch["resid"] = dval, resid
    return q, (const - gam[jstar] * dval) % p
GZ.build_q = build_q
middle, mst = GZ.prove_middle_zk(live, sym, wires, sst["coms"], context=ctx)
GZ.build_q = _bq
print("batch residual before the patch:", patch["resid"], " shift of the dead opening:", patch["dval"])
print("middle diagnostic (hidden witness, constraints vs ORIGINAL transcript):", mst["first_violated"])
public2 = list(public); public2[tpos] = (public2[tpos] + patch["dval"]) % p
blob = PW.encode_step(p, ctx, d, 3, True, spine, public2, middle, sym)

tmp = tempfile.mkdtemp(prefix="forge-"); path = os.path.join(tmp, "mind-0.ledger")
Lg = PW.Ledger(path, "mind-0", genesis=dict(d=d, owner_pk=None, custodians=["c0", "c1", "c2"],
                                            roots={k: gen[k].roots for k in ("W1", "W2")}))
verdict = Lg.accept(p, blob, tab)
print("LEDGER:", verdict)
c = sst["child"]["W1"]
committed = [sum(c.rows[i][r][cc] for i in range(3)) % p for r in range(c.Rd) for cc in range(c.C)]
honest = [(W1[i][j] - honest_d1[i] * x[j]) % p for i in range(d) for j in range(d)]
print("committed child W1n row 0 minus honest W1 - d1 x^T:", [MF.centered((a - b) % p, p) for a, b in zip(committed[:d], honest[:d])])
os.remove(path); os.rmdir(tmp)
print("FALSIFIER", "PASS (refused)" if not verdict[0] else "FAIL (accepted)")
sys.exit(0 if not verdict[0] else 1)
