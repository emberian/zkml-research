"""
SLOT-DEPENDENCY GATE -- which CRT slots does each output slot depend on?

WHY A SECOND GATE.  ideal_quotient_gate.py asks, per CRT ideal I_k,
    exists x = y (mod I_k)  with  F(x) != F(y) (mod I_k)                     (OLD GATE)
and calls a map an "escape" when that holds at all eight k.  An external reviewer's
correction (verified at the algebra level, 2026-09-05): for R_q = (F_{q^2})^8 a
ring-POLYNOMIAL map acts slot-by-slot, and sigma_e is ring-polynomial iff
e in <q> = {1, 31} mod 32 -- but "not ring-polynomial" is NOT "mixes slots".  A bare
sigma_5 merely PERMUTES the eight slots (an 8-cycle): it passes the old gate at all
eight ideals while its slot-dependency matrix is a permutation matrix.  The
reviewer's composition theorem: rounds built only from (1) slotwise nonlinear maps,
(2) R_q-linear mixing among state words, (3) one global sigma_e applied to every
word, compose to a SLOT-SEPARABLE map F(x)_i = f_i(x_{pi(i)}) -- a one-slot input
difference stays a one-slot output difference forever, a two-query distinguisher
against an ideal permutation with advantage ~ 8(L-1)/(L^8-1), L = q^2.
Our sigma-layer x + c*sigma_k(x) makes output slot i depend on slots i AND pi_k(i);
it is not of type (3), so the theorem does not apply as stated, and whether the
WHOLE round function is slot-separable is exactly what must be MEASURED.  The old
gate cannot measure it.  This script can.

THE INSTRUMENT.  For F : R_q^w -> R_q^w' and CRT slots i, j in {1,3,...,15}:
    Dep_ij(F) := exists x, y : (forall k != j, x = y (mod I_k))  and  F(x) !=_i F(y)
Perturb slot j only: y = x + cof_j * r with cof_j = prod_{k != j} f_k and r uniform,
so y agrees with x in every slot but j and its slot-j component is uniform in
F_{q^2}.  Then read off which output slots moved (evaluation at zeta^i).
Two granularities:
  WHOLE-STATE 8x8     : perturb slot j of EVERY word at once; Dep_ij = 1 if slot i
                        of ANY output word moves.
  PER-WORD (8w')x(8w) : perturb slot j of ONE word a; entry ((b,i),(a,j)).
A 1 is a WITNESS (the pair x, y was exhibited).  A 0 is "NOT OBSERVED in N samples",
never "proved absent".  For a genuine dependency the miss probability per sample is
~ q^-2 = 2^-128 (two uniform F_{q^2} values agreeing), so N is a formality here, not
a confidence interval.  Sample counts are printed with every table.

Everything runs at the REAL modulus q = 2^64-257 on the GROUND-TRUTH round functions
(sigma_poseidon.frog_like, design_gadget_feistel.Feistel), imported/exec'd verbatim
through ideal_quotient_gate.py's own definitions (its F_{q^2}, zeta, f_k, ev, rate).
"""
import os, sys, time, json

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

# ------------------------------------------------------------ the old gate's definitions, verbatim
_gate_path = os.path.join(HERE, "ideal_quotient_gate.py")
_src = open(_gate_path).read()
_cut = _src.index('print("=" * 100)')            # everything above its first banner = definitions
G = {"__file__": _gate_path, "__name__": "ideal_quotient_gate_defs"}
exec(compile(_src[:_cut], "ideal_quotient_gate.py[defs]", "exec"), G)
Q, D, SLOTS, FK = G["Q"], G["D"], G["SLOTS"], G["FK"]
add, sub, mul = G["add"], G["sub"], G["mul"]
ev, congr, rand_elt, rate, show = G["ev"], G["congr"], G["rand_elt"], G["rate"], G["show"]
SP, Feistel, gadget = G["SP"], G["Feistel"], G["gadget"]
rng = G["rng"]
assert Q == 2**64 - 257 and D == 16 and len(SLOTS) == 8

N_WHOLE = 4          # samples per input slot, whole-state perturbation
N_WORD = 2           # samples per (word, slot), per-word perturbation
OUT_JSON = os.path.join(HERE, "slot_dependency_gate.json")
RESULTS = {}

# ------------------------------------------------------------ slot perturbation
COF = {}                                         # cof_j = prod_{k != j} f_k  (degree 14: no wrap)
for j in SLOTS:
    c = [1] + [0]*(D-1)
    for k in SLOTS:
        if k != j: c = mul(c, FK[k])
    assert all(ev(c, k) == (0, 0) for k in SLOTS if k != j) and ev(c, j) != (0, 0)
    COF[j] = c

def perturb(x, j):
    """y agrees with x in every slot but j; its slot-j component is uniform."""
    y = add(x, mul(COF[j], rand_elt()))
    assert all(congr(x, y, k) for k in SLOTS if k != j)
    return y

# ------------------------------------------------------------ the dependency matrices
def dep_whole(fn, w, N=N_WHOLE):
    """8x8: M[i][j] = 1 iff perturbing slot j of every word moved slot i of some output word."""
    M = [[0]*8 for _ in range(8)]
    for jj, j in enumerate(SLOTS):
        for _ in range(N):
            x = [rand_elt() for _ in range(w)]
            y = [perturb(xa, j) for xa in x]
            fx, fy = fn(x), fn(y)
            for ii, i in enumerate(SLOTS):
                if any(not congr(a, b, i) for a, b in zip(fx, fy)): M[ii][jj] = 1
    return M

def dep_perword(fn, w, N=N_WORD):
    """(8w')x(8w): M[b*8+i][a*8+j] = 1 iff perturbing slot j of word a moved slot i of word b."""
    M = None
    for _ in range(N):
        x = [rand_elt() for _ in range(w)]
        fx = fn(x); wp = len(fx)
        if M is None: M = [[0]*(8*w) for _ in range(8*wp)]
        for a in range(w):
            for jj, j in enumerate(SLOTS):
                y = list(x); y[a] = perturb(x[a], j)
                fy = fn(y)
                for b in range(wp):
                    for ii, i in enumerate(SLOTS):
                        if not congr(fx[b], fy[b], i): M[b*8+ii][a*8+jj] = 1
    return M

def collapse(Mw, w, wp):
    """OR the per-word matrix down to 8x8 over all (word_out, word_in) pairs."""
    M = [[0]*8 for _ in range(8)]
    for b in range(wp):
        for a in range(w):
            for ii in range(8):
                for jj in range(8):
                    if Mw[b*8+ii][a*8+jj]: M[ii][jj] = 1
    return M

def classify(M):
    n, m = len(M), len(M[0]); nnz = sum(map(sum, M))
    if nnz == n*m: return "FULL", nnz
    if n == m and all(sum(r) == 1 for r in M) and all(sum(c) == 1 for c in zip(*M)):
        return ("PERMUTATION (identity)" if all(M[i][i] for i in range(n)) else "PERMUTATION (derangement)"), nnz
    return f"{nnz}/{n*m}", nnz

def fmt8(M):
    return "  ".join("".join(str(v) for v in r) for r in M)

def report(label, fn, w, whole=True, perword=True, oldgate=False):
    t0 = time.time(); rec = {}
    line = f"  {label:<46}"
    if whole:
        M = dep_whole(fn, w); tag, nnz = classify(M)
        supp = sorted({sum(r) for r in M})
        line += f" 8x8 nnz={nnz:>2} {tag:<24} rows(in-slots/out-slot)={supp}"
        rec["whole"] = M; rec["whole_class"] = tag
    if perword:
        Mw = dep_perword(fn, w); wp = len(Mw)//8; tagw, nnzw = classify(Mw)
        Mc = collapse(Mw, w, wp); tagc, _ = classify(Mc)
        line += f" | per-word {8*wp}x{8*w} nnz={nnzw}/{64*w*wp} {tagw}"
        if whole: line += f" (OR-collapse {'==' if Mc == M else '!='} whole)"
        rec["perword_nnz"] = nnzw; rec["perword_shape"] = [8*wp, 8*w]; rec["perword_class"] = tagw
    if oldgate:
        res = rate(fn, w); esc = all(res[k][0] == 0 for k in SLOTS)
        line += f" | OLD gate: {'escape (PASSES the old gate)' if esc else 'not escape'}"
        rec["old_gate_escape"] = esc
    print(line + f"   [{time.time()-t0:.0f}s]"); sys.stdout.flush()
    if whole: print(f"      {fmt8(M)}")
    RESULTS[label] = rec
    return rec

print("=" * 110)
print(f"SLOT-DEPENDENCY GATE at q = 2^64-257 (q mod 32 = 31), d=16, tau=2, ell=8 slots F_(q^2)")
print(f"  Dep_ij: perturb input slot j only (y = x + cof_j*r), watch output slot i.  1 = witnessed, 0 = not observed.")
print(f"  samples: N_WHOLE={N_WHOLE} per input slot (whole-state), N_WORD={N_WORD} per (word, slot) (per-word).")
print(f"  8x8 rows are OUTPUT slots i = 1,3,..,15 (top to bottom); columns are INPUT slots j = 1,3,..,15.")
print("=" * 110)

# ============================================================ (A) sigma-Poseidon
print("\n(A) sigma-POSEIDON, frog_like(q=2^64-257): t=9, RF=8, RP=22, alpha=7, sigma every round")
P = SP.frog_like(q=Q); T = P.t; NR = P.RF + P.RP
assert P.R.tau == 2 and P.R.ell == 8
R = P.R
for name, ok, note in P.validate():
    print(f"    [{'PASS' if ok else 'FAIL'}] {name:<42} {note}")

def sp_rounds(P, state, r_lo, r_hi):
    """rounds r_lo..r_hi-1 of SP.permutation, loop body copied verbatim (guarded below)."""
    R, t = P.R, P.t
    s = list(state); nrounds = P.RF + P.RP; half = P.RF // 2
    for rd in range(r_lo, r_hi):
        s = [R.add(x, P.rc[rd][i]) for i, x in enumerate(s)]
        full = rd < half or rd >= nrounds - half
        if full: s = [R.pow(x, P.alpha) for x in s]
        else:    s = [R.pow(s[0], P.alpha)] + s[1:]
        s = [SP._mds_row(R, P.mds, s, i, t) for i in range(t)]
        if rd in P.sigma_rounds:
            k = P.sigma_exps[rd]
            s = [R.add(x, R.mul(P.sc[rd][i], R.sigma(x, k))) for i, x in enumerate(s)]
    return s
for _ in range(2):                                # guard: the copy IS the ground truth
    st = [rand_elt() for _ in range(T)]
    assert sp_rounds(P, st, 0, NR) == SP.permutation(P, st)

# the slot permutation of sigma_e, read off the instrument itself (bare sigma_e, one word)
def slot_perm_of(e):
    M = dep_whole(lambda s: [R.sigma(x, e) for x in s], 1, N=1)
    return {SLOTS[ii]: [SLOTS[jj] for jj in range(8) if M[ii][jj]] for ii in range(8)}
print("  slot permutation of bare sigma_e (out slot i <- in slot j), read off the instrument:")
for e in (5, 25, 17, 31):
    pm = slot_perm_of(e)
    print(f"    sigma_{e:<2}: " + " ".join(f"{i}<-{pm[i][0] if len(pm[i])==1 else pm[i]}" for i in SLOTS))
    assert all(len(pm[i]) == 1 for i in SLOTS)
    assert all(pm[i][0] == min((i*e) % 32, (-i*e) % 32) for i in SLOTS), "out slot i depends on in slot class(i*e)"
print("    (matches the group law: out slot i <- in slot class(i*e), class(m) = min(m mod 32, -m mod 32))")

print("\n  layers alone (round-0 tables):")
report("round constants  s + rc",        lambda s: [R.add(x, P.rc[0][i]) for i, x in enumerate(s)], T)
report("S-box  x^7",                     lambda s: [R.pow(x, 7) for x in s], T)
report("R_q-MDS",                        lambda s: [SP._mds_row(R, P.mds, s, i, T) for i in range(T)], T)
for k in (1, 31, 5, 25, 17):
    lab = {1: "identity", 31: "Frobenius", 5: "8-cycle", 25: "two 4-cycles", 17: "four 2-cycles"}[k]
    report(f"sigma-layer x + c*sigma_{k}(x) [{lab}]",
           lambda s, k=k: [R.add(x, R.mul(P.sc[0][i], R.sigma(x, k))) for i, x in enumerate(s)], T)
print("  the reviewer's counterexample, reproduced (bare automorphism, no coefficient):")
report("BARE sigma_5(x)      (reviewer's counterexample)", lambda s: [R.sigma(x, 5) for x in s], T, oldgate=True)
report("BARE sigma_25(x)",  lambda s: [R.sigma(x, 25) for x in s], T, oldgate=True)
report("BARE sigma_17(x)",  lambda s: [R.sigma(x, 17) for x in s], T, oldgate=True)
report("BARE sigma_31(x)     (Frobenius: componentwise)", lambda s: [R.sigma(x, 31) for x in s], T, oldgate=True)

print("\n  single rounds r (sigma exponent in brackets); per-word matrices are 72x72:")
single = {}
for r in range(NR):
    rec = report(f"round {r:>2}  [sigma_{P.sigma_exps[r]}]", lambda s, r=r: sp_rounds(P, s, r, r+1), T)
    single[r] = rec["whole_class"]
print("  ==> single-round whole-state classes: " + ", ".join(f"r{r}:{single[r].split()[0]}" for r in range(NR)))

print("\n  windows and cumulative rounds 0..r-1 (first FULL is the round count to full dependency):")
report("rounds 8-11 (the slot-diagonal window)", lambda s: sp_rounds(P, s, 8, 12), T)
first_full = None
for r in (1, 2, 3, 4, 5, 6, 7, 8, 30):
    rec = report(f"rounds 0..{r-1}  ({r} round{'s' if r>1 else ''})", lambda s, r=r: sp_rounds(P, s, 0, r), T)
    if first_full is None and rec["whole_class"] == "FULL": first_full = r
RESULTS["sigma_poseidon_first_full_rounds"] = first_full
print(f"  ==> sigma-Poseidon (frog_like schedule): first FULL whole-state dependency at {first_full} rounds")

print("\n  schedule controls (same tables, exponents replaced):")
P5 = SP.frog_like(q=Q); P5.sigma_exps = [5]*NR
ff5 = None
for r in (1, 2, 3, 4, 5, 6, 7, 8):
    rec = report(f"sigma_5 EVERY round, rounds 0..{r-1}", lambda s, r=r: sp_rounds(P5, s, 0, r), T, perword=False)
    if ff5 is None and rec["whole_class"] == "FULL": ff5 = r
RESULTS["sigma5_every_round_first_full"] = ff5
P3 = SP.frog_like(q=Q); P3.sigma_exps = [(5, 25, 17)[r % 3] for r in range(NR)]
ff3 = None
for r in (1, 2, 3, 4):
    rec = report(f"exps (5,25,17) repeating, rounds 0..{r-1}", lambda s, r=r: sp_rounds(P3, s, 0, r), T, perword=False)
    if ff3 is None and rec["whole_class"] == "FULL": ff3 = r
RESULTS["sched_5_25_17_first_full"] = ff3
P0 = SP.frog_like(q=Q); P0.sigma_rounds = set()
report("CONTROL sigma OFF, 30 rounds (ring-Poseidon)", lambda s: SP.permutation(P0, s), T, perword=False)
print(f"  ==> sigma_5 every round: first FULL at {ff5} rounds;  exps (5,25,17): first FULL at {ff3} rounds")

print("\n  the reviewer's diffusion layer L = (I+2s^4)(I+2s^2)(I+2s), s = sigma_5, and a 3-row alternative:")
def L_rev(x):
    two = [2] + [0]*(D-1)
    s1 = R.add(x, R.mul(two, R.sigma(x, 5)))
    s2 = R.add(s1, R.mul(two, R.sigma(s1, 25)))
    return R.add(s2, R.mul(two, R.sigma(s2, 17)))
report("(I+2s)    alone",                  lambda s: [R.add(x, R.mul([2]+[0]*(D-1), R.sigma(x, 5))) for x in s], T, perword=False)
report("L_rev = (I+2s^4)(I+2s^2)(I+2s)",   lambda s: [L_rev(x) for x in s], T)
c1, c2 = rand_elt(), rand_elt()
def L3(x):                                  # (I + c1*sigma_5 + c2*sigma_29)^3, one Def.9 row per application
    for _ in range(3):
        x = R.add(x, R.add(R.mul(c1, R.sigma(x, 5)), R.mul(c2, R.sigma(x, 29))))
    return x
report("(I+c1*s5+c2*s29)^3  [pp=(s5,s29), 3 rows]", lambda s: [L3(x) for x in s], T, perword=False)
report("(I+c1*s5+c2*s29)^2  (control: 2 rows)",   lambda s: [L3.__wrapped__(x) if False else _L3k(x, 2) for x in s], T, perword=False) \
    if False else None
def _L3k(x, k):
    for _ in range(k):
        x = R.add(x, R.add(R.mul(c1, R.sigma(x, 5)), R.mul(c2, R.sigma(x, 29))))
    return x
report("(I+c1*s5+c2*s29)^2  (control: 2 rows)",   lambda s: [_L3k(x, 2) for x in s], T, perword=False)
report("(I+c1*s5+c2*s25)^3  (control: pp=(s5,s25))", lambda s: [_L3k_e(x, 3, 25) for x in s], T, perword=False) \
    if False else None
def _L3k_e(x, k, e2):
    for _ in range(k):
        x = R.add(x, R.add(R.mul(c1, R.sigma(x, 5)), R.mul(c2, R.sigma(x, e2))))
    return x
report("(I+c1*s5+c2*s25)^3  (control: pp=(s5,s25))", lambda s: [_L3k_e(x, 3, 25) for x in s], T, perword=False)

# ============================================================ (B) gadget-Feistel
print("\n(B) GADGET-FEISTEL, Feistel(q=2^64-257): w=4 per branch (state 8), B=2^16, K=4, P=2, NR=16")
Fe = Feistel(Q, seed=2026); W = Fe.w
def planes_map(s):                               # G^-1 alone: all K planes of each element (4 -> 16 words)
    return [pl for x in s for pl in gadget(add(x, Fe.a[0][0]), Q, Fe.base, Fe.k)]
def feistel_rounds(nr):
    return lambda s: (lambda LR: LR[0] + LR[1])(Fe.perm(s[:W], s[W:], rounds=nr))
report("G^-1 alone (4 elts -> 16 planes)", planes_map, W)
report("F_0 = G^-1, products, linear (P=2)", lambda s: Fe.F(s, 0), W)
fff = None
for nr in (1, 2, 3, 16):
    rec = report(f"{nr} round{'s' if nr>1 else ''} (state 8: L|R)", feistel_rounds(nr), 2*W)
    if fff is None and rec["perword_class"] == "FULL": fff = nr
RESULTS["feistel_first_full_perword_rounds"] = fff
print(f"  ==> gadget-Feistel: whole-state FULL from 1 round; per-word (every word x slot -> every word x slot) FULL at {fff} rounds")

json.dump(RESULTS, open(OUT_JSON, "w"), indent=1)
print(f"\nwrote {OUT_JSON}\nDONE.")
