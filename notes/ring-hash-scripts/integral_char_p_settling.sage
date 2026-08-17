# integral_char_p_settling.sage
# =============================================================================
# Ring-hash cryptanalysis lane, ITEM #1 -- the tau=2 integral-cryptanalysis
# "settling experiment", EXECUTED at our parameters.  (2026-08-17)
#
# WHAT: Beyne-Verbauwhede, "Integral cryptanalysis in characteristic p"
#   (ASIACRYPT 2025, eprint 2025/932).  Runs the authors' own "SHARK-like
#   properties with higher divisibility based on saturating sboxes" Newton-
#   polytope model from their SPN.ipynb, reporting the LAST ROUND that carries a
#   mod-q^2 integral (division) property -- the invariant the paper shows
#   survives FAR past algebraic-degree saturation in large prime characteristic.
#   The machinery (get_polytope_permutation / _reduced_linear_permutation /
#   compose_permutations) is copied VERBATIM from SPN.ipynb; only a round-indexed
#   bookkeeping wrapper + a safety cap are added.
#
# WHY: ring-hash-design.md sec 4.5 / ring-hash-tau-verdict.md named this as THE
#   experiment that converts the tau choice from argument into measurement.  The
#   paper's published table (last round 1/13/20/21 for prime/deg-2/deg-4/deg-8)
#   holds the FIELD size ~2^64 fixed by SHRINKING the base prime (2^64/2^31/2^17/
#   2^8); our regime instead holds the BASE PRIME at ~2^64 and grows the field
#   (tau=1/2/4 -> F_q / F_{q^2} / F_{q^4}), with e*t = 16 = ring dimension.  The
#   design note's own caveat: "the round counts do not transfer ... the magnitude
#   at our parameters is unmeasured."  This measures it.
#
# HOW TO RUN (needs a SageMath kernel; laptop has none, so via Docker):
#   docker pull --platform linux/amd64 sagemath/sagemath:latest
#   # Apple Silicon: Rosetta lacks a CPU ext FLINT uses (matmul -> illegal
#   # instruction), so force qemu for amd64 (only affects amd64 emulation):
#   docker run --privileged --rm tonistiigi/binfmt --install amd64
#   docker run --rm --platform linux/amd64 -e PYTHONUNBUFFERED=1 \
#     -v "$PWD":/work -w /work sagemath/sagemath:latest sage /work/integral_char_p_settling.sage
#
# RESULTS (2026-08-17, sage 10.9; both Frog q=15912092521325583641 AND the dual-
#   mode q=2^64-257 give identical last-round numbers -- the count depends on
#   field size + (e,t,d), not the specific ~2^64 prime):
#
#     PHASE A (falsification guard, reproduces the paper EXACTLY):
#        prime e1 t8 -> 1 ; deg-2 e2 t8 -> 13 ; deg-4 e4 t8 -> 20 ; deg-8 e8 t8 -> 21
#
#     PHASE B (OUR base prime ~2^64):
#        tau=1  e=1 t=16  ->  2
#        tau=2  e=2 t=8   -> 24        <-- vs the paper's 13 at the SAME (e=2,t=8)
#                                          but base 2^31: the survival ~1.85x LONGER,
#                                          a pure base-prime effect.
#        tau=4  e=4 t=4   -> >= 42     (still climbing when stopped at round 42;
#                                          degree-saturation ceiling ~91, so it dies
#                                          much later -- integral-infeasible round
#                                          budget for any sane NR)
#
# READING IT: the SHARK/x^7 model IS the sigma-Poseidon candidate (power map +
#   MDS-ish slot layer).  A 24-round distinguisher at tau=2 leaves only ~6 rounds
#   of margin over the borrowed RF=8/RP=22=30 budget, and the real sigma-layer is
#   only slot-MDS in full rounds (WEAKER mixing than SHARK -> survival can only be
#   >= 24).  The round count must be DERIVED, and it is larger than the borrowed
#   set.  tau=2 stays the pick (ordering tau1<tau2<tau4 holds; tau1 out on
#   challenge space), but its round-count margin is thinner than the note assumed.
#   Set max_rounds low (e.g. 45) to reproduce the fast cases without the slow tau=4
#   tail; tau=4 alone runs ~1-2 min/round and rising under qemu.
# =============================================================================

# ---- model machinery (copied verbatim from SPN.ipynb cell 1 + cell 2) --------

def compose_permutations(P1, P2, n): # return polytope for F2 \circ F1
    ieqs = []
    eqns = []
    for ieq in P1.inequalities_list():
        ieqs.append(ieq[:2*n+1] + [0]*n + ieq[-1:] + [0])
    for eqn in P1.equations_list():
        eqns.append(eqn[:2*n+1] + [0]*n + eqn[-1:] + [0])
    for ieq in P2.inequalities_list():
        ieqs.append(ieq[:1] + [0]*n + ieq[1:2*n+1] + [0] + ieq[-1:])
    for eqn in P2.equations_list():
        eqns.append(eqn[:1] + [0]*n + eqn[1:2*n+1] + [0] + eqn[-1:])
    M = [[matrix.zero(ZZ, i, j) for j in (n, n, n, 1, 1)] for i in (n, n, 1)]
    M[0][0] = matrix.identity(ZZ, n)
    M[1][2] = matrix.identity(ZZ, n)
    M[2][3] = matrix.identity(ZZ, 1)
    M[2][4] = matrix.identity(ZZ, 1)
    return Polyhedron(ieqs=ieqs, eqns = eqns).linear_transformation(block_matrix(M))

def get_polytope_permutation(p, n, d):
    ieqs = []
    for i in range(2*n):
        ieqs.append([0] + [0]*i + [1] + [0]*(2*n-i))
        ieqs.append([p-1] + [0]*i + [-1] + [0]*(2*n-i))
    ieqs.append([0]*(2*n+1) + [1]) # ord_p is at least 0
    ieqs.append([0] + [-1]*n + [d]*n + [d*(p-1)]) # constraints from function
    ieqs.append([-1] + [0]*n + [1]*n + [0]) # special treatment for output character 1
    ieqs.append([(p-1)*n-1] + [-1]*n + [0]*n + [0]) # special treatment for input character of maximal wheight
    P1 = Polyhedron(ieqs=ieqs)
    ieqs = []
    eqns = []
    for i in range(n):
        ieqs.append([0] + [0]*n + [0]*i + [1] + [0]*(n-i))
        ieqs.append([p-1] + [0]*n + [0]*i + [-1] + [0]*(n-i))
        eqns.append([p-1] + [0]*i + [-1] + [0]*(n-1-i) + [0]*(n+1))
    ieqs.append([-1] + [0]*(2*n) + [1]) # ordp is at least 1 in this case
    ieqs.append([-1] + [0]*n + [1]*n + [0]) # special treatment for output character 1
    ieqs.append([(p-1)*n-1] + [0]*n + [-1]*n + [0]) # special treatment for output character of maximal wheight
    P2 = Polyhedron(ieqs=ieqs,eqns=eqns)
    P3 = Polyhedron(vertices=[[0]*(2*n+1), [p-1]*2*n + [0]])
    return P1.convex_hull(P2).convex_hull(P3)

def get_polytope_reduced_linear_permutation(p, n):
    ieqs = []
    for i in range(2):
        ieqs.append([0] + [0]*i + [1] + [0]*(2-i))
        ieqs.append([n*(p-1)] + [0]*i + [-1] + [0]*(2-i))
    ieqs.append([0, 0, 0, 1]) # ord_p is at least 0
    ieqs.append([0, -1, 1, p-1]) # constraints from function
    ieqs.append([-1, 0, 1, 0]) # special treatment for output character 1
    ieqs.append([(p-1)*n-1, -1, 0, 0]) # special treatment for input character of maximal wheight
    P1 = Polyhedron(ieqs=ieqs)
    ieqs = []
    eqns = []
    ieqs.append([0, 0, 1, 0])
    ieqs.append([n*(p-1), 0, -1, 0])
    eqns.append([p-1, -1, 0, 0])
    ieqs.append([-1, 0, 0, 1]) # ordp is at least 1 in this case
    ieqs.append([-1, 0, 1, 0]) # special treatment for output character 1
    ieqs.append([(p-1)*n-1, 0, -1, 0]) # special treatment for output character of maximal wheight
    P2 = Polyhedron(ieqs=ieqs,eqns=eqns)
    P3 = Polyhedron(vertices=[[0]*3, [n*(p-1), n*(p-1), 0]])
    return P1.convex_hull(P2).convex_hull(P3)

# ---- the SHARK saturating-sbox experiment, generalized to (p, e, t, d) -------
# Faithful to SPN.ipynb cells 10 (e=1) / 22 (e=2) / 39 (e=4) / 49 (e=8):
# For e=1 the inner loop over i degenerates to a single term with p^0 = 1 and
# p^e - 1 = p - 1, reproducing cell 10 exactly.

def last_round_with_psquare_property(p, e, t, d, max_rounds=80, verbose=True):
    # Faithful transcription of SPN.ipynb cells 10/22/39/49; the ONLY additions
    # are the round-indexed bookkeeping (last_hit) and a safety cap. The loop
    # body, the eqns, and the P_full <- compose(P_full, P_round) advance are the
    # authors'.
    P_cell = get_polytope_permutation(p**e, 1, d)
    P_round = compose_permutations(t*P_cell, get_polytope_reduced_linear_permutation(p**e, t), 1)
    P_full = get_polytope_reduced_linear_permutation(p**e, t)
    r = 1
    last_hit = 0
    hit_cap = False
    while True:
        any_hit = False
        res = 0
        for cells in range(1, t):
            res = 0
            for i in range(e):
                Pred = (P_full & Polyhedron(eqns=[[-p**i, 0, 1, 0],
                                                  [-(p**e-1)*cells, 1, 0, (p**e-1)]])
                        ).linear_transformation(Matrix(ZZ, 1, 3, [[0, 0, 1]]))
                res += min(ceil(x[0]) for x in Pred.vertices_list())
            if res >= 2:
                any_hit = True
                if verbose:
                    print(f"      round {r:2d}  cells={cells:2d}  valuation={res}")
        if any_hit:
            last_hit = r
        if cells == t-1 and res <= 1:        # authors' termination condition
            break
        if r >= max_rounds:
            hit_cap = True
            break
        r += 1
        P_full = compose_permutations(P_full, P_round, 1)   # ADVANCE ONE ROUND
    if hit_cap:
        print(f"      ** hit max_rounds={max_rounds} cap; last_hit is a LOWER BOUND **")
    return last_hit


# ---- PHASE A: falsification guard -- reproduce the paper's published table ----
def report(label, p, e, t, expected=None, verbose=False):
    lr = last_round_with_psquare_property(p, e, t, 7, verbose=verbose)
    tag = ""
    if expected is not None:
        tag = "  OK" if lr == expected else f"  ** MISMATCH (paper: {expected}) **"
    print(f"  {label:44s} last round = {lr}{tag}")
    return lr

print("="*74); print("PHASE A -- reproduce Beyne-Verbauwhede (must be 1 / 13 / 20 / 21)"); print("="*74)
report("prime  2^64-2^32+1     e=1 t=8", 2**64-2**32+1, 1, 8, 1)
report("deg-2  (2^31-2^24+1)^2 e=2 t=8", 2**31-2**24+1, 2, 8, 13)
report("deg-4  (2^17-1)^4      e=4 t=8", 2**17-1,       4, 8, 20)
report("deg-8  (2^8+1)^8       e=8 t=8", 2**8+1,        8, 8, 21)

print("\n" + "="*74); print("PHASE B -- OUR PARAMETERS (base prime ~2^64, e*t = 16)"); print("="*74)
for qlabel, Q in [("Frog  q=15912092521325583641", 15912092521325583641),
                  ("dual  q=2^64-257",             2**64 - 257)]:
    print(f"\n### {qlabel}")
    report("tau=1  e=1 t=16", Q, 1, 16)
    report("tau=2  e=2 t=8 ", Q, 2, 8)
    report("tau=4  e=4 t=4  (SLOW; >=42, raise max_rounds to chase the exact death)", Q, 4, 4)
print("\nDONE")
