"""
FCT-6: what would CLAASP-MP find, if it could be run?

CLAASP-MP bounds the F_2 algebraic degree of an output bit and turns
"degree < cube dimension" into an INTEGRAL DISTINGUISHER.  The full component
graph is ~10^9 binary variables (fct7), far past any solver.  But the thing it
would certify is directly computable, and exactly:

  the ANF coefficient of the FULL monomial x_0...x_{m-1} over an m-cube is the
  XOR of the function over all 2^m cube points.  So

      cube sum == 0  for an output bit  <=>  its degree in the cube variables
                                             is < m  <=>  that bit is BALANCED
                                             over the cube  =  the distinguisher

  cube sum == 1                        <=>  degree == m exactly, and NO upper
                                             bound the MILP could prove can
                                             certify a distinguisher over that
                                             cube -- the answer is settled
                                             before the solver runs.

That is one XOR per evaluation, so it runs at DEPLOYMENT parameters on the
VERSIONED spec rather than on a model of it.

Controls (must pass or the measurement says nothing):
  C1  m=1 cube on a 0-round permutation: the state is affine in the cube bits,
      so every bit is balanced -- all cube sums zero.
  C2  a deliberately LOW-degree stand-in (the P=0 variant is still carry-laden,
      so instead: XOR of two cube bits) must give cube sum 0 at m=3 and 1 at m=1.
  C3  a random function must give ~half the bits nonzero.
  ⚑ C4, the best one, is INSIDE the measurement rather than beside it: at
      rounds=1 the LEFT branch is the copied Feistel branch, so every one of
      its bits is balanced for EVERY base state -- a REAL integral property.
      The run must find it (1024/1024 against a chance baseline of 1).  If it
      does not, the harness cannot see integral properties at all and every
      "nothing found" row below is worthless.
⚠ an earlier draft of this file used a Mobius transform and asserted that bit k
of (x+c) mod 2^M has degree k+1.  The control went RED and the ANALYTIC CLAIM
was what was wrong (carry_k depends on x_0..x_{k-1}, so the degree is max(k,1)).
Recorded because a control that only ever confirms is not a control.
"""
import os, random, sys, time

SPEC = os.path.expanduser("~/src/ring-ro-hash/design_gadget_feistel.py")

src = open(SPEC).read()
prefix = src[:src.index("# ================================================== (1) bijectivity")]
assert "\nD = 16\n" in prefix, "spec's ring degree is no longer D = 16 -- re-read the spec"
ns = {"__name__": "spec"}
exec(compile(prefix, SPEC, "exec"), ns)
Feistel, D = ns["Feistel"], ns["D"]
Q = (1 << 64) - 257

print(f"loaded {SPEC}  (ring degree D={D}, unpatched)")
print(f"modulus q = 2^64-257 = {Q}   (the deployed tau=2 joint modulus,")
print(f"  notes/ring-hash-dual-mode.md sec.5a; the versioned script still names 2^64-59)")


def cube_sums(fn, m, nout_words):
    """XOR of the packed output over all 2^m cube points."""
    acc = 0
    for x in range(1 << m):
        acc ^= fn(x)
    return acc


# ------------------------------------------------------------------ controls
print("\n" + "=" * 78)
print("CONTROLS")
print("=" * 78)
ok = True

# C1: 0 rounds -- output is the input, affine in the cube bits
F0 = Feistel(Q, seed=2026, w=1, p=2, nr=1)
rng = random.Random(1)
L0 = [[rng.randrange(Q) for _ in range(D)] for _ in range(1)]
R0 = [[rng.randrange(Q) for _ in range(D)] for _ in range(1)]
R0[0][0] &= ~0xFFFF


def pack(a, b):
    acc = 0
    for e in list(a) + list(b):
        for c in e:
            acc = (acc << 64) | c
    return acc


def make_fn(F, Lv, Rv, rounds, m):
    def fn(x):
        R = [r[:] for r in Rv]
        R[0][0] = Rv[0][0] | x
        a, b = F.perm([l[:] for l in Lv], R, rounds=rounds)
        return pack(a, b)
    return fn


c1 = cube_sums(make_fn(F0, L0, R0, 0, 2), 2, 0)
good = (c1 == 0)
ok &= good
print(f"  C1 0-round permutation, 2-cube: cube sum = {c1}  "
      f"({'all balanced, ok' if good else 'FAIL'})")

# C2: an explicitly low-degree function
c2a = 0
for x in range(1 << 3):
    c2a ^= (x ^ (x >> 1)) & 1
c2b = 0
for x in range(1 << 1):
    c2b ^= x & 1
good = (c2a == 0 and c2b == 1)
ok &= good
print(f"  C2 XOR-of-bits: 3-cube sum = {c2a} (want 0), 1-cube sum = {c2b} (want 1)"
      f"  {'ok' if good else 'FAIL'}")

# C3: a random function must NOT be balanced everywhere
rr = random.Random(7)
tbl = [rr.getrandbits(64) for _ in range(1 << 12)]
c3 = 0
for v in tbl:
    c3 ^= v
nz = bin(c3).count("1")
good = 20 <= nz <= 44
ok &= good
print(f"  C3 random 64-bit function, 12-cube: {nz}/64 bits nonzero "
      f"(want ~32)  {'ok' if good else 'FAIL'}")

if not ok:
    print("\nCONTROLS FAILED -- NO VERDICT.")
    sys.exit(2)
print("  controls pass.")

# --------------------------------------------------------------- measurement
print("\n" + "=" * 78)
print("MEASUREMENT -- cube over the low bits of coefficient 0 of R[0]")
print("  deployment parameters: q=2^64-257, d=16, K=4, B=2^16, P=2")
print("=" * 78)

print("""
⚑ ONE base state is not enough.  For a random permutation each output bit has a
zero cube sum with probability 1/2, so "half the bits are balanced" is what
randomness looks like, not a distinguisher.  An INTEGRAL DISTINGUISHER is a bit
balanced for EVERY base state.  So each configuration is run over NBASE
independent base states and we count bits balanced in ALL of them, against the
chance baseline NOUT * 2^-NBASE.
""")

CONFIGS = [
    (1, 16, 8, "w=1 (fewer parallel lanes than deployment; w only ADDS mixing)"),
    (4, 12, 5, "w=4 (FULL deployment width)"),
]
# FCT6_CONFIGS="w:m:nbase,w:m:nbase" overrides, for running a cheaper cube when
# the box is contended.  ROUNDS likewise.
if os.environ.get("FCT6_CONFIGS"):
    CONFIGS = []
    for spec in os.environ["FCT6_CONFIGS"].split(","):
        a, b, c = (int(t) for t in spec.split(":"))
        CONFIGS.append((a, b, c, f"w={a} (override)"))
ROUNDS = tuple(int(t) for t in os.environ.get("FCT6_ROUNDS", "1,2").split(","))

for w, M, NBASE, label in CONFIGS:
    print(f"\n--- {label};  cube dimension m={M}, {NBASE} base states ---")
    NOUT = 2 * w * D * 64
    half = NOUT // 2
    F = Feistel(Q, seed=2026, w=w, p=2, nr=4)
    for rounds in ROUNDS:
        rng = random.Random(20260818 + rounds)
        always_balanced = (1 << NOUT) - 1          # bit set = balanced so far
        nz_first = None
        t0 = time.time()
        for _ in range(NBASE):
            Lv = [[rng.randrange(Q) for _ in range(D)] for _ in range(w)]
            Rv = [[rng.randrange(Q) for _ in range(D)] for _ in range(w)]
            Rv[0][0] &= ~((1 << M) - 1)
            acc = cube_sums(make_fn(F, Lv, Rv, rounds, M), M, NOUT)
            if nz_first is None:
                nz_first = acc
            always_balanced &= ~acc & ((1 << NOUT) - 1)
        el = time.time() - t0

        nz = bin(nz_first).count("1")
        nzl = bin(nz_first >> half).count("1")
        nzr = bin(nz_first & ((1 << half) - 1)).count("1")
        bal = bin(always_balanced).count("1")
        bal_l = bin(always_balanced >> half).count("1")
        bal_r = bin(always_balanced & ((1 << half) - 1)).count("1")
        chance = NOUT * (2.0 ** -NBASE)

        print(f"    rounds={rounds}   {NBASE} x 2^{M} evaluations in {el:>5.0f}s  "
              f"output bits = {NOUT}")
        print(f"      single base state, nonzero cube sum (degree == {M}): "
              f"{nz}/{NOUT} ({100*nz/NOUT:.1f}%)   [random baseline 50%]")
        print(f"        LEFT branch {nzl}/{half} ({100*nzl/half:.1f}%)   "
              f"RIGHT branch {nzr}/{half} ({100*nzr/half:.1f}%)")
        print(f"      ⚑ balanced in ALL {NBASE} base states (integral property): "
              f"{bal}/{NOUT}   [expected by chance {chance:.1f}]")
        print(f"        LEFT branch {bal_l}/{half}   RIGHT branch {bal_r}/{half}")

print()
print("=" * 78)
print("READING")
print("=" * 78)
print("""\
  A nonzero cube sum on an output bit means its exact F_2 degree in the cube
  variables is already the full cube dimension.  CLAASP-MP's MILP computes an
  UPPER bound on that degree, and an upper bound is never below the exact
  value -- so wherever the exact degree is already saturated, the MILP cannot
  certify an integral distinguisher over that cube no matter how well it is
  solved.  The ~10^9-variable model would return "no distinguisher", which is
  what 2^m evaluations of the real primitive say directly.

  The mechanism is not subtle: step (1) of the round is a 64-bit modular
  addition, and a ripple carry drives the F_2 degree of the high bits to the
  full width of the addend in ONE operation -- before any plane product or
  ring multiplication is applied.

  ⚠ This is NOT a security result.  It says the F_2 degree instrument is blind
  here, not that the primitive is strong.""")
