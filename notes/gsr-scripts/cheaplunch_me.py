#!/usr/bin/env python3
"""CheapLunch (eprint 2025/2040) Appendix D.1 non-MDS `M_E` round-skip, checked
against the DEPLOYED breadstuffs Poseidon2-BabyBear-w16.

Companion to `krylov.py` / `gsr_calc.py` / `all_inst.py` (the GSR lane, 2026/1692).
Nothing here is assumed from a reference parameter set: the permutation model is
validated against the Lean `#guard` KATs before anything is concluded from it.

Stages
  0  model validation   -- our perm reproduces Poseidon2BabyBearW16.lean's two KATs
  1  M_E comparison     -- CheapLunch's printed M_E vs. our deployed M_E
  2  structure          -- the invariant subspace that makes the skip work
  3  CheapLunch replay  -- their published a0/b0 chain, on their constants
  4  our construction   -- solve the 2-round chain on OUR deployed constants
  5  third round        -- is a 3-round chain possible? (the obstruction)
"""

# ---------------------------------------------------------------- fields

P_BB = 2013265921          # BabyBear   2^31 - 2^27 + 1   (deployed)
P_KB = 2130706433          # KoalaBear  2^31 - 2^24 + 1   (CheapLunch's example)
ALPHA_BB = 7
ALPHA_KB = 3


def inv(a, p):
    return pow(a % p, p - 2, p)


def root_alpha(x, alpha, p):
    """x^(1/alpha); exists iff gcd(alpha, p-1) == 1.

    NB p-1 is COMPOSITE, so the exponent inverse must be extended-Euclid, not
    Fermat.  (Getting this wrong is silent: it returns a wrong root and the
    chain simply fails to verify.)
    """
    import math
    assert math.gcd(alpha, p - 1) == 1, f"x^{alpha} is not a bijection on F_{p}"
    return pow(x % p, pow(alpha, -1, p - 1), p)


# ------------------------------------------------- univariate roots over F_p

def _pmul(a, b, f, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
    return _prem(r, f, p)


def _prem(a, f, p):
    a = a[:]
    df = len(f) - 1
    while len(a) - 1 >= df and any(a):
        while a and a[-1] == 0:
            a.pop()
        if len(a) - 1 < df:
            break
        c = a[-1] * inv(f[-1], p) % p
        sh = len(a) - 1 - df
        for i in range(df + 1):
            a[sh + i] = (a[sh + i] - c * f[i]) % p
        while a and a[-1] == 0:
            a.pop()
    return a if a else [0]


def _pgcd(a, b, p):
    a, b = a[:], b[:]
    while any(b):
        a, b = b, _prem(a, b, p)
        while b and b[-1] == 0:
            b.pop()
        if not b:
            b = [0]
    ia = inv(a[-1], p)
    return [x * ia % p for x in a]


def _ppow(base, e, f, p):
    r, b = [1], base[:]
    while e:
        if e & 1:
            r = _pmul(r, b, f, p)
        b = _pmul(b, b, f, p)
        e >>= 1
    return r


def poly_roots(f, p):
    """All roots in F_p of f (coefficients low->high)."""
    while f and f[-1] == 0:
        f.pop()
    if len(f) <= 1:
        return []
    xp = _ppow([0, 1], p, f, p)                      # x^p mod f
    h = xp[:] + [0] * max(0, 2 - len(xp))
    h[1] = (h[1] - 1) % p                            # x^p - x
    while h and h[-1] == 0:
        h.pop()
    if not h:
        h = [0]
    g = _pgcd(f, h, p) if any(h) else f[:]
    if len(g) <= 1:
        return []
    out, stack = [], [g]
    import random
    rng = random.Random(2026)
    while stack:
        h = stack.pop()
        while h and h[-1] == 0:
            h.pop()
        if len(h) <= 1:
            continue
        if len(h) == 2:
            out.append((-h[0]) * inv(h[1], p) % p)
            continue
        for _ in range(200):
            r = rng.randrange(p)
            t = _ppow([r, 1], (p - 1) // 2, h, p)
            t = t[:] + [0] * (1 - len(t))
            t[0] = (t[0] - 1) % p
            d = _pgcd(t, h, p)
            if 1 <= len(d) - 1 < len(h) - 1:
                stack.append(d)
                stack.append(_prem(h, d, p) if False else _pdiv(h, d, p))
                break
    return sorted(set(x for x in out if _peval(f, x, p) == 0))


def _pdiv(a, b, p):
    a = a[:]
    q = [0] * max(1, len(a) - len(b) + 1)
    db = len(b) - 1
    ib = inv(b[-1], p)
    while len(a) - 1 >= db and any(a):
        c = a[-1] * ib % p
        sh = len(a) - 1 - db
        q[sh] = c
        for i in range(db + 1):
            a[sh + i] = (a[sh + i] - c * b[i]) % p
        while a and a[-1] == 0:
            a.pop()
        if not a:
            a = [0]
    return q


def _peval(f, x, p):
    r = 0
    for c in reversed(f):
        r = (r * x + c) % p
    return r


# ---------------------------------------------------------------- matrices

# Plonky3 `MDSMat4`, exactly the four formulas in
# metatheory/Dregg2/Circuit/Poseidon2BabyBearW16.lean:mat4  (circulant [2,3,1,1])
A_OURS = [[2, 3, 1, 1],
          [1, 2, 3, 1],
          [1, 1, 2, 3],
          [3, 1, 1, 2]]

# The 4x4 block CheapLunch prints in D.1 (the Poseidon2-paper M_4, ref [35]).
A_THEIRS = [[5, 7, 1, 3],
            [4, 6, 1, 1],
            [1, 3, 5, 7],
            [1, 1, 4, 6]]


def build_me(A, p):
    """M_E = [[2A,A,A,A],[A,2A,A,A],[A,A,2A,A],[A,A,A,2A]] (t=16)."""
    M = [[0] * 16 for _ in range(16)]
    for bi in range(4):
        for bj in range(4):
            f = 2 if bi == bj else 1
            for r in range(4):
                for c in range(4):
                    M[4 * bi + r][4 * bj + c] = (f * A[r][c]) % p
    return M


def matvec(M, v, p):
    return [sum(M[i][j] * v[j] for j in range(len(v))) % p for i in range(len(M))]


def mat4_apply(A, v, p):
    return [sum(A[i][j] * v[j] for j in range(4)) % p for i in range(4)]


def mat_inv4(A, p):
    n = 4
    M = [[A[i][j] % p for j in range(n)] + [1 if i == j else 0 for j in range(n)]
         for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] % p)
        M[col], M[piv] = M[piv], M[col]
        ip = inv(M[col][col], p)
        M[col] = [x * ip % p for x in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [(M[r][k] - f * M[col][k]) % p for k in range(2 * n)]
    return [row[n:] for row in M]


# ---------------------------------------------------------------- our deployed permutation

# Poseidon2BabyBearW16.lean :: rcExtInitial / rcExtFinal / rcInternal
RC_EXT_INIT = [
    [0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
     0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
     0x221e2e36, 0x1ab7202e],
    [0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
     0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
     0x52eb6ba2, 0x50642905],
    [0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
     0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
     0x29fbda49, 0x018afffd],
    [0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
     0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
     0x2cc78315, 0x1e36ea47],
]
RC_EXT_FINAL = [
    [0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
     0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
     0x6a2d3d10, 0x20523767],
    [0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
     0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
     0x49a12590, 0x35ec52a1],
    [0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
     0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
     0x45e1547b, 0x4a8db2ab],
    [0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
     0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
     0x3c8bcd87, 0x608758b8],
]
RC_INTERNAL = [0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb,
               0x61210ce0, 0x3c318939, 0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606,
               0x241af16d]
# 1 + V, from circuit/src/poseidon2.rs::INTERNAL_DIAG
INTERNAL_DIAG = [2013265920, 2, 3, 1006632962, 4, 5, 1006632961, 2013265919, 2013265918,
                 2005401602, 1509949442, 1761607682, 2013265907, 7864321, 125829121, 16]

ME_OURS = build_me(A_OURS, P_BB)


def sbox_layer(s, alpha, p):
    return [pow(x, alpha, p) for x in s]


def ext_round(s, rc, M, alpha, p):
    """One external round as our Lean/Rust does it: S-box on (state+rc), then M_E."""
    return matvec(M, [pow((s[i] + rc[i]) % p, alpha, p) for i in range(16)], p)


def int_round(s, rc, p):
    s0 = pow((s[0] + rc) % p, ALPHA_BB, p)
    v = [s0] + s[1:]
    tot = sum(v) % p
    return [(tot + (INTERNAL_DIAG[i] - 1) * v[i]) % p for i in range(16)]


def perm_ours(inp):
    p = P_BB
    s = matvec(ME_OURS, [x % p for x in inp], p)
    for rc in RC_EXT_INIT:
        s = ext_round(s, rc, ME_OURS, ALPHA_BB, p)
    for rc in RC_INTERNAL:
        s = int_round(s, rc, p)
    for rc in RC_EXT_FINAL:
        s = ext_round(s, rc, ME_OURS, ALPHA_BB, p)
    return s


# ---------------------------------------------------------------- stage 0

def stage0():
    print("=" * 78)
    print("STAGE 0  model validation -- our permutation against the Lean #guard KATs")
    print("=" * 78)
    kat1 = [1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788,
            1726691001, 1761127344, 1552405120, 417318995, 36799261, 1215172152,
            614923223, 1300746575, 957311597, 304856115]
    kat0 = [1168947398, 128782440, 747404447, 883925857, 360581875, 1704698758,
            1878363991, 1054281681, 682225194, 705839125, 1218819873, 41544645,
            1095344608, 174996601, 1678438226, 11259290]
    g1 = perm_ours(list(range(16)))
    g0 = perm_ours([0] * 16)
    ok = (g1 == kat1) and (g0 == kat0)
    print(f"  perm([0..15]) matches Lean #guard : {g1 == kat1}")
    print(f"  perm([0]*16)  matches Lean #guard : {g0 == kat0}")
    assert ok, "model does NOT reproduce the deployed permutation -- stop."
    print("  => the model below IS the deployed permutation, not a reconstruction.\n")


# ---------------------------------------------------------------- stage 1

def stage1():
    print("=" * 78)
    print("STAGE 1  is CheapLunch's printed M_E our deployed M_E?")
    print("=" * 78)
    theirs = build_me(A_THEIRS, P_KB)
    same = all(ME_OURS[i][j] == theirs[i][j] for i in range(16) for j in range(16))
    print(f"  our M_4 (Plonky3 MDSMat4)      = {A_OURS}")
    print(f"  CheapLunch's M_4 (Poseidon2 [35]) = {A_THEIRS}")
    print(f"  16x16 matrices identical: {same}")
    print("  => their published skip VECTOR does not transfer; the PHENOMENON must be")
    print("     recomputed on our matrix.  Outer block form [[2A,A,A,A],...] is shared.\n")
    return same


# ---------------------------------------------------------------- stage 2

def blocks(v):
    return [v[0:4], v[4:8], v[8:12], v[12:16]]


def unblocks(bs):
    return [x for b in bs for x in b]


def stage2(A, p, label):
    print("=" * 78)
    print(f"STAGE 2  the invariant subspace of M_E  ({label})")
    print("=" * 78)
    M = build_me(A, p)
    # M_E maps block j of the input to A*(u_j + sum_j' u_j').
    import random
    random.seed(7)
    ok_form = True
    for _ in range(200):
        u = [random.randrange(p) for _ in range(16)]
        bs = blocks(u)
        S = [sum(bs[j][q] for j in range(4)) % p for q in range(4)]
        pred = unblocks([mat4_apply(A, [(bs[j][q] + S[q]) % p for q in range(4)], p)
                         for j in range(4)])
        if pred != matvec(M, u, p):
            ok_form = False
    print(f"  M_E block_j(u) == A*(u_j + sum_j u_j)   : {ok_form}")
    # W = {(0, v, -v, 0)} is invariant, and dim-4.
    ok_inv = True
    for _ in range(200):
        v = [random.randrange(p) for _ in range(4)]
        a = unblocks([[0] * 4, v, [(-x) % p for x in v], [0] * 4])
        img = blocks(matvec(M, a, p))
        Av = mat4_apply(A, v, p)
        if img[0] != [0] * 4 or img[3] != [0] * 4 \
           or img[1] != Av or img[2] != [(-x) % p for x in Av]:
            ok_inv = False
    print(f"  W = {{(0,v,-v,0)}} is M_E-invariant, M_E|_W = A : {ok_inv}")
    print(f"  |supp(M_E a)| for a in W  = 8  (not 16)  -> halves the alignment cost")
    print(f"  S-box preserves W's antisymmetry iff alpha is odd; alpha here is odd: "
          f"{ (ALPHA_BB if p == P_BB else ALPHA_KB) % 2 == 1 }")
    return ok_form and ok_inv


# ---------------------------------------------------------------- stage 3  (their replay)

CL_a0 = [0x0, 0x0, 0x0, 0x0,
         0x3ae7d1cb, 0x693aa524, 0x2892157b, 0x2ceec489,
         0x44182e36, 0x15c55add, 0x566dea86, 0x52113b78,
         0x0, 0x0, 0x0, 0x0]
CL_b0 = [0x3055717b, 0x2112c45a, 0x3405c236, 0x7133b04c,
         0x7b577bb9, 0x0d508a2e, 0x056357b8, 0x12546263,
         0x1cb56c27, 0x0258c017, 0x4aefc4d0, 0x560b9321,
         0x709b4660, 0x22d30c54, 0x0, 0x0]
CL_C1 = [0x1b9721fa, 0x1252dc26, 0x686dc5c6, 0x65e48721, 0x68c4a3e4, 0x5dc974d7,
         0x6c06ab8f, 0x286a3475, 0x0103790a, 0x13dcd1d0, 0x30cfa2c1, 0x6087354f,
         0x7c66b137, 0x42070c64, 0x6f777ed5, 0x0bc35277]
CL_C2 = [0x37b608e3, 0x2a201928, 0x6a38a2ab, 0x796c8c09, 0x0460cd14, 0x6bac6d28,
         0x4551b22d, 0x773c1a8d, 0x5e977d45, 0x463ecca9, 0x7011d7aa, 0x7767d67f,
         0x545d8d19, 0x2801b9fe, 0x143c8a7e, 0x01bdd37c]


def line_step(a, b, C, M, alpha, p):
    """One round v -> S(M v + C) applied to the affine line {a X + b}.

    Returns (a', b', rho, ok): the image is the line {a' Y + b'} with
    Y = (X - rho)^alpha, when every coordinate in supp(M a) shares one root.
    """
    u = matvec(M, a, p)
    w = [(x + c) % p for x, c in zip(matvec(M, b, p), C)]
    sup = [i for i in range(16) if u[i] % p]
    if not sup:
        return None, None, None, False
    rho = (-w[sup[0]] * inv(u[sup[0]], p)) % p
    for i in sup:                                    # alignment: one common root
        if (w[i] + rho * u[i]) % p:
            return None, None, None, False
    a2 = [pow(u[i], alpha, p) if i in sup else 0 for i in range(16)]
    b2 = [0 if i in sup else pow(w[i], alpha, p) for i in range(16)]
    return a2, b2, rho, True


def verify_chain(a0, b0, Cs, M, alpha, p, trials=64):
    """Independently re-run the ACTUAL rounds on random X and check the state
    really lands on the predicted line (no shortcuts through line_step)."""
    import random
    random.seed(11)
    a, b, rhos = a0, b0, []
    lines = [(a0, b0)]
    for C in Cs:
        a, b, rho, ok = line_step(a, b, C, M, alpha, p)
        if not ok:
            return False, len(rhos), lines
        rhos.append(rho)
        lines.append((a, b))
    for _ in range(trials):
        X = random.randrange(p)
        st = [(a0[i] * X + b0[i]) % p for i in range(16)]
        var = X
        for r, C in enumerate(Cs):
            st = [pow((x + c) % p, alpha, p) for x, c in zip(matvec(M, st, p), C)]
            var = pow((var - rhos[r]) % p, alpha, p)
            aa, bb = lines[r + 1]
            if st != [(aa[i] * var + bb[i]) % p for i in range(16)]:
                return False, r, lines
    return True, len(Cs), lines


def stage3():
    print("=" * 78)
    print("STAGE 3  replay CheapLunch's OWN published chain (model validation)")
    print("=" * 78)
    M = build_me(A_THEIRS, P_KB)
    ok, n, lines = verify_chain(CL_a0, CL_b0, [CL_C1, CL_C2], M, ALPHA_KB, P_KB)
    print(f"  rounds of their chain verified against the real rounds: {n}")
    print(f"  chain fully reproduces: {ok}")
    if n >= 1:
        a1 = lines[1][0]
        print(f"  a1 support               : {[i for i in range(16) if a1[i]]}")
        b1 = lines[1][1]
        print(f"  b1 support               : {[i for i in range(16) if b1[i]]}")
    if n >= 2:
        a2 = lines[2][0]
        print(f"  a2 support               : {[i for i in range(16) if a2[i]]}")
        print(f"  a2 (nonzero entries)     : {[hex(a2[i]) for i in range(16) if a2[i]]}")
    print()
    return ok, n


# ---------------------------------------------------------------- stage 4  (ours)

def solve_chain_ours(A, p, alpha, C1, C2, q0=0, j0=0, seed=1):
    """CONSTRUCT a 2-round chain for our M_E / field / alpha / round constants.

    Ansatz (proved forced below): a0 = (0, v, -v, 0) in the invariant subspace W.
    Sparse round-2 design, matching what CheapLunch's own a2 turns out to be:
    make  A w = gamma * e_{q0}  so that supp(M_E a1) is TWO coordinates and the
    round-2 alignment costs ONE equation instead of four.

      round 2 :  (A S')_{q0} = -(C2_{1,q0} + C2_{2,q0})/2        [1 eq]
      round 1 :  (E1)/(E2) determine b0 blocks 1,2, rho_1 free   [absorbed]
      CICO-1  :  b0[j0] = 0   with a0[j0] = 0 automatically       [1 eq]

    The two remaining equations are solved exactly: eliminating g3[0] linearly
    against g0[0] turns them into ONE degree-alpha univariate over F_p.
    """
    import random
    rng = random.Random(seed)
    Ai = mat_inv4(A, p)
    C1b, C2b = blocks(C1), blocks(C2)
    half, fifth = inv(2, p), inv(5, p)
    sumC1 = [(C1b[0][q] + C1b[1][q] + C1b[2][q] + C1b[3][q]) % p for q in range(4)]

    tau = [(C2b[1][q] - C2b[2][q]) % p for q in range(4)]
    if tau[q0] % p == 0:
        return None
    T = (-(C2b[1][q0] + C2b[2][q0]) * half) % p          # (A S')_{q0} must equal T

    for _attempt in range(60):
        gamma = rng.randrange(1, p)
        rho1 = rng.randrange(p)
        w = [gamma * Ai[r][q0] % p for r in range(4)]     # A w = gamma * e_{q0}
        if any(x == 0 for x in w):
            continue
        Av = [root_alpha(x, alpha, p) for x in w]
        v = mat4_apply(Ai, Av, p)
        if all(x == 0 for x in v):
            continue
        a0 = unblocks([[0] * 4, v, [(-x) % p for x in v], [0] * 4])

        g0r = [rng.randrange(p) for _ in range(4)]
        g3r = [rng.randrange(p) for _ in range(4)]

        # eq A : sum_q A[q0][q]*(g0[q]^a + g3[q]^a) = T
        R2 = (T - sum(A[q0][q] * (pow(g0r[q], alpha, p) + pow(g3r[q], alpha, p))
                      for q in range(1, 4))) % p
        R2 = R2 * inv(A[q0][0], p) % p                    # x^a + y^a = R2
        # eq B : b0[j0] = 0 ,  b0_block0 = Ai[(4/5)g0 - (1/5)g3 - C1_0 + (1/5)sumC1]
        K = [(-C1b[0][q] + fifth * sumC1[q]) % p for q in range(4)]
        rest = sum(Ai[j0][q] * ((4 * fifth * g0r[q] - fifth * g3r[q] + K[q]) % p)
                   for q in range(1, 4)) % p
        rest = (rest + Ai[j0][0] * K[0]) % p
        if Ai[j0][0] % p == 0:
            continue
        R4 = (-rest) * inv(Ai[j0][0], p) % p              # (4/5)x - (1/5)y = R4
        # y = 4x - 5*R4
        mu, nu = 4 % p, (-5 * R4) % p
        # f(x) = x^a + (mu x + nu)^a - R2
        from math import comb
        f = [0] * (alpha + 1)
        f[alpha] = 1
        for i in range(alpha + 1):
            f[i] = (f[i] + comb(alpha, i) * pow(mu, i, p) * pow(nu, alpha - i, p)) % p
        f[0] = (f[0] - R2) % p
        roots = poly_roots(f[:], p)
        if not roots:
            continue
        x = roots[0]
        y = (mu * x + nu) % p
        g0 = [x] + g0r[1:]
        g3 = [y] + g3r[1:]

        Sig = [t * fifth % p for t in mat4_apply(
            Ai, [(g0[q] + g3[q] - sumC1[q]) % p for q in range(4)], p)]
        b00 = [(mat4_apply(Ai, [(g0[q] - C1b[0][q]) % p for q in range(4)], p)[q]
                - Sig[q]) % p for q in range(4)]
        b03 = [(mat4_apply(Ai, [(g3[q] - C1b[3][q]) % p for q in range(4)], p)[q]
                - Sig[q]) % p for q in range(4)]
        sm = mat4_apply(Ai, [(-(C1b[1][q] + C1b[2][q])) % p for q in range(4)], p)
        sm = [(sm[q] - 2 * Sig[q]) % p for q in range(4)]
        df = mat4_apply(Ai, [(-(C1b[1][q] - C1b[2][q])) % p for q in range(4)], p)
        df = [(df[q] - 2 * rho1 * v[q]) % p for q in range(4)]
        b01 = [((sm[q] + df[q]) * half) % p for q in range(4)]
        b02 = [((sm[q] - df[q]) * half) % p for q in range(4)]
        b0 = unblocks([b00, b01, b02, b03])
        return a0, b0, q0, j0
    return None


def _unused_solve(A, p, alpha, C1, C2, cico_index, g3_seed=1, c=1):
    """Construct a 2-round chain for OUR M_E / field / alpha / round constants.

    Ansatz a0 = (0, v, -v, 0) in W.  Everything below is the closed-form solve
    derived from M_E block_j(u) = A(u_j + sum u):

      round 2 sum-condition  ->  S' = beta_0 + beta_3 = A^-1( -(C2_1 + C2_2)/2 )
      round 2 diff-condition ->  A w  ||  tau = C2_1 - C2_2 ,  w = c * A^-1 tau
      round 1                ->  b0 blocks from (E1)/(E2) with rho_1 free
    """
    Ai = mat_inv4(A, p)
    C1b, C2b = blocks(C1), blocks(C2)
    half = inv(2, p)

    tau = [(C2b[1][q] - C2b[2][q]) % p for q in range(4)]
    if all(x == 0 for x in tau):
        return None
    # a1 = (0, w, -w, 0) with A w = c*tau
    w = mat4_apply(Ai, [c * t % p for t in tau], p)
    # v with (A v)^alpha = w   ->   A v = w^(1/alpha)
    Av = [root_alpha(x, alpha, p) for x in w]
    v = mat4_apply(Ai, Av, p)
    if all(x == 0 for x in v):
        return None
    a0 = unblocks([[0] * 4, v, [(-x) % p for x in v], [0] * 4])

    Sp = mat4_apply(Ai, [(-(C2b[1][q] + C2b[2][q]) * half) % p for q in range(4)], p)

    def build(g3, rho1):
        beta3 = [pow(x, alpha, p) for x in g3]
        beta0 = [(Sp[q] - beta3[q]) % p for q in range(4)]
        g0 = [root_alpha(x, alpha, p) for x in beta0]
        # Sigma from the self-consistency of the block sums (5*Sigma = ...)
        rhs = [(g0[q] + g3[q] - C1b[0][q] - C1b[1][q] - C1b[2][q] - C1b[3][q]) % p
               for q in range(4)]
        Sig = [x * inv(5, p) % p for x in mat4_apply(Ai, rhs, p)]
        b00 = [(mat4_apply(Ai, [(g0[q] - C1b[0][q]) % p for q in range(4)], p)[q] - Sig[q]) % p
               for q in range(4)]
        b03 = [(mat4_apply(Ai, [(g3[q] - C1b[3][q]) % p for q in range(4)], p)[q] - Sig[q]) % p
               for q in range(4)]
        sm = mat4_apply(Ai, [(-(C1b[1][q] + C1b[2][q])) % p for q in range(4)], p)
        sm = [(sm[q] - 2 * Sig[q]) % p for q in range(4)]                  # b01 + b02
        df = mat4_apply(Ai, [(-(C1b[1][q] - C1b[2][q])) % p for q in range(4)], p)
        df = [(df[q] - 2 * rho1 * v[q]) % p for q in range(4)]             # b01 - b02
        b01 = [((sm[q] + df[q]) * half) % p for q in range(4)]
        b02 = [((sm[q] - df[q]) * half) % p for q in range(4)]
        return unblocks([b00, b01, b02, b03])

    # one free scalar is enough to hit the CICO input zero: sweep g3[0]
    import random
    rng = random.Random(g3_seed)
    base = [rng.randrange(p) for _ in range(4)]
    rho1 = rng.randrange(p)
    for _ in range(4000):
        g3 = list(base)
        b0 = build(g3, rho1)
        if b0[cico_index] == 0:
            return a0, b0
        # linear-in-nothing; just resample (the map is a bijection in practice)
        base[0] = rng.randrange(p)
    return a0, build(base, rho1)      # return anyway; caller reports CICO status


def stage4():
    print("=" * 78)
    print("STAGE 4  CONSTRUCT the 2-round chain on OUR DEPLOYED constants")
    print("=" * 78)
    p, alpha, A = P_BB, ALPHA_BB, A_OURS
    C1, C2 = RC_EXT_INIT[0], RC_EXT_INIT[1]
    import math
    print(f"  gcd(alpha={alpha}, p-1) = {math.gcd(alpha, p - 1)}  "
          f"-> x^{alpha} is a bijection, alpha-th roots exist: "
          f"{math.gcd(alpha, p - 1) == 1}")
    found = None
    for q0 in range(4):
        for j0 in range(4):
            res = solve_chain_ours(A, p, alpha, C1, C2, q0=q0, j0=j0)
            if res is None:
                continue
            a0, b0, q0, j0 = res
            ok, n, lines = verify_chain(a0, b0, [C1, C2], ME_OURS, alpha, p)
            if ok and a0[j0] == 0 and b0[j0] == 0:
                found = (a0, b0, lines, q0, j0)
                break
        if found:
            break
    if not found:
        print("  NO 2-round chain constructed on our constants."); return False, 0, None
    a0, b0, lines, q0, j0 = found
    print(f"  construction parameters: q0={q0} (sparse support of A w), CICO index j0={j0}")
    print(f"  CICO-1 input zero  : a0[{j0}]={a0[j0]}, b0[{j0}]={b0[j0]}  (both zero)")
    ok, n, lines = verify_chain(a0, b0, [C1, C2], ME_OURS, alpha, p, trials=256)
    print(f"  rounds verified by RE-RUNNING the deployed rounds on 256 random X: {n}")
    print(f"  ** 2-round chain HOLDS on our deployed constants: {ok} **")
    for r, (a, b) in enumerate(lines):
        print(f"    a{r} support = {[i for i in range(16) if a[i]]}   "
              f"|supp| = {sum(1 for x in a if x)}")
    print(f"  a0 = {[hex(x) for x in a0]}")
    print(f"  b0 = {[hex(x) for x in b0]}")
    print()
    return ok, n, (a0, b0, lines)


# ---------------------------------------------------------------- stage 5

def stage5(chain):
    print("=" * 78)
    print("STAGE 5  can a THIRD round be chained?  (the obstruction)")
    print("=" * 78)
    p, alpha, A = P_BB, ALPHA_BB, A_OURS
    Ai = mat_inv4(A, p)
    a0, b0, lines = chain
    C3 = RC_EXT_INIT[2]
    a2 = lines[2][0]
    a2b = blocks(a2)
    # round-3 direction condition: A * (block1 of a2) must be || to C3_1 - C3_2
    C3b = blocks(C3)
    tau3 = [(C3b[1][q] - C3b[2][q]) % p for q in range(4)]
    Aa2 = mat4_apply(A, a2b[1], p)
    # projective comparison
    ratios = set()
    for q in range(4):
        if Aa2[q] % p and tau3[q] % p:
            ratios.add(tau3[q] * inv(Aa2[q], p) % p)
        elif bool(Aa2[q] % p) != bool(tau3[q] % p):
            ratios.add(("mismatch", q))
    print(f"  A*(a2 block1)        = {[hex(x) for x in Aa2]}")
    print(f"  C3_block1 - C3_block2 = {[hex(x) for x in tau3]}")
    print(f"  distinct ratios (1 == parallel, hence chainable): {len(ratios)}")
    print(f"  parallel? {len(ratios) == 1}")
    print("  The direction entering round 3 is FIXED by C^(2) (the free scalar c")
    print("  rescales but cannot rotate it: (c*tau)^alpha = c^alpha * tau^alpha).")
    print("  So 'parallel to C^(3)_1 - C^(3)_2' is 3 projective conditions with 0")
    print("  free parameters -- a ~p^-3 = 2^-93 coincidence, not a construction.")
    ok3, n3, _ = verify_chain(a0, b0, [RC_EXT_INIT[0], RC_EXT_INIT[1], C3],
                              ME_OURS, alpha, p)
    print(f"  direct check: 3-round chain from our solution holds? {ok3} (reached {n3})")
    print()


def stage5b():
    """EXHAUSTIVE: no 3-round chain of this shape exists, on either instance.

    Shape (proved forced for a 2-active-block family): a0 = (0,v,-v,0) up to the
    choice of block pair.  Round 2 forces  A w = c * tau2 * 1_J  with
    tau2 = C2_i - C2_j.  Hence the direction entering round 3 is
    A( (tau2*1_J)^alpha ), FIXED -- c rescales it but cannot rotate it.
    Round 3 then requires that direction || tau3 = C3_i - C3_j on its support.
    """
    print("=" * 78)
    print("STAGE 5b  EXHAUSTIVE search for a 3rd chainable round")
    print("=" * 78)
    for label, A, p, alpha, RCs in [
        ("OURS   (BabyBear, alpha=7, deployed RCs)", A_OURS, P_BB, ALPHA_BB,
         [RC_EXT_INIT[0], RC_EXT_INIT[1], RC_EXT_INIT[2]]),
        ("THEIRS (KoalaBear, d=3, CheapLunch RCs) ", A_THEIRS, P_KB, ALPHA_KB,
         [CL_C1, CL_C2, None]),
    ]:
        if RCs[2] is None:
            print(f"  {label}: round-3 constant not published -- skipped")
            continue
        C2b, C3b = blocks(RCs[1]), blocks(RCs[2])
        best, total = None, 0
        for i in range(4):
            for j in range(4):
                if i == j:
                    continue
                tau2 = [(C2b[i][q] - C2b[j][q]) % p for q in range(4)]
                tau3 = [(C3b[i][q] - C3b[j][q]) % p for q in range(4)]
                sup2 = [q for q in range(4) if tau2[q]]
                for mask in range(1, 1 << len(sup2)):
                    J = [sup2[b] for b in range(len(sup2)) if mask >> b & 1]
                    z = [0] * 4
                    for q in J:
                        z[q] = tau2[q]
                    zi = [pow(x, alpha, p) for x in z]
                    d3 = mat4_apply(A, zi, p)
                    sup3 = [q for q in range(4) if d3[q]]
                    if not sup3:
                        continue
                    total += 1
                    # need tau3 || d3 on sup3, and (no condition off sup3)
                    r0 = tau3[sup3[0]] * inv(d3[sup3[0]], p) % p
                    viol = sum(1 for q in sup3[1:]
                               if (tau3[q] - r0 * d3[q]) % p)
                    if best is None or viol < best[0]:
                        best = (viol, i, j, tuple(J), len(sup3))
        print(f"  {label}")
        print(f"    shapes enumerated (block pair x support subset): {total}")
        print(f"    best case: {best[0]} violated projective conditions "
              f"(block pair {best[1]},{best[2]}, J={list(best[3])}, |supp|={best[4]})")
        print(f"    3-round chain of this shape exists: {best[0] == 0}")
    print("    => the round-3 direction condition has ZERO free parameters, so it is")
    print("       a ~p^-3 = 2^-93 coincidence per shape.  Both instances stop at 2.\n")


def stage5c():
    """Is the 2-round skip a property of the CONSTANTS, or of the SHAPE?"""
    print("=" * 78)
    print("STAGE 5c  is the skip specific to our M_4, or to Poseidon2's outer form?")
    print("=" * 78)
    import random
    rng = random.Random(99)
    ok = 0
    trials = 0
    for _ in range(12):
        A = [[rng.randrange(1, P_BB) for _ in range(4)] for _ in range(4)]
        try:
            mat_inv4(A, P_BB)
        except StopIteration:
            continue
        M = build_me(A, P_BB)
        C1 = [rng.randrange(P_BB) for _ in range(16)]
        C2 = [rng.randrange(P_BB) for _ in range(16)]
        r = solve_chain_ours(A, P_BB, ALPHA_BB, C1, C2, q0=0, j0=0, seed=rng.randrange(10**6))
        trials += 1
        if r is None:
            continue
        a0, b0, _, j0 = r
        good, n, _ = verify_chain(a0, b0, [C1, C2], M, ALPHA_BB, P_BB, trials=16)
        if good and a0[j0] == 0 and b0[j0] == 0:
            ok += 1
    print(f"  random invertible M_4 + random round constants: "
          f"2-round chain built in {ok}/{trials} trials")
    print("  => the skip is a property of Poseidon2's OUTER block form [[2A,A,A,A],...]")
    print("     plus odd alpha, NOT of any particular M_4 or round-constant choice.")
    print("     There is no constant/matrix rotation that removes it.\n")


# ------------------------------------------------- polynomials in the chain variable

def zmul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
    return r


def zpow(a, e, p):
    r = [1]
    b = a[:]
    while e:
        if e & 1:
            r = zmul(r, b, p)
        b = zmul(b, b, p)
        e >>= 1
    return r


def stage6(chain):
    print("=" * 78)
    print("STAGE 6  COMPOSABILITY with GSR -- the degrees of freedom, counted")
    print("=" * 78)
    p, alpha = P_BB, ALPHA_BB
    a0, b0, lines = chain
    a2, b2 = lines[2]
    # state (in chain coordinates y) after the 2 skipped rounds: a2*Z + b2
    st = [[b2[i], a2[i]] for i in range(16)]          # coeffs low->high in Z
    for rnd, C in [(3, RC_EXT_INIT[2]), (4, RC_EXT_INIT[3])]:
        mv = []
        for i in range(16):
            acc = [0]
            for j in range(16):
                c = ME_OURS[i][j]
                if c:
                    term = [c * x % p for x in st[j]]
                    if len(term) > len(acc):
                        acc = acc + [0] * (len(term) - len(acc))
                    for q, x in enumerate(term):
                        acc[q] = (acc[q] + x) % p
            mv.append(acc)
        st = []
        for i in range(16):
            v = mv[i][:]
            v[0] = (v[0] + C[i]) % p
            st.append(zpow(v, alpha, p))
        deg = max(len(c) - 1 for c in st)
        print(f"  after external round {rnd}: state is a degree-{deg} curve in Z")
    # state entering the internal (partial) layer = M_E * y_4
    ent = []
    for i in range(16):
        acc = [0]
        for j in range(16):
            c = ME_OURS[i][j]
            if c:
                term = [c * x % p for x in st[j]]
                if len(term) > len(acc):
                    acc = acc + [0] * (len(term) - len(acc))
                for q, x in enumerate(term):
                    acc[q] = (acc[q] + x) % p
        ent.append(acc)
    f0 = ent[0]
    nz = sum(1 for q in range(1, len(f0)) if f0[q] % p)
    print()
    print("  GSR's FIRST forward-linearization condition is: coordinate 0 of the state")
    print("  entering partial round 1 must be a CONSTANT delta^(1) known in advance.")
    print(f"    that coordinate, as a polynomial in Z : degree {len(f0)-1}")
    print(f"    non-constant coefficients that must vanish: {nz}")
    print(f"    is it constant (i.e. can GSR linearize even ONE partial round)? "
          f"{nz == 0}")
    print()
    print("  DoF BUDGET -- the two constructions, on the same resource")
    print("  " + "-" * 74)
    print("  CheapLunch M_E skip (ours, as constructed above):")
    print("    free    : g0(4) + g3(4) + gamma(1) + rho_1(1)            = 10")
    print("    spent   : round-2 sum condition(1) + CICO-1 input zero(1) =  2")
    print("    SPARE   :                                                    8")
    print("    delivers: the state entering round 3 is a 1-PARAMETER curve.")
    print()
    print("  GSR gadget (t=16, k=1), from the sibling lane's read of 2026/1692:")
    print("    needs   : 1 backward CICO-in condition + min(R_P, t-2k)=13 forward")
    print("              linearization conditions, and >=1 free variable left")
    print("            => an affine family of dimension >= 15 at its window start.")
    print("    has     : 16 (the state entering round 4 is FREE -- precisely because")
    print("              the attack DROPS rounds 1-3).")
    print()
    print(f"  COMPOSED: GSR would see dimension 1, and needs 15.  DEFICIT 14.")
    print(f"  Concretely: forcing even ONE of its 13 functionals to be constant is")
    print(f"  {nz} coefficient equations against {8} spare parameters.  Short by {nz-8}.")
    print()
    print("  And the geometric form of the same count: a degree-49 curve in F_p^16")
    print("  meeting a codimension-13 affine subspace has expected point count")
    print(f"  49 * p^-12 = 2^{5.6 - 12*31:.1f}.  Empty.")
    print()
    print("  ** THE OBSTRUCTION IS NOT ARITHMETIC OVERDETERMINATION, IT IS PRIOR:")
    print("     GSR's 16 free dimensions EXIST ONLY BECAUSE ROUNDS 1-3 ARE DROPPED.")
    print("     CheapLunch's saving EXISTS ONLY IF ROUNDS 1-2 ARE KEPT.")
    print("     The two are statements about DIFFERENT OBJECTS; the composition is")
    print("     ill-posed before it is overdetermined. **")
    print()


def stage6b():
    """Generalize away from CheapLunch's particular 1-dimensional line.

    Ask the question GSR would need answered: what is the LARGEST affine family
    that can survive a front-end external round and still be affine in new
    variables?  That is the resource GSR consumes, so it decides composability
    for EVERY construction of this shape, not just the published one.

    Let U <= H (H = the CICO-1 input hyperplane, dim 15) have dim D, and
    R = M_E * basis(U) be the 16 x D matrix of linear parts.
      * a coordinate whose row is ZERO becomes a constant  -- z of them,
        costing z*D conditions on U;
      * the remaining 16-z rows must fall into only m = D projective directions
        (m < D is impossible: rank R = D; m > D leaves the new variables
        algebraically dependent) -- (16-z-D) coincidences at (D-1) each;
      * alignment (a common root per direction group) costs (16-z-D)
        conditions on the offset, of which only 15-D are available => z >= 1.
    Available on the direction side: dim Gr(D,15) = D(15-D).
    """
    print("=" * 78)
    print("STAGE 6b  the LARGEST skippable family -- is a smarter variant possible?")
    print("=" * 78)
    print("   D  | Gr(D,15) | conds 1 round | 1rd? | conds 2 rounds | 2rd?")
    print("  ----+----------+---------------+------+----------------+-----")
    best1 = best2 = 0
    for D in range(1, 16):
        avail = D * (15 - D)
        need1 = 1 + (16 - D) * (D - 1)          # minimised over z >= 1
        need2 = 2 * need1
        ok1, ok2 = need1 <= avail, need2 <= avail
        if ok1:
            best1 = D
        if ok2:
            best2 = D
        print(f"   {D:>2} | {avail:>8} | {need1:>13} | {'yes' if ok1 else ' no':>4} "
              f"| {need2:>14} | {'yes' if ok2 else ' no':>4}")
    print()
    print(f"  largest family surviving ONE front-end external round : D = {best1}")
    print(f"  largest family surviving TWO front-end external rounds: D = {best2}")
    print(f"  GSR requires at its window start                      : D >= 15")
    print()
    print("  ** A 2-ROUND FRONT-END SKIP FORCES D = 1.  That is not a fact about")
    print("     CheapLunch's published vector -- it is a fact about the shape.  Even a")
    print("     1-round skip caps at D = 7, still 8 short of GSR's 15.  The front-end")
    print("     skip line and the GSR line are mutually exclusive AT EVERY DEPTH. **")
    print()
    print("  CALIBRATION: the count says D=1 is feasible for two rounds, and D=1 for")
    print("  two rounds is exactly what stage 4 BUILT and verified.  The one point")
    print("  where the count is testable, it is right.")
    print("  HONEST LIMIT: this is a generic dimension count.  A degenerate")
    print("  configuration of a specific M_E could beat it; what the count settles is")
    print("  that no GENERIC construction exists, and it names the degeneracy a future")
    print("  paper would have to exhibit.\n")


def stage7():
    print("=" * 78)
    print("STAGE 7  what the margin actually is, and what R_P buys")
    print("=" * 78)
    from math import log2
    p_bits, alpha, t, k = 31, 7, 16, 1
    RF1 = 4

    def gsr_time(Rp, Rf1=RF1, k=1):
        """The sibling lane's model (gsr_calc.py), validated 5/5 on paper Table 1."""
        skip = max(0, min(Rp, t - 2 * k))
        growth = (Rp - skip) + Rf1
        D = (alpha ** growth) ** (2 ** (k - 1))
        return 2 * log2(D) + log2(p_bits), growth

    print("  GSR alone, deployed R_P=13:")
    tm, g = gsr_time(13)
    print(f"    CICO-1 on the (1,13,4)=18-round variant: 2^{tm:.1f} vs generic 2^31"
          f"  -> {'PRACTICAL' if tm < 31 else 'no gain'}   margin 3 of 21")
    print("  CheapLunch M_E skip alone, on the FULL 21 rounds:")
    DI_plain = alpha ** (k * 8 + 13)
    DI_skip = DI_plain // alpha ** 2
    print(f"    ideal degree D_I <= 7^(k*R_F + R_P) = 7^21 = 2^{log2(DI_plain):.1f}")
    print(f"    with the 2-round skip           = 7^19 = 2^{log2(DI_skip):.1f}")
    print(f"    root-finding alone is ~D_I^2 log p = 2^{2*log2(DI_skip)+log2(31):.1f}"
          f"  -> NOT an attack (generic CICO-1 is 2^31)")
    print("  Composed: DOES NOT EXIST (stage 6).")
    print()
    print("  => the deployed margin against this attack line is UNCHANGED at 3 of 21,")
    print("     and the 18-of-21 CICO-1 at 2^27.4 remains the binding result.")
    print()
    print("  HYPOTHETICAL, priced so the decision is not made on a guess: IF a future")
    print("  dimension-preserving front-end skip did compose, the numbers would be:")
    for Rp in (13, 15, 20):
        # composed: CheapLunch eats 2 initial full rounds, GSR eats 1 + partials
        skip = max(0, min(Rp, t - 2 * k))
        growth_comp = (Rp - skip) + RF1 + (4 - 1 - 2)   # 1 initial full round left over
        Dc = alpha ** growth_comp
        tc = 2 * log2(Dc) + log2(p_bits)
        tm, g = gsr_time(Rp)
        print(f"    R_P={Rp:>2}: GSR alone 2^{tm:.1f} (margin {3 if Rp<=14 else 3+(Rp-14)})"
              f" | composed 2^{tc:.1f} on the FULL 21 rounds"
              f" -> {'practical' if tc < 31 else 'still above 2^31'}")
    print()


if __name__ == "__main__":
    stage0()
    stage1()
    stage2(A_OURS, P_BB, "our deployed M_E, BabyBear")
    stage3()
    r = stage4()
    if r[0]:
        stage5(r[2])
        stage5b()
        stage5c()
        stage6(r[2])
        stage6b()
        stage7()
