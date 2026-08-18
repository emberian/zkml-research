#!/usr/bin/env python3
"""Q1, settled by computation, not assumption.

GSR (eprint 2026/1692 §5.2) imposes, on the state X1 entering the partial layer,
the linear functionals  e_0^T M_I^j  for j = 0 .. (t-2k-1).
They are independent  <=>  dim Krylov(M_I^T, e_0) >= t-2k.

Poseidon2's internal matrix is M_I = J + diag(V)  (all-ones + diagonal), which is
SYMMETRIC, so M_I^T = M_I. We compute the Krylov dimension over F_p directly for
the DEPLOYED constants read from circuit/src/poseidon2.rs:92.
"""
P = 2013265921  # BabyBear

def inv(a):
    return pow(a % P, P - 2, P)

# INTERNAL_DIAG stores d_i = 1 + V[i]; the layer computes x_i' = sum(x) + V[i]*x_i.
INTERNAL_DIAG_16 = [2013265920, 2, 3, 1006632962, 4, 5, 1006632961, 2013265919,
                    2013265918, 2005401602, 1509949442, 1761607682, 2013265907,
                    7864321, 125829121, 16]
V16 = [(d - 1) % P for d in INTERNAL_DIAG_16]

# w24 instance (chain/gnark/poseidon2_w24.go raw-V convention documented in the header)
V24_SPEC = "[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/2^7, 1/2^9, 1/2^27, -1/2^8, -1/4, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^27]"
def parse(tok):
    tok = tok.strip()
    neg = tok.startswith('-')
    if neg: tok = tok[1:]
    if '/' in tok:
        num, den = tok.split('/')
        if '^' in den:
            b, e = den.split('^'); den = int(b) ** int(e)
        else:
            den = int(den)
        val = int(num) * inv(int(den)) % P
    else:
        val = int(tok) % P
    return (-val) % P if neg else val
V24 = [parse(t) for t in V24_SPEC.strip('[]').split(',')]

def matvec(V, x):
    """(J + diag(V)) x  ->  x_i' = sum(x) + V[i]*x_i"""
    s = sum(x) % P
    return [(s + V[i] * x[i]) % P for i in range(len(x))]

def krylov_dim(V, seed_index=0):
    t = len(V)
    e = [0] * t
    e[seed_index] = 1
    basis = []          # row-echelon basis
    pivots = []
    v = e[:]
    dim = 0
    for step in range(t + 2):
        # reduce v against basis
        w = v[:]
        for b, pc in zip(basis, pivots):
            if w[pc]:
                f = w[pc] * inv(b[pc]) % P
                w = [(w[i] - f * b[i]) % P for i in range(t)]
        nz = next((i for i in range(t) if w[i]), None)
        if nz is None:
            break
        basis.append(w); pivots.append(nz); dim += 1
        v = matvec(V, v)
    return dim

for name, V, t in [("BabyBear w16 (DEPLOYED)", V16, 16),
                   ("BabyBear w24 (segment-digest sponge)", V24, 24)]:
    d = krylov_dim(V, 0)
    print(f"{name}")
    print(f"    t = {t},  dim Krylov(M_I, e_0) = {d}   ({'FULL' if d == t else 'DEFICIENT'})")
    for k in (1, 2, 3):
        need = t - 2 * k
        print(f"      k={k}: GSR needs {need} independent functionals -> "
              f"{'INDEPENDENT, gadget applies in full' if d >= need else 'DEFICIENT'}")
    print()

# Also: does e_0 lie in a proper invariant subspace? (the Poseidon2 design criterion)
print("Poseidon2's own design criterion (Grassi-Rechberger-Schofnegger, ToSC 2021) is that")
print("M_I admits NO nontrivial invariant subspace -- which is exactly what makes the")
print("Krylov space full, and therefore exactly what makes GSR's constraints independent.")
