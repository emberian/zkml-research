"""Experiment 1a: the ct x ct integer rescale certificate (VERDICTS 7.5 Hole B), priced three ways.

2026-11-06. For ONE real BFV ct x ct we construct honest arithmetic witnesses and estimate elements
for several candidate certificate designs. This is not an independent verifier: some relations
are checked on honest values, others are only counted. Counts omit a complete sound range/carry
argument and the later B/B61 canonical-quotient pin. Counts only; no clock.

What is certified, per output component k in {0,1,2} and coefficient j:
    d_k = lifted integer tensor (d0 = a0 b0, d1 = a0 b1 + a1 b0, d2 = a1 b1 in Z[X]/(X^N+1))
    t d_k + floor(Q/2) = Q y_k + s_k,   0 <= s_k < Q,   out_k = y_k mod Q.
Proving c_raw = a b in R_Q proves nothing about out (the Q=31, t=4 pair: falsifier at the end).

Designs (each is ONE concrete arithmetization; its count is an upper bound for that design, not a
lower bound for every protocol):
  A  native p61 @ N=4096: proof field P = Q = p61. Integers in signed base-2^w digits, column
     identities with carries, every column bounded below P/2 so the field identity lifts to Z.
  B  PRISM-style RNS-202 @ N=8192: one field per RNS prime (Q basis + an extension basis B), every
     per-prime polynomial identity native; cross-field consistency through canonical-integer witnesses
     (v_i in [0, q_i), opened in every field, range-proved once: PRISM 2026/1956's MF-PCS move);
     base extensions Q->B and B->Q as exact integer relations a = sum v_i Q/q_i - u Q.
  C  row-interleaved RNS-202 @ N=8192 over BabyBear: the deployed layout's choice (all residues bridged
     into one 31-bit field), so all integer arithmetic is digit emulation as in A but with P = BabyBear.
"""
import math
import random
import sys

import bfv_ref as bfv

BABYBEAR = 2013265921
P61 = 127 * 2 ** 54 + 1
T = 1032193
LOOKUP = 16

def lookups(bits):
    return max(1, math.ceil(bits / LOOKUP))

# ---------------------------------------------------------------- digit machinery (designs A, C)
def signed_digits(x, w, L):
    """x = sum d_i 2^{w i}, d_i in [-2^{w-1}, 2^{w-1}); exactly L digits (asserts it fits)."""
    ds = []
    half = 1 << (w - 1)
    for _ in range(L):
        d = ((x + half) % (1 << w)) - half
        ds.append(d)
        x = (x - d) >> w
    assert x == 0, "value does not fit in L signed digits"
    return ds

def unsigned_digits(x, w, L):
    """Canonical nonnegative base-2^w digits, used for interval witnesses."""
    assert 0 <= x < 1 << (w * L), "value outside unsigned digit range"
    return [(x >> (w * i)) & ((1 << w) - 1) for i in range(L)]

def digit_polys(poly, w, L):
    cols = [signed_digits(c, w, L) for c in poly]
    return [[cols[j][i] for j in range(len(poly))] for i in range(L)]

def choose_w(N, terms, in_bits, pbits):
    """Largest w with every product-column coefficient below P/4 (headroom for the carry and K terms)."""
    for w in range(40, 2, -1):
        L = math.ceil((in_bits + 1) / w) + 1
        col = N * terms * L * (1 << (2 * (w - 1)))
        if col.bit_length() <= pbits - 3:
            return w, L
    raise ValueError("no digit width fits")

def product_certificate(pairs, N, in_bits, pbits, w=None, L=None):
    """pairs: list of (a, b) integer polys whose negacyclic products are SUMMED (d1 has two terms).
    Builds: input digits (counted by the caller), per column m: K_m quotient poly, z_m digit poly,
    carry poly c_m with  sum_{i+j=m} a_i b_j = (z_m + 2^w c_m - c_{m-1}) + (X^N+1) K_m  over Z,
    each coefficient bounded below P/2 (checked). Returns (counts, z_true, max_bits)."""
    terms = len(pairs)
    if w is None:
        w, L = choose_w(N, terms, in_bits, pbits)
    M = 2 * L - 1
    col = [[0] * N for _ in range(M)]
    colK = [[0] * (N - 1) for _ in range(M)]
    for a, b in pairs:
        ad, bd = digit_polys(a, w, L), digit_polys(b, w, L)
        for i in range(L):
            for j in range(L):
                z, k = bfv.negacyclic_mul(ad[i], bd[j])
                cm, km = col[i + j], colK[i + j]
                for x in range(N):
                    cm[x] += z[x]
                for x in range(N - 1):
                    km[x] += k[x]
    # carries: z_m digit = (col_m + c_{m-1}) mod 2^w (signed), c_m = (col_m + c_{m-1} - z_m) / 2^w
    half = 1 << (w - 1)
    carry = [0] * N
    zdig, carries = [], []
    maxbits = 0
    for m in range(M):
        zm, cm_ = [], []
        for x in range(N):
            v = col[m][x] + carry[x]
            maxbits = max(maxbits, abs(col[m][x]).bit_length(), abs(colK[m][x - 1] if x else 0).bit_length())
            dgt = ((v + half) % (1 << w)) - half
            c = (v - dgt) >> w
            zm.append(dgt)
            cm_.append(c)
        zdig.append(zm)
        carries.append(cm_)
        carry = cm_
    # the integer z is the digit sum plus the final carry (top part)
    z_rebuilt = [sum(zdig[m][x] << (w * m) for m in range(M)) + (carry[x] << (w * M)) for x in range(N)]
    z_true = [0] * N
    for a, b in pairs:
        z, _ = bfv.negacyclic_mul(a, b)
        z_true = bfv.poly_add(z_true, z)
    assert z_rebuilt == z_true, "column certificate does not reconstruct the integer product"
    assert maxbits <= pbits - 2, f"a column coefficient ({maxbits} bits) does not fit below P/2"
    carry_bits = max(abs(c).bit_length() for cm in carries for c in cm) + 1
    counts = dict(w=w, L=L, M=M, K=M * (N - 1), z=M * N, carry=M * N,
                  range_lookups=M * N * (lookups(w) + lookups(carry_bits)) + M * (N - 1) * lookups(pbits - 2),
                  col_bits=maxbits)
    return counts, z_true

def scale_certificate(z, Q, N, w, pbits, native_mod_P):
    """t z + floor(Q/2) = Q y + s, 0 <= s < Q, in signed base-2^w digits with carries.
    Checked over Z; columns bounded below P/2. If native_mod_P (P == Q) the field reduction of y's digits
    IS out = y mod Q, else the caller must add an output-reduction certificate."""
    ys, ss = [], []
    for x in z:
        y, s = divmod(T * x + Q // 2, Q)
        ys.append(y)
        ss.append(s)
        assert 0 <= s < Q
    ybits = max(abs(y).bit_length() for y in ys) + 1
    qbits = Q.bit_length() + 1
    Ly, Ls, Lq = math.ceil(ybits / w) + 1, math.ceil(qbits / w) + 1, math.ceil(qbits / w) + 1
    for x in range(N):
        assert T * z[x] + Q // 2 - Q * ys[x] - ss[x] == 0
        signed_digits(ys[x], w, Ly)
        unsigned_digits(ss[x], w, Ls)
        unsigned_digits(Q - 1 - ss[x], w, Ls)     # s < Q: the complement is a nonnegative digit vector
    cols = Ly + Lq                              # columns of the linear identity
    col_bits = (Lq * (1 << (2 * w))).bit_length() + 2
    assert col_bits <= pbits - 2
    counts = dict(y=Ly * N, s=Ls * N, s_complement=Ls * N, carry=cols * N,
                  range_lookups=(Ly + 2 * Ls) * N * lookups(w) + cols * N * lookups(col_bits))
    return counts, ys

def output_reduction_certificate(ys, moduli, N, w):
    """Design C only: out_i = y mod q_i for each RNS prime, as y - out_i = q_i u_i over Z in digits."""
    total = 0
    lk = 0
    for q in moduli:
        ubits = max(abs((y - (y % q)) // q).bit_length() for y in ys) + 1
        Lu = math.ceil(ubits / w) + 1
        Lo = math.ceil(q.bit_length() / w) + 1
        total += (Lu + Lo + Lu + Lo) * N      # u digits, out digits, carries
        lk += (Lu + Lo) * N * lookups(w) + (Lu + Lo) * N * lookups(w + 8)
    return dict(out_reduction=total, range_lookups=lk)

def crt_lift_certificate(n_polys, moduli, N, w, Q):
    """Design C only: the centered integer lift of each input poly from its residues,
    a = sum_i v_i Q/q_i - u Q, in digits: v_i (residue digits are the committed bridge felts already),
    u small, plus the integer identity's digits and carries."""
    L = len(moduli)
    Lint = math.ceil((Q.bit_length() + 8) / w) + 1
    per_coef = L * (math.ceil(36 / w) + 1) + 1 + Lint + Lint   # v digits, u, integer digits, carries
    return dict(crt_lift=n_polys * per_coef * N,
                range_lookups=n_polys * N * (L * (math.ceil(36 / w) + 1) + Lint) * lookups(w))

# ---------------------------------------------------------------- design B (PRISM-style, native per prime)
def prism_style(ct1, ct2, Qprimes, Bprimes, N, scheme):
    """Honest-data checks for selected input/product relations; scale and output extension are counted only."""
    Q = math.prod(Qprimes)
    Bm = math.prod(Bprimes)
    allp = Qprimes + Bprimes
    d, ks, (a0, a1, b0, b1) = scheme.tensor_lifted(ct1, ct2)
    # 1. base extension of the 4 input polys, exact: a_pos = sum v_i Q/q_i - u Q  (a_pos in [0,Q)),
    #    centered a = a_pos - Q*[a_pos > Q/2]: fold the sign into u (u in [0, L+1)).
    Qhat = [Q // q for q in Qprimes]
    Qhat_inv = [pow(Q // q, -1, q) for q in Qprimes]
    n_v = n_u = 0
    for poly in (a0, a1, b0, b1):
        for x in poly:
            res = [x % q for q in Qprimes]
            v = [r * hi % q for r, hi, q in zip(res, Qhat_inv, Qprimes)]
            s = sum(vi * qh for vi, qh in zip(v, Qhat))
            u = (s - x) // Q
            assert s - u * Q == x and 0 <= u <= len(Qprimes)
            for p in Bprimes:      # the native linear relation in each B field
                assert (sum(vi * (qh % p) for vi, qh in zip(v, Qhat)) - u * (Q % p) - x) % p == 0
            n_v += len(v)
            n_u += 1
    in_B_res = 4 * N * len(Bprimes)
    # 2. per-prime tensor identity, native in each F_p: lhs = z_p + (X^N+1) K_p   (K_p committed)
    zbits = max(abs(c).bit_length() for comp in d for c in comp) + 1
    assert Q * Bm > 2 ** (zbits + 1), "Q.B too small to hold the lifted tensor"
    # verify per-prime: (a b) mod p == z mod p, with z the integer tensor (only three primes are exercised below, at fixed
    # illustrative points; this is not a sound adversarial polynomial-identity verifier)
    for p in allp[:2] + allp[-1:]:
        for comp_pairs, dk, kk in (([(a0, b0)], d[0], ks[0]), ([(a0, b1), (a1, b0)], d[1], ks[1]), ([(a1, b1)], d[2], ks[2])):
            acc_z = [0] * N
            acc_k = [0] * (N - 1)
            for a, b in comp_pairs:
                z, k = bfv.negacyclic_mul([c % p for c in a], [c % p for c in b])
                acc_z = bfv.poly_add(acc_z, z)
                acc_k = bfv.poly_add(acc_k, k)
            # the per-prime witness: z_p = dk mod p, K_p = (lhs - z_p)/(X^N+1) mod p; check identity at r
            r = random.Random(p).randrange(p)
            lhs = sum((c % p) * pow(r, i, p) for i, c in enumerate(acc_z)) % p
            lhsK = sum((c % p) * pow(r, i, p) for i, c in enumerate(acc_k)) % p
            zp = sum((c % p) * pow(r, i, p) for i, c in enumerate(dk)) % p
            # acc = negacyclic(a b) + (X^N+1) acc_k over Z; d_k = negacyclic sum: so a(r)b(r) = d_k(r) + (r^N+1) K(r)
            assert (lhs - zp) % p == 0
    n_z = 3 * N * len(allp)
    n_K = 3 * (N - 1) * len(allp)
    # 3. s = [t z + floor(Q/2)]_Q needs its integer: base extension Q->B (v', u'); y in B natively
    ys, ss = scheme.scale(d[0] + d[1] + d[2])
    ybits = max(abs(y).bit_length() for y in ys) + 1
    assert Bm > 2 ** (ybits + 1), "B too small to hold y"
    n_vs = 3 * N * len(Qprimes)
    n_us = 3 * N
    # 4. out = y mod Q by base extension B->Q (v'', u'')
    n_vy = 3 * N * len(Bprimes)
    n_uy = 3 * N
    elems = dict(v_inputs=n_v, u_inputs=n_u, inputs_in_B=in_B_res, z_residues=n_z, K_residues=n_K,
                 v_s=n_vs, u_s=n_us, v_y=n_vy, u_y=n_uy)
    vbits = max(p.bit_length() for p in allp)
    lk = (n_v + n_vs + n_vy) * lookups(vbits) + (n_u + n_us + n_uy) * 1
    return elems, lk, zbits, ybits

# ---------------------------------------------------------------- the Q=31, t=4 falsifier
def falsifier():
    Q, t = 31, 4
    z_true, z_alias = 32, 1          # 2*16 and 1*1: same residue mod 31
    out = lambda z: (t * z + Q // 2) // Q
    assert z_true % Q == z_alias % Q and out(z_true) % Q != out(z_alias) % Q
    # a certificate that only checks mod Q accepts the alias: t z + Q//2 - s = 0 mod Q deletes y
    s_true = (t * z_true + Q // 2) % Q
    accepts_mod_Q = (t * z_alias + Q // 2 - s_true) % Q == 0
    # the integer certificate refuses: no y with t z_alias + Q//2 = Q y + s_true and claimed y = out(z_true)
    refuses_int = t * z_alias + Q // 2 != Q * out(z_true) + s_true
    return accepts_mod_Q, refuses_int, out(z_true), out(z_alias)

def run(design, seed=7):
    if design == "A":
        N, Q = 4096, P61
        scheme = bfv.BFV(N, Q, T, seed=seed)
    else:
        N = 8192
        pb, cnt = (61, 3) if design == "B61" else (34, 6)
        Qp = bfv.ntt_primes(pb, cnt, 2 * N)
        Q = math.prod(Qp)
        scheme = bfv.BFV(N, Q, T, seed=seed)
    scheme.keygen()
    rng = random.Random(seed)
    m1 = [rng.randrange(16) for _ in range(N)]
    m2 = [rng.randrange(16) for _ in range(N)]
    ct1, ct2 = scheme.encrypt(m1), scheme.encrypt(m2)
    d, ks, (a0, a1, b0, b1) = scheme.tensor_lifted(ct1, ct2)
    outs = []
    for dk in d:
        y, s = scheme.scale(dk)
        outs.append([yy % Q for yy in y])
    dec = scheme.decrypt(outs)
    want, _ = bfv.negacyclic_mul(m1, m2)
    assert dec == [x % T for x in want], "BFV ct x ct does not decrypt to m1 m2"
    row = dict(design=design, N=N, logQ=round(math.log2(Q), 2))
    in_bits = Q.bit_length()
    if design in ("A", "C"):
        P = P61 if design == "A" else BABYBEAR
        pbits = P.bit_length()
        tot = dict(inputs=0, K=0, z=0, carry=0, scale=0, extra=0, range_lookups=0)
        comps = [[(a0, b0)], [(a0, b1), (a1, b0)], [(a1, b1)]]
        w, L = choose_w(N, 2, in_bits, pbits)        # one digit width for the whole design
        for pairs in comps:
            c, z = product_certificate(pairs, N, in_bits, pbits, w, L)
            tot["K"] += c["K"]; tot["z"] += c["z"]; tot["carry"] += c["carry"]
            tot["range_lookups"] += c["range_lookups"]
            sc, ys = scale_certificate(z, Q, N, w, pbits, native_mod_P=(design == "A"))
            tot["scale"] += sc["y"] + sc["s"] + sc["s_complement"] + sc["carry"]
            tot["range_lookups"] += sc["range_lookups"]
            if design == "C":
                o = output_reduction_certificate(ys, Qp, N, w)
                tot["extra"] += o["out_reduction"]; tot["range_lookups"] += o["range_lookups"]
        tot["inputs"] = 4 * L * N                     # signed digits of the 4 centered input polys
        if design == "C":
            cl = crt_lift_certificate(4, Qp, N, w, Q)
            tot["extra"] += cl["crt_lift"]; tot["range_lookups"] += cl["range_lookups"]
        cert = sum(v for k, v in tot.items() if k != "range_lookups")
        row.update(field_bits=pbits, digit_w=w, digits_per_coef=L, cert_elems=cert,
                   cert_bits=cert * pbits, range_lookups=tot["range_lookups"], detail=tot)
    else:
        # size the extension basis from the bounds: B must hold y (|y| ~ t|z|/Q) and Q.B must hold z
        zb = max(abs(c).bit_length() for comp in d for c in comp) + 2
        yb = zb + T.bit_length() - Q.bit_length() + 2
        need = max(yb, zb - Q.bit_length()) + 1
        pbits_B = Qp[0].bit_length()
        Bp = bfv.ntt_primes(pbits_B, math.ceil(need / (pbits_B - 1)), 2 * N, exclude=set(Qp))
        elems, lk, zbits, ybits = prism_style(ct1, ct2, Qp, Bp, N, scheme)
        cert = sum(elems.values())
        row.update(field_bits=pbits_B, digit_w=None, digits_per_coef=None, cert_elems=cert, cert_bits=cert * pbits_B,
                   range_lookups=lk, detail=dict(elems, B_primes=len(Bp), zbits=zbits, ybits=ybits))
    return row

if __name__ == "__main__":
    designs = sys.argv[1:] or ["A", "B", "B61", "C"]
    acc, ref, o1, o2 = falsifier()
    print(f"falsifier Q=31,t=4: mod-Q check accepts the alias: {acc}; integer certificate refuses it: {ref} "
          f"(out(32)={o1}, out(1)={o2})")
    assert acc and ref
    for dsg in designs:
        r = run(dsg)
        print(r, flush=True)
