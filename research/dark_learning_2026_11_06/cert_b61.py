"""The B61 ct x ct certificate with an explicit witness and an explicit verifier (FHE fork of the d=64 step).

2026-11-06. Scheme decision §2: BFV, N = 8192, Q = three ~61-bit NTT-friendly primes, each its own proof
field; an extension basis B of ~61-bit primes; canonical-integer witnesses (v, u) carry values across
fields (PRISM 2026/1956's move). The verifier below is what the custodians run BEFORE releasing any
partial decryption of the product ("decryption only on proof", C8).

Statement verified, for committed handles H(ct1), H(ct2), H(out):
    out_k = round(t * d_k / Q) mod Q,  d = integer tensor of the centered lifts of ct1, ct2,  k = 0, 1, 2.
Checks (all in the field where a succinct verifier would check them):
  (1) the opened residues hash to the committed handles (one handle covers ALL limbs: Hole A);
  (2) base extension of every input coefficient Q -> B:  a = sum_i v_i Qhat_i - u Q  (centered fold in u),
      v_i = [a q~_i]_{q_i} in [0, q_i), u in [0, L+1]; checked in every B field;
  (3) per-prime tensor identity at a Fiat-Shamir point r_l:  sum a(r) b(r) = d_l(r) + (r^N + 1) K_l(r);
  (4) s = [t d + floor(Q/2)]_Q from the Q residues; its B residues by base extension (v_s, u_s);
      y_B = (t d_B + floor(Q/2) - s_B) Q^{-1} (native);
  (5) out = y mod Q by base extension B -> Q (v_y, u_y), y centered.
Range checks (v < prime, u small) are counted as LogUp-16 lookups, checked here directly.
"""
import hashlib
import math

import bfv_ref as bfv

def handle(ct, primes):
    m = hashlib.sha256()
    for comp in ct:
        for q in primes:
            m.update(b"|")
            m.update(",".join(str(c % q) for c in comp).encode())
    return m.hexdigest()

def fs_point(tag, p):
    return int(hashlib.sha256(tag.encode()).hexdigest(), 16) % p

def evalp(poly, r, p):
    acc = 0
    for c in reversed(poly):
        acc = (acc * r + c) % p
    return acc

class Basis:
    def __init__(self, primes):
        self.primes = primes
        self.M = math.prod(primes)
        self.hat = [self.M // q for q in primes]
        self.hat_inv = [pow(self.M // q, -1, q) for q in primes]

    def canonical_u(self, v, centered):
        """The ONLY u the verifier accepts: the one that makes sum v_i hat_i - u M the canonical
        representative (in [0, M), or centered in (-M/2, M/2]). Without this pin u is a free witness and a
        prover can shift the value by a multiple of M (a wrong output that passes every residue check).
        In a circuit this is a range proof of the reconstructed value: counted as digits in counts()."""
        s = sum(vi * h for vi, h in zip(v, self.hat))
        u = s // self.M
        if centered and s - u * self.M > self.M // 2:
            u += 1
        return u

    def extend_witness(self, x, centered=True):
        res = [x % q for q in self.primes]
        v = [r * hi % q for r, hi, q in zip(res, self.hat_inv, self.primes)]
        u = self.canonical_u(v, centered)
        assert sum(vi * h for vi, h in zip(v, self.hat)) - u * self.M == x
        return v, u

    def check_extension(self, res, v, u, target_primes, target_res, centered=True):
        """res: x mod each own prime; claims x mod each target prime = target_res."""
        for vi, r, hi, q in zip(v, res, self.hat_inv, self.primes):
            if not (0 <= vi < q) or vi != r * hi % q:
                return False
        if u != self.canonical_u(v, centered):
            return False
        for p, tr in zip(target_primes, target_res):
            if (sum(vi * (h % p) for vi, h in zip(v, self.hat)) - u * (self.M % p) - tr) % p:
                return False
        return True

def build(scheme, Qp, Bp, ct1, ct2):
    """Returns (out_ct, witness). Prover side: knows only ciphertexts (no plaintext), as the host does."""
    Q, t, N = scheme.Q, scheme.t, scheme.N
    QB, BB = Basis(Qp), Basis(Bp)
    d, ks, ins = scheme.tensor_lifted(ct1, ct2)
    out = []
    w = dict(ext_in=[], z_res=[], K_res=[], ext_s=[], ext_y=[])
    for poly in ins:                               # (2) the four input polys' base extensions
        w["ext_in"].append([QB.extend_witness(x) for x in poly])
    for k in range(3):
        w["z_res"].append({p: [c % p for c in d[k]] for p in Qp + Bp})
        w["K_res"].append({p: [c % p for c in ks[k]] for p in Qp + Bp})
        ys, ss = scheme.scale(d[k])
        w["ext_s"].append([QB.extend_witness(s, centered=False) for s in ss])
        w["ext_y"].append([BB.extend_witness(y) for y in ys])
        out.append([y % Q for y in ys])
    w["opened"] = (ct1, ct2)
    return out, w

def counts(N, Qp, Bp):
    L, k = len(Qp), len(Bp)
    elems = (4 * N * (L + 1)          # v, u of the four inputs
             + 4 * N * k              # input residues in B
             + 3 * N * (L + k)        # z residues
             + 3 * (N - 1) * (L + k)  # K residues
             + 3 * N * (L + 1)        # s extension
             + 3 * N * (k + 1))       # y extension
    bits = elems * max(q.bit_length() for q in Qp + Bp)
    pb = max(q.bit_length() for q in Qp + Bp)
    vlookups = (4 * N * L + 3 * N * L + 3 * N * k) * math.ceil(pb / 16)
    canon = (4 * N + 3 * N) * math.ceil(L * pb / 16) + 3 * N * math.ceil(k * pb / 16)  # u pins: value ranges
    return dict(cert_elems=elems, cert_bits=bits, range_lookups=vlookups + canon)

def witness_hash(w):
    """Stands in for the commitment roots of the z and K residues: the identity-(3) point MUST depend on
    them, or a prover who knows the point picks K after the fact (fs_binding_falsifiers.py)."""
    m = hashlib.sha256()
    for key in ("z_res", "K_res"):
        for comp in w[key]:
            for p in sorted(comp):
                m.update(",".join(map(str, comp[p])).encode())
    return m.hexdigest()

def verify(scheme, Qp, Bp, h1, h2, hout, out_ct, w, sample=None, legacy_fs=False):
    """True iff every check passes. `sample` limits the per-coefficient base-extension checks to a
    coefficient subset for runtime (the polynomial identities (3) always use all coefficients); the
    harness runs sample=None (all coefficients) for the honest run and for every attack."""
    Q, t, N = scheme.Q, scheme.t, scheme.N
    QB, BB = Basis(Qp), Basis(Bp)
    ct1, ct2 = w["opened"]
    if handle(ct1, Qp) != h1 or handle(ct2, Qp) != h2 or handle(out_ct, Qp) != hout:
        return False, "handle mismatch (an input or output is not the committed ciphertext)"
    ins = [bfv.poly_centered(c, Q) for c in (ct1[0], ct1[1], ct2[0], ct2[1])]
    idx = range(N) if sample is None else sample
    # (2) base extension of inputs; B residues of inputs derived from (v, u)
    inB = []
    for poly, ext in zip(ins, w["ext_in"]):
        resB = {}
        for p in Bp:
            resB[p] = [0] * N
        for j in idx:
            v, u = ext[j]
            res = [poly[j] % q for q in Qp]
            tgt = [(sum(vi * (hh % p) for vi, hh in zip(v, QB.hat)) - u * (QB.M % p)) % p for p in Bp]
            if not QB.check_extension(res, v, u, Bp, tgt):
                return False, "input base extension"
        for p in Bp:
            resB[p] = [(sum(vi * (hh % p) for vi, hh in zip(ext[j][0], QB.hat)) - ext[j][1] * (QB.M % p)) % p
                       for j in range(N)]
        inB.append(resB)
    a0, a1, b0, b1 = range(4)
    pairs = [[(a0, b0)], [(a0, b1), (a1, b0)], [(a1, b1)]]
    wh = witness_hash(w)
    for k in range(3):
        for p in Qp + Bp:
            r = fs_point(f"{h1}{h2}{hout}{k}{p}" if legacy_fs else f"{h1}{h2}{hout}{wh}{k}{p}", p)
            def res(i):
                return [c % p for c in ins[i]] if p in Qp else inB[i][p]
            lhs = sum(evalp(res(i), r, p) * evalp(res(j), r, p) for i, j in pairs[k]) % p
            rhs = (evalp(w["z_res"][k][p], r, p) + (pow(r, N, p) + 1) * evalp(w["K_res"][k][p], r, p)) % p
            if lhs != rhs:
                return False, f"tensor identity fails in F_{p.bit_length()}b prime (component {k})"
        # (4) s from Q residues; extension to B
        for j in idx:
            s_res = [(t * w["z_res"][k][q][j] + Q // 2) % q for q in Qp]
            v, u = w["ext_s"][k][j]
            if [vi for vi in v] != [sr * hi % q for sr, hi, q in zip(s_res, QB.hat_inv, Qp)]:
                return False, "s extension witness"
            if u != QB.canonical_u(v, centered=False):
                return False, "s not canonical (u not pinned)"
            sval_B = [(sum(vi * (hh % p) for vi, hh in zip(v, QB.hat)) - u * (QB.M % p)) % p for p in Bp]
            y_B = [((t * w["z_res"][k][p][j] + Q // 2 - sb) * pow(Q, -1, p)) % p for p, sb in zip(Bp, sval_B)]
            vy, uy = w["ext_y"][k][j]
            if not BB.check_extension(y_B, vy, uy, Qp, [out_ct[k][j] % q for q in Qp]):
                return False, f"y / output base extension (component {k}, coefficient {j})"
    return True, "accept"
