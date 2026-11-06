"""Well-formed partial decryption: the per-crossing proof that closes the FHE fork's conversion hole.

2026-11-06. Before this file, the d = 64 FHE fork converted a ciphertext to SPDZ shares by letting each
custodian decrypt its OWN private share and then authenticate it. Nothing tied the authenticated value
to the designated ciphertext except the sampled conversion audit (2/3 per audit). A custodian who
authenticated a share of a DIFFERENT ciphertext produced a wrong step that every always-on check
accepted.

The repair changes the crossing, not just the proof:

  E2S (encryption -> shares) is a MASKED PUBLIC DECRYPTION.
    Preprocessing hands out a pair (Enc(R), [R_k]) with R uniform mod t on all N coefficients.
    Anyone computes ct' = ct - Enc(R) from the handle-bound ct. Each custodian i publishes a partial
    decryption p_i = s_i c1' + s2_i c2' + e_i with a proof of R_PD below. The combination
    c0' + sum p_i is decoded PUBLICLY to v = m - R mod t, and [m_k] = [R_k] + v_k.
    No custodian ever holds a private plain share, so there is no share to substitute.
  S2E (shares -> encryption) is a MASKED PUBLIC ENCRYPTION.
    Preprocessing hands out (Enc_exact(R'), [R'_k]). The custodians open v = m - R' through SPDZ (MAC
    checked), and anyone computes Enc_exact(R') + round(Q v / t). This step needs no new proof.

Relation R_PD, proved by custodian i for one crossing and checked before the decode:
  public:    ct' (the verifier computes it), p_i, the long-term key commitment K_i = Com(s_i, s2_i), E
  witness:   s_i, s2_i (opened against K_i), e_i, and one quotient polynomial k_q per Q-prime
  relation:  for every prime q | Q, in F_q[X]:
                 p_i = s_i c1' + s2_i c2' + e_i - (X^N + 1) k_q
             checked at a Fiat-Shamir point r_q (soundness 2N/q per prime here; an extension field in a
             deployment);
             |e_i|_inf <= E (e_i + E as ceil(log2(2E+1)/16) LogUp-16 digits per coefficient).
  s_i, s2_i and e_i are integers below every prime, so one digit commitment serves all the per-prime
  fields (PRISM's master commitment for small values). The k_q are native per prime.

The verifier below reads s_i and s2_i and checks them against K_i. That stands in for a PCS opening
at r_q; it is not zero knowledge. The counts in `counts()` are those of the succinct form.
"""
import hashlib
import math

import bfv_ref as bfv
from cert_b61 import evalp, fs_point

def key_commit(s, s2):
    return hashlib.sha256(("K|" + ",".join(map(str, s)) + "|" + ",".join(map(str, s2))).encode()).hexdigest()

def ct_handle(ct, Q):
    return hashlib.sha256(("|".join(",".join(str(c % Q) for c in comp) for comp in ct)).encode()).hexdigest()

def partial(scheme, s, s2, ct, e):
    """Prover: p = s c1 + s2 c2 + e mod Q over Z[X]/(X^N+1), plus the integer quotient k of the products."""
    Q, N = scheme.Q, scheme.N
    c1 = bfv.poly_centered(ct[1], Q)
    z, k = bfv.negacyclic_mul(s, c1)
    if len(ct) == 3:
        z2, k2 = bfv.negacyclic_mul(s2, bfv.poly_centered(ct[2], Q))
        z, k = bfv.poly_add(z, z2), bfv.poly_add(k, k2)
    p = [(zz + ee) % Q for zz, ee in zip(z, e)]
    return p, k

def prove(scheme, Qp, s, s2, ct, e):
    p, k = partial(scheme, s, s2, ct, e)
    return p, dict(e=list(e), k={q: [c % q for c in k] for q in Qp}, s=s, s2=s2)

def witness_hash(p, w):
    """Stands in for the commitment roots of (p_i, e_i, k_q) in the succinct form: the Fiat-Shamir point
    MUST depend on them. With a point derived from public data only (legacy_fs), a custodian who knows the
    point in advance picks k_q after the fact and passes any p_i (fs_binding_falsifiers.py)."""
    m = hashlib.sha256()
    m.update(",".join(map(str, p)).encode())
    m.update(",".join(map(str, w["e"])).encode())
    for q in sorted(w["k"]):
        m.update(",".join(map(str, w["k"][q])).encode())
    return m.hexdigest()

def pd_point(tag, h, wh, q, legacy_fs=False):
    return fs_point(f"PD|{tag}|{h}|{q}" if legacy_fs else f"PD|{tag}|{h}|{wh}|{q}", q)

def verify(scheme, Qp, ct, p, Kcom, w, E, tag, legacy_fs=False):
    """True iff R_PD holds for the DESIGNATED ct (the caller passes the ct the protocol designates)."""
    Q, N = scheme.Q, scheme.N
    if key_commit(w["s"], w["s2"]) != Kcom:
        return False, "key opening does not match the custodian's long-term key commitment"
    if any(abs(x) > E for x in w["e"]):
        return False, "smudging term out of range (|e| > E): an offset hidden in the error"
    h = ct_handle(ct, Q)
    wh = witness_hash(p, w)
    for q in Qp:
        r = pd_point(tag, h, wh, q, legacy_fs)
        lhs = evalp([x % q for x in p], r, q)
        rhs = (evalp([x % q for x in w["s"]], r, q) * evalp([x % q for x in ct[1]], r, q)
               + evalp([x % q for x in w["e"]], r, q)
               - (pow(r, N, q) + 1) * evalp(w["k"][q], r, q))
        if len(ct) == 3:
            rhs += evalp([x % q for x in w["s2"]], r, q) * evalp([x % q for x in ct[2]], r, q)
        if (lhs - rhs) % q:
            return False, f"partial-decryption identity fails in F_q (q = {q.bit_length()}-bit prime)"
    return True, "accept"

def counts(N, Qp, E, comps):
    """One R_PD proof (one custodian, one crossing), succinct form. Long-term key commitments are not
    per-step and are excluded."""
    L = len(Qp)
    pb = max(q.bit_length() for q in Qp)
    edig = math.ceil((2 * E + 1).bit_length() / 16)
    k_elems = L * (N - 1)                         # native quotient per prime
    e_digits = N * edig                           # 16-bit digits, shared across fields
    opens = L * (4 + (1 if comps == 3 else 0))    # p, s, e, k (+ s2) at r_q
    return dict(pd_elems=k_elems + e_digits, pd_bits=k_elems * pb + e_digits * 16,
                pd_range_lookups=e_digits, pd_openings=opens)
