"""Pinned key generation for the custodians' HE keys, and the whole-ciphertext simulator for the HE helpers'
returns (dark learning gen 4, item 3; decision doc section 21).

2026-11-06.

CEREMONY (one per epoch, among the n custodians, over the ledger's authenticated broadcast):
  1. commit: custodian i draws a 256-bit r_i and posts c_i = H(epoch, i, r_i, salt_i).
  2. reveal: only after ALL n commitments are on the ledger, each posts (r_i, salt_i); everyone checks them.
     seed = H(epoch, c_0..c_{n-1}, r_0..r_{n-1}).  With one honest custodian, r_honest is uniform and independent of
     the others' committed values, so the seed is uniform; nobody can grind it after seeing others' coins.
     SELECTIVE ABORT (Codex review): the last revealer can compute the seed first and reveal only if it likes it.
     An adversary that aborts k times makes any event of probability p (over the seed) happen with probability at
     most (k + 1) p, since it sees at most k + 1 candidate seeds. A non-revealer is blamed; with 3-of-3 custody
     the ceremony cannot finish without it, so every abort is on the ledger, and replacing a custodian that keeps
     aborting is a governance decision. Removing the bias needs a delay function or a threshold reveal [not built].
  3. keys: custodian j sets a_j = public_a(seed/j) (the scholar's rejection sampler on the registry seed), samples
     s_j ternary, e_j in [-8,8]^N, posts b_j = -(a_j s_j + e_j) and a ZKPoPK of the key relation alone
     (zkpopk_ligero kind "key"), bound to (epoch, j, seed, the ceremony transcript hash).
  4. registry: every custodian verifies every key proof; the registry records seed, commitments, reveals, b_j and
     the proof digest. Recipients of HE traffic accept only keys from this registry (zkpopk_ligero.verify checks a_j
     against the seed; a = 1 or any chosen a is refused).
  The FHE (b) joint key is the same ceremony with a = public_a(seed/"joint") and b = sum_j b_j: each share is proved
  well formed, so the joint secret is sum s_j (|.| <= n) and the joint error sum e_j (|.| <= 8n).

WHAT THE PROOF DOES AND DOES NOT GIVE. It proves a_j is the ceremony's, and that j KNOWS short (s_j, e_j) with
b_j + a_j s_j + e_j = 0: the extractor hands a simulator s_j. It does not prove s_j was sampled honestly; nothing
below needs that (the returner's privacy uses only a_j's uniformity and the returner's own fresh u, e1).

WHOLE-CIPHERTEXT SIMULATION (the argument; section 21 states it with its terms). Returner i, recipient j (corrupt,
holding s_j). i returns   c1 = P c1_in + a_j u + e1,   c0 = P c0_in + b_j u + e0 + Encode(M) + U,  U uniform in
[-F, F]^N. With phase_in = c0_in + c1_in s_j = Encode(m) - e (bounded by the ZKPoPK) and b_j = -(a_j s_j + e_j):
    c0 = -s_j c1 + Encode(y) + shift + U,   y = P m + M (mod t),
    shift = P (phase_in - Encode(m)) + (P Encode(m) + Encode(M) - Encode(y)) + (e0 + s_j e1 - e_j u)
with ||shift||_inf <= B (the scholar's envelope, recomputed here per return kind).
  H0 real.
  H1 drop shift: statistical, TV <= ||shift||_1/(2F+1) <= N B/(2F+1) per return (ring smudging lemma; holds
     conditionally on c1 and everything else, because U is fresh and independent).
  H2 replace a_j u + e1 by uniform: decisional RLWE with secret u (ternary, i's fresh coins) and public a_j uniform
     (the ceremony). One sample per return. After H1 nothing else depends on (u, e1).
  H3 = the simulator: c1 uniform, c0 = -s_j c1 + Encode(y) + U. It needs y (which j learns anyway: masked by M,
     uniform) and a secret s under which the INPUT batch's phase bound holds. It takes (s, m) extracted from the
     very batch proof that admitted the input ciphertexts: that proof carries the key relation b_j + a_j s + e = 0
     too, and the rewrite of b_j u above holds for ANY short pair satisfying it. So no lemma that the key proof and
     the batch proof extract the same s is needed (Codex review raised the obligation; this discharges it), and y is
     the ideal functionality's output on the extracted input m. The key proof's role is to pin a_j to the seed.
     H2's assumption, exactly: decisional RLWE for a_j u + e1 with u ternary, e1 uniform in [-8, 8], and
     a_j = public_a(seed/j) from a public seed, i.e. RLWE with a random-oracle-derived a (programmable XOF model).
     Computational part per step: (number of returns) x Adv_RLWE. The ZK proofs' simulators and the Fiat-Shamir
     random-oracle programming compose on top; that composition is argued, not machine-checked.
"""
import hashlib
import math
import secrets

import bfv_ref as bfv
import he_matvec as HM
import zkpopk_ligero as Z
from scholar_zkpopk import canonical, public_a


def H(*parts):
    return hashlib.sha256(canonical(list(parts))).hexdigest()


def he_profile(name="ledger"):
    """The HE parameter set the ledger profile pins (proofwire.PROFILES[name]["HE"])."""
    import proofwire as PW
    return dict(PW.PROFILES[name]["HE"])


class CeremonyError(Exception):
    pass


class Ceremony:
    """The ledger's view of one ceremony. Every method validates what it is handed; nothing trusts a custodian."""

    def __init__(self, epoch, n, N, primes, t, T=309):
        self.epoch, self.n, self.N, self.primes, self.t, self.T = epoch, n, N, tuple(primes), t, T
        self.commits, self.reveals, self.keys, self.aborts = {}, {}, {}, []
        self.seed = None

    def _idx(self, i):
        if type(i) is not int or not 0 <= i < self.n:      # Codex review: 0.0 / True aliased custodian 0 in the dicts
            raise CeremonyError("unknown custodian index")
        return i

    def commit(self, i, c):
        self._idx(i)
        if self.seed is not None or i in self.commits or not (0 <= i < self.n):
            raise CeremonyError("commit refused: out of phase, duplicate or unknown custodian")
        if type(c) is not str or len(c) != 64:
            raise CeremonyError("commit refused: shape")
        self.commits[i] = c

    def reveal(self, i, r, salt):
        self._idx(i)
        if len(self.commits) != self.n:
            raise CeremonyError("reveal refused: not every commitment is on the ledger yet")
        if i in self.reveals:
            raise CeremonyError("reveal refused: duplicate")
        if H("dl-keygen-commit", self.epoch, i, r, salt) != self.commits[i]:
            raise CeremonyError(f"reveal refused: custodian {i} does not open its commitment (blamed)")
        self.reveals[i] = (r, salt)
        if len(self.reveals) == self.n:
            self.seed = H("dl-keygen-seed", self.epoch, [self.commits[k] for k in range(self.n)],
                          [self.reveals[k][0] for k in range(self.n)])

    def transcript(self):
        return H("dl-keygen-transcript", self.epoch, self.seed, [self.commits[k] for k in range(self.n)])

    def key_seed(self, j):
        self._idx(j)
        if self.seed is None:
            raise CeremonyError("no seed yet")
        return f"{self.seed}/{j}"

    def context(self, j):
        return ["dl-keygen-key", self.epoch, j, self.transcript()]

    def register(self, j, b, proof):
        self._idx(j)
        if self.seed is None or j in self.keys or not (0 <= j < self.n):
            raise CeremonyError("key refused: out of phase, duplicate or unknown custodian")
        reg = Z.KeyRegistry(self.N, self.primes, self.t, self.key_seed(j), f"custodian-{j}", b)
        st = Z.Statement(reg, "key", [], [], self.context(j))
        ok, why = Z.verify(st, proof, T=self.T)
        if not ok:
            raise CeremonyError(f"key refused: custodian {j}'s key proof: {why}")
        self.keys[j] = dict(registry=reg, proof_digest=hashlib.sha256(proof).hexdigest())
        return reg

    def registry(self, j):
        return self.keys[j]["registry"]


class Custodian:
    def __init__(self, i, rng=None):
        self.i = i
        self.r, self.salt = secrets.token_hex(32), secrets.token_hex(32)

    def commitment(self, epoch):
        return H("dl-keygen-commit", epoch, self.i, self.r, self.salt)

    def make_key(self, cer):
        N, primes, t = cer.N, cer.primes, cer.t
        Q = math.prod(primes)
        rng = secrets.SystemRandom()
        s = [rng.choice((-1, 0, 1)) for _ in range(N)]
        e = [rng.randint(-8, 8) for _ in range(N)]
        a = public_a(cer.key_seed(self.i), N, Q)
        as_, _ = bfv.negacyclic_mul(a, s)
        b = [(-x - y) % Q for x, y in zip(as_, e)]
        reg = Z.KeyRegistry(N, primes, t, cer.key_seed(self.i), f"custodian-{self.i}", b)
        proof = Z.prove(Z.Statement(reg, "key", [], [], cer.context(self.i)), dict(s=s, e_pk=e), T=cer.T)
        self.s, self.e, self.a, self.b = s, e, a, b
        return b, proof


def run_ceremony(epoch, n, N, primes, t, T=309):
    cer = Ceremony(epoch, n, N, primes, t, T)
    cs = [Custodian(i) for i in range(n)]
    for c in cs:
        cer.commit(c.i, c.commitment(epoch))
    for c in cs:
        cer.reveal(c.i, c.r, c.salt)
    for c in cs:
        b, proof = c.make_key(cer)
        cer.register(c.i, b, proof)
    return cer, cs


class CeremonyKey(HM.OwnKey):
    """he_matvec/he_outer's key object, built from the ceremony's (a_j, s_j, e_j) instead of a local random a."""

    def __init__(self, N, Q, t, cust, seed=0):
        self.sch = bfv.BFV(N, Q, t, seed=seed)
        self.sch.s = list(cust.s)
        self.pk = (list(cust.b), list(cust.a))


# ------------------------------------------------------------------------------------------- simulator
def simulate_return(y, s, N, Q, t, F, rng):
    """H3: what corrupt j sees, from y (its decrypted, masked result) and its own s alone."""
    c1 = [rng.randrange(Q) for _ in range(N)]
    cs, _ = bfv.negacyclic_mul(c1, s)
    enc = [(2 * Q * bfv.centered(v, t) + t) // (2 * t) for v in y]
    c0 = [(e - x + rng.randint(-F, F)) % Q for e, x in zip(enc, cs)]
    return c0, c1


# ------------------------------------------------------------------------------------------- distances
def envelopes(d, N, t):
    """Per-return phase-shift bounds B (||shift||_inf) and per-step return counts for the MPC step's HE helpers:
    the scholar's matvec envelopes (scholar_privacy.bound) plus the HE outer product's value and MAC returns."""
    dc, dr = HM.layout(d, N)
    A, pk = t // 2, 16 * N + 9
    Bf = ((d // dc) * dr * dc * A * 17 + 1) // 2 + pk
    Bb = ((d // dr) * dr * dc * A * 17 + 1) // 2 + pk
    # outer: D_a(X) has dr nonzeros (<= A); H_b's ciphertext error <= 8.5 per coefficient; one block per return
    Bo = (dr * A * 17 + 1) // 2 + pk
    n = 3
    ret_f = 2 * n * (n - 1) * (d // dr)          # two forward matvec calls
    ret_b = n * (n - 1) * (d // dc)              # one transpose call
    ret_o = 2 * n * (n - 1) * 2 * (d // dr) * (d // dc)   # two outers, value + MAC returns
    return dict(B_forward=Bf, B_backward=Bb, B_outer=Bo, returns_forward=ret_f, returns_backward=ret_b,
                returns_outer=ret_o, returns=ret_f + ret_b + ret_o)


def distances(d, N, L, F_bits, steps=10**6):
    pr = bfv.ntt_primes(61, L + 1, 2 * N)
    Qp, t = pr[:L], pr[L]
    Q = math.prod(Qp)
    ev = envelopes(d, N, t)
    F = 1 << F_bits
    l1 = N * (ev["returns_forward"] * ev["B_forward"] + ev["returns_backward"] * ev["B_backward"]
              + ev["returns_outer"] * ev["B_outer"])
    stat_step = l1 / (2 * F + 1)
    Bmax = max(ev["B_forward"], ev["B_backward"], ev["B_outer"])
    return dict(d=d, N=N, L=L, log2_Q=round(math.log2(Q), 2), F_bits=F_bits, **ev,
                decrypt_margin_ok=2 * t * (F + Bmax + 1) < Q,
                log2_margin_bits=round(math.log2(Q / (2 * t * (F + Bmax + 1))), 2),
                log2_stat_per_step=round(math.log2(stat_step), 2),
                log2_stat_million=round(math.log2(min(1.0, stat_step * steps)), 2) if stat_step * steps < 1 else 0.0,
                rlwe_samples_per_step=ev["returns"], rlwe_samples_million=ev["returns"] * steps)


def check_params(d, N, L, F_bits):
    """Refuse a flood that would break decryption (the simulator's y is what j decrypts only inside the margin)."""
    r = distances(d, N, L, F_bits)
    if not r["decrypt_margin_ok"]:
        raise ValueError(f"F = 2^{F_bits} breaks decryption at N = {N}, L = {L}, d = {d}")
    return r


def max_flood_bits(d, N, L):
    """The largest F = 2^f that still decrypts: 2 t (F + B + 1) < Q."""
    f = 0
    while distances(d, N, L, f + 1)["decrypt_margin_ok"]:
        f += 1
    return f
