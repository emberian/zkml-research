"""Item 3 executed: the key-generation ceremony and its attacks, then an MPC step with BOTH HE helpers run on the
ceremony's keys, with every return captured to (a) measure the realized phase shift against the envelope the
distance bound uses, and (b) run the simulator on the same outputs. Plus the distance table.

    python3 run_keygen_ceremony.py N L d F_bits T      # e.g. 256 3 4 118 309 (Mac); 16384 4 64 175 309 (forge)
    writes keygen_ceremony_results_N{N}_L{L}_d{d}.json
"""
import json
import math
import random
import sys
import time

import bfv_ref as bfv
import he_matvec as HM
import he_outer as HO
import keygen_ceremony as K
import mpc_fork as MF
import spdz
import step_spec as S
import zkpopk_ligero as Z
from scholar_zkpopk import public_a


class Recorder(random.Random):
    """The returner's rng, recording every flood draw (the only randint with a range above 2^64) with the kind of
    return it floods: 'f' forward matvec, 'b' transpose matvec, 'o' outer."""
    log, kinds, current = [], [], {"mv": "f"}

    def __init__(self, seed, src):
        super().__init__(seed)
        self.src = src

    def randint(self, a, b):
        v = super().randint(a, b)
        if b - a > 1 << 64:
            Recorder.log.append(v)
            Recorder.kinds.append("o" if self.src == "ou" else Recorder.current["mv"])
        return v


_orig_call = HM.HEMatvec.__call__


def _tagged_call(self, W, v, transpose=False):
    Recorder.current["mv"] = "b" if transpose else "f"
    return _orig_call(self, W, v, transpose)


HM.HEMatvec.__call__ = _tagged_call


def main():
    N, L, d, F_bits, T = (int(x) for x in sys.argv[1:6])
    pr = bfv.ntt_primes(61, L + 1, 2 * N)
    Qp, t = pr[:L], pr[L]
    Q = math.prod(Qp)
    K.check_params(d, N, L, F_bits)
    out = dict(N=N, L=L, d=d, F_bits=F_bits, T=T, rows={})
    allgood = True

    def record(name, ok, why, expect):
        nonlocal allgood
        good = ok == expect
        allgood &= good
        out["rows"][name] = dict(verdict="ACCEPT" if ok else "REFUSED", by=why, as_expected=good)
        print(f"{name:60s} {'ACCEPT ' if ok else 'REFUSED'} {why}{'' if good else '   <-- UNEXPECTED'}", flush=True)

    def attempt(name, fn, expect=False):
        try:
            fn()
            record(name, True, "accepted", expect)
        except (K.CeremonyError, ValueError) as ex:
            record(name, False, str(ex), expect)

    # ------------------------------------------------------------------ honest ceremony
    t0 = time.time()
    cer, cs = K.run_ceremony(epoch=1, n=3, N=N, primes=Qp, t=t, T=T)
    out["ceremony_seconds"] = round(time.time() - t0, 1)
    out["key_proof_bytes"] = Z.proof_bytes(**{k: v for k, v in Z.shape(Z.Statement(cer.registry(0), "key", [], [],
                                                                                    cer.context(0)), T).items()
                                               if k in ("k", "th", "T", "m1", "m2")})
    record("honest ceremony: three keys registered with proofs", True, f"seed {cer.seed[:16]}..", True)

    # ------------------------------------------------------------------ ceremony attacks
    c2 = K.Ceremony(2, 3, N, Qp, t, T)
    cu = [K.Custodian(i) for i in range(3)]
    c2.commit(0, cu[0].commitment(2))
    attempt("reveal before every commitment is posted (rushing)", lambda: c2.reveal(0, cu[0].r, cu[0].salt))
    c2.commit(1, cu[1].commitment(2)); c2.commit(2, cu[2].commitment(2))
    attempt("equivocation: reveal a different r than committed", lambda: c2.reveal(1, cu[1].r[::-1], cu[1].salt))
    attempt("second commitment by the same custodian", lambda: c2.commit(2, cu[2].commitment(2)))
    for c in cu:
        c2.reveal(c.i, c.r, c.salt)
    attempt("commitment after the seed is fixed", lambda: c2.commit(0, cu[0].commitment(2)))

    def own_a_key():
        # custodian 0 generates its key with its OWN a (here a = 1, the scholar's attack) and tries to register it
        s = [random.choice((-1, 0, 1)) for _ in range(N)]
        a1 = [1] + [0] * (N - 1)
        b = [(-x) % Q for x in s]                      # b = -(a s + 0) with a = 1
        reg = Z.KeyRegistry(N, Qp, t, c2.key_seed(0), "custodian-0", b)
        as_, _ = bfv.negacyclic_mul(list(reg.a), s)
        e_forced = [bfv.centered(-(x + y), Q) for x, y in zip(b, as_)]
        proof = Z.prove(Z.Statement(reg, "key", [], [], c2.context(0)), dict(s=s, e_pk=e_forced), T=T,
                        cheat=dict(raw=True))
        c2.register(0, b, proof)
    attempt("key built on a chosen a = 1, proof forged against the ceremony's a", own_a_key)

    def random_b():
        b = [random.randrange(Q) for _ in range(N)]
        reg = Z.KeyRegistry(N, Qp, t, c2.key_seed(1), "custodian-1", b)
        proof = Z.prove(Z.Statement(reg, "key", [], [], c2.context(1)),
                        dict(s=[0] * N, e_pk=[bfv.centered(-x, Q) for x in b]), T=T, cheat=dict(raw=True))
        c2.register(1, b, proof)
    attempt("random b (no short secret), forged digits", random_b)

    attempt("custodian index 0.0 (aliases 0 in a dict)", lambda: c2.register(0.0, cs[0].b, b""))
    attempt("custodian index True", lambda: c2.commit(True, "0" * 64))
    attempt("reveal by an unknown custodian", lambda: c2.reveal(7, "00", "00"))
    b0, p0 = cu[2].make_key(c2)
    attempt("custodian 2's honest key proof registered as custodian 1's", lambda: c2.register(1, b0, p0))
    attempt("epoch 1's key proof replayed into epoch 2", lambda: c2.register(0, cs[0].b, b"" + _proof_of(cer, cs[0], T)))
    attempt("honest key, epoch 2", lambda: c2.register(2, b0, p0), expect=True)

    # ------------------------------------------------------------------ an MPC step on the ceremony's keys
    keys = [K.CeremonyKey(N, Q, t, c, seed=200 + c.i) for c in cs]
    tab = MF.tables(t)
    rng = random.Random(d)
    W1 = [[rng.randint(-7, 7) for _ in range(d)] for _ in range(d)]
    W2 = [[rng.randint(-7, 7) for _ in range(d)] for _ in range(d)]
    x = [rng.randint(-7, 7) for _ in range(d)]
    y = [rng.randint(-7, 7) for _ in range(d)]
    m = lambda M: [[v % t for v in r] for r in M]
    eng = spdz.Engine(t, 3, spdz.Dealer(t, 3, 5))
    noise = (N * (t // 2) * 32).bit_length()
    mv = HM.HEMatvec(eng, keys, N, Q, flood_bits=F_bits - noise)
    ou = HO.HEOuter(eng, keys, N, Q, flood_bits=F_bits - (N * (t // 2) * 16 * 2).bit_length())
    mv.rng, ou.rng = Recorder(11, "mv"), Recorder(13, "ou")
    captured, reals = [], []
    for kk, key in enumerate(keys):
        real = key.sch.decrypt
        reals.append(real)

        def dec(ct, real=real, kk=kk):
            res = real(ct)
            captured.append((kk, ct, res))
            return res
        key.sch.decrypt = dec
    t0 = time.time()
    W1n, W2n, _ = MF.run_step(eng, m(W1), m(W2), [v % t for v in x], [v % t for v in y], tab, 9, mv=mv, ou=ou)
    eng.mac_check("he")
    e1, e2, _ = S.step(W1, W2, x, y)
    rev = lambda X: [[MF.reveal(eng, c) for c in r] for r in X]
    refines = rev(W1n) == e1 and rev(W2n) == e2
    out["step_seconds"] = round(time.time() - t0, 1)
    record("MPC step (HE matvec + HE outer) on the ceremony's keys refines step_spec", refines, "", True)
    # realized shift versus envelope, and the simulator on the same outputs
    ev = K.envelopes(d, N, t)
    F = 1 << F_bits
    if len(Recorder.log) != N * len(captured):
        record("capture alignment", False, f"{len(Recorder.log)} flood draws for {len(captured)} returns", True)
    worst = {"f": 0, "b": 0, "o": 0}
    sim_ok, sim_phase_ok = True, True
    srng = random.Random(99)
    for idx, (kk, (c0, c1), res) in enumerate(captured):
        s = cs[kk].s
        U = Recorder.log[idx * N:(idx + 1) * N]
        kind = Recorder.kinds[idx * N]
        cs1, _ = bfv.negacyclic_mul(c1, s)
        phase = [bfv.centered(a + b, Q) for a, b in zip(c0, cs1)]
        enc = [(2 * Q * bfv.centered(v, t) + t) // (2 * t) for v in res]
        shift = [bfv.centered(ph - en - u, Q) for ph, en, u in zip(phase, enc, U)]
        worst[kind] = max(worst[kind], max(abs(v) for v in shift))
        sc0, sc1 = K.simulate_return(res, s, N, Q, t, F, srng)
        if reals[kk]((sc0, sc1)) != res:
            sim_ok = False
        ss1, _ = bfv.negacyclic_mul(sc1, s)
        if max(abs(bfv.centered(a + b - en, Q)) for a, b, en in zip(sc0, ss1, enc)) > F:
            sim_phase_ok = False
    out["returns_captured"] = len(captured)
    out["returns_formula"] = ev["returns"]
    env = {"f": ev["B_forward"], "b": ev["B_backward"], "o": ev["B_outer"]}
    out["realized_vs_envelope_log2"] = {k: (round(math.log2(max(worst[k], 1)), 2), round(math.log2(env[k]), 2))
                                        for k in env}
    record("every return's realized shift is inside its kind's envelope", all(worst[k] <= env[k] for k in env),
           f"(realized, envelope) log2: {out['realized_vs_envelope_log2']}", True)
    record("simulator: decrypts to the same y on every return", sim_ok, f"{len(captured)} returns", True)
    record("simulator: phase within the flood of Encode(y)", sim_phase_ok, "", True)
    record("returns captured = the step's return count (formula)", len(captured) == ev["returns"],
           f"{len(captured)} vs {ev['returns']}", True)
    out["distances"] = {f"d{dd}": K.distances(dd, N, L, F_bits) for dd in (64, 1024, 4096)}
    out["all_as_expected"] = bool(allgood)
    json.dump(out, open(f"keygen_ceremony_results_N{N}_L{L}_d{d}.json", "w"), indent=1, default=str)
    print(json.dumps(out["distances"], indent=1))
    print("ALL AS EXPECTED" if allgood else "SOME ROW UNEXPECTED", flush=True)
    sys.exit(0 if allgood else 1)


def _proof_of(cer, cust, T):
    """Re-prove custodian's epoch-1 key under epoch 1's context (a genuine old proof, replayed)."""
    reg = cer.registry(cust.i)
    return Z.prove(Z.Statement(reg, "key", [], [], cer.context(cust.i)), dict(s=cust.s, e_pk=cust.e), T=T)


if __name__ == "__main__":
    main()
