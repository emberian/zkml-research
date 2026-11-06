"""The batched Ligero ZKPoPK (zkpopk_ligero.py), executed and attacked.

    python3 run_zkpopk_ligero.py [N L M T [attacks]]   # default 16 3 3 309 all; writes zkpopk_ligero_results_N{N}_L{L}_M{M}[_T{T}].json (no suffix: the ledger profile, T = 309)

Honest secret-key batch (the MPC helper send: forward layout, d_c slots; plus one transpose-layout ciphertext) and
public-key batch (FHE (b) masks), then the attacks the brief names (malformed keys, mixed limbs, oversized error,
changed response, stale context), the Fiat-Shamir ordering falsifier, layout and codec cases, and the recipient gate
in front of he_matvec.ptxct. Every executed proof's byte length is compared with the count formula.
"""
import json
import math
import random
import sys
import time

import bfv_ref as bfv
import he_matvec as HM
import zkpopk_ligero as Z


def crt(residues, primes):
    Q = math.prod(primes)
    x = 0
    for r, q in zip(residues, primes):
        Mq = Q // q
        x += r * Mq * pow(Mq, -1, q)
    return x % Q


def sk_batch(N, Qp, t, M, rng, key_seed="registry-seed-0", key_id="custodian-1"):
    reg, s, epk = Z.keygen(N, Qp, t, key_seed, key_id, rng)
    dc = min(64, N // 2)
    cts, ws, slots = [], [], []
    for j in range(M):
        if j == M - 1 and M > 1:                       # transpose layout: slots at 64 r (here: stride N / dc)
            S = list(range(0, N, max(1, N // dc)))[:dc]
        else:
            S = [dc - 1 - c for c in range(dc)][::-1]
        m = [0] * N
        for k in S:
            m[k] = rng.randrange(t)
        ct, w = Z.encrypt_sk(reg, s, m, S, rng)
        cts.append(ct); ws.append(w); slots.append(S)
    return reg, dict(s=s, e_pk=epk, cts=ws), cts, slots


def main():
    a = sys.argv[1:]
    N, L, M, T = (int(x) for x in a[:4]) if len(a) >= 4 else (16, 3, 3, 309)
    attacks = a[4] if len(a) > 4 else "all"
    pr = bfv.ntt_primes(61, L + 1, 2 * N)
    Qp, t = pr[:L], pr[L]
    Q = math.prod(Qp)
    rng = random.Random(N * 1000 + M)
    ctx = ("mind-0", 0, 7, "matvec-fwd-0", "custodian-1", ("custodian-0", "custodian-2"))
    out = dict(N=N, L=L, M=M, T=T, P_bits=Z.P.bit_length(), rows={}, counts={})

    def record(name, ok, why, expect):
        good = (ok == expect)
        out["rows"][name] = dict(verdict="ACCEPT" if ok else "REFUSED", by=why, as_expected=good)
        print(f"{name:52s} {'ACCEPT ' if ok else 'REFUSED'} {why}{'' if good else '   <-- UNEXPECTED'}", flush=True)
        return good

    reg, wit, cts, slots = sk_batch(N, Qp, t, M, rng)
    st = Z.Statement(reg, "sk", cts, slots, ctx)
    t0 = time.time()
    blob = Z.prove(st, wit, T=T, rng=rng)
    tp = time.time() - t0
    t0 = time.time()
    ok, why = Z.verify(st, blob, T=T)
    tv = time.time() - t0
    sh = Z.shape(st, T)
    formula, _ = Z.batch_proof_bits("sk", N, Qp, t, [len(S) for S in slots], T)
    out["counts"]["sk"] = dict(bytes=len(blob), formula_bits=formula, exact=8 * len(blob) == formula, k=sh["k"],
                               rows=sh["m1"] + sh["m2"], digits=sh["n1"] + sh["n2"], prove_s=round(tp, 1),
                               verify_s=round(tv, 1))
    print("sk counts", out["counts"]["sk"], flush=True)
    allgood = record("honest secret-key batch", ok, why, True)
    allgood &= out["counts"]["sk"]["exact"]
    if attacks == "honest":
        json.dump(out, open(f"zkpopk_ligero_results_N{N}_L{L}_M{M}{'' if T == 309 else f'_T{T}'}.json", "w"), indent=1)
        sys.exit(0 if allgood else 1)

    # --- stale context, other recipient, other sender's key
    for name, c2 in (("stale context: next step", ctx[:2] + (8,) + ctx[3:]),
                     ("stale context: other epoch", (ctx[0], 1) + ctx[2:]),
                     ("other recipient set", ctx[:5] + (("custodian-0", "custodian-3"),)),
                     ("other call (replay into the transpose)", ctx[:3] + ("matvec-T-0",) + ctx[4:])):
        allgood &= record(name, *Z.verify(Z.Statement(reg, "sk", cts, slots, c2), blob, T=T), False)
    reg_other, _, _ = Z.keygen(N, Qp, t, "registry-seed-9", "custodian-2", rng)
    allgood &= record("verified against another custodian's registered key",
                      *Z.verify(Z.Statement(reg_other, "sk", cts, slots, ctx), blob, T=T), False)

    # --- malformed keys
    bad = Z.KeyRegistry(N, Qp, t, reg.seed, reg.key_id, reg.b)
    bad.a = tuple([1] + [0] * (N - 1))                  # the scholar's a = 1 key, presented as registered
    allgood &= record("malformed key: a = 1 instead of the pinned seed's a",
                      *Z.verify(Z.Statement(bad, "sk", cts, slots, ctx), blob, T=T), False)
    rb = Z.KeyRegistry(N, Qp, t, "registry-seed-0", "custodian-1", [rng.randrange(Q) for _ in range(N)])
    # b not of the form -(a s + e) with short s, e: a malicious registration. The sender keeps its real s for the
    # ciphertexts, so e_pk = -(b + a s) is a full-size integer; the forger packs it (and the quotients it forces)
    # into single non-binary digits so that the linear test holds.
    as_, _ = bfv.negacyclic_mul(list(rb.a), wit["s"])
    epk_big = [bfv.centered(-(x + y), Q) for x, y in zip(rb.b, as_)]
    st_rb = Z.Statement(rb, "sk", cts, slots, ctx)
    b2 = Z.prove(st_rb, dict(wit, e_pk=epk_big), T=T, rng=rng, cheat=dict(raw=True))
    allgood &= record("malformed key: b random, prover forges e_pk = -(b + a s)", *Z.verify(st_rb, b2, T=T), False)

    # --- mixed limbs: limb 0 encrypts m, limbs 1.. encrypt m' (same a, s)
    j = 0
    S = slots[j]
    m2 = [0] * N
    for k in S:
        m2[k] = rng.randrange(t)
    ctB, wB = Z.encrypt_sk(reg, wit["s"], m2, S, random.Random(5))
    c0 = [crt([cts[j][0][k] % Qp[0]] + [ctB[0][k] % q for q in Qp[1:]], Qp) for k in range(N)]
    c1 = [crt([cts[j][1][k] % Qp[0]] + [ctB[1][k] % q for q in Qp[1:]], Qp) for k in range(N)]
    cts_mix = [(c0, c1)] + cts[1:]
    st_mix = Z.Statement(reg, "sk", cts_mix, slots, ctx)
    b3 = Z.prove(st_mix, wit, T=T, rng=rng, cheat=dict(forge=True))
    allgood &= record("mixed limbs: limb 0 encrypts m, limbs 1+ encrypt m'", *Z.verify(st_mix, b3, T=T), False)

    # --- oversized error: a ciphertext whose error is 9 at one coefficient
    e9 = list(wit["cts"][0]["e"]); e9[N // 2] = 9
    m0 = [0] * N
    for k, v in zip(slots[0], wit["cts"][0]["m"]):
        m0[k] = v
    ct9, w9 = Z.encrypt_sk(reg, wit["s"], m0, slots[0], random.Random(6), e=e9)
    cts9 = [ct9] + cts[1:]
    st9 = Z.Statement(reg, "sk", cts9, slots, ctx)
    wit9 = dict(wit, cts=[w9] + wit["cts"][1:])
    g1, _ = Z.layout(st9)
    vals = {"s": wit["s"], "e_pk": wit["e_pk"]}
    for jj, w in enumerate(wit9["cts"]):
        vals[f"e{jj}"], vals[f"r{jj}"] = list(w["e"]), w["r"]
    vals["e0"][N // 2] = 8
    d1 = Z.values_to_digits(g1, vals)
    pos = 2 * N + 5 * N + 5 * (N // 2)                  # s, e_pk, then e0
    d1[pos] = 2                                          # digits (2,1,1,1,1) = 17 = 9 + 8: a non-binary digit
    b4 = Z.prove(st9, wit9, T=T, rng=rng, cheat=dict(digits1=d1, values1={"e0": e9}))
    allgood &= record("oversized error 9, carried by a non-binary digit", *Z.verify(st9, b4, T=T), False)
    vals["e0"][N // 2] = 8
    b5 = Z.prove(st9, wit9, T=T, rng=rng, cheat=dict(values1=dict(vals)))
    allgood &= record("oversized error 9, prover claims 8 (binary digits)", *Z.verify(st9, b5, T=T), False)

    # --- layout: plaintext nonzero off the slots
    mo = list(m0); off_slot = next(k for k in range(N) if k not in set(slots[0])); mo[off_slot] = 12345
    cto, wo = Z.encrypt_sk(reg, wit["s"], mo, sorted(set(slots[0]) | {off_slot}), random.Random(7))
    wo2 = dict(e=wo["e"], m=[mo[k] for k in slots[0]],
               r=[Z._round_scale(Q, t, mo[k])[1] for k in slots[0]])
    sto = Z.Statement(reg, "sk", [cto] + cts[1:], slots, ctx)
    b6 = Z.prove(sto, dict(wit, cts=[wo2] + wit["cts"][1:]), T=T, rng=rng, cheat=dict(forge=True))
    allgood &= record("plaintext off the layout (padding coefficient nonzero)", *Z.verify(sto, b6, T=T), False)

    # --- changed responses and codec
    sh = Z.shape(st, T)
    k, th = sh["k"], sh["th"]
    wstart = 64
    col0 = 64 + 32 * ((k + th) + (2 * k + th - 1) + (2 * k + 2 * th - 1))

    def flip(b, at):
        return b[:at] + bytes([b[at] ^ 1]) + b[at + 1:]
    for name, bb in (("changed response: proximity message w", flip(blob, wstart + 31)),
                     ("changed response: linear message q", flip(blob, wstart + 32 * (k + th) + 31)),
                     ("changed response: quadratic message p", flip(blob, wstart + 32 * (3 * k + 2 * th - 1) + 31)),
                     ("changed response: an opened column value", flip(blob, col0 + 31)),
                     ("changed response: a leaf salt", flip(blob, col0 + 32 * (sh["m1"] + 3) + 5)),
                     ("changed commitment: root 1", flip(blob, 3)),
                     ("changed commitment: root 2", flip(blob, 40)),
                     ("truncated by one byte", blob[:-1]),
                     ("one trailing byte", blob + b"\x00"),
                     ("noncanonical element (w_0 replaced by 2^256 - 1 >= P)",
                      blob[:64] + ((1 << 256) - 1).to_bytes(32, "big") + blob[96:])):
        allgood &= record(name, *Z.verify(st, bb, T=T), False)

    # --- Fiat-Shamir ordering: a malformed ciphertext (c0 junk, outside every plaintext's noise neighbourhood)
    junk = [(Q // (2 * t) + 7 * k) % Q for k in range(N)]
    st_j = Z.Statement(reg, "sk", [(junk, [0] * N)] + cts[1:], slots, ctx)
    forged = Z.simulate_legacy(st_j, T=T, rng=rng)
    allgood &= record("FS falsifier: simulated proof of a malformed ct, LEGACY verifier",
                      *Z.verify(st_j, forged, T=T, legacy=True), True)
    allgood &= record("FS falsifier: the same proof, real verifier", *Z.verify(st_j, forged, T=T), False)

    # --- public-key batch (FHE (b) masks under the joint key)
    regj, _, _ = Z.keygen(N, Qp, t, "joint-seed-0", "joint", rng)
    pcts, pws, psl = [], [], []
    for jj in range(max(1, M - 1)):
        Sx = list(range(min(N, 8)))
        m = [0] * N
        for kk in Sx:
            m[kk] = rng.randrange(t)
        ct, w = Z.encrypt_pk(regj, m, Sx, rng)
        pcts.append(ct); pws.append(w); psl.append(Sx)
    stp = Z.Statement(regj, "pk", pcts, psl, ctx)
    bp = Z.prove(stp, dict(cts=pws), T=T, rng=rng)
    fpk, _ = Z.batch_proof_bits("pk", N, Qp, t, [len(x) for x in psl], T)
    out["counts"]["pk"] = dict(bytes=len(bp), formula_bits=fpk, exact=8 * len(bp) == fpk)
    allgood &= out["counts"]["pk"]["exact"]
    allgood &= record("honest public-key batch (joint key)", *Z.verify(stp, bp, T=T), True)
    e0 = list(pws[0]["e0"]); e0[1] = 9
    mm = [0] * N
    for kk, v in zip(psl[0], pws[0]["m"]):
        mm[kk] = v
    ctb, wb = Z.encrypt_pk(regj, mm, psl[0], random.Random(8), e0=e0)
    stb = Z.Statement(regj, "pk", [ctb] + pcts[1:], psl, ctx)
    wb["e0"] = list(e0); wb["e0"][1] = 8
    bb = Z.prove(stb, dict(cts=[wb] + pws[1:]), T=T, rng=rng, cheat=dict(forge=True))
    allgood &= record("public key: oversized e0 = 9, prover claims 8", *Z.verify(stb, bb, T=T), False)

    # --- Codex review trace (gen 4): profile and wraparound regressions; run the suite under python3 -O too
    pw = bfv.ntt_primes(61, 6, 4)
    rw, _, _ = Z.keygen(2, pw[:5], pw[5], "audit-overflow", rng=random.Random(0))
    stw = Z.Statement(rw, "sk", [([rw.Q - 1, 0], [0, 0])], [[]], "audit")
    try:
        r_ = Z.verify(stw, bytes(100), T=T)
    except Exception as ex:                                  # a crash is a failure of this row
        r_ = (True, f"verifier raised {type(ex).__name__}")
    allgood &= record("regression: five 61-bit primes (Q 305 bits), zero bytes", *r_, False)
    qbig = bfv.ntt_primes(256, 1, 4)[0]
    rbig = Z.KeyRegistry(2, [qbig], 3, "audit-optimized", "custodian", [0, 0])
    stb_ = Z.Statement(rbig, "sk", [([Z.P, 0], [0, 0])], [[]], "audit")
    try:
        bz = Z.prove(stb_, dict(s=[0, 0], e_pk=[0, 0], cts=[dict(e=[0, 0], m=[], r=[])]), T=T, rng=rng,
                     cheat=dict(raw=True))
        r_ = Z.verify(stb_, bz, T=T)
    except ValueError as ex:
        r_ = (False, f"prover refused: {ex}")
    allgood &= record(f"regression: 256-bit prime, false statement (asserts {'ON' if __debug__ else 'STRIPPED'})", *r_, False)
    allgood &= record("regression: 256-bit prime registry, verifier on arbitrary bytes", *Z.verify(stb_, bytes(4096), T=T), False)

    # --- independent review (gen 4): a small limb prime made the fold grindable (1/q per try)
    small = bfv.ntt_primes(17, 1, 2 * N)[0]
    Qs = small * math.prod(Qp[1:])
    rs = Z.KeyRegistry(N, [small] + Qp[1:], t, "registry-seed-0", "custodian-1", [x % Qs for x in reg.b])
    cts_s = [([x % Qs for x in c0], [x % Qs for x in c1]) for c0, c1 in cts]
    allgood &= record("regression: a 17-bit limb prime in the registry",
                      *Z.verify(Z.Statement(rs, "sk", cts_s, slots, ctx), blob, T=T), False)

    # --- Codex review 2: one limb with Q ~ t has no decryption margin
    q1 = bfv.ntt_primes(61, 1, 4)[0]
    t1 = next(x for x in range(q1 - 2, 1 << 60, -2) if bfv.is_probable_prime(x))
    r1 = Z.KeyRegistry(2, [q1], t1, "audit-margin", "custodian", [0, 0])
    allgood &= record("regression: one limb with Q < 17 t (no decryption margin)",
                      *Z.verify(Z.Statement(r1, "sk", [([8, 8], [0, 0])], [[]], "audit"), bytes(64), T=T), False)
    allgood &= record("regression: verify(None) fails closed", *Z.verify(None, b""), False)

    # --- the recipient gate in front of he_matvec.ptxct
    calls = {"n": 0}
    real = HM.ptxct

    def counted(Pm, ct, Qx):
        calls["n"] += 1
        return real(Pm, ct, Qx)

    def multiply_verified(Pm, statement, proof):
        ok_, why_ = Z.verify(statement, proof, T=T)
        if not ok_:
            raise ValueError("ciphertext batch refused: " + why_)
        return [counted(Pm, ct, statement.reg.Q) for ct in statement.cts]

    Pm = [rng.randrange(-5, 6) for _ in range(N)]
    prods = multiply_verified(Pm, st, blob)
    try:
        multiply_verified(Pm, st_j, forged)
        refused = False
    except ValueError:
        refused = True
    out["gate"] = dict(products_after_accept=len(prods), ptxct_calls=calls["n"], forged_refused=refused,
                       ptxct_calls_on_refusal=calls["n"] - len(prods))
    allgood &= refused and calls["n"] == len(prods)
    print("gate", out["gate"], flush=True)
    out["all_as_expected"] = bool(allgood)
    json.dump(out, open(f"zkpopk_ligero_results_N{N}_L{L}_M{M}{'' if T == 309 else f'_T{T}'}.json", "w"), indent=1, default=str)
    print("ALL AS EXPECTED" if allgood else "SOME ROW UNEXPECTED", flush=True)
    sys.exit(0 if allgood else 1)


if __name__ == "__main__":
    main()
