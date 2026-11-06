#!/usr/bin/env python3
"""Exact counts for minidregg's Tower256 additive FRI (succinct controller), from the Lean
definitions. Counts, not clocks. Stdlib only.

Byte layouts transcribed from minidregg (lane/tower256-final-check @ 7015c0c06):
  encodeLength n = [0]*n + [1]                       (Tower256CshakeMerkleController:63, unary)
  envelope b     = encodeLength(len b) ++ b          (:67)  -> 2|b|+1 bytes
  hashLeaf       = cSHAKE(leafCust, 0 :: envelope(value32))         -> 66 data bytes
  hashNode       = cSHAKE(nodeCust, 1 :: env(d32) ++ env(d32))      -> 131 data bytes
  basisPrefix    = env(encLen ell) ++ env(encLen m) ++ env(offset32) ++ concat_i env(basisFrame i)
  basisFrame i   = env(encLen i) ++ env(value32)                    (Tower256AdditiveFriController:239)
  challengeInput j = env(statementBytes) ++ env(basisPrefix) ++
                     concat_{n<=j} (env(encLen n) ++ env(root32))   (SuccinctController.challengeInput)
  queryPrefix    = env(stmt) ++ env(basis) ++ concat_{n<=m}(env(encLen n) ++ env(root32))
                   ++ concat_{j<m} env(value32)
  seed a input   = queryPrefix ++ env(encLen a)
cSHAKE256: rate 136 bytes. A call with customization S costs one bytepad(encode_string(N) ||
encode_string(S)) block (constant per S, cacheable) plus ceil((L+1)/136) Keccak-f for L data
bytes (the 2-bit cSHAKE suffix and pad10*1 need at least one byte). Output 32 bytes < rate.

[A] Merkle path codec: siblings * 32 bytes plus a 4-byte count (merklePathStream's framing
not transcribed). [A] Tower256 value codec = 32 bytes. [A] additive NTT = (N/2) log2 N mults.
"""
import math, sys

RATE = 136

def env(n, unary=True):
    return (n + 1 + n) if unary else (4 + n)

def enclen(n, unary=True):
    return (n + 1) if unary else 4

def kf(L, cached_prefix=True):
    return math.ceil((L + 1) / RATE) + (0 if cached_prefix else 1)

def basis_prefix(ell, m, u):
    b = env(enclen(ell, u), u) + env(enclen(m, u), u) + env(32, u)
    for i in range(ell):
        frame = env(enclen(i, u), u) + env(32, u)
        b += env(frame, u)
    return b

def transcript(ell, m, q, S, u=True):
    head = env(S, u) + env(basis_prefix(ell, m, u), u)
    per_root = lambda n: env(enclen(n, u), u) + env(32, u)
    ch = []
    acc = head
    for j in range(m):
        acc += per_root(j)
        ch.append(acc)
    qp = head + sum(per_root(n) for n in range(m + 1)) + m * env(32, u)
    seeds = [qp + env(enclen(a, u), u) for a in range(q)]
    return ch, qp, seeds

def counts(ell, lb, m, q, S=256, unary=True, cache=False):
    n0 = 2 ** ell
    leaf = 66 if unary else 4 + 1 + 32 + 0  # 0::env(value)
    node = 131 if unary else 1 + 2 * (4 + 32)
    assert kf(leaf) == 1 and kf(node) == 1
    merkle_kf = sum(2 ** (ell - n) + (2 ** (ell - n) - 1) for n in range(m + 1))
    ch, qp, seeds = transcript(ell, m, q, S, unary)
    ch_kf = sum(kf(L) for L in ch)
    if cache:  # absorb queryPrefix's full blocks once, then each seed absorbs only its tail
        full = qp // RATE
        seed_kf = full + sum(math.ceil(((qp - full * RATE) + (L - qp) + 1) / RATE) for L in seeds)
    else:
        seed_kf = sum(kf(L) for L in seeds)
    fold_mul = sum(2 * 2 ** (ell - j - 1) for j in range(m))
    encode_mul = (n0 // 2) * ell
    fin = 2 ** (ell - m)
    final_coeffs = 2 ** (ell - lb - m)
    interp_mul = (fin // 2) * (ell - m)
    # proof bytes
    paths = sum(q * (2 * (ell - j) + (ell - j - 1)) for j in range(m))
    proof = 32 * (m + 1) + 32 * m + 32 * 3 * m * q + 32 * paths + 4 * 3 * m * q + 32 * final_coeffs
    # verifier
    ver_path_kf = sum(q * (2 * (1 + (ell - j)) + (1 + (ell - j - 1))) for j in range(m))
    ver_final_kf = fin + (fin - 1)
    ver_mul = 2 * m * q + fin * final_coeffs
    ud_bits = q * -math.log2((1 + 2 ** -lb) / 2)
    return dict(ell=ell, lb=lb, m=m, q=q, ud_bits=round(min(ud_bits, 255), 1),
                prover_kf=merkle_kf + ch_kf + seed_kf, merkle_kf=merkle_kf,
                challenge_kf=ch_kf, seed_kf=seed_kf, query_prefix_bytes=qp,
                last_seed_bytes=seeds[-1] if seeds else 0,
                encode_mul=encode_mul, fold_mul=fold_mul, interp_mul=interp_mul,
                proof_bytes=proof, verifier_kf=ver_path_kf + ver_final_kf + ch_kf + seed_kf,
                verifier_mul=ver_mul)

def q_for(lb, bits=100):
    return math.ceil(bits / -math.log2((1 + 2 ** -lb) / 2))

if __name__ == "__main__":
    rows = []
    for ell, lb in [(14, 2), (16, 2), (20, 2), (22, 2), (16, 1), (20, 1)]:
        m = ell - lb - 2
        q = q_for(lb)
        for unary, cache, label in [(True, False, "unary"), (True, True, "unary+cache"),
                                    (False, False, "u32")]:
            c = counts(ell, lb, m, q, unary=unary, cache=cache)
            c["codec"] = label
            rows.append(c)
    keys = ["ell", "lb", "m", "q", "ud_bits", "codec", "prover_kf", "merkle_kf", "challenge_kf",
            "seed_kf", "query_prefix_bytes", "last_seed_bytes", "encode_mul", "fold_mul",
            "interp_mul", "proof_bytes", "verifier_kf", "verifier_mul"]
    print("\t".join(keys))
    for r in rows:
        print("\t".join(str(r[k]) for k in keys))
