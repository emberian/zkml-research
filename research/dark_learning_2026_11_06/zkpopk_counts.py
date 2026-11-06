"""Per-step ZKPoPK counts for the fork table (gen 4): the batched Ligero proof (zkpopk_ligero.py) priced on the
existing schedules. Sizes come from zkpopk_ligero.proof_bytes on each batch's shape, the same function the executed
codec is checked against (run_zkpopk_ligero.py asserts len(blob) == proof_bytes for every executed proof).

Schedules, read from the code that builds them:
  MPC (HE matvec + HE outer): per step 3 matvec calls (he_matvec.counts default: forward, forward, transpose) and
  2 outer calls (he_outer.counts default). In each call every custodian sends one batch of distinct ciphertexts:
  forward d/d_c ciphertexts with d_c slots, transpose d/d_r with d_r slots, outer d/d_c with d_c slots
  (he_matvec.layout, he_outer.layout). One proof per (custodian, call), verified by the n - 1 recipients.
  A recipient must verify BEFORE it returns a product (privacy), so a batch cannot span calls.
  FHE (b): step_counts.mask_nonideal's mask ciphertexts, public-key encryptions under the joint key. Each custodian
  posts one per mask pair per step ('pairs'), and the pairs use 'used' plaintext coefficients in all
  (step_counts.json). They are preprocessing, so one proof per custodian per step.
  Bits are counted posted (one copy per proof) and delivered (x (n - 1)).

    python3 zkpopk_counts.py      # writes zkpopk_counts.json
"""
import json
import math

import bfv_ref as bfv
import he_matvec as HM
import he_outer as HO
import zkpopk_ligero as Z

STERN_PER_PROOF = 235_113_860_648        # scholar_zkpopk_results / zkpopk-design.md, one proof at N = 8192
MODEL_PER_CT = lambda N, L: 2 * L * (N - 1) * 61 + 7 * N * 61     # he_matvec.counts' old unbuilt estimate


def params(N, L):
    pr = bfv.ntt_primes(61, L + 1, 2 * N)
    return pr[:L], pr[L]


def mpc_batches(d, N):
    dc, dr = HM.layout(d, N)
    calls = [("matvec-fwd", d // dc, dc), ("matvec-fwd", d // dc, dc), ("matvec-T", d // dr, dr)]
    odc, odr = HO.layout(d, d, N)
    calls += [("outer", d // odc, odc)] * 2
    return calls


def even(total, k):
    q, r = divmod(total, k)
    return [q + (1 if i < r else 0) for i in range(k)]


def step(d, N, L, T, fhe_pairs=None, n=3):
    primes, t = params(N, L)
    out = dict(d=d, N=N, L=L, T=T)
    rows, posted, cts = [], 0, 0
    cache = {}
    for name, M, S in mpc_batches(d, N):
        key = (M, S)
        if key not in cache:
            cache[key] = Z.batch_proof_bits("sk", N, primes, t, [S] * M, T)
        bits, sh = cache[key]
        rows.append(dict(call=name, cts_per_sender=M, slots=S, proof_bits=bits, k=sh["k"], rows=sh["m1"] + sh["m2"],
                         digits=sh["n1"] + sh["n2"]))
        posted += n * bits
        cts += n * M
    out["mpc"] = dict(batches=rows, proofs=n * len(rows), distinct_cts=cts, deliveries=cts * (n - 1),
                      posted_bits=posted, delivered_bits=posted * (n - 1),
                      stern_delivered_bits=cts * (n - 1) * STERN_PER_PROOF,
                      old_model_delivered_bits=cts * (n - 1) * MODEL_PER_CT(N, L))
    if fhe_pairs:
        pairs, used = fhe_pairs
        bits, sh = Z.batch_proof_bits("pk", N, primes, t, even(used, pairs), T)
        out["fhe_b"] = dict(proofs=n, cts_per_custodian=pairs, slots_per_custodian=used, proof_bits=bits,
                            k=sh["k"], digits=sh["n1"] + sh["n2"], posted_bits=n * bits,
                            delivered_bits=n * bits * (n - 1),
                            stern_bits=n * pairs * STERN_PER_PROOF)
    return out


def main():
    sc = json.load(open("step_counts.json"))
    res = {}
    for T in (97, 309):
        for d in (64, 1024, 4096):
            mp = sc[str(d)]["fhe_b"]["mask_pairs"]
            r = step(d, 8192, 3, T, (mp["pairs"], mp["used"]))
            res[f"N8192_L3_T{T}_d{d}"] = r
            m = r["mpc"]
            print(f"N=8192 L=3 T={T} d={d}: MPC {m['proofs']} proofs, {m['distinct_cts']} cts, delivered "
                  f"{m['delivered_bits']/1e9:.3f} Gbit (Stern {m['stern_delivered_bits']/1e12:.1f} Tbit); "
                  f"FHE(b) delivered {r['fhe_b']['delivered_bits']/1e9:.3f} Gbit", flush=True)
            r2 = step(d, 16384, 4, T)
            res[f"N16384_L4_T{T}_d{d}"] = r2
            print(f"N=16384 L=4 T={T} d={d}: MPC delivered {r2['mpc']['delivered_bits']/1e9:.3f} Gbit", flush=True)
    json.dump(res, open("zkpopk_counts.json", "w"), indent=1)


if __name__ == "__main__":
    main()
