"""Workload 2 schedule model: the Tower256 leaf prover end to end on one GPU, per proof, from
measured rates (TOWER256-SCHEDULE.md). Stage times are max(arith, bytes / copy rate) per kernel
class, summed (one stream), plus launches and host work amortized over the batch.

    python3 -I tower256_schedule_model.py
"""
LB = 2
Q = 148

# Measured (sources in TOWER256-SCHEDULE.md section 1). Ranges are session-to-session on T4.
T4 = dict(name="T4", mul=(2.9e8, 5.4e8), keccak=(4.35e8, 6.9e8), copy=234e9, launch_us=12.0,
          host_hash_us_per_kb=6.0, host_assembly_ms=1.5, pcie=6e9)
# H100: copy measured (paid-h100-mma-03); mul and Keccak scaled from T4 by INT32 SIMT throughput
# (132 SM x 1.98 GHz against 40 SM x 1.59 GHz, same 64 INT32 lanes per SM): 4.11x [A].
SC = 132 * 1.98 / (40 * 1.59)
H100 = dict(name="H100", mul=(2.9e8 * SC, 5.4e8 * SC), keccak=(4.35e8 * SC, 6.9e8 * SC), copy=3.03e12,
            launch_us=8.0, host_hash_us_per_kb=3.0, host_assembly_ms=0.8, pcie=20e9)


def counts(ell):
    n, L, m = 1 << ell, 1 << (ell - LB), ell - LB - 2
    D = ell - LB                                   # encode depths (constant polynomial at depth ell - lb)
    c = {}
    # encode, per depth: scale L mults, Taylor (log2 bsz - 1) XOR passes, deinterleave, butterfly n/2 mults
    c["encode_mults"] = D * L + D * n // 2 + 2 * L
    taylor_passes = sum(max(0, (ell - LB - d) - 1) for d in range(D))
    c["encode_bytes"] = 96 * D * L + 40 * L * taylor_passes + 64 * D * L + 80 * n * D + 32 * n
    c["encode_mul_bytes"] = 96 * D * L + 80 * n * D   # bytes of the multiply kernels (overlap their arith)
    c["fold_mults"] = sum(1 << (ell - j - 1) for j in range(m))
    c["fold_bytes"] = 128 * c["fold_mults"]
    sizes = [1 << (ell - j) for j in range(m)] + [1 << (ell - m)]
    c["keccak"] = sum(2 * s - 1 for s in sizes)
    c["merkle_bytes"] = sum(64 * s + 96 * s for s in sizes)
    c["launches"] = sum(12 + max(0, (ell - LB - d) - 1) + 1 for d in range(D)) + sum(6 + (ell - j) for j in range(m)) + 20
    c["host_hash_kb"] = m * 5.0 + 6.0               # challenges (head + roots, ~5 KB each) + the prefix copy
    c["upload_bytes"] = 32 * L
    return c


def predict(hw, ell, batch, fast):
    c = counts(ell)
    mul = hw["mul"][1 if fast else 0]
    kec = hw["keccak"][1 if fast else 0]
    bw = hw["copy"]
    enc_arith = c["encode_mults"] / mul
    enc_mem_only = (c["encode_bytes"] - c["encode_mul_bytes"]) / bw
    encode = max(enc_arith, c["encode_mul_bytes"] / bw) + enc_mem_only
    merkle = max(c["keccak"] / kec, c["merkle_bytes"] / bw)
    folds = max(c["fold_mults"] / mul, c["fold_bytes"] / bw)
    launches = c["launches"] * hw["launch_us"] * 1e-6 / batch
    host = c["host_hash_kb"] * hw["host_hash_us_per_kb"] * 1e-6 + hw["host_assembly_ms"] * 1e-3
    upload = c["upload_bytes"] / hw["pcie"]
    device = encode + merkle + folds
    serial = device + launches + host + upload
    return dict(encode=encode, merkle=merkle, folds=folds, launches=launches, host=host, upload=upload,
                device=device, serial=serial, overlap_bound=device + upload)


def at_rates(ell, batch, mul, keccak, hw=T4):
    """The model at one multiply and one Keccak rate (e.g. a run's own session rates)."""
    h = dict(hw, mul=(mul, mul), keccak=(keccak, keccak))
    return predict(h, ell, batch, True)


if __name__ == "__main__":
    import sys
    if len(sys.argv) == 3:   # session rates: mul keccak
        mul, kec = float(sys.argv[1]), float(sys.argv[2])
        for ell, B in ((18, 64), (20, 16), (22, 4)):
            p = at_rates(ell, B, mul, kec)
            print("T4 at mul %.2e, Keccak %.2e: ell %d device bound %.1f ms (encode %.1f, Merkle %.1f, folds %.1f, upload %.1f)"
                  % (mul, kec, ell, 1e3 * p["overlap_bound"], 1e3 * p["encode"], 1e3 * p["merkle"], 1e3 * p["folds"], 1e3 * p["upload"]))
        raise SystemExit(0)
    for hw, plan in ((T4, ((18, 64), (20, 16), (22, 4))), (H100, ((18, 256), (20, 64), (22, 16)))):
        for ell, B in plan:
            lo, hi = predict(hw, ell, B, True), predict(hw, ell, B, False)
            f = lambda k: "%.1f-%.1f" % (1e3 * lo[k], 1e3 * hi[k])
            print("%-5s ell %d B %3d | encode %s | merkle %s | folds %s | launch %s | host %s | upload %s | "
                  "per proof (one stream) %s ms | device-only bound %s ms"
                  % (hw["name"], ell, B, f("encode"), f("merkle"), f("folds"), f("launches"), f("host"),
                     f("upload"), f("serial"), f("overlap_bound")))
