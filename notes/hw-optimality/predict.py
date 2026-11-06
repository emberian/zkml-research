#!/usr/bin/env python3
"""Predicted optimum per workload x target, from calibrated bounds (stdlib only; `python3 -I predict.py`).

Every number is max over units of (work / sustained rate), i.e. the time a perfectly pipelined kernel of the stated
ALGORITHM reaches. Inputs are tagged: [READ] source, [MEASURED] our runs, [SASS] counted by sassbound on SASS that
nvcc 12.9 emits for that target, [A] assumed, [ROT] taken from ROTATION.md / `mma_counts.py --rotation`.
"""
import math

# ---------------------------------------------------------------- targets
# simt_clk: the clock integer SIMT sustains. T4: 1.19 GHz from the measured LOP3 rate (3.0-3.1e12 / (40*64)); the
# 70 W cap and short timing windows put real runs anywhere in 0.58-1.3 GHz (PREDICTORS.md section 2).
# H100/H200 integer SIMT at 1.98 GHz: hashcat Keccak/SHA2 SXM vs PCIe scale with SMs x boost clock [READ].
# bw: (assumed sustained, pessimistic). T4 both MEASURED copy. B200 pessimistic = STREAM Triad 4.14 TB/s [READ
# arXiv 2512.02189]; others 0.75 of datasheet as F3 assumed and T4 measured.
T = {
    "T4":   dict(sms=40,  clk=1.19e9, bw=(0.242e12, 0.242e12), arch="sm_75"),
    "A100": dict(sms=108, clk=1.41e9, bw=(1.53e12, 1.53e12),   arch="sm_80"),
    "H100": dict(sms=132, clk=1.98e9, bw=(2.9e12, 2.5e12),     arch="sm_90a"),   # SXM; 0.87 and 0.75 of 3.35
    "H200": dict(sms=132, clk=1.98e9, bw=(4.1e12, 3.6e12),     arch="sm_90a"),
    "B200": dict(sms=148, clk=1.9e9,  bw=(6.0e12, 4.14e12),    arch="sm_100a"),
    "B300": dict(sms=160, clk=1.9e9,  bw=(6.0e12, 4.14e12),    arch="sm_103a"),
}
LANES = 64  # LOP3 / SHF / IMAD lanes per SM per clock on every target here [READ Table 5]

# ---------------------------------------------------------------- SASS-counted unit costs (SM-clocks per warp-op)
# Keccak-f[1600], one round = 136 LOP3 + 58 SHF (sm_75..sm_90a: 97.5 clk/warp-round; sm_100a/103a 96) [SASS]
KECCAK_ROUND_CLK = {"sm_75": 97.5, "sm_80": 97.5, "sm_90a": 97.5, "sm_100a": 96.0, "sm_103a": 96.0}
# NTT butterfly, 61-bit prime (SM-clk per warp-butterfly, FMA-pipe bound) [SASS, sassbound on bfly.cu / ntt kernel]
BFLY = {
    "current radix-8 Shoup (accel_rns_ntt.cu fwdBr<0,3>)": {"sm_75": 191.5 / 12, "sm_80": 191.5 / 12,
                                                            "sm_90a": 188.5 / 12, "sm_100a": 180.5 / 12,
                                                            "sm_103a": 180.5 / 12},
    "Harvey lazy 61-bit": {"sm_75": 47.5 / 4, "sm_80": 47.5 / 4, "sm_90a": 47.5 / 4, "sm_100a": 90.5 / 8,
                           "sm_103a": 90.5 / 8},
    # Harvey's [0, 4p) range in one u32 needs p < 2^30 (Codex): 7 primes of ~30 bits replace 3 of 61 (183 bits),
    # i.e. 7/3 small butterflies per 61-bit butterfly; costs from b32_shoup (Harvey form) in bfly.cu.
    "30-bit primes (Harvey), 7/3 per 61 bits": {"sm_75": 7 / 3 * 16.0 / 4, "sm_80": 7 / 3 * 16.0 / 4,
                                                "sm_90a": 7 / 3 * 13.75 / 4, "sm_100a": 7 / 3 * 24.25 / 8,
                                                "sm_103a": 7 / 3 * 24.25 / 8},
}


def simt_s(t, warp_ops_clk_total):
    """warp_ops_clk_total: SM-clocks summed over all warps of the job."""
    x = T[t]
    return warp_ops_clk_total / (x["sms"] * x["clk"])


def keccak_rate(t):
    return 32.0 / (24 * KECCAK_ROUND_CLK[T[t]["arch"]]) * T[t]["sms"] * T[t]["clk"]


def line(*cols, w=(34, 11, 11, 11, 11, 11, 11)):
    print("".join(str(c).rjust(ww) if i else str(c).ljust(ww) for i, (c, ww) in enumerate(zip(cols, w))))


def main():
    tg = list(T)
    print("Predicted optimum per target (bound = max over units of work / sustained rate). Times in ms unless noted.")
    print("SIMT clock: T4 1.19 GHz (measured LOP3), others [A]. HBM: (assumed / pessimistic).\n")

    # ---------------------------------------------------------- 1. Keccak and the Tower256 Merkle layer
    print("1. Keccak-f[1600] (SIMT, LOP3/SHF bound; no tensor form)")
    line("", *tg)
    line("Keccak-f/s, bound", *[f"{keccak_rate(t):.2e}" for t in tg])
    hashcat = {"T4": 7.09e8, "A100": 2.138e9, "H100": 2.7946e9 * 1.357}
    line("hashcat Keccak-256 [READ]", *[f"{hashcat[t]:.2e}" if t in hashcat else "-" for t in tg])
    for ell, kf in ((14, 65_493), (20, 4_190_000), (22, 4 * 2 ** 22)):
        line(f"Merkle per proof, ell {ell} (ms)", *[f"{kf / keccak_rate(t) * 1e3:.3f}" for t in tg])
    print("   hashcat 17800 runs 23 full rounds + a pruned final round on a state with constant lanes: ~4-5% less work.")
    print("   ROTATION's xor3 theta (Codex) gives <= 180 ops/round = 4,320 per Keccak-f: a 7% lower floor than this SASS.")
    print("   T4 measured Merkle ell 20: 14.1 ms (dryrun-04, device); T4 at 1.26 GHz bound: "
          f"{4.19e6 / keccak_rate('T4') * 1.19 / 1.26 * 1e3:.1f} ms\n")

    # ---------------------------------------------------------- 2. RNS NTT (BFV), N = 8192, L = 3
    N, L = 8192, 3
    bfl = N // 2 * int(math.log2(N))
    print(f"2. RNS NTT, N = {N}, 61-bit primes (us per NTT, batched; FMA pipe vs one-pass HBM 16N bytes)")
    line("", *tg)
    for name, c in BFLY.items():
        line(name[:34], *[f"{simt_s(t, bfl / 32 * c[T[t]['arch']]) * 1e6:.3f}" for t in tg])
    line("HBM one pass (assumed BW)", *[f"{16 * N / T[t]['bw'][0] * 1e6:.3f}" for t in tg])
    print("   T4 measured 1.77 us (sustained), 1.35 us (burst, two-pass Montgomery radix-2)\n")

    # per return (he_outer, K = 1): 5L NTTs + compulsory bytes ~ (C^ in + ct out + ct re-read + plaintext out)
    ret_bytes = (6 * L * N + N) * 8
    print(f"   per he_outer return (5L = {5 * L} NTTs; HBM ledger of one fused schedule {ret_bytes / 1e6:.2f} MB, not a lower")
    print("   bound; NTT arithmetic only: pointwise, finalize, HPS and randomness are not priced -> partial-work roofline), us:")
    line("   current butterfly", *[f"{max(5 * L * simt_s(t, bfl / 32 * BFLY[list(BFLY)[0]][T[t]['arch']]), ret_bytes / T[t]['bw'][0]) * 1e6:.2f}" for t in tg])
    line("   Harvey", *[f"{max(5 * L * simt_s(t, bfl / 32 * BFLY['Harvey lazy 61-bit'][T[t]['arch']]), ret_bytes / T[t]['bw'][0]) * 1e6:.2f}" for t in tg])
    line("   30-bit RNS (7 primes, bytes x7/6)", *[f"{max(5 * L * simt_s(t, bfl / 32 * BFLY['30-bit primes (Harvey), 7/3 per 61 bits'][T[t]['arch']]), ret_bytes * 7 / 6 / T[t]['bw'][0]) * 1e6:.2f}" for t in tg])
    print("   T4 measured 49.5 us per return; BFV.md model H100 4.3-7.0, B200 3.1-5.5")
    steps = 49_152
    line("   d=4096 step, current bfly (s)", *[f"{steps * max(5 * L * simt_s(t, bfl / 32 * BFLY[list(BFLY)[0]][T[t]['arch']]), ret_bytes / T[t]['bw'][0]):.3f}" for t in tg])
    print("   (outer returns only; T4 measured 2.45 s outer, 2.77 s step)\n")

    # ---------------------------------------------------------- 1b. Tower256 encode, ell 20 (multiply-bound)
    print("1b. Tower256 encode + folds, ell 20 [ROT tensor fixed-r route; MEASURED T4 tables 12,000-17,400 op-eq]")
    rot = {"T4": 13.7, "H100": 2.5, "B300": 0.95}
    line("", *tg)
    line("tensor fixed-r route [ROT] (ms)", *[f"{rot[t]:.2f}" if t in rot else "-" for t in tg])
    mults = 14.2e6 + 2.4e6  # encode multiplies [MEASURED counts] + folds (~2^ell * 2 rounds-sum) [A]
    line("table multiply at 12,000 op (ms)", *[f"{mults * 12000 / (T[t]['sms'] * LANES * T[t]['clk']) * 1e3:.2f}" for t in tg])
    print("   T4 measured encode 86.8 + folds 6.9 ms; bit-sliced measured 52,700 op/mult (TOWER256.md 8): loses\n")

    # ---------------------------------------------------------- 3. BabyBear^8 sumcheck (HBM-bound everywhere)
    gb = 10.7e9  # [ROT] bytes, degree-2 sumcheck, 2^25, all rounds (ROTATION 2(a) floor x 0.75 BW)
    print("3. BabyBear^8 degree-2 sumcheck, 2^25, HBM-bound on every target [ROT bytes 10.7 GB] (ms)")
    line("", *tg)
    line("assumed BW", *[f"{gb / T[t]['bw'][0] * 1e3:.2f}" for t in tg])
    line("pessimistic BW", *[f"{gb / T[t]['bw'][1] * 1e3:.2f}" for t in tg])
    # L2 residency: rounds whose table fits in L2 move at L2 bandwidth; first-round table 1.07 GB
    print("   rounds after the table fits L2 (H100 50 MB: last ~20 of 25 rounds) are L2-bound; they carry ~5% of bytes\n")

    # ---------------------------------------------------------- 4. MXFP4 gpt-oss-20b exact decode, per token
    act = 3.6e9      # active parameters per token [A: model card]; PROXY: treats all as MXFP4 (only MoE weights are)
    wbytes = act * 4.25 / 8   # MXFP4 packed with E8M0 per 32
    print("4. gpt-oss-20b exact recompute, decode (batch 1), per token: weight bytes bound (ms)")
    line("", *tg)
    line("packed MXFP4 read once", *[f"{wbytes / T[t]['bw'][0] * 1e3:.3f}" for t in tg])
    line("int8-unpacked + scales (33/32)", *[f"{act * 33 / 32 / T[t]['bw'][0] * 1e3:.3f}" for t in tg])
    print("   batch >= ~100 tokens per expert turns it compute-bound: ROTATION 2(d) (SIMT scale handling)\n")


if __name__ == "__main__":
    main()
