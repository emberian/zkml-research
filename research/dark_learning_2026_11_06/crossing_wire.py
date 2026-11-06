"""Experiment 1b: wire elements of ONE fused activation/derivative crossing at N = 8192, RNS-202.

2026-11-06. The crossing takes a ciphertext of d = 4096 pre-activations z (one N = 8192 BFV ciphertext,
coefficient-packed), and returns ONE fresh ciphertext holding sigma(z) and sigma'(z) (4096 + 4096 = N
coefficients: the fused output, F2's derivative column keyed on the input code).

  E2S   encryption-to-shares (Mouchet-Troncoso-Pastoriza-Bossuat-Hubaux, multiparty HE from RLWE):
        parties 2..n send h_i = s_i c1 - Delta M_i + e_i to party 1; party 1 decodes M_1 = m - sum M_i.
  F     the nonlinearity on additive shares mod t: requantize (probabilistic truncation, one masked
        opening) then a table lookup at a masked index (one masked opening), two outputs per input.
  S2E   shares-to-encryption with a common reference polynomial a: each party sends
        h_i = -s_i a + Delta M'_i + e_i; ct = (sum h_i, a).

E2S and S2E are EXECUTED here (real polynomials, checked by decryption) and their messages are counted
element by element. F's online opening messages are counted by formula, not executed on the shares;
a centralized toy table supplies the outputs for the S2E arithmetic check; its PREPROCESSING is counted by formula for two published lookup styles, because it is where the
cost of an exact lookup in MPC actually lives. Counts only; no clock. Smudging noise e_i is drawn at a
small toy width here: its size changes no element count.
"""
import math
import random

import bfv_ref as bfv

N, NPARTY, D = 8192, 3, 4096
T = 1032193
TABLE_BITS = 16

class Bus:
    def __init__(self):
        self.log = {}

    def send(self, phase, frm, to, elems):
        self.log.setdefault(phase, 0)
        self.log[phase] += elems

def run(seed=11):
    Qp = bfv.ntt_primes(34, 6, 2 * N)
    Q = math.prod(Qp)
    L = len(Qp)
    rng = random.Random(seed)
    sch = bfv.BFV(N, Q, T, seed=seed)
    shares = [sch.ternary() for _ in range(NPARTY)]
    sch.s = [sum(c) for c in zip(*shares)]
    z = [rng.randrange(-(1 << 15), 1 << 15) % T for _ in range(D)] + [0] * (N - D)
    ct = sch.encrypt(z)
    bus = Bus()
    delta = Q // T
    # ---- E2S
    hs, Ms = [], []
    for i in range(1, NPARTY):
        Mi = [rng.randrange(T) for _ in range(N)]
        si_c1, _ = bfv.negacyclic_mul(shares[i], bfv.poly_centered(ct[1], Q))
        e = sch.small_error(1 << 10)
        h = [(x - delta * m + ee) % Q for x, m, ee in zip(si_c1, Mi, e)]
        bus.send("E2S", i, 0, N * L)                 # one polynomial in RNS form: N coefficients x L residues
        hs.append(h)
        Ms.append(Mi)
    s0_c1, _ = bfv.negacyclic_mul(shares[0], bfv.poly_centered(ct[1], Q))
    acc = [(c0 + x + sum(h[j] for h in hs)) % Q for j, (c0, x) in enumerate(zip(ct[0], s0_c1))]
    M0 = [((T * bfv.centered(x, Q) * 2 + Q) // (2 * Q)) % T for x in acc]
    Ms = [M0] + Ms
    assert all(sum(M[j] for M in Ms) % T == z[j] for j in range(N)), "E2S shares do not reconstruct z"
    # ---- F: formula-only opening count; centralized toy outputs (not an MPC lookup)
    table_mask = (1 << TABLE_BITS) - 1
    opened = 0
    for j in range(D):
        # opening 1: masked value for probabilistic truncation; opening 2: masked table index
        for _ in range(2):
            for i in range(NPARTY):
                bus.send("F-online", i, None, NPARTY - 1)   # each party sends its masked share to every other
            opened += 1
    out_vals = []
    for j in range(D):
        x = bfv.centered(z[j], T)
        idx = (x >> 4) & table_mask                    # requantize 20 -> 16 bits
        out_vals.append((idx * 3) % T)                 # sigma(x) stand-in: the table content is irrelevant here
    for j in range(D):
        x = bfv.centered(z[j], T)
        idx = (x >> 4) & table_mask
        out_vals.append((idx + 1) % T)                 # sigma'(x) column of the same row
    # reshare the outputs additively
    Mo = [[rng.randrange(T) for _ in range(N)] for _ in range(NPARTY - 1)]
    Mo = [[(out_vals[j] - sum(M[j] for M in Mo)) % T for j in range(N)]] + Mo
    # ---- S2E
    a = sch.uniform()                                  # common reference polynomial (CRS seed: 0 wire)
    total = [0] * N
    for i in range(NPARTY):
        si_a, _ = bfv.negacyclic_mul(shares[i], bfv.poly_centered(a, Q))
        e = sch.small_error(1 << 10)
        h = [(-x + delta * m + ee) % Q for x, m, ee in zip(si_a, Mo[i], e)]
        bus.send("S2E", i, "host", N * L)
        total = [(u + v) % Q for u, v in zip(total, h)]
    fresh = (total, a)
    assert sch.decrypt(fresh) == out_vals, "S2E ciphertext does not decrypt to the fused outputs"
    # ---- F preprocessing, by formula, per input value
    T_entries = 1 << TABLE_BITS
    pre_rotated = D * NPARTY * 2 * T_entries         # shares of the table rotated by the mask, two columns
    dpf_bits = (128 + 2) * TABLE_BITS                # 2-party DPF key, Boyle-Gilboa-Ishai style, per lookup
    pre_dpf = D * 2 * math.ceil(dpf_bits / 20) * 2   # two outputs, two keys, in 20-bit elements
    return dict(N=N, L=L, logQ=round(math.log2(Q), 2), parties=NPARTY, d=D, wire=bus.log,
                online_total=sum(bus.log.values()),
                payload_bits=(bus.log["E2S"] + bus.log["S2E"]) * max(q.bit_length() for q in Qp)
                             + bus.log["F-online"] * T.bit_length(),
                ciphertext_components=2, function_openings_executed=False,
                preprocessing_rotated_table=pre_rotated, preprocessing_dpf_2party=pre_dpf,
                openings=opened)

if __name__ == "__main__":
    r = run()
    print(r)
