"""Tables, input and accel_rns_ref expected output for one batched N-point forward NTT (Shoup, MODE 0),
in the exact layout accel_rns_ntt.cu / accel_bench_cuda.Ctx uses. Lane hw-opt-sim, 2026-11-06.
    python3 gen_ntt.py REF_DIR OUT_DIR N L ROWS
REF_DIR holds accel_rns_ref.py and bfv_ref.py (zkml-research/research/dark_learning_2026_11_06).
Writes tw.bin twq.bin (L x N u64), mc.bin (L x 8 u64, struct ModC), in.bin, expect.bin (ROWS x N u64)."""
import sys, os
import numpy as np
ref_dir, out, N, L, rows = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
sys.path.insert(0, ref_dir)
import accel_rns_ref as R
Qp, _t = R.primes(N, L)
T = [R.Tables(q, N) for q in Qp]
Rm = 1 << 64
sq = lambda w, p: (w << 64) // p
tw, twq, mc = [], [], []
for q, Tq in zip(Qp, T):
    pn = (-pow(q, -1, Rm)) % Rm
    last = Tq.ipsi_brv[1] * Tq.ninv % q
    tw.append(Tq.psi_brv); twq.append([sq(w, q) for w in Tq.psi_brv])
    mc.append([q, pn, Tq.ninv, sq(Tq.ninv, q), last, sq(last, q), Rm * Rm % q, Rm % q])
os.makedirs(out, exist_ok=True)
u = lambda x: np.array(x, dtype=np.uint64)
u(tw).tofile(f"{out}/tw.bin"); u(twq).tofile(f"{out}/twq.bin"); u(mc).tofile(f"{out}/mc.bin")
rng = np.random.default_rng(11)
x = np.stack([rng.integers(0, Qp[r % L], N, dtype=np.uint64) for r in range(rows)])
x.tofile(f"{out}/in.bin")
exp = np.stack([np.array([int(v) for v in R.fwd([int(v) for v in x[r]], T[r % L])], dtype=np.uint64) for r in range(rows)])
exp.tofile(f"{out}/expect.bin")
print(f"N={N} L={L} rows={rows} primes={Qp}")
