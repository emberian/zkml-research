"""
Arithmetization cost model for Fiat-Shamir hashing inside an R_q-CCS verifier circuit.
Baseline reproduces eprint 2026/1127 App. C.3 (Frog ring, LatticeFold impl parameters).
Unit throughout: R1CS-over-R_q CONSTRAINTS (one R_q multiplication = one constraint).
"""
import math

# --- 2026/1127 Frog / LatticeFold parameters (paper Sec 5.1 + App C.3) ---
RF, RP, ALPHA, r_f, c_f = 8, 22, 7, 20, 4      # Poseidon (Frog ring params, [Net])
S_ALPHA = 4                                     # x^7 by square-and-multiply: x2,x4,x6,x7
d, lgq  = 16, 64                                # Frog ring dim, q ~ 2^64
tau     = 4                                     # X^16+1 splits into 4 quartics
ell     = d // tau                              # = 4 NTT slots
k, lgm, kappa, lin = 16, 17, 42, 42
l_Zq    = (lgq - 1) // 8                        # = 7 bytes usable per Z_q element
l_small = 1

def sec(msg): print(f"\n{'='*74}\n{msg}\n{'='*74}")

# ---------- BASELINE: Poseidon over Z_q, ring elements decomposed to coefficients ----------
sec("BASELINE  --  2026/1127 App. C.3: Poseidon over Z_q inside an R_q circuit")
perm_cost   = S_ALPHA * (RF * (r_f + c_f) + RP)          # per permutation
absorb_cost = perm_cost + 2 * r_f                        # + 2 constant-checks per Z_q element
print(f"  per permutation           : S_a*(RF*(r+c)+RP) = {S_ALPHA}*({RF}*{r_f+c_f}+{RP}) = {perm_cost}")
print(f"  per absorb of r={r_f} Z_q elts: {perm_cost} + 2*{r_f} = {absorb_cost}")
print(f"  per Z_q element           : {absorb_cost/r_f:.2f}")
base_per_ring = d * absorb_cost / r_f
print(f"  per RING element (d={d})   : {d} * {absorb_cost/r_f:.2f} = {base_per_ring:.1f} constraints")
print(f"  per BIT of transcript     : {base_per_ring/(d*lgq):.4f}")

# transcript size, in Z_q elements (paper's 7-item list, App C.3)
T = {
 "1 evalccs instance":        (lgm + kappa + tau + 5 + lin + 1) * d,
 "2 splitccs instance":       k * (kappa + lin) * d,
 "3 regular challenges (sq)": tau * (2*lgm + 1 + 6*k),
 "4 small challenges (sq)":   math.ceil(2*k*d*l_small / l_Zq),
 "5 decomposition msgs":      k*d*(tau + kappa + 5 + lin),
 "6 sum-check msgs":          5*d*lgm,
 "7 folding msgs":            2*k*d*(tau + 5),
}
tot_zq = sum(T.values()); squeezes = T["3 regular challenges (sq)"] + T["4 small challenges (sq)"]
N_sponge = tot_zq / r_f; N_abs = (tot_zq - squeezes) / r_f
print(f"\n  transcript  = {tot_zq} Z_q elements  ->  N_sponge = {N_sponge:.0f}, N_abs = {N_abs:.0f}")
small_ch = 3 * lgq * math.ceil(2*k*d*l_small/l_Zq); pow_ch = 2*k*(2*tau+5)
base_total = 2*r_f*N_abs + N_sponge*perm_cost + small_ch + pow_ch
print(f"  absorb/squeeze = {2*r_f*N_abs + N_sponge*perm_cost:,.0f}   small-ch = {small_ch:,}   power-ch = {pow_ch:,}")
print(f"  BASELINE FS COST = {base_total:,.0f} constraints  = 2^{math.log2(base_total):.2f}")
print(f"  (paper states the Poseidon count is 'over 2^22' and dominates a total of 2^22-2^23)")

# ---------- CANDIDATE: ring-native sigma-Poseidon ----------
sec("CANDIDATE  --  ring-native sigma-augmented Poseidon (state in R_q elements)\n    !! SUPERSEDED BY density_repricing.py -- the gains below assume ONE sigma\n    !! application per round (sigma-support 3), which is exactly the sparse regime that\n    !! got Chaghri broken in 2^38 (eprint 2022/991). Respecting that lesson the\n    !! defensible headline is ~3.9x-4.8x, NOT 8.9x-12.8x.")
tot_ring = (T["1 evalccs instance"] + T["2 splitccs instance"] + T["5 decomposition msgs"]
            + T["6 sum-check msgs"] + T["7 folding msgs"]) // d \
           + (2*lgm + 1 + 6*k) + 2*k          # challenges are now ONE ring element each
print(f"  transcript  = {tot_ring} RING elements (same data, no coefficient decomposition)")

def candidate(t_ring, r_ring, RPx, sigma_rounds, label):
    sbox  = S_ALPHA * (RF * t_ring + RPx)
    sigma = sigma_rounds * t_ring                 # 1 constraint + 1 witness per elt per sigma layer
    per_perm = sbox + sigma
    per_ring = per_perm / r_ring
    n_perm = tot_ring / r_ring
    total  = n_perm * per_perm + small_ch + pow_ch   # small challenges still need bit decomp
    print(f"  {label}")
    print(f"    t={t_ring} r={r_ring} R_P={RPx}, sigma in {sigma_rounds}/{RF+RPx} rounds"
          f"  ->  {sbox} S-box + {sigma} sigma = {per_perm}/perm")
    print(f"    per RING element = {per_ring:.1f}   per BIT = {per_ring/(d*lgq):.4f}")
    print(f"    TOTAL FS COST = {total:,.0f} = 2^{math.log2(total):.2f}"
          f"   ->  {base_total/total:.1f}x cheaper than baseline")
    return total

candidate(9, 8, 22,  8, "A) sigma only where diffusion needs it (2*log2 d = 8 rounds)")
candidate(9, 8, 22, 30, "B) sigma in EVERY round (conservative wide-trail)")
candidate(9, 8, 42, 50, "C) + R_P raised for the width-t*d=144 F_q state, sigma every round")
candidate(13,12, 42, 54, "D) wider rate r=12 (capacity c=1 ring elt = 1024 bits)")

# ---------- the "obvious" alternative: SWIFFT / Ajtai, i.e. an MSIS hash ----------
sec("COMPARISON  --  SWIFFT / Ajtai (MSIS) hash, arithmetized over R_q\n    !! SUPERSEDED BY msis_correction.py -- the 3-constraints-per-bit figure below is\n    !! the price of a BINARY predicate (App C.3). App C.4 shows the paper delegates the\n    !! SMALL-NORM predicate to LatticeFold's own infinity-norm check, making MSIS/SWIFFT\n    !! ~FREE in constraints. The corrected conclusion is the OPPOSITE of the one below:\n    !! SWIFFT is CHEAP; it is simply not a random oracle.")
print("  y = sum_i a_i * x_i  over R_q, x_i with BINARY coefficients.")
print("  The R_q-linear part is FREE (it folds into the CCS matrices).")
print("  The cost is ENTIRELY the input encoding: every input BIT must appear as an")
print("  R_q witness element proved (i) boolean and (ii) constant -- the paper's own")
print("  accounting is 3 constraints per bit (1 for x(x-1)=0, 2 automorphism checks).")
swifft_per_bit = 3.0
print(f"    SWIFFT per BIT absorbed  = {swifft_per_bit:.4f} constraints")
print(f"    baseline Poseidon/bit    = {base_per_ring/(d*lgq):.4f}")
print(f"    candidate B per bit      = {(S_ALPHA*(RF*9+22)+30*9)/8/(d*lgq):.4f}")
print(f"  => SWIFFT is {swifft_per_bit/(base_per_ring/(d*lgq)):.1f}x WORSE than the field baseline")
print(f"     and {swifft_per_bit/((S_ALPHA*(RF*9+22)+30*9)/8/(d*lgq)):.0f}x worse than the candidate,")
print("     DESPITE being linear. Linearity is not what makes a hash cheap over R_q;")
print("     the small-norm/binary INPUT PREDICATE is the whole cost, and it is unavoidable")
print("     (drop it and the map is R_q-linear, hence invertible by linear algebra).")

# ---------- diffusion cost law ----------
sec("DIFFUSION COST LAW  --  constraints per ring element to reach full F_q-diffusion")
print("  A linear layer with sigma-support s costs (s-1) constraints/elt/round and")
print("  multiplies the reachable slot set by <= s per round: log_s(d) rounds to full.")
print(f"  {'d':>6} | {'s=2':>7} {'s=4':>7} {'s=8':>7} {'one-shot s=d':>13} | {'optimal':>8}")
for dd in [16, 32, 64, 128, 256, 1024]:
    row = []
    for s in [2, 4, 8]:
        row.append((s-1) * math.ceil(math.log(dd, s)))
    best = min(((s-1)*math.ceil(math.log(dd, s)), s) for s in range(2, dd+1))
    print(f"  {dd:>6} | {row[0]:>7} {row[1]:>7} {row[2]:>7} {dd-1:>13} | {best[0]:>4} (s={best[1]})")
print("  => full F_q-diffusion over R_q costs THETA(log d) constraints per ring element,")
print("     not THETA(d).  This is the quantitative content of the construction.")
