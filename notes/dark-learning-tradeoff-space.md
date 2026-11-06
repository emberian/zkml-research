# Dark learning: the construction space in counts, and its Pareto set

2026-11-05. Script: `notes/dark-learning-scripts/tradeoff_space.py` (pure Python, no deps, < 1 s).
Saved output: `notes/dark-learning-scripts/tradeoff_space.out.txt`. Companion of
`docs/DARK-LEARNING-PROGRAM.md` §3. **No clock appears anywhere**; every number is a count from stated
formulas, and every constant that is not derived is tagged [MODEL] or [CLAIM] in the script header.

## 1. The axes

| axis | values | why it is an axis |
|---|---|---|
| modulus | RNS3-109@4096 (deployed), p61@4096, gold64@4096, RNS-202@8192 | FRONTIER-QUEUE G1/G2 |
| proof field | BabyBear-ext (bridged residues) / native (single prime only) | G1's actual prize |
| custody | FHE + MPC boundary / FHE + bootstrapping / MPC only / TEE plaintext | P1–P3 of the program |
| base | dark W₀ / public trunk | the welfare choice ember owns |
| update | backprop-full / low-rank r / append-rank1 / ZO-seeded | C1, C3, C4, C14 |
| rank | 1; 8, 16, 64 (low-rank); 0 or 16 (ZO full vs adapter) | `low-rank-updates.md` break-even |
| audit rate p | 1, 0.1, 0.01, 0.001 | `AuditSampling.lean` |

Fixed: d = 4096, L = 32 one-matrix layers, batch 1, NPARTY = 3, 10^6 steps (all overridable: `--d`,
`--L`).

## 2. Objectives (minimized) and gates (hard)

Objectives: amortized **proof felts** per step (p × step proof + unconditional envelope), **host work**
(local modular mults; ct×ct = 10 NTT-equivalents [MODEL]), **online elements** among the quorum,
**read leakage** log2 over the run, **expected undetected injected displacement** in units of the
envelope cap B (= 1/q).

Gates: **PQ** (log Q ≤ quantum-128 ceiling for N [CLAIM, HE standard from memory]); **depth** between
crossings ≥ what the update needs; **wrap** (plaintext does not wrap over the merge period: F1);
**read** (smudging union bound ≤ 2^-40 over the run: F5).

## 3. Controls

The script asserts two published counts before printing anything: 49,152 committed felts per deployed
ciphertext in the bridged row-interleaved layout (`cross-limb-binding.md` §3 table) and the
3·4096·109 = 1,339,392 booleanity figure (VERDICTS §7.5, 09-05). It prints the derived k_wrap (longest
wrap-free signed dot product, 10,532 at 4×4-bit against `bfv_coeff_matmul.rs`'s 504 at 4×8-bit) and the
integer-state wrap period (10,532 steps).

## 4. v1 was wrong in ways that mattered; v2 is the version to read

v1 (commit `9443850d`) was attacked by Codex round 2 (`notes/dark-learning-codex-synthesis.md` §Round 2).
Its defects, all repaired in v2: a double-counted dense product in full backprop; "public full training"
kept public after the first secret update; d²/N packing that ignored the t-wrap of split dot products and
the ceil(N/k) tiling; fractional crossings (2Ld/N instead of 2L·⌈d/N⌉); no split-sign doubling of ct×pt
(`bfv_coeff_matmul.rs:17-36` evaluates W⁺v and W⁻v); low-rank A(Bx) at depth 1 instead of 2; append-only
backward not traversing the factor history; dense updates granted free weight refreshes; the envelope
charged as committed felts instead of as an unconditional proof; a log-Q step function for smudging
instead of a ledger; 1/q instead of 2B/q; and a "welfare price" that compared dark FHE against public MPC.
**v1's headline numbers (×125 welfare price, the 87× audit knee, "every Pareto point is public-trunk
low-rank") are withdrawn.**

## 5. Results, v2, at d = 4096, L = 32 [MEASURED, script]

- **784 constructions; 112 pass all four gates.** Failures: depth 528, read 336, PQ 112, wrap 0 (with
  4-bit activations the wrap is no longer binding at d = 4096; at 8-bit activations it would be, k = 504).
  Single-prime rows (p61, gold64) now fail BOTH depth (A(Bx) is depth 2) and the read budget (2^+7.6 per
  event: the smudge does not fit a 61-bit modulus). Every bootstrapping row fails depth.
- **The deployed reference** (RNS3-109@4096, fully dark, backprop, p = 0.01): 1.45×10^9 proof felts per
  step, fails PQ (quantum-128 table) and read (2^-14.2 over the run).
- **Separate frontiers per opacity regime.** Fully dark: 11 Pareto rows — MPC-only (backprop at p = 0.001,
  low-rank r = 8 at every rate) and FHE+MPC at RNS-202@8192 (backprop, append-rank1, low-rank). Public
  trunk: 10 rows, same two custodies, low-rank and append-rank1.
- **The opacity price within a custody** (cheapest fully-dark vs cheapest public-trunk, p = 0.01): FHE+MPC
  ×2.0 proof, ×1.2 host, ×1.0 online; MPC ×2.9 proof, ×39.9 host, ×65 online. Full opacity is cheap on the
  FHE route and expensive in bandwidth on the MPC route.
- **The envelope is the new floor.** With the unconditional envelope priced as proof work on ciphertexts,
  the audit knee flattens: RNS-202, public, r = 16 goes 5.48×10^10 → 1.82×10^9 → 1.34×10^9 proof felts from
  p = 1 → 0.01 → 0.001, and the envelope is 70.6% of the cost at p = 0.01 and 96% at p = 0.001. **Below
  p ≈ 0.01 sampling buys almost nothing; the cheap mandatory checks are no longer cheap once they must be
  proved on ciphertexts.** This is the dark-learning version of "the commitment is the step"
  (VERDICTS §5b): once the sampled proof is cheap, the unconditional envelope is the step.
- E[undetected injected displacement] = 2B/q: 2.1B at p = 1, 210B at p = 0.01.

## 6. Sensitivity

- `--d 1024 --L 12`: 14 dark and 12 public Pareto rows; MPC fully-dark backprop leads proof felts at
  p ≤ 0.01; MPC public ZO-on-adapter enters at p = 0.001 (its envelope is one scalar).
- What would flip the FHE-vs-MPC fork: C_PRE (host cost per Beaver triple, [MODEL] 100), KAPPA, the ct×ct
  certificate size, and whether the envelope can be proved by the quorum on shares (F13 route b) instead of
  by the host on ciphertexts. The first hbox experiment measures the certificate and crossing counts.

## 7. What the model leaves out (so it is not mistaken for a price)

- Rotations, key-switches, extraction and repacking schedules (Codex round 2 b names them; only the tile
  count and the partial-sum crossings are charged).
- MPC round latency, topology, preprocessing storage, distributed proving for public verifiability.
- Accuracy: every integer recipe (4-bit factors, ZO) is assumed to train equally well. It may not; ZO's 12×
  is not an equal-utility comparison.
- E = 2^32 in the smudging window is a fold envelope, not established for training ct×ct outputs.
- Quantum-128 table passes are conditional (ternary-secret table; deployed secret is CBD(20)).
- ε_chk is a constant 2^-100; no soundness number from this script may be quoted.
