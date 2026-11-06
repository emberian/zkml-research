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
3·4096·109 = 1,339,392 booleanity figure (VERDICTS §7.5, 09-05). If either drifts, it refuses to print.

## 4. Results at d = 4096, L = 32 [MEASURED, script]

- **784 constructions; 104 pass all four gates.** Failures: read 336, depth 368, PQ 112, wrap 96. Every
  bootstrapping row fails depth (RNS-202 gives ~4 levels [MODEL]; one bootstrap ~15 [MODEL]); every
  p61/gold64/RNS3 FHE+MPC row fails the read budget (2^-6.1 over the run at 2^-32 per session).
- **The deployed reference** (RNS3-109@4096, fully dark, backprop, p = 0.01): 1.87×10^9 proof felts per
  step, fails PQ and read.
- **G1 block** (Hole B certificate per ct×ct): 9 integer limbs / 307,200 felts at the deployed modulus over
  BabyBear; 3 limbs / 159,744 at native p61; 15 limbs / 1,056,768 at RNS-202@8192. The certificate is
  3–20× the ciphertext's own felts at every row: **on the fully-dark route Hole B is the bill.**
- **Pareto set (tier C, all gates): 8 rows, every one public-trunk low-rank r = 8**, MPC-only custody at
  every audit rate and FHE+MPC at RNS-202@8192 at every audit rate. MPC wins proof felts and host work;
  FHE wins online traffic (6.45×10^7 vs 1.01×10^8 elements per step).
- **Welfare price** (cheapest fully-dark gated point vs cheapest public-trunk point, p = 0.01): FHE route
  ×125 proof felts, ×0.6 online; MPC route ×3.4 proof felts, ×65 online.
- **Per family at p = 0.01**: low-rank is undominated; backprop-full dominated by 3 rows; append-rank1 by
  6 (it saves depth, not work, once the merge is charged); ZO by 5 (the 12× step multiplier [CLAIM]).
- **Audit knee** (p61 native, public, r = 16): p 1 → 0.01 cuts amortized felts 87× (2.68×10^9 →
  3.09×10^7) and raises E[undetected injected displacement] from 1.05B to 105B.

## 5. Sensitivity (one run each, same script)

- `--d 1024 --L 12`: 9 Pareto rows; **MPC public backprop-full enters the frontier at p = 0.001** (the
  d²/N ct×ct terms shrink faster than the low-rank adapter's crossings). The low-rank dominance is a
  large-d fact, not a law.
- What would flip the FHE-vs-MPC fork: C_PRE (host cost per Beaver triple, [MODEL] 100) and the ct×ct
  certificate size. Both are what the first hbox experiment measures (program §6.3).

## 6. What the model leaves out (said so it is not mistaken for a price)

- Ciphertext packing beyond "N inner-product terms per ct×ct"; rotations/key-switches; repacking.
- MPC round latency (only elements are counted), network topology, preprocessing storage.
- Accuracy: every integer recipe (F1 factor quantization, ZO) is assumed to train. It may not.
- The envelope's own cost beyond committed factor felts (the norm range proof is small but nonzero).
- ε_chk is a constant 2^-100; at today's UDR (34 bits) q is still set by p, so the ranking does not
  change, but no soundness number from this script may be quoted.
