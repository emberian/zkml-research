# NEXT — `speedup_wave_2026_11_21`

## Immediate High-Leverage Next Steps (For Maintainer Approval / Follow-On Lanes)

1. **Fold Approved Verdicts into `docs/VERDICTS.md` & `docs/AGENDA.md`:**
   - Close `docs/AGENDA.md:111-113` (`ePrint 2026/347` `Qāren` rejected as Mod-PCS/integer backend; hold repaired Barycentric `Lagrange-Check` for `vFHE` Hole B).
   - Fold `notes/einsum-speedup-wave.md`, `notes/trace-packing-and-zk-whir.md`, `notes/qaren-and-gptoss-nonlin-speedups.md`, and `notes/proximity-and-hw-delta-2026-11.md` into `docs/VERDICTS.md` §§1b, 2, 4, 5, 7, 9, 9a (exact proposed diffs are at the bottom of each note).

2. **Land Lean 4 Upgrades in `/Users/ember/dev/minidregg` (`Selvage`):**
   - **Zero-diff Mode 1 vs Mode 2 Gruen `eq`-skip (`Assurance/ZkmlEinSumcheck.lean`):** Mode 1 already verifies against unmodified `AirSumcheckCubic.lean`; formalize Mode 2 (`2/|F|` per-round error, `0` prover inversions) + the `step_β` carry-chain virtual window identity (`einsum-speedup-wave.md` §3.1) for $W = 128$ sliding-window GQA.
   - **Formalize `DKT26` Theorem 5.12 (`O_ρ(n/η_0^3)` all-characteristic Johnson MCA) in `Selvage/JohnsonRegime.lean` / `TwoRegimeQueryBudget.lean`:** Gains `+6.96..14.79` bits of provable commit/fold margin across BabyBear, KoalaBear, Goldilocks, and `Tower256` (`quangvdao/rs-beyond-johnson` formalized list size in Lean, leaving Theorem 5.12 MCA open!).
   - **Formalize `Frigo–shelat (2026/2770)` + `Bloemen (2026)` Theorem 5 (`H = Tr`) + odd-char Eq. (9) sign fix:** Gives zero-quadratic-constraint ZK bit unpacking inside WHIR for ZK MoE router binding.

3. **Prototype in `gptoss-int` / `breadstuffs` Prover Pipeline:**
   - Delete the 4 provably-dead/subsumed clamp sites in the ZK lowering of `research/exact_recompute_2026_11_06/layer.py` (`lines 227, 256, 258-hi, 260` — instant `-28.14B` cells at $T=4096$ with zero output change) and wire the 4-into-1 `gu_even -> key` `ClampRq` + 15-entry row-`TwoPow` `norm_int` + `W=128` windowed GQA.
   - Implement the 7-bucket 0-mul E2M1 Horner + `b -> j -> k` delayed block-bind kernel (`16.8 MB` `Ext4` working set fits inside L3 cache!) and `ProveKit v2` subdomain projection $\pi(x) = x^{2^{k_1 - m_2}}$ for `EXP_TAB || G_TAB` multiplicities.
