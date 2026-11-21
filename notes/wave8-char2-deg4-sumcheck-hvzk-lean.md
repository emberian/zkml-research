# Wave 8 — Char-2 degree-≤4 sumcheck and BaseFold round-polynomial HVZK in Lean (gate `G8 / #125`)

**Date:** 2026-11-21 · **Lane:** `w8-char2-round-hvzk` (`wave8_forward_extrapolation_2026_11_21`)
**Artifact `[EXECUTED]`:** [Char2Degree4SumcheckHvzk.lean](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean)
(789 lines, Lean `v4.35.0`, imports only Mathlib; 0 `sorry` / custom `axiom` / `native_decide`;
25 `#guard_msgs`-pinned `#print axioms`, every one ⊆ `{propext, Classical.choice, Quot.sound}`).
**Verifier `[EXECUTED]`:** [build_and_verify.sh](file:///Users/ember/dev/zkml-research/research/wave8_forward_extrapolation_2026_11_21/formal_char2_hvzk/build_and_verify.sh)
→ `exit 0`: hygiene OK, `scripts/check-import-boundary.sh` passed, `0 warnings, 0 errors` (7 s;
wipes and rewrites `formal_char2_hvzk/build/`; never invokes `lake` in minidregg).
Not edited: `Theory.lean`, `Tower256AlgebraicCert.lean`, `notes/README.md`, `docs/VERDICTS.md`. The
module is not in the `Theory` umbrella; wiring it in is the maintainer's call.

## 1. Corrections to the brief (`[DERIVED]`, each machine-checked)

- **"Any multilinear mask sums to 0" is false.** What holds is the *affine* (total-degree-1) case
  `a₀ + ∑ aₖxₖ` for `m ≥ 2` ([charTwo_affine_cubeSum_eq_zero](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L91)).
  Falsifier: `∑_{x∈{0,1}²} x₀x₁ = 1` ([multilinear_x0x1_cubeSum_eq_one](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L123)).
  The `m ≥ 2` guard matters: `∑_{x∈{0,1}} x = 1` ([ell1_affine_cubeSum_eq_one](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L130)).
  A multilinear column's hypercube sum in char 2 is its top coefficient. So the zero-sum premise on
  `m_lin + P₁u₁` is a sampling constraint, not a free fact.
- **"`(x_k²+x_k)·u` has degree ≤ 2" holds only when `u` is constant in `X`**
  ([z2_constant_term_degree_le_two](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L513)).
  With a multilinear `u` the degree is 3: `c₃` is then covered by `u`'s slope, but `c₄` is still
  always `0`. The leak the proof needs is the **3-column** one: with no `Z₃` column, the masked `c₄`
  equals the honest `c₄` for every `m_lin, u₁, u₂`
  ([threeColumn_c4_eq_zero](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L522),
  [threeColumn_transcripts_separate](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L528)).
  Over `ZMod 2`, the honest polynomials `0` and `X + X⁴` share claim 0 but give disjoint transcript
  supports, so `TVD = 1` ([zmod2_threeColumn_distinguisher](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L703)).
- **Char-2 claim constraint confirmed:** `p(0)+p(1) = c₁+c₂+c₃+c₄`, so `c₀` is free
  ([peval_zero_add_one_five](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L153)).
  This fails in `ZMod 3` ([zmod3_c0_not_free](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L164)).

## 2. Per-round algebra of the 4-column mask (`[EXECUTED]`)

- **Hypercube grounding.** [roundPartialSum_eq](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L442):
  take round `j` with prefix `r_{<j}` fixed and columns multilinear in `X`. The sum over the
  Boolean suffix of `m_lin + P₁u₁ + Z₂u₂ + Z₃u₃` is a polynomial whose coefficient vector is
  [roundMaskCoeffs](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L416).
  The suffix parts of `Z₂` and `Z₃` vanish because `x²+x = x³+x² = 0` on `{0,1}`. Factored form:
  `(a₀+a₁X) + (E+ζ'X)(b₀+b₁X) + (w₀+w₁X) + (C₂+ζ'(X²+X))(s₀+s₁X) + (C₃+ζ'(X³+X²))(t₀+t₁X)`,
  with `ζ' = ζ^{j+1}`. `E, C₂, C₃` are the prefix sums from
  [stdPublic](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L389), which mirror `P₁, Z₂, Z₃` in
  [evalCombinedPhiC](file:///Users/ember/dev/minidregg/Compiler/Tower256AlgebraicCert.lean#L2742-L2807).
- **Full-rank pivots.** [roundMaskEquiv](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L481):
  if `ζ' ≠ 0`, the map from `(a₀, a₁, b₁, s₁, t₁)` to `(c₀, …, c₄)` is a bijection. It is
  triangular: `t₁ → c₄` (`u₃` via `Z₃`), `s₁ → c₃` (`u₂`), `b₁ → c₂` (`u₁` via `P₁`), `a₁ → c₁`,
  `a₀ → c₀` (`m_lin`). [card_roundMask_hyperplane](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L503):
  exactly `|F|⁴` pivot vectors land on each claim hyperplane, a 4-dimensional slice. The mask claim
  never involves `a₀` ([roundMask_claim](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L493)).

## 3. Multi-round HVZK, `TVD = 0` (`[EXECUTED]`)

- [sumcheck_mask_hvzk](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L242):
  draw masks uniformly from the zero-claim chain-consistent transcripts. Then any two honest
  `D`-round degree-≤4 transcripts with the same claim give the same mask count for **every** event
  on `h + ρ·M`. This is an equality of event counts, hence `TVD = 0`. The proof is a translation
  ([shift_event_card_eq](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L222))
  and works in any field.
- [char2_deg4_sumcheck_hvzk](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L576) (capstone):
  assume `[CharP F 2] [Fintype F]`, `ζ ≠ 0`, `ρ ≠ 0`. Then the 4-column pivot space and the
  simulator's support (consistent transcripts) both have `|F|^{4D}` elements. Each consistent
  transcript has exactly one pivot preimage, and each inconsistent one has none. So the real view
  equals the uniform simulator, whatever the target `Φ` is. The count comes from
  [consistentEquiv](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L356):
  each round has free `(c₀, c₂, c₃, c₄)` and `c₁` is solved from the running claim.
  The premises are inhabited ([zmod2_capstone_premises_inhabited](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L694)).
- **BaseFold degree 2.** In char 2, `eq(r_j,X) = (1+r_j) + X`
  ([eqFactor_charTwo](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L610)).
  So the round polynomial of `eq(r,x)·g(x)` is `κ(e+X)(β₀+β₁X)`, which has a root at `e`
  ([bfRound_root](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L622)).
  If `κ ≠ 0`, the map from `β` to its image is injective
  ([bfRound_injective](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L626))
  and onto all quadratics with root `e`
  ([bfRound_surj_root](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L638)).
  [basefold_hvzk](file:///Users/ember/dev/minidregg/Theory/Char2Degree4SumcheckHvzk.lean#L665):
  event-count equality over all `D` rounds for any two honest `γ, γ'` with the same claim.

## 4. What this does *not* close

- `[OPEN]` **Chained columns.** The multi-round theorems assume each round's pivots range over all
  chain-consistent values ("fresh pivots per round", or the distinct-fiber reading of the brief).
  With one multilinear table per column, round `j`'s slopes are set by round `j-1`: for example
  `t₁^{(j)} = U₃^{(j-1)}(r_{j-1})`, so the masked `c₄^{(j)}` depends only on the past. Full rank of
  the chained map from the 4 tables to `Consistent r 0` is unproved. `[HYPOTHESIS]`: a padding
  cascade (`s₁` pads `t₀` in `c₃`, `b₁` pads `s₀` in `c₂`, …) keeps the rank at `4D`. The next
  step is that rank lemma.
- `[OPEN]` **Terminal opening.** The final check reveals mask-column evaluations at `r`. This
  depends on `zero_position_disclosure_hiding` in `Tower256AlgebraicCert.lean` and is not
  composed here. In this model the round-polynomial fiber is a singleton, so there is no slack
  left to absorb an additional pinned evaluation.
- `[OPEN]` **BaseFold support count and fold-oracle leakage** are not formalized. Only the
  round-polynomial event equality is.
- **Scope:** honest verifier, fixed challenges, coefficient level. Not a claim about the Rust prover.

## 5. Proposed `VERDICTS.md` fold (for the maintainer)

`G8 / #125`: `[OPEN]` → **closed at round-polynomial / fresh-pivot scope** (Lean `v4.35.0`,
`char2_deg4_sumcheck_hvzk`, `basefold_hvzk`). Chained-column rank and terminal-opening composition
stay `[OPEN]`. Also record the correction: "every degree-1 polynomial", not "every multilinear".
