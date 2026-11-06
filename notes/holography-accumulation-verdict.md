# Holography accumulation (ePrint 2026/538) against our accumulation machinery: verdict

2026-11-06. Initiative 14, lane F4 (draft for the F3+F4 owner to land). Revised the same day
after the Codex audit; the changes are listed in §6. Tags: [READ] inspected source at
file:line or paper section; [MEASURED] I ran it; [X] measured elsewhere; [INFERRED] derived
here; [A] assumption; [CLAIM] someone's unverified statement.

Source text: the mirror PDF `IACR-eprint-mirror/2026/538.pdf` carries CreationDate 2026-03-17
[READ pdfinfo], so it is the March ePrint version and not the SCN 2026 camera-ready, which may
differ. Section and line numbers refer to the March text as extracted to `538.txt`. The paper
has no implementation and gives no concrete counts; its efficiency statements are asymptotic
(Thm 5, Thm 6, Tables 1-2) [READ].

## 0. Verdict

**ADAPT.** Keep commitment-free structural accumulation as a candidate. Revisit it once the
leaf relation and the recursive circuit exist and their structural-check share has been
measured. Do not adopt it now as a lever on the recursion verifier.

What the paper supplies, and what it does not:
- **It supplies no cheaper hash-based atomic PCS accumulation.**
  - Def 4 (538.txt:975-980) and Remark 3 *assume* a reduction `Π_batchPCEP : R*_PCEP → R_PCEP`.
  - §2.3 (538.txt:705-708) permits full verification with an empty PCS accumulator ("In the
    case of full recursion accPCEP is empty and VbatchPCEP is the evaluation proof verifier").
  - Barebones and §5.2 (538.txt:2008-2017, 2067-2085) give nothing cheaper for the PCS half.
  - So over our cSHAKE-Merkle receipts, the paper's own construction verifies each child's
    PCS evaluation proof in full at every step [READ].
- **What it does supply:** accumulation of the holographic (index-polynomial) claims.
  - At `ν = log n` this needs no commitment (Cor 2; Fig 3-4; §1.1 item 4) [READ].
  - It moves the structural evaluation from every step to the decider.
  - The paper's stated benefit is mainly **prover** work: no commitments to the structure
    polynomials, O(n) instead of O(K) cryptographic cost (538.txt:139-147, 607-614).
- I make **no separation claim**. I do not claim that hash-based PCS accumulation needs
  homomorphism, or that a stateless and cheap scheme over Merkle is impossible.
  - The hash-based accumulators I read (Arc, WARP, BMNW24, our `AccRbrBcs`) all carry a codeword
    witness [READ 2024/474:305-309, 2024/1731:586, 2025/753:104, `Rbr.lean:166-168`,
    `AccRbrBcs.lean:333-335,346-350`].
  - That is an observation about those schemes, not a theorem.

## 1. Per-step recursion verifier, in counts

### 1.1 Leaf and unit costs

Leaf = Tower256 additive-FRI receipt, `lb = 2`, `q = 148` (UD-100), unary codec, from
`tower256_fri_counts.py` [MEASURED: `python3 -I`; matches TOWER256-FRI-PROVER-WORK §2].

In-circuit unit: **Keccak-f = 38,400 SIMD-R1CS constraints per permutation**, packed three per
instance at 92% fill [X: 2026/1656 §3 "Circuits"].
- 38,400/0.92 = 41,739 "slots" per permutation.
- The slot conversion assumes witness size equals constraint count [A], which is not
  established for our Tower256 path.
- Tower256 multiplication costs either 3 constraints (field-valued coefficients) or 6,561 ANDs
  (bit-level) [A]; under either it is at most 0.9% of the leaf verifier.

The script counts three Merkle paths per query-round (`tower256_fri_counts.py:78`). The landed
pair layout recomputes one path per pair:
- two leaf hashes, the pair parent, and `k − 1` ancestors, so `k + 2` Keccak-f at level `k = ell − j`
  (md-arklib `Compiler/Tower256SuccinctCheck.lean:172-176` `CPairOpening.leftFull`, `:585`
  `openedC`) [READ];
- seeds finished from the cached prefix.
The script itself should be updated at source by its owner.

| ell | V Keccak-f, script (3 paths) | V, pair layout + cached seeds | V mults |
|---:|---:|---:|---:|
| 14 | 53,263 | **17,793** | 3,024 |
| 16 | 68,985 | **23,163** | 3,616 |
| 20 | 105,982 | **35,757** | 4,800 |
| 22 | 127,256 | **42,980** | 5,392 |

[MEASURED: `/private/tmp/claude-501/-Users-ember-dev-aidev/78fef112-a52f-425f-8503-f3fa24ff087c/scratchpad/holo-counts/pair_variant.py`]

### 1.2 Per step, arity K = 2 (Keccak-f)

| ell | (a) full recursion, pair layout | (c) holography acc. | (b)/(d) single-codeword path model, t = 148 | ratio (a)/(b) | state per input (message) |
|---:|---:|---|---:|---:|---:|
| 14 | 35,586 | (a) − 2H + T | 6,660 | 5.3 | 128 KiB |
| 16 | 46,326 | (a) − 2H + T | 7,548 | 6.1 | 512 KiB |
| 20 | 71,514 | (a) − 2H + T | 9,324 | 7.7 | 8 MiB |
| 22 | 85,960 | (a) − 2H + T | 10,212 | 8.4 | 32 MiB |

**What the columns are.**
- (b)/(d) is `(K+1)·t·(ell+1)`, a **single-codeword Merkle-path model only**: K inputs plus one
  output, t paths each, one leaf and `ell` nodes per path [INFERRED]. It is not an established
  Arc or WARP count:
  - Arc's R1CS scheme keeps two codewords (2024/1731:175-183).
  - OOD checks, sumcheck/transcript work and the security accounting are missing.
  - The real count is higher by an amount I have not derived.
- t = 148 matches the FRI receipt's per-query error at UD; the Johnson count would be 100.
- H is the structural (holographic) evaluation share per child. T is the accumulation sumcheck's
  transcript. My 23 Keccak-f for T counted bytes only and ignored the sequential Fiat-Shamir
  absorptions, one per round, so T is a lower bound.
- Steady state (child is itself a wrap; fixed point under the slot assumption):
  - (a) settles near ell = 28, at 2·68,388 = 136,776 Keccak-f per step.
  - The (b) path model settles near ell = 23, at 10,656, a ratio of about 13×.
  - Both inherit the slot assumption and the (b) model's omissions.

**H is model-dependent and not yet measurable** [INFERRED]:
- **Today H = 0.** The receipt is a bare low-degree test with no relation (TOWER256-FRI-PROVER-WORK
  §3).
- **SIMD-R1CS leaf, BinarySpartan shape.** The verifier evaluates the shared block matrices
  directly (2026/1656 lines 184-193). The share depends on the in-circuit price of an `F_{2^128}`
  product:
  - with field-valued constraint coefficients, about 31 Keccak-f-equivalents per Keccak-f block,
    small against the PCS term;
  - with bit-level Karatsuba, about 2.9e9 constraints per block evaluation, which is 1.3× the script's leaf verify and
    3.9× the pair-layout one (17,793 × 41,739 = 7.4e8). The structural share would then dominate.
- **Non-uniform wrap glue.** The sparsity of the glue matrices is unknown; my earlier 2,000
  nonzeros per permutation was an assumption.
- So no single percentage can be given. The earlier "0-5%" is withdrawn.

**Paid once by a decider:**
- (a): one native verification plus the root's structural check.
- (c): the same, plus one index evaluation. §5.3's homomorphic PC2 makes that a single opening.
  Over hashes it is either a same-point batched opening or direct evaluation (H3, algebra only).
- (b): WARP's `O(|p̂|)` decider (2025/753 Thm 1) [READ].

## 2. Where commitment properties enter 2026/538

1. **Holographic accumulation: none needed at `ν = log n`.**
   - Cor 2 runs `Π_GBF2` with `u = Λ(X,α)` and `v = Λ(X,β)`, both computed by the verifier.
   - Fig 4's `R_PCE` outputs reduce to the `h`-polynomials, and those exist only at `ν = 1`.
   - The `[M_i]` are index commitments, never opened before the decider.
   - The univariate variant commits 4 polynomials per step (Thm 6).
   - [READ §1.1, §4.3, Fig 3-4, Thm 6]
2. **The PCS half assumes Def 4's `Π_batchPCEP` (Remark 3).**
   - The paper names KZG/Pedersen-style accumulation, or arithmetizing the verifier (FRI, STIR,
     WHIR, Binius, BaseFold) as the fallback (§1.1 "Generic PCD Construction"; §2.3).
   - It constructs nothing cheaper for hash PCSs [READ].
3. **§5.3 decider: homomorphic PC2, assumed explicitly**, to combine `ℓ·t_M` matrix commitments.
   - Linearity of the MLE (H3) means the same values can be obtained by same-point openings.
   - That is an algebraic identity. Whether a batched Merkle opening realizes it soundly within
     the paper's knowledge-soundness proof is not shown here.
4. Corollary 3 gives PCD for **constant-depth** predicates only [READ]. An aggregate has depth
   `log_K N`.

## 3. What our machinery proves, read (not reconstructed)

- **`AccRbrBcs`**: an Arc/WARP-shaped `Reduction` at the Merkle alphabet.
  - The verifier checks `t` opened columns per round and outputs a full word
    (`AccRbrBcs.lean:318-350`; `Rbr.lean:166-168`).
  - Def 4.2 is built at `(t+k)·accRbrError` with FS (`:527`, `:749`), in the whole-code-mask/UD
    regime.
- **⚠ It does not price our parameters.** The synthesized-word = committed-word route
  (`bcsWord_committed`, `AccRbrBcs.lean:189-195`) needs `d ≤ t` with distinct opening positions
  (`hdt : d ≤ t`, `hq : Function.Injective (dom ∘ q)`). At ell = 14 and rate 1/4 the code
  dimension is 2^12 = 4,096, and 148 openings do not meet it. **"`AccRbrBcs` prices this" is
  false at these parameters.** The sub-`d` regime is `[ZK-RBR-extract]` open lemma A.
- **Residuals, all open:**
  - `[ACC-rbr-bcs-resid]` (`AccRbrBcs.lean:1037-1075`): (a) fold-root schedule; (b)
    `[ZK-RBR-extract]` lemma A; (c) the floor `[FS-ROM]`, `[COMMIT-CR]`, `hPG`.
  - Shifted: `accRbrKnowledgeSoundBcsShifted` has floor one. The linked object
    `[ACC-rbr-bcs-shifted-linked]` is satisfiable at 1, refuted at 0, and open at `accRbrError`
    (`AccRbrBcsShifted.lean:550-571`). The log-route statement
    `linkedAdaptiveIncrementSound_proved` is at `OracleLogLinkedAssembly.lean:461`.
- **`Depth.lean`** composes the rounds of ONE reduction (`OB2_depth_composition_nonneg`,
  `Depth.lean:1872`), not recursion layers. Nothing here prices a depth-`log_K N` aggregate.
- **`AccRbrFold`** needs a linear commit map (`FoldCommitScheme.commit : W →ₗ[R] C`,
  `AccRbrFold.lean:179-183`). It is inapplicable to Merkle roots, as the file says (`:13-14`).
  It has no cost model (`:41-45`); `[FOLD-msis]` is the computational residual.

**The brief's example target.** Does the accumulated holographic check over a hash PCS reduce to
an opening that `AccRbrFold`/`AccRbrBcs` already prices? **No.**
- Per step, the holographic half reduces to a claim on a fixed index with no opening. H1 shows
  the algebra only, not protocol soundness.
- At the decider it is one index evaluation.
- Neither file prices the witness half at our parameters: `AccRbrBcs` because of `d ≤ t`,
  `AccRbrFold` because of linearity.

## 4. Lean statements (draft, UNCHECKED)

**Typecheck status: not checked.** The existing oleans are from a different toolchain:
- `lake env lean` reports "incompatible header" on `Selvage/EqPolynomial.olean`.
- Direct v4.35.0 and v4.30.0 `lean` with a read-only `LEAN_PATH` fail the same way, on the
  Selvage oleans and on `importGraph` respectively.
- A check would need a rebuild, which the brief forbids. The proofs were checked by reading
  only. See §6 for the package side effect.

File: `/private/tmp/claude-501/-Users-ember-dev-aidev/78fef112-a52f-425f-8503-f3fa24ff087c/scratchpad/holo-lean/HoloAcc.lean`. It imports `Selvage.EqPolynomial` and uses `eqMle`
(`EqPolynomial.lean:42`), `eqMle_fold` (`:69`), `cubePt`, `mle`, `mle_agrees`, and
`MLEExample.fAnd` (`MultilinearExtension.lean:104,117,135,711`).

```lean
import Selvage.EqPolynomial

namespace Minidregg.Selvage.HoloAcc
open Minidregg.Selvage

section Algebra
variable {F : Type*} [CommRing F] {m K : ℕ}

def HoloClaims (M : (Fin m → Bool) → F) (r : Fin K → Fin m → F) (v : Fin K → F) : Prop :=
  ∀ k, mle M (r k) = v k

def holoWeight (γ : Fin K → F) (r : Fin K → Fin m → F) (x : Fin m → F) : F :=
  ∑ k, γ k * eqMle (r k) x

/-- H1: K claims on one index → one hypercube sum of w·M; the sumcheck on w·mle M ends in
`w(r*)·mle M r*`, a fresh claim on the SAME index. No commitment, no witness in the type. -/
theorem holo_batch_sum (M : (Fin m → Bool) → F) (r : Fin K → Fin m → F) (γ : Fin K → F) :
    ∑ b, holoWeight γ r (cubePt b) * M b = ∑ k, γ k * mle M (r k) := by
  unfold holoWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← eqMle_fold (r k) M, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem holo_batch_sum_of_claims {M : (Fin m → Bool) → F} {r : Fin K → Fin m → F}
    {v : Fin K → F} (h : HoloClaims M r v) (γ : Fin K → F) :
    ∑ b, holoWeight γ r (cubePt b) * M b = ∑ k, γ k * v k := by
  rw [holo_batch_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [h k]

theorem holo_summand_cube (M : (Fin m → Bool) → F) (r : Fin K → Fin m → F)
    (γ : Fin K → F) (b : Fin m → Bool) :
    holoWeight γ r (cubePt b) * mle M (cubePt b) = holoWeight γ r (cubePt b) * M b := by
  rw [mle_agrees]

/-- H3: the §5.3 decider's homomorphic combine has a value-side twin (same-point openings). -/
theorem mle_lincomb {J : Type*} [Fintype J] (η : J → F)
    (Ms : J → (Fin m → Bool) → F) (x : Fin m → F) :
    mle (fun b => ∑ j, η j * Ms j b) x = ∑ j, η j * mle (Ms j) x := by
  unfold mle
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
end Algebra

section Soundness
variable {F : Type*} [Field F] {m K : ℕ}

/-- H2 (Lemma 1's 1/|F|, coordinate form): a false claim k₀ leaves at most one value of γ k₀,
other coordinates fixed, that passes the batched check. -/
theorem holo_batch_coord_unique {M : (Fin m → Bool) → F} {r : Fin K → Fin m → F}
    {v : Fin K → F} {k₀ : Fin K} (hbad : mle M (r k₀) ≠ v k₀)
    {γ γ' : Fin K → F} (hoff : ∀ k, k ≠ k₀ → γ k = γ' k)
    (h : ∑ k, γ k * mle M (r k) = ∑ k, γ k * v k)
    (h' : ∑ k, γ' k * mle M (r k) = ∑ k, γ' k * v k) :
    γ k₀ = γ' k₀ := by
  have hd : ∀ g : Fin K → F, (∑ k, g k * mle M (r k) = ∑ k, g k * v k) ↔
      ∑ k, g k * (mle M (r k) - v k) = 0 := by
    intro g
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.symm
  have e1 := (hd γ).1 h
  have e2 := (hd γ').1 h'
  have hdiff : ∑ k, (γ k - γ' k) * (mle M (r k) - v k) = 0 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, e1, e2, sub_zero]
  rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [hoff k hk, sub_self, zero_mul])
    (fun h => absurd (Finset.mem_univ k₀) h)] at hdiff
  have hne : mle M (r k₀) - v k₀ ≠ 0 := sub_ne_zero.mpr hbad
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hne)
end Soundness

namespace Example
abbrev M₀ : (Fin 2 → Bool) → ZMod 5 := MLEExample.fAnd
def r₀ : Fin 2 → Fin 2 → ZMod 5 := ![![2, 3], ![4, 1]]
-- non-vacuity: true claims hold (mle fAnd x = x0·x1: 2·3 = 1, 4·1 = 4)
theorem claims_true : HoloClaims M₀ r₀ ![1, 4] := by
  intro k; fin_cases k <;> decide
-- falsifier: a wrong value is refuted
theorem claims_false : ¬ HoloClaims M₀ r₀ ![1, 3] := by
  intro h; have := h 1; revert this; decide
theorem batch_fires :
    ∑ b, holoWeight ![1, 2] r₀ (cubePt b) * M₀ b = (1 * 1 + 2 * 4 : ZMod 5) := by
  rw [holo_batch_sum_of_claims claims_true]; decide
-- H2 teeth: the false claim is caught by γ = (1,1)
theorem batch_catches :
    (∑ k, (![1, 1] : Fin 2 → ZMod 5) k * mle M₀ (r₀ k))
      ≠ ∑ k, (![1, 1] : Fin 2 → ZMod 5) k * (![1, 3] : Fin 2 → ZMod 5) k := by decide
-- H2 falsifier without hbad: true claims admit γ, γ' agreeing off k₀ = 1 but differing at 1
theorem hbad_needed :
    (∑ k, (![1, 0] : Fin 2 → ZMod 5) k * mle M₀ (r₀ k)
        = ∑ k, (![1, 0] : Fin 2 → ZMod 5) k * (![1, 4] : Fin 2 → ZMod 5) k)
      ∧ (∑ k, (![1, 1] : Fin 2 → ZMod 5) k * mle M₀ (r₀ k)
        = ∑ k, (![1, 1] : Fin 2 → ZMod 5) k * (![1, 4] : Fin 2 → ZMod 5) k)
      ∧ (![1, 0] : Fin 2 → ZMod 5) 1 ≠ (![1, 1] : Fin 2 → ZMod 5) 1 := by decide
theorem lincomb_fires :
    mle (fun b => ∑ j : Fin 2, (![1, 2] : Fin 2 → ZMod 5) j * M₀ b) ![2, 3]
      = ∑ j : Fin 2, (![1, 2] : Fin 2 → ZMod 5) j * mle M₀ ![2, 3] := by
  rw [mle_lincomb]
end Example
end Minidregg.Selvage.HoloAcc
```

**Scope of H1-H3: these are sound algebraic lemmas, not protocol soundness.**
- H1 is the completeness-side identity behind the multi-point to one-point reduction.
- H2 is the coordinate form of Lemma 1's batching bound.
- H3 is MLE linearity.
- None of them is a `Reduction`, an RBR bound, or a statement about any commitment.
- Falsifier caveat for H1: a wrong claimed value changes the batched target only when its
  coefficient is nonzero, and absent cancellation between several wrong values. H2 prices that
  event one coordinate at a time.

| statement | non-vacuity | falsifier / teeth |
|---|---|---|
| H1 | `batch_fires` | `claims_false` refutes a wrong claim; the batched target moves only under a nonzero coefficient and no cancellation |
| H2 | hypotheses jointly satisfiable at `v = ![1,3]`, `γ = γ' = ![1,0]` | `hbad_needed`: drop `hbad` and the conclusion fails; `batch_catches` |
| H3 | `lincomb_fires` | an identity; its content is that it holds at every point |

**Not stated:**
- RBR soundness of the sumcheck on `w·mle M`; the place for it is
  `MultilinearExtension.lean:338-545` (`roundSum`/`roundPoly`).
- Any separation result for hash-based PCS accumulation (see §0).

## 5. What I could not settle

1. The in-circuit price of an `F_{2^128}` product, and whether our future Tower256 zerocheck
   admits field-coefficient constraints. This decides H between small and dominant.
2. The glue sparsity of a recursive wrap circuit that does not yet exist.
3. A real Arc/WARP per-step count: two codewords, OOD, sumcheck, sequential FS, and the security
   accounting.
4. The witness-size-equals-constraints slot assumption.
5. Whether the SCN version changes Def 4, Remark 3 or §5.3.
6. **The bar.** Stateless versus stateful is one axis among several. The others are total prover
   work (where 2026/538 claims its win), state storage and transfer, privacy, decider cost, and
   which assumptions are discharged in Lean. The aggregate should be priced on all of them once
   the relation and wrap exist. A verifier count alone does not decide it.

## 6. Session side effect, and revision log

**`lake env lean` touched package checkouts.** At 2026-11-06 11:47:30 -0800 my `lake env lean`
in `/Users/ember/dev/minidregg` printed "checking out revision" for the eight packages in
`.lake/packages`. It moved each to its `lake-manifest.json` revision:

| package | moved to |
|---|---|
| mathlib | `56a0058` (from `1c2b90b`) |
| plausible | `dfa4f38` |
| LeanSearchClient | `d6b4c7b` |
| proofwidgets | `df72b02` |
| aesop | `4a174c49` |
| Qq | `dce0ad7` |
| batteries | `66e469188` |
| Cli | `c24fe60` |

- At 11:47:48 the mathlib reflog shows a move back to `1c2b90b`, by a process that was not mine.
  The same back-and-forth appears at 2026-11-05 21:01/21:02.
- At my last check every package's HEAD was at its pre-run commit.
- The typecheck still failed ("incompatible header"). Two settings in minidregg's `.lake`
  disagree: the root `lean-toolchain` is v4.35.0, and mathlib at `1c2b90b` pins v4.30.0.

**Revision log (Codex audit, accepted):**
- Verdict changed from "ignore" to ADAPT. The homomorphism and "binary choice" separations are
  removed.
- "0-5%" is withdrawn; H is model-dependent (0, small, or 1.3-3.9× a leaf verify).
- Pair-path count corrected from `k+1` to `k+2`.
- The (b) column is relabelled a single-codeword path model; the slot and FS caveats are added.
- The `AccRbrBcs` `d ≤ t` failure at our parameters is recorded, with its residuals and the
  `Depth` scope.
- H1-H3 are scoped as algebra.
- The bar is multi-axis.
