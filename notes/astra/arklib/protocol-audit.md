# ArkLib protocol statement audit

[READ] Source snapshot: `/Users/ember/src/ArkLib-latest`, upstream `4d9d67be` (2026-11-05). Paths below beginning `ArkLib/` are relative to that checkout; `Selvage/` paths are relative to `/Users/ember/dev/minidregg` at `c4ecabe0fad1c8b9eb32a6b3cc2340f689078f55`. This is a source statement audit, **not a new Lean build or a new transitive axiom-closure check**. The parent audit owns those measurements. [INFERRED] Mathematical witnesses below demonstrate inhabited parameter regimes; their stated inequalities are not claimed to be newly Lean-checked.

## Decisions

| Component | Verdict | Comparison and exact consumer |
|---|---|---|
| Sumcheck RBR | **MIRROR / retain Selvage** | [READ] `ArkLib/ProofSystem/Sumcheck/Spec/General.lean:513` and `:528` prove round and ordinary knowledge soundness. Compared with `Selvage/SumcheckRbr.lean:268` `sumcheckRbrKnowledgeSound` and `:334` `sumcheckRbr_err`, same `d/|F|` per-round price on the shared Boolean-field specialization. ArkLib is broader on evaluation domains; Selvage directly inhabits its compiler interface. No drop-in import replacement. |
| Multiplicative FRI | **MIRROR / cross-check** | [READ] `ArkLib/ProofSystem/Fri/Spec/Soundness.lean:57`, `:81`, `:100` prove adaptive ordinary/RBR soundness. Compare `Selvage/HalfThresholdFriQuery.lean:417` `friAdaptive_sampled_sound`. Incomparable interfaces: ArkLib ordinary oracle execution and powers-MCA sum versus Selvage ideal-binding opened words and a supplied fold transition. Neither subsumes the other by import. |
| Binary BaseFold | **MIRROR into compiler; ArkLib is a usable specification/reference** | [READ] `ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:324` proves exact-encoding completeness plus ordinary knowledge soundness for unique-radius compatibility. Compare `Selvage/AdditiveBaseFold.lean:553` `lch_opening_complete` (algebraic completeness only), and `Selvage/AdditiveFriQuery.lean:781` `additiveFriAdaptive_coherent_sampled_sound_UD` (proximity, ideal binding, different regime). ArkLib has the stronger complete protocol assembly but no direct theorem replacement. |
| Ring switching + Binary BaseFold | **ADAPT, not a claimed drop-in import** | [READ] `ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean:261`, `:277` prove ordinary knowledge soundness and the combined completeness theorem. [INFERRED] This is a new connector in Selvage, not a replacement for an existing ring-switching theorem. A bare “IMPORT the statements” does not make the native Selvage compiler consume it. |

[INFERRED] If an optional ArkLib-backed protocol branch is created, its exact imports are `ArkLib.ProofSystem.Sumcheck.Spec.General`, `ArkLib.ProofSystem.Fri.Spec.Soundness`, `ArkLib.ProofSystem.Fri.ErrorBounds`, `ArkLib.ProofSystem.Binius.BinaryBasefold.General`, and `ArkLib.ProofSystem.Binius.FRIBinius.RingSwitch`. These import names identify reference modules; **none is presented as an immediately substitutable Selvage theorem**. Direct imports for pure coding theory belong to the separate coding audit.

## 1. Sumcheck: actual statement, inhabited assumptions, scope

[READ] `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` at `ArkLib/ProofSystem/Sumcheck/Spec/General.lean:513` has the following essential type (ambient variables at `:118`, `:151`, `:479`):

```lean
-- R : Type, [CommSemiring R] [DecidableEq R] [SampleableType R]
-- D : Fin m ↪ R, deg n : Nat, arbitrary ambient oracle spec oSpec
-- init : ProbComp σ, impl : QueryImpl oSpec (StateT σ ProbComp)
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] [IsDomain R] :
  (oracleVerifier R deg D n oSpec).toVerifier.rbrKnowledgeSoundness init impl
    (relationRound R n deg D 0) (relationRound R n deg D (.last n))
    (fun _ => (deg : ℝ≥0) / Fintype.card R)
```

[READ] The relation at `ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:145` is an actual partial sum of the oracle polynomial at the previously sampled challenge prefix. The oracle polynomial is a bounded-individual-degree subtype (`:142`), rather than a completely unconstrained function. The output relation is the terminal evaluation. Thus this theorem relates the claimed sum to the *named polynomial*, unlike a word-free DFA statement. It is a reduction theorem; the terminal evaluation still needs a backend check/opening when used as a proof system.

[READ] `oracleVerifier_knowledgeSoundness` at `General.lean:528` sums the challenge-index errors. Its guarded-form proof at `:504` retains every round check; the proof at `:519` calls `OracleVerifier.seqCompose_rbrKnowledgeSoundness_of_guarded`. This is actual composition code, not the earlier admitted general composition theorem.

[INFERRED] Explicit nonempty/useful witness: `R = ZMod 17`, `m=2`, `D(0)=0`, `D(1)=1`, `deg=2`, `n=1`, empty ambient oracle specification, singleton state initialized by `pure ()`, uniform field sampling. The polynomial `X₀²`, target `1`, and empty initial challenge vector satisfy the input relation. Changing the target to `0` does not. The error is `2/17 < 1`. More generally `n*deg < |R|` supplies a useful total error. `n=0`, `m=0`, or `deg ≥ |R|` are legal but can give trivial or weak specializations; they are not evidence of empty general hypotheses.

[READ] Selvage's `sumcheckRbrKnowledgeSound` (`Selvage/SumcheckRbr.lean:268`) accepts an honest round-polynomial stream, prefix measurability, degree `<d+1`, and its Boolean sum consistency. Its `extractTime := 0` and native `RbrKnowledgeSoundness` return object are explicit at `:276–280`; `sumcheckRbr_err` at `:334` computes exactly `d/|F|`. `Selvage/QuadraticSumcheck.lean:246` `quad_sumcheck_soundness` provides the concrete product-difference honest stream with total `2m/|F|`.

[INFERRED] Compared at the same Boolean domain and translated event, the numeric bound agrees. ArkLib's general finite evaluation domain is broader than this particular Selvage object, and its stateful oracle execution model adds a different interface. Selvage's arbitrary honest stream representation and direct compiler integration prevent calling ArkLib a universally stronger substitute. A useful repair is an event-and-relation bridge, not deletion of the native RBR object.

## 2. FRI: genuine execution soundness, conditional numeric usefulness

[READ] `Fri.Spec.soundnessError` (`ArkLib/ProofSystem/Fri/Spec/Soundness.lean:52`) is

```lean
(∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l
```

[READ] `foldingError` at `ArkLib/ProofSystem/Fri/Spec/RoundSoundness.lean:39` is the `.toNNReal` of **worst-case powers-generator MCA error for the actual next RS code**, with maximum exponent `2^(s i)-1`. The protocol has `k+1` folds, positive step sizes `s : Fin (k+1) → ℕ+`, positive final degree bound `d`, domain `ω : SmoothCosetFftDomain n F`, and `hdom : 2^(∑j (s j).val)*d.val ≤ 2^n`. The field must satisfy `NonBinaryField` and finite/uniform sampling instances.

[READ] `soundness_proximity` at `Soundness.lean:57` bounds **any acceptance** (output language `Set.univ`) outside the strict-distance input language. `soundness` at `:81` transports this to the existing closed-ball input relation; `rbr_soundness` at `:100` establishes every fixed-prefix challenge bound. The arbitrary prover can have private state, while verifier/prover share ambient oracle state. `InputRelation.lean:41` names the initial word and the actual code; the initial code degree is `< 2^(sum s)*d`. This is not a theorem merely about the existence of a low-degree trace.

[READ] The theorem permits arbitrary real `θ, δ`; useful numbers require additional MCA hypotheses. `l=0` gives query term 1. It proves ordinary/RBR **soundness**, not knowledge soundness, extraction complexity, Merkle binding, Fiat–Shamir, or soundness of a native implementation. Those limitations are explicitly stated at `Soundness.lean:22–28`.

[READ] Numeric theorem `Fri.foldingAgreementFailure_prob_le_generalizedJohnson` (`ArkLib/ProofSystem/Fri/ErrorBounds.lean:40`) requires `d>0`, fold exponent `k>0`, `2^k≤|F|`, the actual next-code relative minimum distance `δmin`, `0<η<δmin`, and

```lean
(θ : ℝ) ≤ 1 - (1 - (δmin : ℝ) + (η : ℝ)) ^
  ((1 : ℝ) / ((2 ^ k - 1 : ℕ) + 2))
```

Its bound is the `linear_mcaError_powers_le` formula. For a binary fold the exponent is `1/3`, so one must not silently replace this wired powers estimate by a full Johnson `1/2` exponent or transplant the pure RS MCA result without a generator/normalization bridge.

[INFERRED] Explicit useful parameter witness: `F=ZMod 257`; initial domain size 16 (`n=4`) with root `2`, since `2^8=-1` and `2^16=1`; one binary fold (`k=0` in **protocol** notation, `s 0=1`), final degree `<1` (`d=1`), and eight queries `l=8`. Set `θ=δ=1/4`, next-code distance `δmin=1` (the length-eight constant code), `η=1/8`. Then the numeric bound's folding exponent is `k=1`, not the protocol's count `k=0`. All domain and positive slack assumptions hold and the generalized-Johnson cap is `1-(1/8)^(1/3)=1/2`, above `θ`.

[INFERRED] To certify a simple rational upper estimate without a floating-point claim, put `a=sqrt(1/8)`. Since `1/3≤a≤3/8`, the first term is at most `128/(3*257)`; the larger second term is at most `128/257` (the competing term is `48/257`). Hence total FRI error is at most `512/771+(3/4)^8 = 38612963/50528256 < 1`. This bounds the numerical powers-MCA estimate underlying `foldingError`; a dedicated Lean specialization was not built in this audit.

[INFERRED] Honest input witness: zero polynomial and zero oracle throughout. Nonvacuous false-input witness: eight domain positions map to 0, eight to 1. A nonconstant degree-<2 polynomial matches at most two positions of that word, and constants match at most eight, so its distance from the initial affine-linear code is 1/2, outside radius 1/4. This excludes an accidental universal input language for the displayed regime.

[READ] Corresponding Selvage theorem `friAdaptive_sampled_sound` (`Selvage/HalfThresholdFriQuery.lean:417`) returns `m*b/|F|+(1-tau)^qCount` from an adaptive committed transcript, ideal `BindingCommitment`, an explicit fold-distance transition for each round, radius-gap assumptions, and initial farness. The ArkLib statement supplies actual oracle execution and worst-case MCA terms; Selvage supports its opened-word and compiler infrastructure. The numeric quantities are not interchangeable until those events and code-degree/radius conventions are transported.

## 3. Binary BaseFold: what “full” now means

[READ] `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness_and_knowledgeSoundness` at `ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:324` is a conjunction:

1. exact-encoding perfect completeness;
2. ordinary knowledge soundness for the initial **unique-decoding-radius compatibility** relation;
3. error supplied by `concreteBinaryBasefoldKnowledgeError` at `:224`:

```lean
2 * (ℓ : ℝ≥0) / Fintype.card L
  + (2 ^ (ℓ + 𝓡) : ℝ≥0) / Fintype.card L
  + ((1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ 𝓡)) ^ γ_rep
```

[READ] The conjunction itself contains the first two items, with the third as its soundness parameter; `fullRbrKnowledgeError_sum_le_concrete` at `:233` proves the conversion from the actual challenge ledger. `fullOracleVerifier_rbrKnowledgeSoundness` at `:204` composes the actual core and query verifiers by `append_rbrKnowledgeSoundness_of_guarded_first`. No ring-switching batching is included in this standalone error.

[READ] Hypotheses at `General.lean:50–64`: finite fields `K,L`, `|K|=2`, `Algebra K L`, linearly independent `β : Fin r→L` with `β 0=1`, positive `r,ℓ,R,ϑ`, `ℓ+R<r`, and `ϑ∣ℓ`. The arbitrary two-point sumcheck domain embedding is explicit. These are substantive characteristic-two and capacity restrictions, not an arbitrary-field theorem.

[READ] A plausible hidden escape was examined: `KnowledgeInvariant` (`Relations.lean:610`) contains `badEventExists ∨ good`. At the initial frontier, however, `not_hasIncrementalBadEvent_zero` (`Relations/Initial.lean:55`) proves that escape false for every oracle; `mem_roundRelation_zero_iff` (`:84`) gives the actual initial conjunction. Thus the initial relation is not automatically true from its bad-event disjunct.

[READ] `PairUniqueDecodingClose` (`Code.lean:295`) means `2*HammingDistance < codeDistance`. The first-oracle compatibility is **functional**, proved at `Commitment.lean:101` by encoding injectivity and the triangle inequality; exact encoding has coverage at `:121`. This “binding” is full-word code uniqueness, not collision resistance of a short digest. `Opening.lean:113` names both source-polynomial evaluation and compatibility with the supplied first oracle. It is therefore materially stronger than a detached terminal evaluation lemma.

[INFERRED] Inhabited useful witness: `K=GF(2)`, `L=GF(16)=K[X]/(X^4+X+1)`, `r=4`, basis `(1,α,α²,α³)`, `ℓ=R=ϑ=1`, Boolean domain `{0,1}`, `γ=4`, singleton ambient state and empty oracle spec. The quartic has no roots and is not divisible by the only monic irreducible quadratic `X²+X+1` (remainder 1), so it is irreducible. All basis/rate assumptions hold, and the bound is `177/256<1`. Zero source polynomial, its exact zero first oracle, and evaluation claim 0 inhabit the completeness relation. Claim 1 on that same zero oracle is false by uniqueness, so the input language is not universal. The witness does not pretend that `L=GF(2)` can satisfy the positive rate parameters.

[READ] Selvage's `lch_opening_complete` at `Selvage/AdditiveBaseFold.lean:553` proves an algebraic descent and its terminal MLE value for a fixed packing/basis. `exists_unique_table_novelPack` at `:529` proves full-polynomial uniqueness. The closest native adversarial acceptance theorem is `additiveFriAdaptive_coherent_sampled_sound_UD` (`Selvage/AdditiveFriQuery.lean:781`) with ideal binding, coherent queries, and an explicit one-third-style radius band. [INFERRED] ArkLib has a stronger assembled interactive evaluation-opening protocol, but not a literal extension of either differently typed theorem. Keep the native basis-ambiguity falsifier (`AdditiveBaseFold.lean:804`) when adapting: the basis must stay part of the statement identity.

## 4. Ring switching: composed and inhabited, with a new interface to build

[READ] `Binius.FRIBinius.RingSwitch.fullVerifier_knowledgeSoundness` at `ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean:261` and the completeness conjunction at `:277` use **the same packed-polynomial witness and first oracle** across ring switching and Binary BaseFold. `opening_input_eq` at `:65` proves equality of the frontend output relation and backend contextual input relation; `opening_strict_input_eq` at `:75` does so for completeness. This is real conjunction through a common object, rather than co-locating independent claims.

[READ] The upstream capstone type is ordinary knowledge soundness of the actual `fullVerifier`, against `TensorPrefix.relIn`, with error

```lean
(κ : ℝ≥0) / Fintype.card L
  + (ℓ' : ℝ≥0) * (2 / Fintype.card L)
  + BinaryBasefold.FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ' R γ
```

The extra frontend term is `κ/|L| + 2ℓ'/|L|`; counting only the Binary BaseFold ledger would omit both contributions. `fullError_sum` at `:128` proves the per-challenge sum, not a hand-written optimistic ledger.

[READ] The basis is `β : Basis (Fin (2^κ)) K L`, not merely a linearly independent prefix. With `|K|=2`, this fixes `|L|=2^(2^κ)`. Other hypotheses (`:37–42`, `:102`) include `ℓ',R,ϑ>0`, `ϑ∣ℓ'`, `ℓ'+R<2^κ`, `ℓ=ℓ'+κ`, and `β 0=1`. The challenges are fresh uniform samples through explicit `SampleableType` instances (`:95`). The surviving query context and initial oracle are carried through the relation equality, rather than supplied independently.

[INFERRED] Use the same GF16 basis, now `κ=2`, `ℓ'=R=ϑ=1`, `ℓ=3`, `γ=4`. All dimension/rate hypotheses hold. The honest source is the zero polynomial over the base representation, which packs to zero, and its evaluation statement and first oracle are zero. The total error is `2/16+2/16+177/256 = 241/256<1`. For stronger toy assurance increase `γ`; the algebraic floor remains `10/16` at this intentionally small field. A security-sized parameter choice is a separate engineering task.

[INFERRED] There is no exact existing Selvage ring-switch capstone to replace in the compared files. An import-only recommendation that names `lch_opening_complete` as the replacement would be wrong: that theorem concerns a different source/representation, and the compiler consumes Selvage's native RBR interface. Recommended repair: a new `Selvage/ArkLibRingSwitchBridge.lean` (name proposed only) translating **source representation, packed basis, initial oracle, extraction witness and every error term**, with this GF16 witness and changed-evaluation falsifier. Until that bridge is proved, call the decision “adapt/reference” or “mirror”, not “ring switching imported into Selvage”.

## Reproduced arithmetic

[MEASURED] [EXECUTED] Python 3 standard-library arithmetic (executed in the research checkout):

```python
from fractions import Fraction
print(Fraction(2+2+2+4,16)+Fraction(3,4)**4)
print(Fraction(2+4,16)+Fraction(3,4)**4)
print(Fraction(512,771)+Fraction(3,4)**8)
print(pow(2,8,257),pow(2,16,257))
```

```text
241/256
177/256
38612963/50528256
256 1
```

[OPEN] These numbers certify arithmetic in the displayed source formulas, not a fresh compiled Lean specialization, not a transitive axiom check, and not a deployed prover. They are useful nonvacuity witnesses and concrete targets for the eventual adapter tests.
