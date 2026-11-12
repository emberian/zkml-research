/-
# Selvage.SmallField — [OB-8]: the deployed-field reality — extension degree buys the bits.

Every soundness bound in the tower is `(numerator)/|F|` (Sumcheck's `v·d/|F|`, the
γ-fold's `(t−1)ℓ/|F|`, …). Those theorems are stated over an ABSTRACT field; the
DEPLOYED base field is small (BabyBear `p = 15·2²⁷ + 1 = 2013265921 ≈ 2³¹`), so
instantiating them at the base field yields ~25 bits of security at protocol-sized
numerators — nowhere near a λ = 100+ target — and at a genuinely small field the
bound exceeds 1 and constrains NOTHING. The standard deployment fix: sample the
verifier's challenges from a field EXTENSION `F_{q^k}`; the SAME theorems,
instantiated at the extension, give error `N/q^k` — the extension degree `k`
multiplies the security exponent. This file makes that dial rigorous. No new
probability is derived; the point is INSTANTIATION AT THE RIGHT FIELD, stated so
the deployed-security claim is legible (λ bits ⟺ `q^k ≥ N·2^λ`).

**What is proved here (no `sorry`, no vacuity):**

* `securityBits` — the bit-count of a soundness bound `N/Q`: `log₂(Q/N)`. Its
  calculus: `le_securityBits_iff` (λ bits ⟺ `N·2^λ ≤ Q`), `securityBits_lt_iff`
  (the failure direction), `err_le_inv_two_pow_iff` (the same fact at the error
  level, `N/Q ≤ 2^{−λ} ⟺ N·2^λ ≤ Q`), `securityBits_pow`
  (`securityBits N (q^k) = k·log₂ q − log₂ N` — the exponent is LINEAR in the
  extension degree), and the monotonicities `err_extension_le` (`N/q^k ≤ N/q`,
  the extension only shrinks the error) and `securityBits_mono_deg` (a higher
  extension degree never loses bits).
* `sumcheck_lambda_secure` — the landed `sumcheck_soundness` (≤ `v·d/|F|`,
  Selvage/Sumcheck.lean) instantiated against a security target: if
  `v·d·2^λ ≤ |F|`, a false claim survives with probability ≤ `2^{−λ}`.
* `card_extension` + `sumcheck_lambda_secure_ext` — the deployed rendering:
  `|F_{q^k}| = q^k` (`Module.card_eq_pow_finrank` at the algebra structure), so
  the premise reads `v·d·2^λ ≤ q^k` — the base size `q` and extension degree `k`
  are the two dials, and `k` is the cheap one.
* The base/extension SEPARATION (§4): the prover's committed words live over the
  cheap base field, the verifier's challenges over the extension. `liftWordₗ` is
  the `F_q`-linear embedding of base words; `liftWord_mem_reedSolomonCode` — a
  base-field RS codeword lifts to an extension-field RS codeword at the SAME
  degree bound (`Polynomial.degree_map`); `fold_liftWord_mem` — the γ-fold with
  an EXTENSION challenge γ of base-committed codewords is again an extension
  codeword (the extension code is a `F_{q^k}`-module and base words land in it);
  `evalExtₗ` — evaluation of a base-committed polynomial at an extension
  challenge is `F_q`-linear, and agrees with mapping-then-evaluating.
* **Keystones, both poles built** (§5): satisfiable — at `|F| = 2³¹`, `N = 100`:
  between 24 and 25 bits (computed, both directions); at the degree-4 extension
  `2¹²⁴`: between 117 and 118 bits; at the REAL BabyBear prime `2013265921`:
  24–25 bits, and its degree-4 extension gives 116–117 — NOT the 117 the round
  `2³¹` suggests (quote the pessimistic number: the deployed prime loses the
  117th bit). Teeth — at `|F| = 5`, `N = 100` the "bound" `100/5 = 20 ≥ 1` is
  VACUOUS: `smallField_bound_vacuous` proves it for EVERY event with no
  soundness reasoning at all, and `smallField_bound_allows_certainty` exhibits
  the probability-ONE event satisfying it — zero security; `securityBits` is
  NEGATIVE there; and the SAME numerator at extension degree 60 clears λ = 128
  (`smallField_rescued_by_extension`) — the extension is load-bearing, not
  decoration. End-to-end: `sumcheck_lambda_secure` FIRES over F₅ (λ = 2, its
  ceiling: `smallField_lambda_ceiling` shows the λ = 3 premise is FALSE at the
  base) and over the genuine quadratic extension GF(25) at λ = 4
  (`sumcheck_lambda_secure_ext`, `GaloisField 5 2`, finrank = 2) — same
  numerator, same theorems, more bits; the accepting event is NONEMPTY
  (`acceptsFalse_witness`), so the secured bound constrains a real event.

**Honest residual [OB-8-tower] (prose, named realizer):** the binary-tower-field
specifics are NOT here — the tower embedding `F₂ ⊂ F₄ ⊂ … ⊂ F_{2^{2^ℓ}}` and its
packed arithmetic, sumcheck over towers à la Basefold/Binius, and WARP App. D's
base-change accounting (`|Λ(C_F,δ)| = |Λ(C_{𝔹^e},δ)|` transfers soundness but
costs O(λ) prover linearity — LOOM §5's stated open problem, the OB-8
contribution slot). Realizer: a tower-field instantiation of §4's algebra-map
machinery (`Algebra F₂ (towerField ℓ)` + the packing isomorphism) plus a
mechanized App. D transfer; the linearity-loss avoidance is open research. The
CORE — extension buys bits, small fields secure nothing — is proved above and
does not depend on the tower specifics.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.GaloisField
import Selvage.Sumcheck

namespace Minidregg.Selvage

open Polynomial

/-! ## §1 `securityBits` and its calculus

A soundness bound `err = N/Q` (numerator `N`, field size `Q`) is worth
`log₂(Q/N)` bits: the false-accept probability is `2^{−securityBits}`. All the
deployment arithmetic — how many bits a field buys, what the extension degree
must be — is this one definition plus four inequalities. -/

/-- The security (in bits) of a soundness bound `N/Q`: `log₂ (Q/N)`.
`err = N/Q = 2^{−securityBits N Q}` whenever both are positive. -/
noncomputable def securityBits (N Q : ℝ) : ℝ := Real.logb 2 (Q / N)

/-- **λ bits ⟺ the field is big enough**: `λ ≤ securityBits N Q ↔ N·2^λ ≤ Q`.
The deployment inequality, at the bit level. -/
theorem le_securityBits_iff {N Q : ℝ} (hN : 0 < N) (hQ : 0 < Q) (lam : ℕ) :
    (lam : ℝ) ≤ securityBits N Q ↔ N * 2 ^ lam ≤ Q := by
  rw [securityBits, Real.le_logb_iff_rpow_le one_lt_two (by positivity),
    Real.rpow_natCast, le_div_iff₀ hN, mul_comm]

/-- The failure direction: `securityBits N Q < λ ↔ Q < N·2^λ` — a too-small
field provably MISSES the target, it does not merely fail to be proven. -/
theorem securityBits_lt_iff {N Q : ℝ} (hN : 0 < N) (hQ : 0 < Q) (lam : ℕ) :
    securityBits N Q < (lam : ℝ) ↔ Q < N * 2 ^ lam := by
  rw [securityBits, Real.logb_lt_iff_lt_rpow one_lt_two (by positivity),
    Real.rpow_natCast, div_lt_iff₀ hN, mul_comm]

/-- The same fact at the error level: `N/Q ≤ 2^{−λ} ⟺ N·2^λ ≤ Q`. This is the
inequality every `…_lambda_secure` theorem below discharges. -/
theorem err_le_inv_two_pow_iff {N Q : ℝ} (hQ : 0 < Q) (lam : ℕ) :
    N / Q ≤ 1 / 2 ^ lam ↔ N * 2 ^ lam ≤ Q := by
  rw [div_le_div_iff₀ hQ (by positivity), one_mul]

/-- The deployment iff at the extension, verbatim: `N/q^k ≤ 2^{−λ} ⟺
q^k ≥ N·2^λ` — the extension degree `k` is what you tune for λ. -/
theorem extension_secure_iff {N q : ℝ} (hq : 0 < q) (k lam : ℕ) :
    N / q ^ k ≤ 1 / 2 ^ lam ↔ N * 2 ^ lam ≤ q ^ k :=
  err_le_inv_two_pow_iff (by positivity) lam

/-- **The extension only shrinks the error**: `N/q^k ≤ N/q` for `k ≥ 1`. -/
theorem err_extension_le {N q : ℝ} (hN : 0 ≤ N) (hq : 1 ≤ q) {k : ℕ} (hk : 1 ≤ k) :
    N / q ^ k ≤ N / q := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hqk : q ≤ q ^ k := by
    calc q = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ k := by gcongr
  gcongr

/-- **The security exponent is linear in the extension degree**:
`securityBits N (q^k) = k·log₂ q − log₂ N`. Each unit of extension degree buys
`log₂ q` fresh bits; the numerator is a one-time toll. -/
theorem securityBits_pow {N q : ℝ} (hN : N ≠ 0) (hq : q ≠ 0) (k : ℕ) :
    securityBits N (q ^ k) = k * Real.logb 2 q - Real.logb 2 N := by
  rw [securityBits, Real.logb_div (pow_ne_zero k hq) hN, Real.logb_pow]

/-- A larger field never loses bits (monotone in `Q`). -/
theorem securityBits_mono {N Q Q' : ℝ} (hN : 0 < N) (hQ : 0 < Q) (h : Q ≤ Q') :
    securityBits N Q ≤ securityBits N Q' :=
  Real.logb_le_logb_of_le one_lt_two (by positivity) (by gcongr)

/-- A higher extension degree never loses bits (monotone in `k`). -/
theorem securityBits_mono_deg {N q : ℝ} (hN : 0 < N) (hq : 1 ≤ q) {k k' : ℕ}
    (h : k ≤ k') :
    securityBits N (q ^ k) ≤ securityBits N (q ^ k') :=
  securityBits_mono hN (by positivity) (by gcongr)

/-! ## §2 The landed sumcheck bound, instantiated against a security target

`sumcheck_soundness` (Selvage/Sumcheck.lean) is `≤ v·d/|F|` over an abstract
finite field. Here it meets the deployment inequality: a field with
`v·d·2^λ ≤ |F|` delivers λ bits. Nothing is re-derived — the calc chain is
the landed theorem followed by `err_le_inv_two_pow_iff`. -/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **λ-bit sumcheck soundness.** If the field clears the target —
`v·d·2^λ ≤ |F|` — then the verifier accepts an initially-false claim with
probability at most `2^{−λ}`. The landed `sumcheck_soundness` instantiated, not
re-proved. -/
theorem sumcheck_lambda_secure {v d lam : ℕ}
    {prover honest : ℕ → Polynomial F} {H S : F}
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → F), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1 = scChain S honest (chalOf r) i)
    (hbig : v * d * 2 ^ lam ≤ Fintype.card F) :
    uniformProb (Fin v → F) (AcceptsFalse prover honest H S) ≤ 1 / 2 ^ lam := by
  have hcard : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  calc uniformProb (Fin v → F) (AcceptsFalse prover honest H S)
      ≤ (v : ℝ) * ((d : ℝ) / Fintype.card F) :=
        sumcheck_soundness hProverDeg hHonestDeg hHonest
    _ = ((v * d : ℕ) : ℝ) / Fintype.card F := by push_cast; ring
    _ ≤ 1 / 2 ^ lam := by
        rw [err_le_inv_two_pow_iff hcard]
        exact_mod_cast hbig

/-! ## §3 The extension field: `|F_{q^k}| = q^k`, and the premise in dial form -/

/-- The cardinality of a finite field extension: `|K| = q^k` where `q` is the
base size and `k = [K : F_q]` the extension degree. `Module.card_eq_pow_finrank`
read through the algebra structure. -/
theorem card_extension (Fq K : Type*) [Field Fq] [Fintype Fq] [Field K]
    [Fintype K] [Algebra Fq K] :
    Fintype.card K = Fintype.card Fq ^ Module.finrank Fq K :=
  Module.card_eq_pow_finrank

/-- **λ-bit sumcheck soundness at an extension field, in dial form.** The
premise is stated against the two deployment dials — base size `q` and
extension degree `k`: `v·d·2^λ ≤ q^k`. The base field alone (`k = 1`) caps λ at
`log₂(q/(v·d))`; every further unit of `k` adds `log₂ q` bits. Same theorem,
instantiated at the right field. -/
theorem sumcheck_lambda_secure_ext {Fq K : Type} [Field Fq] [Fintype Fq]
    [Field K] [Fintype K] [DecidableEq K] [Algebra Fq K]
    {v d lam : ℕ} {prover honest : ℕ → Polynomial K} {H S : K}
    (hProverDeg : ∀ i, i < v → (prover i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonestDeg : ∀ i, i < v → (honest i).degree < ((d + 1 : ℕ) : WithBot ℕ))
    (hHonest : ∀ (r : Fin v → K), ∀ i, i < v →
      (honest i).eval 0 + (honest i).eval 1 = scChain S honest (chalOf r) i)
    (hbig : v * d * 2 ^ lam ≤ Fintype.card Fq ^ Module.finrank Fq K) :
    uniformProb (Fin v → K) (AcceptsFalse prover honest H S) ≤ 1 / 2 ^ lam :=
  sumcheck_lambda_secure hProverDeg hHonestDeg hHonest
    (by rw [card_extension Fq K]; exact hbig)

/-! ## §4 The separation: base-field commitments, extension-field challenges

The prover's committed data is CHEAP — words over the base field `F_q`. The
verifier's randomness is SECURE — challenges in `F_{q^k}`. The two meet because
the base words embed `F_q`-linearly into the extension space, RS membership
survives the lift at the SAME degree bound, and the extension code is an
`F_{q^k}`-module — so a γ-fold with an extension challenge of base-committed
codewords is again a first-class extension-code claim. -/

section BaseExtension

variable {ι : Type*} {Fq K : Type*} [Field Fq] [Field K] [Algebra Fq K]

/-- The base-field embedding as a function embedding (fields ⇒ injective). -/
def algebraMapEmb (Fq K : Type*) [Field Fq] [Field K] [Algebra Fq K] : Fq ↪ K :=
  ⟨algebraMap Fq K, (algebraMap Fq K).injective⟩

/-- The evaluation domain, pushed into the extension field. -/
def extDomain (dom : ι ↪ Fq) : ι ↪ K := dom.trans (algebraMapEmb Fq K)

@[simp] theorem extDomain_apply (dom : ι ↪ Fq) (i : ι) :
    (extDomain (K := K) dom) i = algebraMap Fq K (dom i) := rfl

/-- Lift a base-committed word into the extension space. -/
def liftWord (f : ι → Fq) : ι → K := fun i => algebraMap Fq K (f i)

/-- The lift is `F_q`-LINEAR — the base-field commitment structure is preserved
verbatim inside the extension space. -/
def liftWordₗ : (ι → Fq) →ₗ[Fq] (ι → K) := (Algebra.linearMap Fq K).compLeft ι

@[simp] theorem liftWordₗ_apply (f : ι → Fq) (i : ι) :
    (liftWordₗ (K := K) f) i = algebraMap Fq K (f i) := rfl

theorem liftWordₗ_eq_liftWord (f : ι → Fq) :
    liftWordₗ (K := K) f = liftWord f := rfl

/-- Evaluation of a base-committed polynomial at an EXTENSION challenge, as an
`F_q`-linear map: the verifier's fold/evaluation operations act `F_q`-linearly
on the prover's cheap data. -/
noncomputable def evalExtₗ (r : K) : Polynomial Fq →ₗ[Fq] K :=
  (Polynomial.aeval r).toLinearMap

@[simp] theorem evalExtₗ_apply (r : K) (p : Polynomial Fq) :
    evalExtₗ r p = Polynomial.aeval r p := rfl

/-- Mapping the polynomial up and evaluating IS the base-linear evaluation:
`(p.map (algebraMap)).eval r = evalExtₗ r p`. -/
theorem eval_map_algebraMap (r : K) (p : Polynomial Fq) :
    (p.map (algebraMap Fq K)).eval r = evalExtₗ r p := by
  rw [evalExtₗ_apply, Polynomial.aeval_def, Polynomial.eval_map]

/-- **RS membership survives the lift at the same degree bound.** A
base-committed codeword of `RS[F_q, dom, d]` lifts to a codeword of
`RS[F_{q^k}, extDomain dom, d]`: map the witness polynomial along `algebraMap`;
its degree is unchanged (`Polynomial.degree_map`). -/
theorem liftWord_mem_reedSolomonCode {dom : ι ↪ Fq} {d : ℕ}
    {f : ι → Fq} (hf : f ∈ reedSolomonCode dom d) :
    liftWord (K := K) f ∈ reedSolomonCode (extDomain dom) d := by
  obtain ⟨p, hp, hpf⟩ := mem_reedSolomonCode_iff.mp hf
  refine mem_reedSolomonCode_iff.mpr ⟨p.map (algebraMap Fq K), ?_, fun i => ?_⟩
  · rwa [Polynomial.degree_map]
  · rw [extDomain_apply, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      liftWord, hpf i]

/-- **The γ-fold with an extension challenge stays a base-degree extension
codeword.** The separation, closed: base-committed codewords `f, g`, extension
challenge `γ ∈ F_{q^k}` — the folded word `f + γ·g` (computed in the extension,
where the challenge lives) is a codeword of the extension RS code at the SAME
degree bound. Pure `F_{q^k}`-module structure on top of the lift. -/
theorem fold_liftWord_mem {dom : ι ↪ Fq} {d : ℕ}
    {f g : ι → Fq} (γ : K)
    (hf : f ∈ reedSolomonCode dom d) (hg : g ∈ reedSolomonCode dom d) :
    liftWord (K := K) f + γ • liftWord (K := K) g
      ∈ reedSolomonCode (extDomain dom) d :=
  Submodule.add_mem _ (liftWord_mem_reedSolomonCode hf)
    (Submodule.smul_mem _ γ (liftWord_mem_reedSolomonCode hg))

end BaseExtension

/-! ## §5 Keystones: the concrete bit-counts, both poles BUILT

Satisfiable: real fields, real numerators, computed bit-counts (both directions
— quote the pessimistic number). Teeth: the small field genuinely secures
NOTHING (the bound is vacuous for every event, including certainty), and the
extension rescues the same numerator — the extension is load-bearing. -/

section Keystones

/-- **Satisfiable (base field, computed both ways):** at `|F| = 2³¹` and
numerator `v·d = 100`, the bound is worth between 24 and 25 bits. -/
theorem keystone_bits_base31 :
    (24 : ℝ) ≤ securityBits 100 (2 ^ 31) ∧ securityBits 100 (2 ^ 31) < 25 := by
  constructor
  · exact_mod_cast (le_securityBits_iff (by norm_num) (by positivity) 24).mpr
      (by norm_num)
  · exact_mod_cast (securityBits_lt_iff (by norm_num) (by positivity) 25).mpr
      (by norm_num)

/-- **Satisfiable (degree-4 extension):** the same numerator over
`(2³¹)⁴ = 2¹²⁴` is worth between 117 and 118 bits — the extension degree
multiplied the exponent. -/
theorem keystone_bits_ext4 :
    (117 : ℝ) ≤ securityBits 100 ((2 ^ 31 : ℝ) ^ 4) ∧
      securityBits 100 ((2 ^ 31 : ℝ) ^ 4) < 118 := by
  constructor
  · exact_mod_cast (le_securityBits_iff (by norm_num) (by positivity) 117).mpr
      (by norm_num)
  · exact_mod_cast (securityBits_lt_iff (by norm_num) (by positivity) 118).mpr
      (by norm_num)

/-- **The DEPLOYED prime, honestly:** BabyBear is `2013265921 = 15·2²⁷ + 1`,
NOT `2³¹`. At the real prime the base bound is still 24–25 bits… -/
theorem keystone_bits_babyBear :
    (24 : ℝ) ≤ securityBits 100 2013265921 ∧
      securityBits 100 2013265921 < 25 := by
  constructor
  · exact_mod_cast (le_securityBits_iff (by norm_num) (by norm_num) 24).mpr
      (by norm_num)
  · exact_mod_cast (securityBits_lt_iff (by norm_num) (by norm_num) 25).mpr
      (by norm_num)

/-- …but the degree-4 extension of the REAL BabyBear prime is worth only
116–117 bits: `p⁴ < 100·2¹¹⁷`. The round `2³¹` estimate promises 117; the
deployed prime does not deliver it. Quote the pessimistic number: 116. -/
theorem keystone_bits_babyBear_ext4 :
    (116 : ℝ) ≤ securityBits 100 ((2013265921 : ℝ) ^ 4) ∧
      securityBits 100 ((2013265921 : ℝ) ^ 4) < 117 := by
  constructor
  · exact_mod_cast (le_securityBits_iff (by norm_num) (by positivity) 116).mpr
      (by norm_num)
  · exact_mod_cast (securityBits_lt_iff (by norm_num) (by positivity) 117).mpr
      (by norm_num)

/-- **Teeth (negative bits):** at `|F| = 5`, `N = 100` the "security" is
NEGATIVE — `log₂(5/100) < 0`. -/
theorem keystone_smallField_negative_bits : securityBits 100 5 < 0 :=
  Real.logb_neg one_lt_two (by norm_num) (by norm_num)

/-- **Teeth (the bound is vacuous):** over F₅ at `v·d = 100` the sumcheck
"soundness bound" `v·d/|F| = 20 ≥ 1` holds for EVERY event — this proof uses
`uniformProb_le_one` and arithmetic only, no soundness reasoning whatsoever.
A bound that any adversary satisfies secures nothing. -/
theorem smallField_bound_vacuous (E : (Fin 100 → ZMod 5) → Prop) :
    uniformProb (Fin 100 → ZMod 5) E
      ≤ (100 : ℝ) * ((1 : ℝ) / Fintype.card (ZMod 5)) := by
  refine le_trans (uniformProb_le_one E) ?_
  rw [ZMod.card]
  norm_num

/-- **Teeth (certainty passes):** even the probability-ONE event — the
adversary succeeds on every challenge — satisfies the small-field bound. -/
theorem smallField_bound_allows_certainty :
    uniformProb (Fin 100 → ZMod 5) (fun _ => True) = 1 ∧
      uniformProb (Fin 100 → ZMod 5) (fun _ => True)
        ≤ (100 : ℝ) * ((1 : ℝ) / Fintype.card (ZMod 5)) := by
  refine ⟨?_, smallField_bound_vacuous _⟩
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial),
    Nat.card_eq_fintype_card]
  exact div_self (by positivity)

/-- **The extension is load-bearing:** the SAME numerator `N = 100` that is
vacuous over F₅ (`100/5 = 20 ≥ 1`) clears λ = 128 at extension degree 60
(`5⁶⁰ ≥ 100·2¹²⁸`). Nothing but the field changed. -/
theorem smallField_rescued_by_extension :
    (1 : ℝ) ≤ 100 / 5 ∧ (100 : ℝ) / 5 ^ 60 ≤ 1 / 2 ^ 128 := by
  constructor
  · norm_num
  · rw [err_le_inv_two_pow_iff (by positivity)]
    norm_num

end Keystones

/-! ### End-to-end: the λ-security theorem FIRES — base field vs. genuine extension

The same protocol data (prover `g̃ = X`, honest `g = 0`, false claim `H = 1`
against truth `S = 0`, one round, `d = 1`) instantiated twice: over F₅ the
premise caps λ at 2 (`2³ > 5`); over the genuine quadratic extension
`GF(25) = GaloisField 5 2` (finrank 2 over `ZMod 5`) the SAME theorems give
λ = 4. The accepting event is nonempty, so the secured bound constrains a real
event, not an empty one. -/

namespace SmallFieldKeystone

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- λ = 2 over the BASE field F₅: premise `1·1·2² = 4 ≤ 5`. -/
theorem sumcheck_secure_base :
    uniformProb (Fin 1 → ZMod 5)
      (AcceptsFalse (fun _ => (X : Polynomial (ZMod 5))) (fun _ => 0) 1 0)
      ≤ 1 / 2 ^ 2 := by
  refine sumcheck_lambda_secure (d := 1) ?_ ?_ ?_ ?_
  · intro i _
    rw [Polynomial.degree_X]
    decide
  · intro i _
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · intro r i hi
    interval_cases i
    simp [scChain]
  · rw [ZMod.card]
    norm_num

/-- The base field's CEILING: λ = 3 is not reachable over F₅ — the premise
`1·1·2³ ≤ 5` is FALSE. (The theorem goes silent here; going past λ = 2 requires
a bigger field.) -/
theorem smallField_lambda_ceiling : ¬ (1 * 1 * 2 ^ 3 ≤ Fintype.card (ZMod 5)) := by
  rw [ZMod.card]
  norm_num

noncomputable local instance : Fintype (GaloisField 5 2) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 5 2) := Classical.decEq _

/-- λ = 4 over the genuine quadratic EXTENSION GF(25): the dial-form premise
`1·1·2⁴ = 16 ≤ 5² = |ZMod 5|^finrank` fires through
`sumcheck_lambda_secure_ext` — same numerator, same theorems, two more bits,
bought entirely by the extension degree. -/
theorem sumcheck_secure_ext :
    uniformProb (Fin 1 → GaloisField 5 2)
      (AcceptsFalse (fun _ => (X : Polynomial (GaloisField 5 2))) (fun _ => 0) 1 0)
      ≤ 1 / 2 ^ 4 := by
  refine sumcheck_lambda_secure_ext (Fq := ZMod 5) (d := 1) ?_ ?_ ?_ ?_
  · intro i _
    rw [Polynomial.degree_X]
    exact_mod_cast one_lt_two
  · intro i _
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · intro r i hi
    interval_cases i
    simp [scChain]
  · rw [ZMod.card, GaloisField.finrank 5 (by norm_num)]
    norm_num

/-- The accepting event is NONEMPTY (`r = 0` accepts the false claim: the check
`g̃(0)+g̃(1) = 0+1 = H` passes and the final fold `g̃(0) = 0 = g(0)` matches the
truth) — the λ-secured bounds above constrain a real event. -/
theorem acceptsFalse_witness :
    AcceptsFalse (v := 1) (fun _ => (X : Polynomial (ZMod 5))) (fun _ => 0) 1 0
      (fun _ => 0) := by
  refine ⟨?_, ?_, by decide⟩
  · intro i hi
    interval_cases i
    simp [scChain]
  · simp [scChain, chalOf]

/-- The same witness over the EXTENSION field: the λ = 4 bound of
`sumcheck_secure_ext` also constrains a nonempty event. -/
theorem acceptsFalse_witness_ext :
    AcceptsFalse (v := 1) (fun _ => (X : Polynomial (GaloisField 5 2)))
      (fun _ => 0) 1 0 (fun _ => 0) := by
  refine ⟨?_, ?_, one_ne_zero⟩
  · intro i hi
    interval_cases i
    simp [scChain]
  · simp [scChain, chalOf]

end SmallFieldKeystone

/-! ## Audit note

The extension is genuinely load-bearing in the statements above, not decorative:
`smallField_bound_vacuous` derives the small-field "bound" from
`uniformProb_le_one` alone — no soundness content — and
`smallField_bound_allows_certainty` shows the probability-1 event satisfies it,
so F₅ at `N = 100` secures exactly nothing; `smallField_lambda_ceiling` is the
FALSE premise at the base field that `sumcheck_secure_ext`'s extension premise
(`16 ≤ 5²`) repairs with the same numerator and the same theorems. The
satisfiable pole is non-vacuous: `acceptsFalse_witness`/`…_ext` exhibit the
accepting event inhabited (the λ-bounds constrain a real event of probability
`1/5 > 0`), and every bit-count keystone is proved in BOTH directions (lower
AND upper bound), including the honest BabyBear degradation `116 ≤ bits < 117`
at degree 4 — the round `2³¹` estimate's 117th bit is NOT delivered by the
deployed prime.

`#print axioms` on every declaration in this file (`securityBits` through
`SmallFieldKeystone.acceptsFalse_witness_ext`): `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx`, no `native_decide`. -/

end Minidregg.Selvage
