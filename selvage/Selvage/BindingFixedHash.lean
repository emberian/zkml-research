/-
# Selvage.BindingFixedHash -- binding terms for a fixed, unkeyed hash

`BindingGame.SecureAt` bounds every code within a budget. For a fixed hash (minidregg's
cSHAKE256 is fixed by ruling), that quantifier includes the program that prints a known
collision. `secureAt_false_of_fixed_collision` makes that precise, and
`secureAt_false_of_compressing` derives it from compression alone: with constant programs in the
code class, `SecureAt … ε` is false for every `ε < 1`, so a theorem assuming it is vacuous.

The replacement for the fixed-hash case is `cert_and_of_collisionExtractor`. The binding term
is the probability that one named, deterministic reduction outputs a collision. That is the form
of `Compiler.Tower256AdditiveFriRawController.accepts_ideal_or_receiptCollision` and of the
succinct controller's `FinalCollision`. No adversary class is quantified, so nothing is
vacuous. The number is "how often this explicit map produces a cSHAKE collision", a
human-ignorance bound in Rogaway's sense (ePrint 2006/281).
-/
import Selvage.BindingGame

namespace Minidregg.Selvage.BindingGame

set_option autoImplicit false

variable {Ω Code Subject Digest : Type} [Fintype Ω]

/-! ## `SecureAt` is vacuous at a fixed hash -/

/-- A code whose run is a fixed colliding pair has advantage one. -/
theorem advantage_eq_one_of_constant_collision [Nonempty Ω]
    (commit : Subject → Digest) (x y : Subject) (hxy : x ≠ y) (hcol : commit x = commit y)
    (G : Experiment Ω Code (Subject × Subject)) (a : Code) (hconst : ∀ ω, G.run a ω = (x, y)) :
    G.advantage (fun _ => SameRootDifferentSubject commit) a = 1 := by
  unfold Experiment.advantage
  have hall : (fun ω => SameRootDifferentSubject commit (G.run a ω)) = fun _ => True := by
    funext ω
    rw [hconst ω]
    exact propext ⟨fun _ => trivial, fun _ => ⟨hcol, hxy⟩⟩
  rw [hall]
  exact prob_true

/-- **A fixed collision refutes `SecureAt` below one.** If the code class contains, within the
budget, a program that outputs one colliding pair, no `ε < 1` is a valid binding bound. -/
theorem secureAt_false_of_fixed_collision [Nonempty Ω]
    (commit : Subject → Digest) (x y : Subject) (hxy : x ≠ y) (hcol : commit x = commit y)
    (G : Experiment Ω Code (Subject × Subject)) (a : Code) (q t : ℕ)
    (hconst : ∀ ω, G.run a ω = (x, y)) (hbudget : G.Within a q t) {ε : ℝ} (hε : ε < 1) :
    ¬ G.SecureAt (fun _ => SameRootDifferentSubject commit) q t ε := by
  intro hsec
  have h := hsec a hbudget
  rw [advantage_eq_one_of_constant_collision commit x y hxy hcol G a hconst] at h
  linarith

/-- **Compression alone refutes it.** A hash into a smaller finite digest space has a collision
(pigeonhole), so if every constant pair program is admissible, `SecureAt … ε` fails for every
`ε < 1`. This is the fixed, unkeyed cSHAKE256 case: 2^256 digests, unboundedly many inputs. -/
theorem secureAt_false_of_compressing [Nonempty Ω] [Fintype Subject] [Fintype Digest]
    (commit : Subject → Digest) (hcomp : Fintype.card Digest < Fintype.card Subject)
    (G : Experiment Ω Code (Subject × Subject)) (q t : ℕ)
    (hconsts : ∀ s : Subject × Subject, ∃ a, (∀ ω, G.run a ω = s) ∧ G.Within a q t)
    {ε : ℝ} (hε : ε < 1) :
    ¬ G.SecureAt (fun _ => SameRootDifferentSubject commit) q t ε := by
  have hni : ¬ Function.Injective commit := fun hinj =>
    absurd (Fintype.card_le_of_injective commit hinj) (not_le.mpr hcomp)
  obtain ⟨x, y, hcol, hxy⟩ : ∃ x y, commit x = commit y ∧ x ≠ y := by
    by_contra hnone
    push Not at hnone
    exact hni fun x y h => hnone x y h
  obtain ⟨a, hconst, hbudget⟩ := hconsts (x, y)
  exact secureAt_false_of_fixed_collision commit x y hxy hcol G a q t hconst hbudget hε

/-! ## The fixed-hash replacement: a named collision extractor -/

/-- **Conjunction with the binding term charged to one explicit reduction.** `reduce` is a
deterministic map of the world (in deployment, of the accepted transcripts) and `Coll` the
collision predicate of the fixed hash. Whenever the two extracted subjects disagree under one
root, `reduce` outputs a collision, and the binding term is the probability that it does. No
adversary class appears. -/
theorem cert_and_of_collisionExtractor [Nonempty Ω] {Witness : Type}
    (commit : Ω → Subject → Digest) (root : Ω → Digest)
    (w₁ w₂ : Ω → Subject) (V₁ V₂ : Ω → Prop) (P₁ P₂ : Subject → Prop) (ε₁ ε₂ : ℝ)
    (Coll : Ω → Witness → Prop) (reduce : Ω → Witness)
    (h₁ : prob (fun ω => V₁ ω ∧ ¬ (commit ω (w₁ ω) = root ω ∧ P₁ (w₁ ω))) ≤ ε₁)
    (h₂ : prob (fun ω => V₂ ω ∧ ¬ (commit ω (w₂ ω) = root ω ∧ P₂ (w₂ ω))) ≤ ε₂)
    (hext : ∀ ω, SameRootDifferentSubject (commit ω) (w₁ ω, w₂ ω) → Coll ω (reduce ω)) :
    prob (fun ω => V₁ ω ∧ V₂ ω ∧
      ¬ (commit ω (w₁ ω) = root ω ∧ P₁ (w₁ ω) ∧ P₂ (w₁ ω)))
      ≤ min 1 (ε₁ + ε₂ + prob (fun ω => Coll ω (reduce ω))) :=
  cert_and commit root w₁ w₂ V₁ V₂ P₁ P₂ ε₁ ε₂ _ h₁ h₂ (prob_mono hext)

/-! ## Teeth -/

/-- The Keystone constant-hash game is refuted at every `ε < 1`, not only at zero. -/
theorem keystone_refuted_below_one :
    ¬ Keystone.pairGame.SecureAt
      (fun _ => SameRootDifferentSubject Keystone.constantHash) 2 1 (1 / 2) :=
  secureAt_false_of_fixed_collision Keystone.constantHash false true (by decide) rfl
    Keystone.pairGame () 2 1 (fun _ => rfl) Keystone.pairGame_inhabited (by norm_num)

/-- The extractor bound is not vacuous: at the identity hash no collision exists, so its
binding term is zero; at the constant hash the flat extractor `(w₁, w₂)` collides on every
world, so its binding term is one. -/
theorem extractor_term_identity_zero (w₁ w₂ : Unit → Bool) :
    prob (fun ω => SameRootDifferentSubject (fun b : Bool => b) (w₁ ω, w₂ ω)) = 0 := by
  have h : (fun ω => SameRootDifferentSubject (fun b : Bool => b) (w₁ ω, w₂ ω))
      = fun _ => False := by
    funext ω
    exact propext ⟨fun h => h.2 h.1, False.elim⟩
  rw [h]
  simp [prob]

theorem extractor_term_constant_one :
    prob (fun _ : Unit => SameRootDifferentSubject Keystone.constantHash (false, true)) = 1 := by
  have h : (fun _ : Unit => SameRootDifferentSubject Keystone.constantHash (false, true))
      = fun _ => True := by
    funext ω
    exact propext ⟨fun _ => trivial, fun _ => ⟨rfl, by decide⟩⟩
  rw [h]
  exact prob_true

/-- info: 'Minidregg.Selvage.BindingGame.secureAt_false_of_compressing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms secureAt_false_of_compressing
/-- info: 'Minidregg.Selvage.BindingGame.cert_and_of_collisionExtractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cert_and_of_collisionExtractor
/-- info: 'Minidregg.Selvage.BindingGame.keystone_refuted_below_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keystone_refuted_below_one

end Minidregg.Selvage.BindingGame
