/-
# `Selvage/MultilinearZeroTest.lean` — multilinear Schwartz–Zippel, and the zero-test

Selvage's Schwartz–Zippel is **univariate** everywhere it appears: `card_agreeFinset_lt`
(`Selvage/Sumcheck.lean`, the sumcheck's own core), `uniformProb_poly_eval_eq_zero_le`
(`Selvage/LogupStar.lean`), the γ-batch counts in `ConstrainedCode`/`AccSound`. The
MULTIVARIATE statement — for a multilinear function on `m` variables — was named as missing
vocabulary in two places and is proved here:

  `mle_zero_uniform_bound` : `f ≠ 0 → Pr_{z ← F^m}[f̂(z) = 0] ≤ m/|F|`

**The proof.** Induction on `m`, peeling the LSB coordinate with the landed
`mle_lsb_recurrence` (`Selvage/MultiplicativeMleTerminal.lean`): writing `A` for the
low half-table and `Δ` for the difference of the halves (`halfDiff`), the recurrence is
`f̂(x ∷ xs) = Â(xs) + x·Δ̂(xs)`, and

* if `Δ = 0` the value does not depend on the head at all, and `A ≠ 0`, so the induction
  hypothesis on `A` gives `m/|F| ≤ (m+1)/|F|`;
* if `Δ ≠ 0` the event is contained in `{Δ̂(xs) = 0} ∪ {Δ̂(xs) ≠ 0 ∧ Â(xs) + x·Δ̂(xs) = 0}`,
  the first bounded by the induction hypothesis on `Δ` and the second by ONE root in the
  head coordinate per fibre — `uniformProb_or_le` + `uniformProb_prod_le`, both landed.

No new probability toolkit is introduced: `uniformProb_equiv`, `uniformProb_or_le`,
`uniformProb_mono`, `uniformProb_prod_le`, `uniformProb_false` and `uniformProb_mem_finset`
are all cited from `Selvage/Depth.lean` and `Selvage/Sumcheck.lean`.

**What this unlocks.** `eqMle_zero_test`: combined with `Selvage/EqPolynomial.lean`'s
`eqMle_fold` (`Σ_b eq(z,b)·D(b) = D̂(z)`), the single-shot randomization becomes an actual
TEST — a nonzero defect word survives a random `z` with probability at most `m/|F|`. That is
the residual `Assurance/AirSumcheckQuadratic.lean` names as (ii), with strictly better
parameters than the γ-batching round it replaces (`m/|F|` against `(t−1)/|F|`, and `m` is
logarithmic in `t`).

**Teeth.** The bound is SATISFIABLE (`sz_event_nonempty`: a nonzero table whose MLE really
does vanish, so the bound constrains a nonempty event), TIGHT at `m = 1`
(`sz_tight_at_m_one`: the probability is exactly `1/5` over F₅), and the hypothesis is
NECESSARY (`sz_needs_nonzero`: dropping `f ≠ 0` makes the probability `1`, which exceeds the
bound — so the statement is refutable, not a tautology).
-/
import Selvage.MultiplicativeMleTerminal
import Selvage.EqPolynomial

namespace Minidregg.Selvage

/-! ## §1. Table linearity of the MLE, and the half-split -/

section Linearity

variable {F : Type*} [CommRing F] {m : ℕ}

/-- `mle` is linear in the TABLE (subtraction side) — the fact that lets the induction apply
its hypothesis to the DIFFERENCE of the two halves rather than to a difference of MLEs. -/
theorem mle_sub (f g : (Fin m → Bool) → F) (x : Fin m → F) :
    mle (fun b => f b - g b) x = mle f x - mle g x := by
  simp only [mle, sub_mul, Finset.sum_sub_distrib]

/-- The difference of the two half-tables: `Δ(b) = f(1 ∷ b) − f(0 ∷ b)`. -/
def halfDiff {m : ℕ} (f : (Fin (m + 1) → Bool) → F) : (Fin m → Bool) → F :=
  fun b => tableLsb true f b - tableLsb false f b

/-- **The LSB recurrence in half-table form**: `f̂(x ∷ xs) = Â(xs) + x·Δ̂(xs)` with `A` the
low half and `Δ` the half-difference — `mle_lsb_recurrence` with `mle_sub` folded in, so
both coefficients are MLEs of TABLES on `m` variables and the induction hypothesis applies
to each. -/
theorem mle_lsb_halves {F : Type*} [Field F] {m : ℕ} (f : (Fin (m + 1) → Bool) → F)
    (x : F) (xs : Fin m → F) :
    mle f (lsbCons x xs)
      = mle (tableLsb false f) xs + x * mle (halfDiff f) xs := by
  have h : mle (halfDiff f) xs
      = mle (tableLsb true f) xs - mle (tableLsb false f) xs :=
    mle_sub (tableLsb true f) (tableLsb false f) xs
  rw [mle_lsb_recurrence f x xs, h]
  rfl

/-- If both halves vanish, so does the table. -/
theorem table_eq_zero_of_halves {m : ℕ} {f : (Fin (m + 1) → Bool) → F}
    (h0 : tableLsb false f = 0) (hΔ : halfDiff f = 0) : f = 0 := by
  funext b
  have hb : b = lsbCons (b 0) (fun i => b i.succ) := (Fin.cons_self_tail b).symm
  have hlow : tableLsb false f (fun i => b i.succ) = 0 := by rw [h0]; rfl
  have hd : halfDiff f (fun i => b i.succ) = 0 := by rw [hΔ]; rfl
  have hhigh : tableLsb true f (fun i => b i.succ) = 0 := by
    have := hd
    rw [halfDiff, hlow, sub_zero] at this
    exact this
  rw [hb]
  cases hb0 : b 0
  · exact hlow
  · exact hhigh

end Linearity

/-! ## §2. The head/tail split of the challenge space -/

section Split

/-- Split a challenge vector into (tail, head) — the head is the LSB coordinate the
induction peels. Hand-rolled (Depth's house style) so `symm` reduces definitionally. -/
def tailHeadSplit (m : ℕ) (F : Type) : ((Fin m → F) × F) ≃ (Fin (m + 1) → F) where
  toFun y := lsbCons y.2 y.1
  invFun z := (fun i => z i.succ, z 0)
  left_inv _ := rfl
  right_inv z := Fin.cons_self_tail z

@[simp] theorem tailHeadSplit_apply (m : ℕ) (F : Type) (y : (Fin m → F) × F) :
    tailHeadSplit m F y = lsbCons y.2 y.1 := rfl

end Split

/-! ## §3. Multilinear Schwartz–Zippel -/

section SZ

variable {F : Type} [Field F] [Fintype F]

/-- Monotonicity of `·/c` in the numerator, spelled out so the induction's two slack steps
do not depend on a mathlib naming convention. -/
theorem div_le_div_num {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc)

/-- **Multilinear Schwartz–Zippel.** A NONZERO hypercube table's multilinear extension
vanishes at a uniformly random point of `F^m` with probability at most `m/|F|`.

The multivariate companion to `Selvage/Sumcheck.lean`'s univariate
`card_agreeFinset_lt`; the load-bearing new proof term of the degree-3 rung. -/
theorem mle_zero_uniform_bound : ∀ {m : ℕ} {f : (Fin m → Bool) → F}, f ≠ 0 →
    uniformProb (Fin m → F) (fun z => mle f z = 0) ≤ (m : ℝ) / Fintype.card F := by
  intro m
  induction m with
  | zero =>
    intro f hf
    have hd : f default ≠ 0 := fun h => hf (funext fun b => by
      rw [Subsingleton.elim b default, h]; rfl)
    have hval : ∀ z : Fin 0 → F, mle f z = f default := by
      intro z
      rw [mle,
        Fintype.sum_eq_single default fun b hb => absurd (Subsingleton.elim b default) hb,
        chiEval, Fintype.prod_empty, mul_one]
    rw [uniformProb_false fun z => by rw [hval z]; exact hd]
    positivity
  | succ n ih =>
    intro f hf
    set A : (Fin n → Bool) → F := tableLsb false f with hA
    set Δ : (Fin n → Bool) → F := halfDiff f with hΔdef
    -- Reshape the challenge space into (tail, head).
    rw [← uniformProb_equiv (tailHeadSplit n F) (fun z => mle f z = 0)]
    have hpred : ∀ y : (Fin n → F) × F,
        (mle f (tailHeadSplit n F y) = 0) ↔ (mle A y.1 + y.2 * mle Δ y.1 = 0) := by
      intro y
      rw [tailHeadSplit_apply, mle_lsb_halves]
    rw [uniformProb_congr hpred]
    by_cases hz : Δ = 0
    · -- The head does not matter: the value is `Â(xs)`, and `A ≠ 0`.
      have hAne : A ≠ 0 := fun h0 => hf (table_eq_zero_of_halves h0 hz)
      have hcongr : ∀ y : (Fin n → F) × F,
          (mle A y.1 + y.2 * mle Δ y.1 = 0) ↔ (mle A y.1 = 0) := by
        intro y
        rw [hz]
        simp only [mle, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      rw [uniformProb_congr hcongr]
      have hflip : uniformProb ((Fin n → F) × F) (fun y => mle A y.1 = 0)
          = uniformProb (F × (Fin n → F)) (fun w => mle A w.2 = 0) :=
        uniformProb_equiv (Equiv.prodComm (Fin n → F) F) (fun w => mle A w.2 = 0)
      rw [hflip]
      refine le_trans (uniformProb_prod_le (by positivity) fun _ => ih hAne) ?_
      exact div_le_div_num (by push_cast; linarith) (Nat.cast_nonneg _)
    · -- The head matters: one root per fibre, plus the tail event.
      have hstep : ∀ y : (Fin n → F) × F,
          (mle A y.1 + y.2 * mle Δ y.1 = 0) →
            (mle Δ y.1 = 0 ∨ (mle Δ y.1 ≠ 0 ∧ mle A y.1 + y.2 * mle Δ y.1 = 0)) := by
        intro y hy
        by_cases h : mle Δ y.1 = 0
        · exact Or.inl h
        · exact Or.inr ⟨h, hy⟩
      refine le_trans (uniformProb_mono hstep) ?_
      refine le_trans (uniformProb_or_le _ _) ?_
      have hfirst : uniformProb ((Fin n → F) × F) (fun y => mle Δ y.1 = 0)
          ≤ (n : ℝ) / Fintype.card F := by
        have hflip : uniformProb ((Fin n → F) × F) (fun y => mle Δ y.1 = 0)
            = uniformProb (F × (Fin n → F)) (fun w => mle Δ w.2 = 0) :=
          uniformProb_equiv (Equiv.prodComm (Fin n → F) F) (fun w => mle Δ w.2 = 0)
        rw [hflip]
        exact uniformProb_prod_le (by positivity) fun _ => ih hz
      have hsecond : uniformProb ((Fin n → F) × F)
          (fun y => mle Δ y.1 ≠ 0 ∧ mle A y.1 + y.2 * mle Δ y.1 = 0)
          ≤ 1 / Fintype.card F := by
        refine uniformProb_prod_le (by positivity) fun a => ?_
        by_cases ha : mle Δ a = 0
        · rw [uniformProb_false fun _ h => h.1 ha]
          positivity
        · refine le_trans (uniformProb_mono (q := fun x =>
            x ∈ ({-(mle A a) / mle Δ a} : Finset F)) fun x hx => ?_) ?_
          · refine Finset.mem_singleton.mpr ?_
            have h3 := congrArg (fun u => u - mle A a) hx.2
            simp only [add_sub_cancel_left, zero_sub] at h3
            rw [eq_div_iff ha]
            exact h3
          · rw [uniformProb_mem_finset, Finset.card_singleton]
            norm_num
      refine le_trans (add_le_add hfirst hsecond) ?_
      rw [← add_div]
      exact div_le_div_num (by push_cast; linarith) (Nat.cast_nonneg _)

/-- **The single-shot zero-test.** `Selvage/EqPolynomial.lean`'s `eqMle_fold` turns the
`eq`-weighted hypercube sum into `D̂(z)`; multilinear Schwartz–Zippel then says a NONZERO
defect word survives a uniformly random `z` with probability at most `m/|F|`.

This is `Assurance/AirSumcheckQuadratic.lean`'s named residual (ii) — the alternative to the
γ-batching round, with strictly better parameters (`m/|F|` against `(t−1)/|F|`, and `m` is
logarithmic in the number of constraints `t`). -/
theorem eqMle_zero_test {m : ℕ} {D : (Fin m → Bool) → F} (hD : D ≠ 0) :
    uniformProb (Fin m → F) (fun z => ∑ b, eqMle z (cubePt b) * D b = 0)
      ≤ (m : ℝ) / Fintype.card F := by
  refine le_trans (le_of_eq (uniformProb_congr fun z => ?_)) (mle_zero_uniform_bound hD)
  rw [eqMle_fold]

end SZ

/-! ## §4. Teeth over F₅

The three things that could be wrong with the theorem above and would not show up in a
build: the event could be EMPTY (a true bound about nothing), the bound could be
unreachable slack, and the hypothesis could be doing no work. -/

namespace ZeroTestExample

/-- The identity table on one bit: `D(0) = 0`, `D(1) = 1`, so `D̂(x) = x`. Nonzero. -/
def dId : (Fin 1 → Bool) → ZMod 5 := fun b => if b 0 then 1 else 0

theorem dId_ne_zero : dId ≠ 0 := fun h => by
  have : dId (fun _ => true) = 0 := by rw [h]; rfl
  exact absurd this (by decide)

/-- **TEETH — the event is NONEMPTY**: `D̂` really does vanish at `z = 0`, so
`mle_zero_uniform_bound` constrains a real event rather than an empty one. -/
theorem sz_event_nonempty : mle dId ![0] = 0 := by decide

/-- **TEETH — the extension is not identically zero**, so the vanishing above is a genuine
root and not a degenerate table. -/
theorem sz_not_identically_zero : mle dId ![3] ≠ 0 := by decide

/-- **TEETH — the bound is TIGHT at `m = 1`**: `D̂(z) = 0` at exactly one of the five points,
so the probability is exactly `1/5` and the general `m/|F|` cannot be improved. -/
theorem sz_tight_at_m_one :
    (Finset.univ.filter fun z : Fin 1 → ZMod 5 => mle dId z = 0).card = 1 := by decide

/-- **TEETH — the hypothesis is NECESSARY, i.e. the floor is REFUTABLE.** For the ZERO
table the MLE vanishes EVERYWHERE, so the probability is `1`, which exceeds the `1/5` the
theorem would otherwise assert. Dropping `f ≠ 0` makes the statement FALSE — it is not a
tautology that holds for free. -/
theorem sz_needs_nonzero :
    ∀ z : Fin 1 → ZMod 5, mle (0 : (Fin 1 → Bool) → ZMod 5) z = 0 := by decide

end ZeroTestExample

/-! ## §5. Axiom pins (house law) -/

/-- info: 'Minidregg.Selvage.mle_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_sub
/-- info: 'Minidregg.Selvage.mle_lsb_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_lsb_halves
/-- info: 'Minidregg.Selvage.table_eq_zero_of_halves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms table_eq_zero_of_halves
/-- info: 'Minidregg.Selvage.mle_zero_uniform_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_zero_uniform_bound
/-- info: 'Minidregg.Selvage.eqMle_zero_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eqMle_zero_test
/-- info: 'Minidregg.Selvage.ZeroTestExample.sz_event_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ZeroTestExample.sz_event_nonempty
/-- info: 'Minidregg.Selvage.ZeroTestExample.sz_tight_at_m_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ZeroTestExample.sz_tight_at_m_one
/-- info: 'Minidregg.Selvage.ZeroTestExample.sz_needs_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ZeroTestExample.sz_needs_nonzero

end Minidregg.Selvage
