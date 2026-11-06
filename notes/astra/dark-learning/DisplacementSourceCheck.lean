import Mathlib
namespace Minidregg.Selvage
noncomputable def uniformProb (C : Type) [Fintype C] (p : C → Prop) : ℝ :=
  (Nat.card {c : C // p c} : ℝ) / (Fintype.card C : ℝ)

section UniformProb

variable {C : Type} [Fintype C]

/-- The counted set, as a `Nat.card` inequality against the whole space. -/
lemma card_le_of_subtype (p : C → Prop) :
    (Nat.card {c : C // p c} : ℝ) ≤ (Fintype.card C : ℝ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_subtype_le p

lemma uniformProb_nonneg (p : C → Prop) : 0 ≤ uniformProb C p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma uniformProb_le_one (p : C → Prop) : uniformProb C p ≤ 1 := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card C) with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hpos
    calc (Nat.card {c : C // p c} : ℝ) / (Fintype.card C : ℝ)
        ≤ (Fintype.card C : ℝ) / (Fintype.card C : ℝ) := by
          gcongr
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_subtype_le p
      _ = 1 := div_self (ne_of_gt hpos')

lemma uniformProb_congr {p q : C → Prop} (h : ∀ c, p c ↔ q c) :
    uniformProb C p = uniformProb C q := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeEquivRight h)]

lemma uniformProb_false {p : C → Prop} (h : ∀ c, ¬ p c) :
    uniformProb C p = 0 := by
  unfold uniformProb
  have : IsEmpty {c : C // p c} := ⟨fun x => h x.1 x.2⟩
  rw [Nat.card_of_isEmpty]
  simp

/-- Monotone counting: pointwise implication gives a card inequality. -/
lemma card_mono_of_imp {p q : C → Prop} (h : ∀ c, p c → q c) :
    (Nat.card {c : C // p c} : ℝ) ≤ (Nat.card {c : C // q c} : ℝ) := by
  classical
  have : Nat.card {c : C // p c} ≤ Nat.card {c : C // q c} :=
    Nat.card_mono (Set.toFinite {c | q c}) (fun c hc => h c hc)
  exact_mod_cast this

lemma uniformProb_mono {p q : C → Prop} (h : ∀ c, p c → q c) :
    uniformProb C p ≤ uniformProb C q := by
  classical
  unfold uniformProb
  rcases Nat.eq_zero_or_pos (Fintype.card C) with h0 | hpos
  · simp [h0]
  · have hpos' : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast hpos
    gcongr
    · exact Nat.card_mono (Set.toFinite {c | q c}) (fun c hc => h c hc)

/-- Counting form of `Pr[p ∨ q] ≤ Pr[p] + Pr[q]`. -/
lemma uniformProb_or_le (p q : C → Prop) :
    uniformProb C (fun c => p c ∨ q c) ≤ uniformProb C p + uniformProb C q := by
  classical
  unfold uniformProb
  rw [← add_div]
  have hle : Nat.card {c : C // p c ∨ q c} ≤
      Nat.card {c : C // p c} + Nat.card {c : C // q c} := by
    have hunion : {c : C | p c ∨ q c} = {c : C | p c} ∪ {c : C | q c} := rfl
    calc Nat.card {c : C // p c ∨ q c}
        = ({c : C | p c} ∪ {c : C | q c} : Set C).ncard := by
          rw [← Nat.card_coe_set_eq, ← hunion]; rfl
      _ ≤ ({c : C | p c} : Set C).ncard + ({c : C | q c} : Set C).ncard :=
          Set.ncard_union_le _ _
      _ = Nat.card {c : C // p c} + Nat.card {c : C // q c} := by
          rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]; rfl
  gcongr
  exact_mod_cast hle


end UniformProb
end Minidregg.Selvage
namespace Minidregg.Selvage

open Finset

/-! ## 0. Counting toolkit

Three `uniformProb` facts the audit layer needs and `Selvage/Depth.lean` does
not yet carry: the indicator-sum rendering (the bridge between the counting
probability and the finite averages the supermartingale argument takes),
independence on a product coin space, and the certain event. -/

section Counting

variable {Ω : Type} [Fintype Ω]

/-- `Pr[p]` as an average of indicators. The bridge from `uniformProb`'s
`Nat.card`-over-`Fintype.card` counting to `Finset.sum`-based averaging. -/
lemma uniformProb_eq_avg_indicator (p : Ω → Prop) [DecidablePred p] :
    uniformProb Ω p = (∑ ω : Ω, if p ω then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := by
  classical
  unfold uniformProb
  congr 1
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The certain event has probability one on a nonempty space. -/
lemma uniformProb_true [Nonempty Ω] : uniformProb Ω (fun _ => True) = 1 := by
  classical
  unfold uniformProb
  have hcard : Nat.card {_ω : Ω // True} = Fintype.card Ω := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  rw [hcard]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-- **Independence on a product coin space.** An event depending only on the
first coordinate and one depending only on the second have product
probability. This is what "the beacon's randomness and the checker's coins are
drawn independently" MEANS in the counting model — and it is the only place the
audit layer uses independence at all (the adversary is never assumed
independent of anything). -/
lemma uniformProb_prod_indep {A B : Type} [Fintype A] [Fintype B]
    (p : A → Prop) (q : B → Prop) :
    uniformProb (A × B) (fun x => p x.1 ∧ q x.2)
      = uniformProb A p * uniformProb B q := by
  classical
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd (p := p) (q := q)), Nat.card_prod,
    Fintype.card_prod]
  push_cast
  ring

end Counting

/-! ## 1. The composed error budget

Three parameters, three legs, one derived detection rate `q`. Every field is
named and carried; there is no `negl` in this file. -/

/-- The audit's parameters. `p` is the NOMINAL selection rate — the rate the
public rule `Sel` advertises — and the three `ε`s are the three ways the
nominal rate fails to be a detection rate. -/
structure AuditParams where
  /-- Nominal audit rate advertised by the public selection rule `Sel`. -/
  p : ℝ
  /-- Checker error, CONDITIONAL on the audit firing: the probability that a
  fired checker fails to reject a corrupt round it was handed honestly.
  Instantiates as a cryptographic soundness error or as a statistical
  trace-test error; the statement privileges neither. -/
  εchk : ℝ
  /-- Commitment binding error: the probability that the audited object is not
  the object the round actually ran. Priced as a term, never folded away. -/
  εbind : ℝ
  /-- Beacon grindability: the ADDITIVE shortfall of the worst-case realized
  fire probability below the nominal rate, over histories as they stand at
  beacon-emission time. See `BeaconLeg`. -/
  εbeacon : ℝ
  p_nonneg : 0 ≤ p
  p_le_one : p ≤ 1
  εchk_nonneg : 0 ≤ εchk
  /-- A checker with `εchk > 1` is not a checker; the bound would read as a
  spurious gain from a doubly-wrong checker. -/
  εchk_le_one : εchk ≤ 1
  εbind_nonneg : 0 ≤ εbind
  εbeacon_nonneg : 0 ≤ εbeacon

namespace AuditParams

/-- The composed per-round detection rate `q = p(1 − ε_chk) − ε_bind − ε_beacon`.
May be zero or negative — and IS, for a beacon the prover controls
(`grind_honest_q_eq_zero`) or a checker that fails open (`failOpen_no_legs`).
At `q ≤ 0` every statement below is honestly silent, which is the correct
verdict, not a defect. -/
def q (A : AuditParams) : ℝ := A.p * (1 - A.εchk) - A.εbind - A.εbeacon

/-- Detection never beats selection: `q ≤ p`. -/
theorem q_le_p (A : AuditParams) : A.q ≤ A.p := by
  have := A.p_nonneg; have := A.εchk_nonneg; have := A.εbind_nonneg
  have := A.εbeacon_nonneg
  unfold q; nlinarith

theorem q_le_one (A : AuditParams) : A.q ≤ 1 := le_trans A.q_le_p A.p_le_one

end AuditParams

/-! ## 2. The round mechanism

A `Round` is the whole public process, rendered as Boolean decisions of the
history. Histories are coin lists **most recent first**, so extending a history
`h` by this round's coin `ω` is `ω :: h`.

The key modelling commitment, and the one that makes the sequential theorem
about a fully adaptive adversary: `corrupt : List Ω → Bool` takes the history
and NOT the current round's coin. The adversary may condition its cheating on
every past beacon, every past verdict and every past alarm — that is what an
arbitrary function of the history is — but not on the coin of the round it is
cheating in, because the commitment is posted before the beacon emits. That is
exactly `F_{t−1}`-measurability, enforced by the type rather than assumed. -/

/-- The commit-then-audit round, as Boolean decisions of the public history.
`Ω` is the round's whole randomness: the beacon draw together with whatever
coins the checker consumes. -/
structure Round (Ω : Type) where
  /-- The adversary's cheating rule: is this round corrupt? An ARBITRARY
  function of the history — full adaptivity — and, by not taking `ω`, a rule
  fixed before this round's beacon emits. -/
  corrupt : List Ω → Bool
  /-- `Sel(ρ_t, t)`: did the audit fire? -/
  fires : List Ω → Ω → Bool
  /-- Did the round raise an alarm? -/
  alarms : List Ω → Ω → Bool
  /-- Did the checker render a WRONG verdict — accept a corrupt round it was
  handed honestly? Priced by `ε_chk`. -/
  chkErr : List Ω → Ω → Bool
  /-- Did the checker fail to render a verdict at all — crash, time out, refuse
  to parse? Priced by NOTHING; it must force an alarm (`FailClosed`). -/
  chkAbort : List Ω → Ω → Bool
  /-- Was the commitment equivocated — is the audited object not the object the
  round ran? Priced by `ε_bind`. -/
  bindBreak : List Ω → Ω → Bool

namespace Round

variable {Ω : Type} [Fintype Ω] {R : Round Ω} {A : AuditParams}

/-! ### 2.1 The three legs -/

/-- **The `ε_beacon` leg, and the definition of `ε_beacon`.** For EVERY history,
the realized fire probability is within `ε_beacon` of the nominal rate. This is
the spec's `ε_beacon := max_t (p − ess inf Pr[Sel(ρ_t,t) = 1 | F_{t−1}, c_t])`
rendered as a hypothesis: the essential infimum is the `∀ h`, and the option
set is the one available **at beacon-emission time**, since `h` ranges over
every history the adversary can have driven the process into, including ones a
commitment-time quantification would have closed out early (the Gaži et al.
cutoff lesson — later events retroactively promote candidates, so closing the
option set at commitment under-counts).

Not to be confused with the multiplicative `(t + n)` try-count factor of
`Selvage/LightClientGrinding.lean`: that prices a challenge-oracle adversary on
the CHECKER side of the FS/ROM model. Here the degradation is additive and
lands on the SELECTION probability. `BeaconRefutation` below shows the term is
load-bearing, not decoration. -/
def BeaconLeg (A : AuditParams) (R : Round Ω) : Prop :=
  ∀ h : List Ω, A.p - A.εbeacon ≤ uniformProb Ω (fun ω => R.fires h ω)

/-- **The `ε_chk` leg.** Conditional on the audit firing, the checker errs on a
corrupt round with probability at most `ε_chk` — written in the product form
`Pr[fire ∧ chkErr] ≤ Pr[fire] · ε_chk`, which is what independence of the
checker's coins from the beacon's gives (`chkLeg_of_product`). Section 6
instantiates it from the landed light-client bound. -/
def ChkLeg (A : AuditParams) (R : Round Ω) : Prop :=
  ∀ h : List Ω, R.corrupt h = true →
    uniformProb Ω (fun ω => R.fires h ω ∧ R.chkErr h ω)
      ≤ uniformProb Ω (fun ω => R.fires h ω) * A.εchk

/-- **The `ε_bind` leg.** The commitment is equivocated with probability at
most `ε_bind`. Open in the light-client vocabulary as `[ACC-extract]`; named
here so that a deployment cannot forget it exists. -/
def BindLeg (A : AuditParams) (R : Round Ω) : Prop :=
  ∀ h : List Ω, uniformProb Ω (fun ω => R.bindBreak h ω) ≤ A.εbind

/-- **The miss decomposition.** A fired audit of a corrupt round that does not
alarm is a checker error or a binding break — there is no third way to miss.
This is the leg that a fail-open checker breaks (`failOpen_no_legs`), and the
one `missDecomp_of_failClosed` discharges from fail-closedness plus
non-aborting soundness. -/
def MissDecomp (R : Round Ω) : Prop :=
  ∀ (h : List Ω) (ω : Ω), R.corrupt h = true → R.fires h ω = true →
    R.alarms h ω = false → R.chkErr h ω = true ∨ R.bindBreak h ω = true

/-- The four hypotheses of the per-round detection lemma, bundled. -/
structure DetectionLegs (A : AuditParams) (R : Round Ω) : Prop where
  beacon : BeaconLeg A R
  chk : ChkLeg A R
  bind : BindLeg A R
  miss : MissDecomp R

/-! ### 2.2 Fail-closed

Not in any paper on this subject; taken from our own wound-classes. A verdict
that cannot be rendered must not RENDER AS the expected verdict. -/

/-- **Fail-closed.** A fired audit whose checker cannot render a verdict
alarms. -/
def FailClosed (R : Round Ω) : Prop :=
  ∀ (h : List Ω) (ω : Ω), R.fires h ω = true → R.chkAbort h ω = true →
    R.alarms h ω = true

/-- **Fail-open** — the wound. The checker's failure to render a verdict reads
as acceptance. `failOpen_no_legs` shows this is not a hygiene preference: it
makes `DetectionLegs` uninhabitable at any positive `q`. -/
def FailOpen (R : Round Ω) : Prop :=
  ∀ (h : List Ω) (ω : Ω), R.chkAbort h ω = true → R.alarms h ω = false

omit [Fintype Ω] in
/-- Fail-closedness discharges the miss decomposition from the checker's
soundness ON THE RUNS WHERE IT ANSWERS. Without it the `∀ ω` in `MissDecomp`
ranges over aborting runs too, and `ε_chk` would have to absorb them — which is
precisely the substitution that turns a refusal into a verdict. -/
theorem missDecomp_of_failClosed (hfc : FailClosed R)
    (hsound : ∀ (h : List Ω) (ω : Ω), R.corrupt h = true → R.fires h ω = true →
      R.chkAbort h ω = false → R.alarms h ω = false →
      R.chkErr h ω = true ∨ R.bindBreak h ω = true) :
    MissDecomp R := by
  intro h ω hc hf hno
  by_cases hab : R.chkAbort h ω = true
  · exact absurd (hfc h ω hf hab) (by simp [hno])
  · exact hsound h ω hc hf (by simpa using hab) hno

/-! ### 2.3 The per-round detection lemma -/

/-- **Per-round detection.** For EVERY history, a corrupt round alarms with
probability at least `q = p(1 − ε_chk) − ε_bind − ε_beacon`.

Proof shape: `Pr[fire] ≤ Pr[fire ∧ alarm] + Pr[fire ∧ ¬alarm]`; the first term
is at most `Pr[alarm]`, the second is at most `Pr[fire]·ε_chk + ε_bind` by the
miss decomposition; so `Pr[alarm] ≥ Pr[fire](1 − ε_chk) − ε_bind`, and
`Pr[fire] ≥ p − ε_beacon` closes it. The last step is where the composed budget
is slightly generous to the adversary: the sharp form is
`(p − ε_beacon)(1 − ε_chk) − ε_bind`, and `q` drops the `ε_beacon·ε_chk`
cross-term. -/
theorem detect [Nonempty Ω] (hL : DetectionLegs A R) {h : List Ω}
    (hc : R.corrupt h = true) :
    A.q ≤ uniformProb Ω (fun ω => R.alarms h ω) := by
  classical
  set P := uniformProb Ω (fun ω => R.fires h ω) with hP
  set Al := uniformProb Ω (fun ω => R.alarms h ω) with hAl
  -- fire splits into (fire ∧ alarm) ∨ (fire ∧ ¬alarm)
  have hsplit : P ≤ uniformProb Ω (fun ω => R.fires h ω ∧ R.alarms h ω)
      + uniformProb Ω (fun ω => R.fires h ω ∧ ¬ (R.alarms h ω = true)) := by
    refine le_trans (uniformProb_mono (q := fun ω =>
      (R.fires h ω ∧ R.alarms h ω) ∨ (R.fires h ω ∧ ¬ (R.alarms h ω = true)))
      (fun ω hω => ?_)) (uniformProb_or_le _ _)
    by_cases ha : R.alarms h ω = true
    · exact Or.inl ⟨hω, ha⟩
    · exact Or.inr ⟨hω, ha⟩
  have hhit : uniformProb Ω (fun ω => R.fires h ω ∧ R.alarms h ω) ≤ Al :=
    uniformProb_mono fun _ hω => hω.2
  -- the miss is a checker error or a binding break
  have hmiss : uniformProb Ω (fun ω => R.fires h ω ∧ ¬ (R.alarms h ω = true))
      ≤ uniformProb Ω (fun ω => R.fires h ω ∧ R.chkErr h ω)
        + uniformProb Ω (fun ω => R.bindBreak h ω) := by
    refine le_trans (uniformProb_mono (q := fun ω =>
      (R.fires h ω ∧ R.chkErr h ω) ∨ R.bindBreak h ω) (fun ω hω => ?_))
      (uniformProb_or_le _ _)
    rcases hL.miss h ω hc hω.1 (by simpa using hω.2) with he | hb
    · exact Or.inl ⟨hω.1, he⟩
    · exact Or.inr hb
  have hchk := hL.chk h hc
  have hbind := hL.bind h
  have hbeacon := hL.beacon h
  have hP1 : P ≤ 1 := uniformProb_le_one _
  have hchk1 := A.εchk_le_one
  have hchk0 := A.εchk_nonneg
  have hbe0 := A.εbeacon_nonneg
  -- P ≤ Al + P·εchk + εbind, and P ≥ p − εbeacon
  have hkey : P ≤ Al + P * A.εchk + A.εbind := by linarith
  have hmul : (A.p - A.εbeacon) * (1 - A.εchk) ≤ P * (1 - A.εchk) :=
    mul_le_mul_of_nonneg_right hbeacon (by linarith)
  show A.q ≤ Al
  unfold AuditParams.q
  nlinarith

end Round

/-! ## 3. Finite-horizon expectation

The sequential theorem needs expectations over independent uniform draws, one
per round. `expOver n f h` averages `f` over the `n` further coins drawn after
the history `h` — a plain recursive average, so the tower property is
DEFINITIONAL and no measure theory enters. -/

/-- `E[f(H_{|h|+n}) | H_{|h|} = h]` under `n` further independent uniform draws
from `Ω`, most recent first. -/
noncomputable def expOver (Ω : Type) [Fintype Ω] : ℕ → (List Ω → ℝ) → List Ω → ℝ
  | 0, f, h => f h
  | n + 1, f, h => (∑ ω : Ω, expOver Ω n f (ω :: h)) / (Fintype.card Ω : ℝ)

namespace expOver

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

private lemma card_pos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- The average of a constant is the constant. -/
private lemma avg_const (a : ℝ) : (∑ _ω : Ω, a) / (Fintype.card Ω : ℝ) = a := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

private lemma avg_le {f : Ω → ℝ} {c : ℝ} (h : ∀ ω, f ω ≤ c) :
    (∑ ω : Ω, f ω) / (Fintype.card Ω : ℝ) ≤ c := by
  rw [div_le_iff₀ card_pos]
  calc ∑ ω : Ω, f ω ≤ ∑ _ω : Ω, c := Finset.sum_le_sum fun ω _ => h ω
    _ = (Fintype.card Ω : ℝ) * c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = c * (Fintype.card Ω : ℝ) := mul_comm _ _

/-- The average of `a − 1{p}` is `a − Pr[p]`: the one computation the
supermartingale step needs. -/
private lemma avg_sub_indicator (a : ℝ) (p : Ω → Prop) [DecidablePred p] :
    (∑ ω : Ω, (a - if p ω then (1 : ℝ) else 0)) / (Fintype.card Ω : ℝ)
      = a - uniformProb Ω p := by
  rw [Finset.sum_sub_distrib, sub_div, avg_const, uniformProb_eq_avg_indicator]

omit [Nonempty Ω] in
@[simp] lemma zero (f : List Ω → ℝ) (h : List Ω) : expOver Ω 0 f h = f h := rfl

omit [Nonempty Ω] in
lemma succ (n : ℕ) (f : List Ω → ℝ) (h : List Ω) :
    expOver Ω (n + 1) f h
      = (∑ ω : Ω, expOver Ω n f (ω :: h)) / (Fintype.card Ω : ℝ) := rfl

lemma const (a : ℝ) : ∀ (n : ℕ) (h : List Ω), expOver Ω n (fun _ => a) h = a := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih => intro h; rw [succ]; simp only [ih]; exact avg_const a

lemma mono {f g : List Ω → ℝ} (hfg : ∀ h, f h ≤ g h) :
    ∀ (n : ℕ) (h : List Ω), expOver Ω n f h ≤ expOver Ω n g h := by
  intro n
  induction n with
  | zero => intro h; exact hfg h
  | succ n ih =>
    intro h
    rw [succ, succ, div_le_div_iff_of_pos_right card_pos]
    exact Finset.sum_le_sum fun ω _ => ih (ω :: h)

omit [Nonempty Ω] in
lemma smul (c : ℝ) (f : List Ω → ℝ) :
    ∀ (n : ℕ) (h : List Ω),
      expOver Ω n (fun x => c * f x) h = c * expOver Ω n f h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [succ, succ]
    simp only [ih]
    rw [← Finset.mul_sum, mul_div_assoc]

omit [Nonempty Ω] in
lemma sub (f g : List Ω → ℝ) :
    ∀ (n : ℕ) (h : List Ω),
      expOver Ω n (fun x => f x - g x) h = expOver Ω n f h - expOver Ω n g h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [succ, succ, succ]
    simp only [ih]
    rw [Finset.sum_sub_distrib, sub_div]

/-- The history grows by exactly one round per draw. Used by the `ε_beacon`
refutation, where the adversary cheats every round and is never caught. -/
lemma length : ∀ (n : ℕ) (h : List Ω),
    expOver Ω n (fun x => (x.length : ℝ)) h = (h.length : ℝ) + n := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    rw [succ]
    simp only [ih, List.length_cons]
    push_cast
    rw [avg_const]
    ring

/-- **Finite-horizon optional stopping.** A one-step supermartingale
inequality — holding at EVERY history, which is what makes the adversary fully
adaptive — dominates the whole horizon. The tower property is the definitional
unfolding of `expOver`; the induction is the entire content. -/
theorem le_of_step {Φ : List Ω → ℝ}
    (hstep : ∀ h, (∑ ω : Ω, Φ (ω :: h)) / (Fintype.card Ω : ℝ) ≤ Φ h) :
    ∀ (n : ℕ) (h : List Ω), expOver Ω n Φ h ≤ Φ h := by
  intro n
  induction n with
  | zero => intro h; exact le_refl _
  | succ n ih =>
    intro h
    refine le_trans ?_ (hstep h)
    rw [succ, div_le_div_iff_of_pos_right card_pos]
    exact Finset.sum_le_sum fun ω _ => ih (ω :: h)

end expOver

/-! ## 4. The sequential theorem

The run's two observables, the supermartingale, and optional stopping. -/

namespace Round

variable {Ω : Type} [Fintype Ω]

/-- `1{τ ≤ t}` — has an alarm fired at or before the head of the history? -/
def stopped (R : Round Ω) : List Ω → Bool
  | [] => false
  | ω :: h => R.stopped h || R.alarms h ω

/-- `C_{t∧τ}` — corrupt rounds up to and including the first alarm. A corrupt
round that alarms still COUNTS: it leaked its payload before it was caught,
which is exactly why the residual channel is `1/q` rounds wide and not zero.

Note that `count (ω :: h)` does not read `ω`: whether the round is corrupt was
decided before its beacon emitted. -/
def count (R : Round Ω) : List Ω → ℕ
  | [] => 0
  | _ :: h =>
      if R.stopped h then R.count h
      else if R.corrupt h then R.count h + 1 else R.count h

/-- The supermartingale `M_t := q·C_{t∧τ} − 1{τ ≤ t}`. -/
noncomputable def mart (R : Round Ω) (q : ℝ) (h : List Ω) : ℝ :=
  q * (R.count h : ℝ) - (if R.stopped h = true then (1 : ℝ) else 0)

omit [Fintype Ω] in
@[simp] lemma mart_nil (R : Round Ω) (q : ℝ) : R.mart q [] = 0 := by
  simp [mart, count, stopped]

/-- **The supermartingale step.** At every history, one more uniform draw does
not increase `M`. Three cases, and each is the process saying something
different: already stopped (`M` is frozen), honest round (`M` can only fall by
an alarm), corrupt round (`M` gains `q` from the count and loses at least `q`
to the detection probability — this is the only place `detect`'s conclusion is
consumed). -/
theorem mart_step [Nonempty Ω] {R : Round Ω} {q : ℝ}
    (hdet : ∀ h : List Ω, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun ω => R.alarms h ω))
    (h : List Ω) :
    (∑ ω : Ω, R.mart q (ω :: h)) / (Fintype.card Ω : ℝ) ≤ R.mart q h := by
  classical
  by_cases hs : R.stopped h = true
  · -- already stopped: M is frozen, with equality
    have hval : ∀ ω : Ω, R.mart q (ω :: h) = R.mart q h := by
      intro ω
      have hs' : R.stopped (ω :: h) = true := by simp [stopped, hs]
      simp [mart, count, stopped, hs]
    simp only [hval]
    exact le_of_eq (expOver.avg_const _)
  · have hs' : R.stopped h = false := by simpa using hs
    have hstopcons : ∀ ω : Ω, R.stopped (ω :: h) = R.alarms h ω := by
      intro ω; simp [stopped, hs']
    by_cases hc : R.corrupt h = true
    · -- corrupt round: the count gains q, detection takes at least q back
      have hval : ∀ ω : Ω, R.mart q (ω :: h)
          = (q * ((R.count h : ℝ) + 1)) - (if R.alarms h ω = true then (1 : ℝ) else 0) := by
        intro ω
        have hcnt : R.count (ω :: h) = R.count h + 1 := by
          show (if R.stopped h then R.count h
            else if R.corrupt h then R.count h + 1 else R.count h) = _
          rw [if_neg (by simpa using hs'), if_pos (by simpa using hc)]
        rw [mart, hcnt, hstopcons ω]
        push_cast; ring
      simp only [hval]
      rw [expOver.avg_sub_indicator]
      have := hdet h hs' hc
      rw [mart, hs']
      simp only [Bool.false_eq_true, if_false]
      linarith
    · -- honest round: the count is unchanged, an alarm can only help
      have hval : ∀ ω : Ω, R.mart q (ω :: h)
          = (q * (R.count h : ℝ)) - (if R.alarms h ω = true then (1 : ℝ) else 0) := by
        intro ω
        have hcnt : R.count (ω :: h) = R.count h := by
          show (if R.stopped h then R.count h
            else if R.corrupt h then R.count h + 1 else R.count h) = _
          rw [if_neg (by simpa using hs'), if_neg (by simpa using hc)]
        rw [mart, hcnt, hstopcons ω]
      simp only [hval]
      rw [expOver.avg_sub_indicator]
      have hnn := uniformProb_nonneg (C := Ω) (fun ω => R.alarms h ω)
      rw [mart, hs']
      simp only [Bool.false_eq_true, if_false]
      linarith

/-- **THE SEQUENTIAL THEOREM.** For an adversary whose per-round cheating rule
is an arbitrary function of the public history, the expected number of corrupt
rounds before the first alarm is at most `1/q`, at every horizon — hence in the
limit.

No independence between rounds, no fixed cheating rate, no binomial: the only
hypothesis on the adversary is that its choice at round `t` does not read round
`t`'s beacon, which is the type of `Round.corrupt`. `hdet` is required only at
histories where no alarm has yet fired — a deployment stops auditing once it has
raised one — and is discharged there by `Round.detect` from the three legs.

The bound is at horizon `n` and does not depend on `n`; the statement quantifies
over every horizon. The passage to the infinite-horizon `E[C_τ]` is not
formalized (see the residuals). -/
theorem sequential_bound [Nonempty Ω] {R : Round Ω} {q : ℝ} (hq : 0 < q)
    (hdet : ∀ h : List Ω, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun ω => R.alarms h ω))
    (n : ℕ) :
    expOver Ω n (fun h => (R.count h : ℝ)) [] ≤ 1 / q := by
  classical
  have hmart : expOver Ω n (R.mart q) [] ≤ 0 := by
    simpa using expOver.le_of_step (Φ := R.mart q) (mart_step hdet) n []
  have hsplit : expOver Ω n (R.mart q) []
      = q * expOver Ω n (fun h => (R.count h : ℝ)) []
        - expOver Ω n (fun h => if R.stopped h = true then (1 : ℝ) else 0) [] := by
    rw [show R.mart q = fun h => q * (R.count h : ℝ)
        - (if R.stopped h = true then (1 : ℝ) else 0) from rfl,
      expOver.sub, expOver.smul]
  have hind : expOver Ω n (fun h => if R.stopped h = true then (1 : ℝ) else 0) [] ≤ 1 := by
    refine le_trans (expOver.mono (g := fun _ => (1 : ℝ)) (fun h => ?_) n []) ?_
    · by_cases hs : R.stopped h = true <;> simp [hs]
    · exact le_of_eq (expOver.const 1 n [])
  rw [hsplit] at hmart
  rw [le_div_iff₀ hq]
  linarith

/-- **Expected leakage.** With a per-round payload cap `b`, the expected total
leakage before the first alarm is at most `b/q`. `b` is a HYPOTHESIS, not
decoration: without a capacity cap there is no bound at all, since `L` bits in
one message exfiltrate with probability at least `1 − q`. -/
theorem leakage_bound [Nonempty Ω] {R : Round Ω} {q b : ℝ} (hq : 0 < q)
    (hb : 0 ≤ b)
    (hdet : ∀ h : List Ω, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun ω => R.alarms h ω))
    (n : ℕ) :
    expOver Ω n (fun h => b * (R.count h : ℝ)) [] ≤ b / q := by
  rw [expOver.smul]
  calc b * expOver Ω n (fun h => (R.count h : ℝ)) []
      ≤ b * (1 / q) := mul_le_mul_of_nonneg_left (sequential_bound hq hdet n) hb
    _ = b / q := by ring

/-- The composed statement: the three legs give the sequential bound directly. -/
theorem sequential_bound_of_legs [Nonempty Ω] {A : AuditParams} {R : Round Ω}
    (hL : DetectionLegs A R) (hq : 0 < A.q) (n : ℕ) :
    expOver Ω n (fun h => (R.count h : ℝ)) [] ≤ 1 / A.q :=
  sequential_bound hq (fun _ _ hc => detect hL hc) n

end Round

namespace AuditWitness

/-- The audit set: half the beacon's four values. Nominal rate `p = 1/2`. -/
def sel (ω : Fin 4) : Bool := ω.val < 2

/-- A perfect checker over a beacon nobody can grind: the round is corrupt, the
audit fires on half the draws, and a fired audit always rejects. -/
def round : Round (Fin 4) where
  corrupt _ := true
  fires _ ω := sel ω
  alarms _ ω := sel ω
  chkErr _ _ := false
  chkAbort _ _ := false
  bindBreak _ _ := false

/-- `p = 1/2`, all three errors zero, so `q = 1/2`. -/
noncomputable def params : AuditParams where
  p := 1 / 2
  εchk := 0
  εbind := 0
  εbeacon := 0
  p_nonneg := by norm_num
  p_le_one := by norm_num
  εchk_nonneg := le_refl 0
  εchk_le_one := by norm_num
  εbind_nonneg := le_refl 0
  εbeacon_nonneg := le_refl 0

theorem params_q : params.q = 1 / 2 := by
  simp [AuditParams.q, params]

/-- The fire probability, counted: two of four draws. -/
theorem fire_prob (h : List (Fin 4)) :
    uniformProb (Fin 4) (fun ω => round.fires h ω = true) = 1 / 2 := by
  classical
  have hsum : (∑ ω : Fin 4, if round.fires h ω = true then (1 : ℝ) else 0) = 2 := by
    show (∑ ω : Fin 4, if sel ω = true then (1 : ℝ) else 0) = 2
    rw [Fin.sum_univ_four]
    norm_num [sel]
  rw [uniformProb_eq_avg_indicator, hsum, Fintype.card_fin]
  norm_num

/-- The alarm probability, counted: the same two draws — the checker is
perfect, so detection is exactly selection. -/
theorem alarm_prob (h : List (Fin 4)) :
    uniformProb (Fin 4) (fun ω => round.alarms h ω = true) = 1 / 2 :=
  fire_prob h

theorem legs : Round.DetectionLegs params round where
  beacon h := by rw [fire_prob h]; simp [params]
  chk h _ := by
    rw [uniformProb_false (p := fun ω => round.fires h ω = true ∧ round.chkErr h ω = true)
      (fun ω => by simp [round])]
    simp [params]
  bind h := by
    rw [uniformProb_false (p := fun ω => round.bindBreak h ω = true)
      (fun ω => by simp [round])]
    simp [params]
  miss h ω _ hf ha := by
    exact absurd (Eq.trans hf.symm (show round.fires h ω = false from ha)) (by simp)

/-- **The bound is ATTAINED.** The per-round detection lemma fires on this
instance and the inequality is an equality: `q = 1/2` is exactly the alarm
probability. There is no slack to hide behind here — the composed budget is the
detection rate on the nose when the beacon is unforgeable, the checker perfect
and the commitment binding. -/
theorem bound_attained (h : List (Fin 4)) :
    params.q ≤ uniformProb (Fin 4) (fun ω => round.alarms h ω = true) ∧
      uniformProb (Fin 4) (fun ω => round.alarms h ω = true) = params.q := by
  exact ⟨Round.detect legs (by simp [round]), by rw [alarm_prob h, params_q]⟩

/-- **The sequential theorem's premise is INHABITED.** `Round.sequential_bound`
is not a statement about an empty class: this instance satisfies every leg at
`q = 1/2 > 0`, so the bound `E[C_{n∧τ}] ≤ 2` holds of it at every horizon. -/
theorem sequential_fired (n : ℕ) :
    expOver (Fin 4) n (fun h => (round.count h : ℝ)) [] ≤ 1 / params.q :=
  Round.sequential_bound_of_legs legs (by rw [params_q]; norm_num) n

/-- …and the quantity it bounds is not identically zero: after one round the
adversary has already run one corrupt round, with certainty. The bound has
something to bound. -/
theorem count_after_one_round :
    expOver (Fin 4) 1 (fun h => (round.count h : ℝ)) [] = 1 := by
  have hval : ∀ ω : Fin 4, round.count [ω] = 1 := fun ω => rfl
  rw [expOver.succ]
  simp only [expOver.zero, hval]
  norm_num

end AuditWitness
end Minidregg.Selvage
namespace Minidregg.Selvage.AuditDisplacement
open Minidregg.Selvage
variable {Ω V : Type} [Fintype Ω] [NormedAddCommGroup V]

noncomputable def injected (R : Round Ω) (delta honest : List Ω → V) : List Ω → ℝ
  | [] => 0
  | _ :: h => if R.stopped h then injected R delta honest h
    else injected R delta honest h + ‖delta h - honest h‖

theorem injected_le_count (R : Round Ω) (delta honest : List Ω → V) (B : ℝ)
    (hactual : ∀ h, ‖delta h‖ ≤ B) (hhonest : ∀ h, ‖honest h‖ ≤ B)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest h) :
    ∀ h, injected R delta honest h ≤ (2 * B) * (R.count h : ℝ) := by
  intro h
  induction h with
  | nil => simp [injected, Round.count]
  | cons w h ih =>
    by_cases hs : R.stopped h = true
    · simpa [injected, Round.count, hs] using ih
    · have hs' : R.stopped h = false := Bool.eq_false_iff.mpr hs
      by_cases hc : R.corrupt h = true
      · have hd : ‖delta h - honest h‖ ≤ 2 * B :=
          (norm_sub_le _ _).trans (by linarith [hactual h, hhonest h])
        simp only [injected, Round.count, hs', Bool.false_eq_true, ↓reduceIte, hc,
          Nat.cast_add, Nat.cast_one]
        nlinarith
      · have hc' : R.corrupt h = false := Bool.eq_false_iff.mpr hc
        simpa [injected, Round.count, hs', hc', hcoverage h hc'] using ih

theorem displacement_bound [Nonempty Ω]
    (R : Round Ω) (delta honest : List Ω → V) (B q : ℝ)
    (hactual : ∀ h, ‖delta h‖ ≤ B) (hhonest : ∀ h, ‖honest h‖ ≤ B)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest h)
    (hq : 0 < q)
    (hdetect : ∀ h, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun w => R.alarms h w)) (n : ℕ) :
    expOver Ω n (injected R delta honest) [] ≤ 2 * B / q := by
  have hb : 0 ≤ B := (norm_nonneg (delta [])).trans (hactual [])
  exact (expOver.mono (injected_le_count R delta honest B hactual hhonest hcoverage) n []).trans
    (Round.leakage_bound hq (by linarith) hdetect n)

-- Nonvacuity: an actual corrupt delta of +1, honest delta -1, B = 1,
-- and the pre-existing non-grindable q = 1/2 witness.
theorem displacement_witness (n : ℕ) :
    expOver (Fin 4) n (injected AuditWitness.round
      (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ))) [] ≤ 4 := by
  have h := displacement_bound AuditWitness.round (fun _ => (1 : ℝ))
    (fun _ => (-1 : ℝ)) 1 AuditWitness.params.q
    (by intro h; norm_num) (by intro h; norm_num)
    (by intro h hc; simp [AuditWitness.round] at hc)
    (by rw [AuditWitness.params_q]; norm_num)
    (fun h _ hc => Round.detect AuditWitness.legs hc) n
  norm_num [AuditWitness.params_q] at h
  exact h

-- C10b: public linear transitions do not mean naive deletion commutes with later updates.
-- x <- 2*x+d; first teaching a=1, second b=0. Remove a's original contribution
-- from final state gives 1, while retraining without a gives 0.
theorem public_linear_expiry_counterexample :
    (2 * (2 * (0 : ℤ) + 1) + 0) - 1 ≠ 2 * 0 + 0 := by decide

-- C2/F7: invalid steps can cancel, so endpoint equality does not imply prefix validity.
theorem cancelling_corrupt_steps :
    (0 : ℤ) + 1 - 1 = 0 ∧ (0 : ℤ) + 1 ≠ 0 := by decide

-- C23 needs rho >= 0 for monotone substitution in the recurrence proof.
theorem negative_rho_substitution_false :
    ¬ (∀ a b : ℝ, a ≤ b → (-1 : ℝ) * a ≤ (-1 : ℝ) * b) := by
  intro h
  have hx := h 0 1 (by norm_num)
  norm_num at hx

-- Contract check: the actual consumer type names both caps, semantic coverage,
-- positive q and per-history detection; no probability premise is omitted.
example [Nonempty Ω]
    (R : Round Ω) (delta honest : List Ω → V) (B q : ℝ)
    (ha : ∀ h, ‖delta h‖ ≤ B) (hh : ∀ h, ‖honest h‖ ≤ B)
    (hc : ∀ h, R.corrupt h = false → delta h = honest h)
    (hq : 0 < q)
    (hd : ∀ h, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun w => R.alarms h w)) (n : ℕ) :
    expOver Ω n (injected R delta honest) [] ≤ 2 * B / q :=
  displacement_bound R delta honest B q ha hh hc hq hd n

-- Removing the actual cap makes the bound false even with the inhabited
-- non-grindable q=1/2 audit: B=0, one unit of corruption, one step.
theorem no_actual_cap_refutation :
    ¬ (expOver (Fin 4) 1 (injected AuditWitness.round
      (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) [] ≤
        2 * 0 / AuditWitness.params.q) := by
  norm_num [expOver, injected, Round.stopped, AuditWitness.params_q]

/-- info: 'Minidregg.Selvage.AuditDisplacement.no_actual_cap_refutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_actual_cap_refutation

-- Include exactly the axioms observed by the kernel after compilation.
/-- info: 'Minidregg.Selvage.AuditDisplacement.displacement_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms displacement_bound
/-- info: 'Minidregg.Selvage.AuditDisplacement.displacement_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms displacement_witness
/-- info: 'Minidregg.Selvage.AuditDisplacement.public_linear_expiry_counterexample' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms public_linear_expiry_counterexample
/-- info: 'Minidregg.Selvage.AuditDisplacement.cancelling_corrupt_steps' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms cancelling_corrupt_steps
/-- info: 'Minidregg.Selvage.AuditDisplacement.negative_rho_substitution_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms negative_rho_substitution_false
end Minidregg.Selvage.AuditDisplacement
