/-
# Selvage.AuditSampling — commit-then-audit soundness with an explicit composed budget.

**What this file proves.** A prover posts, each round, a commitment to an
execution trace on an append-only ledger. After the commitment is fixed a
beacon emits `ρ_t`; a public selection rule `Sel` fires an audit at nominal
rate `p`; a fired audit runs a checker and alarms on rejection. Two things are
established, over an adversary whose per-round decision to cheat is an
**arbitrary function of the whole public history** (fully adaptive — no
independence, no fixed cheating rate, no binomial model):

* **Per round** (`Round.detect`): if round `t` is corrupt then, for EVERY
  history, the round alarms with probability at least
  `q := p·(1 − ε_chk) − ε_bind − ε_beacon`.
* **Sequentially** (`sequential_bound`, `leakage_bound`): the expected number of
  corrupt rounds before the first alarm is at most `1/q`, and with a per-round
  payload cap `b` the expected leakage is at most `b/q`. Proved by exhibiting
  `M_t := q·C_{t∧τ} − 1{τ ≤ t}` as a supermartingale (`mart_step`) and running
  a finite-horizon optional-stopping argument (`expOver.le_of_step`) — all of it
  elementary counting in the house `uniformProb` vocabulary, no measure theory.

**This is a bound on DETECTION, not on cost.** Sampling amortizes the
*checker*; the *ledger* is paid in full every round, whatever `p` is
(`ledger_paid_in_full` / `sampling_amortizes_only_the_checker`; the underlying
lower bound is Boyle–Komargodski–Vafa 2025/358, whose Ω(log n / log log n)
physical-access cost per logical operation survives constant soundness error
and is NOT priced here). Nothing below says leakage is negligible: it is a
RATE bound with a named residual channel, and the residual is `1/q` rounds'
worth of payload.

**What is assumed, and where.** The three error parameters are *explicit named
fields* of `AuditParams` — never folded into a `negl`:

* `ε_chk` — the checker's error, conditional on the audit firing. The
  abstraction is forced: it instantiates either as a cryptographic soundness
  error (falls with a security parameter) or as a statistical trace-test error
  (an ML distributional assumption that does NOT fall with a parameter). The
  statement privileges neither. Section 7 instantiates it from the landed
  `Selvage/LightClientSound.lean` bound, under two named transport
  obligations that this file does NOT discharge.
* `ε_bind` — commitment binding, priced as a term. Open in the light-client
  vocabulary as `[ACC-extract]`.
* `ε_beacon` — the beacon's grindability, defined as an *additive* degradation
  of the selection-fire probability, quantified over the option set as it
  stands at **beacon-emission** time (`BeaconLeg`). This is NOT the
  multiplicative try-count factor of `Selvage/LightClientGrinding.lean`: that
  theorem lives on the checker side of the FS/ROM model and prices an adversary
  who reorders after seeing oracle answers. The *mechanism* transports — a
  selection made after the coin is visible costs the option count — the
  *statement* does not. `lightClientGrinding_sound` is cited here as motivation
  and as the phenomenon's machine-checked instance, never as a proof of the
  `ε_beacon` leg.

**Teeth.** `AuditWitness` fires the per-round lemma at its bound exactly
(detection probability `1/2` against `q = 1/2`). `BeaconRefutation` exhibits a
grindable beacon — the adversary re-rolls until the audit will not fire, then
cheats — under which the sequential bound is FALSE if `ε_beacon` is dropped
(`grind_beats_beaconless_bound`: three expected corrupt rounds against a
claimed `1/q = 2`), while the honest `ε_beacon` for that beacon is `p`, driving
`q` to `0` and the theorem to silence (`grind_honest_q_eq_zero`) — which is the
correct verdict for a beacon the prover controls. `FailOpenRefutation` is the
house wound-class, in no paper: a checker whose failure to render a verdict
*reads as acceptance* has realized `ε_chk = 1`, so `DetectionLegs` is
UNINHABITABLE at any positive `q` (`failOpen_no_legs`) — a fail-closed checker
is a hypothesis of the theorem (`missDecomp_of_failClosed`), not hygiene.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Selvage.Depth
import Selvage.LightClientSound

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

/-! ## 5. Cost: what sampling does NOT buy

`Cost(round) = Q_ledger + p · Cost(Chk)`. Everything above prices the second
term. The first does not fall under sampling and does not fall under the covert
relaxation either: Boyle–Komargodski–Vafa (2025/358) prove `Ω(log n / log log n)`
physical accesses per logical operation even at constant soundness error — with
"covert" meaning constant soundness error, NOT Aumann–Lindell's simulation
notion. That lower bound is CITED, not formalized here; what is formalized is
only the shape of the cost, which is enough to refuse the sentence "sampling
makes the ledger cheap". -/

/-- The per-round cost of a commit-then-audit protocol. -/
def roundCost (Qledger chkCost p : ℝ) : ℝ := Qledger + p * chkCost

/-- Sampling buys down the CHECKER term and nothing else: the difference
between any two audit rates is entirely in the checker. -/
theorem sampling_amortizes_only_the_checker (Qledger chkCost p p' : ℝ) :
    roundCost Qledger chkCost p - roundCost Qledger chkCost p'
      = (p - p') * chkCost := by
  unfold roundCost; ring

/-- **The ledger is paid in full at every audit rate, zero included.** The
tooth on "sampling makes the ledger cheap": drive `p` to `0` and the cost
floors at `Q_ledger`, which the audit theorem never touches. -/
theorem ledger_paid_in_full (Qledger chkCost : ℝ) (hc : 0 ≤ chkCost) :
    roundCost Qledger chkCost 0 = Qledger ∧
      ∀ p : ℝ, 0 ≤ p → Qledger ≤ roundCost Qledger chkCost p := by
  refine ⟨by simp [roundCost], fun p hp => ?_⟩
  have : 0 ≤ p * chkCost := mul_nonneg hp hc
  simp only [roundCost]; linarith

/-! ## 6. Teeth

Three instances. One satisfies the per-round lemma at its bound exactly; one
refutes the bound when `ε_beacon` is dropped; one refutes the legs when the
checker fails open. Each is a `Round` over a small finite coin space, computed,
not argued. -/

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

namespace BeaconRefutation

/-- A beacon the prover grinds. The raw coin is a fair bit, but the prover
re-rolls (equivalently: chooses among the option set still open at emission
time) until the realized `ρ_t` sits outside the audit set — so on the rounds it
cheats, the selection rule never fires. It cheats every round. -/
def round : Round (Fin 2) where
  corrupt _ := true
  fires _ _ := false
  alarms _ _ := false
  chkErr _ _ := false
  chkAbort _ _ := false
  bindBreak _ _ := false

/-- The parameters a deployment writes down when it FORGETS `ε_beacon`: the
selection rule advertises `p = 1/2`, the checker is sound, the commitment
binds — so the composed rate reads `q = 1/2` and the sequential bound reads
`E[C_τ] ≤ 2`. -/
noncomputable def beaconless : AuditParams where
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

theorem beaconless_q : beaconless.q = 1 / 2 := by
  simp [AuditParams.q, beaconless]

/-- The realized fire probability is zero at every history — the grind always
succeeds. -/
theorem fire_prob_zero (h : List (Fin 2)) :
    uniformProb (Fin 2) (fun ω => round.fires h ω = true) = 0 :=
  uniformProb_false (p := fun ω => round.fires h ω = true) (fun ω => by simp [round])

/-- Nothing ever alarms. -/
theorem never_stops : ∀ h : List (Fin 2), round.stopped h = false
  | [] => rfl
  | ω :: h => by
      show (round.stopped h || round.alarms h ω) = false
      rw [never_stops h]
      rfl

/-- Every round is corrupt and none is caught: the corrupt count is the round
number. -/
theorem count_eq_length : ∀ h : List (Fin 2), round.count h = h.length
  | [] => rfl
  | ω :: h => by
      show (if round.stopped h then round.count h
        else if round.corrupt h then round.count h + 1 else round.count h) = _
      rw [if_neg (by simp [never_stops h]), if_pos (by simp [round]),
        count_eq_length h]
      simp

/-- The expected corrupt count after `n` rounds is exactly `n`. -/
theorem expected_count (n : ℕ) :
    expOver (Fin 2) n (fun h => (round.count h : ℝ)) [] = (n : ℝ) := by
  have hfun : (fun h : List (Fin 2) => (round.count h : ℝ))
      = fun h : List (Fin 2) => (h.length : ℝ) := by
    funext h; rw [count_eq_length h]
  rw [hfun, expOver.length]
  simp

/-- **THE ε_beacon TERM IS LOAD-BEARING.** Drop it — price the beacon as if the
nominal rate were the realized rate — and the sequential bound is FALSE: this
adversary runs three expected corrupt rounds against a claimed `1/q = 2`, and
`n` against `2` at every horizon `n > 2`. The mechanism is exactly the one
`Selvage/LightClientGrinding.lean` machine-checks on the challenge oracle —
a party that selects AFTER seeing the coin pays the option count — transported
onto the selection rule, where it lands additively rather than as that file's
multiplicative `(t + n)` factor. -/
theorem grind_beats_beaconless_bound :
    ¬ (expOver (Fin 2) 3 (fun h => (round.count h : ℝ)) [] ≤ 1 / beaconless.q) := by
  rw [expected_count, beaconless_q]
  norm_num

/-- **Isolation: the other three legs DO hold**, at the very same beaconless
parameters. The refutation above is therefore attributable to `ε_beacon` and to
nothing else — it is not a checker failure, not a binding failure, and not a
gap in the miss decomposition. -/
theorem other_legs_hold :
    Round.ChkLeg beaconless round ∧ Round.BindLeg beaconless round
      ∧ Round.MissDecomp round := by
  refine ⟨fun h _ => ?_, fun h => ?_, fun h ω _ hf _ => ?_⟩
  · rw [uniformProb_false (p := fun ω => round.fires h ω = true ∧ round.chkErr h ω = true)
      (fun ω => by simp [round])]
    simp [beaconless]
  · rw [uniformProb_false (p := fun ω => round.bindBreak h ω = true)
      (fun ω => by simp [round])]
    simp [beaconless]
  · simp [round] at hf

/-- And the reason the true theorem is not contradicted: the beaconless
parameters are refused at the door. `BeaconLeg` is exactly the clause this
adversary violates. -/
theorem beaconless_leg_false : ¬ Round.BeaconLeg beaconless round := by
  intro hleg
  have h0 := hleg []
  rw [fire_prob_zero []] at h0
  simp only [beaconless] at h0
  norm_num at h0

/-- **The honest accounting, and the honest verdict.** For a beacon whose
realized fire probability is zero, the definition of `ε_beacon` forces
`ε_beacon = p`, so `q = 0` and every statement in this file is silent about
this deployment. That is the correct answer — "a datacenter-local PRNG is
vacuous at any audit rate" — and it is reached by pricing the term, not by
noticing the attack. -/
noncomputable def honest : AuditParams where
  p := 1 / 2
  εchk := 0
  εbind := 0
  εbeacon := 1 / 2
  p_nonneg := by norm_num
  p_le_one := by norm_num
  εchk_nonneg := le_refl 0
  εchk_le_one := by norm_num
  εbind_nonneg := le_refl 0
  εbeacon_nonneg := by norm_num

theorem grind_honest_q_eq_zero : honest.q = 0 := by
  simp [AuditParams.q, honest]

/-- Under the honest parameters the beacon leg DOES hold — the statement is
well-posed, it just says nothing, because `q = 0`. Vacuity reached honestly is
different from vacuity reached silently. -/
theorem honest_leg_holds : Round.BeaconLeg honest round := by
  intro h
  rw [fire_prob_zero h]
  simp [honest]

end BeaconRefutation

namespace FailOpenRefutation

/-- The wound: the checker cannot render a verdict — it crashes, times out, or
refuses to parse — and its failure READS AS ACCEPTANCE. Every round is audited
(`p = 1`), every checker run aborts, and no alarm is ever raised. -/
def round : Round (Fin 2) where
  corrupt _ := true
  fires _ _ := true
  alarms _ _ := false
  chkErr _ _ := false
  chkAbort _ _ := true
  bindBreak _ _ := false

theorem is_fail_open : Round.FailOpen round := fun _ _ _ => rfl

theorem not_fail_closed : ¬ Round.FailClosed round := by
  intro hfc
  exact absurd (hfc [] 0 rfl rfl) (by simp [round])

/-- The alarm probability is zero at every history. -/
theorem alarm_prob_zero (h : List (Fin 2)) :
    uniformProb (Fin 2) (fun ω => round.alarms h ω = true) = 0 :=
  uniformProb_false (p := fun ω => round.alarms h ω = true) (fun ω => by simp [round])

/-- **A refusal that renders as acceptance is invisible to the budget.** The
miss decomposition is the clause it breaks: a corrupt round fires, does not
alarm, and yet neither `chkErr` nor `bindBreak` is set — the abort was charged
to nothing. -/
theorem missDecomp_false : ¬ Round.MissDecomp round := by
  intro hm
  rcases hm [] 0 rfl rfl rfl with he | hb
  · simp [round] at he
  · simp [round] at hb

/-- **Hence no parameters at all admit the legs at a positive detection rate.**
Not "the bound gets worse": there is NO `AuditParams` under which this round
satisfies `DetectionLegs` and `q > 0`. Fail-closedness is a hypothesis of the
theorem (`missDecomp_of_failClosed`), not hygiene. -/
theorem failOpen_no_legs (A : AuditParams) (hq : 0 < A.q) :
    ¬ Round.DetectionLegs A round := by
  intro hL
  have := Round.detect (Ω := Fin 2) hL (h := []) (by simp [round])
  rw [alarm_prob_zero []] at this
  linarith

/-- The same round with the abort charged HONESTLY to the checker: every
aborting run is recorded as a checker error. Now the miss decomposition holds —
and the price appears where it belongs. -/
def honest : Round (Fin 2) where
  corrupt _ := true
  fires _ _ := true
  alarms _ _ := false
  chkErr _ _ := true
  chkAbort _ _ := true
  bindBreak _ _ := false

theorem honest_missDecomp : Round.MissDecomp honest := fun _ _ _ _ _ => Or.inl rfl

theorem honest_fire_prob (h : List (Fin 2)) :
    uniformProb (Fin 2) (fun ω => honest.fires h ω = true) = 1 := by
  rw [uniformProb_congr (q := fun _ => True) (fun ω => by simp [honest])]
  exact uniformProb_true

/-- **The honest accounting drives `q` to zero.** Charging the abort to the
checker forces `ε_chk = 1` — the checker is wrong on every run it is asked
about — so `q = p·0 − ε_bind − ε_beacon ≤ 0` and the theorem is silent. Between
this and `failOpen_no_legs`: an unpriced refusal makes the budget
UNINHABITABLE, and a priced one makes it VACUOUS. Neither is a bound; only the
first is invisible. -/
theorem honest_q_nonpos (A : AuditParams) (hchk : Round.ChkLeg A honest) :
    A.q ≤ 0 := by
  have h1 : uniformProb (Fin 2)
      (fun ω => honest.fires [] ω = true ∧ honest.chkErr [] ω = true) ≤ 1 * A.εchk := by
    have := hchk [] (by simp [honest])
    rwa [honest_fire_prob []] at this
  have h2 : (1 : ℝ) ≤ 1 * A.εchk := by
    refine le_trans (le_of_eq ?_) h1
    rw [uniformProb_congr (q := fun _ => True) (fun ω => by simp [honest]),
      uniformProb_true]
  have hbind := A.εbind_nonneg
  have hbeacon := A.εbeacon_nonneg
  have hp := A.p_le_one
  have hp0 := A.p_nonneg
  have hchk1 : (1 : ℝ) ≤ A.εchk := by linarith
  unfold AuditParams.q
  nlinarith

end FailOpenRefutation

/-! ## 7. Where the `ε_chk` leg comes from

Two steps. First a structural one: on a coin space that factors as
`beacon × checker-coins`, the `ε_chk` leg reduces to a bound on the checker's
OWN coins — which is the only shape a proof-system soundness theorem can
possibly supply. Then the valuation: `Selvage/LightClientSound.lean`'s landed
`lightClientSound` supplies exactly that bound, under two transport obligations
this file states as hypotheses and does NOT discharge. -/

namespace Round

/-- **The `ε_chk` leg from independent checker coins.** If the round's coin
space factors as `σ × K` — the beacon's draw and the checker's coins — with the
selection reading only `σ` and the checker's error only `K`, then the leg's
product form follows from a bound on the checker's own coins alone.

The independence used is between the BEACON and the CHECKER, and nothing else:
the adversary remains an arbitrary function of the history throughout. -/
theorem chkLeg_of_product {σ K : Type} [Fintype σ] [Fintype K] [Nonempty K]
    {A : AuditParams} {R : Round (σ × K)}
    {sel : List (σ × K) → σ → Bool} {err : List (σ × K) → K → Bool}
    (hfires : ∀ h x, R.fires h x = sel h x.1)
    (hchk : ∀ h x, R.chkErr h x = err h x.2)
    (hbound : ∀ h, R.corrupt h = true → uniformProb K (fun k => err h k = true) ≤ A.εchk) :
    ChkLeg A R := by
  intro h hc
  have hjoint : uniformProb (σ × K) (fun x => R.fires h x = true ∧ R.chkErr h x = true)
      = uniformProb σ (fun s => sel h s = true)
        * uniformProb K (fun k => err h k = true) := by
    rw [uniformProb_congr (q := fun x : σ × K => (sel h x.1 = true) ∧ (err h x.2 = true))
      (fun x => by rw [hfires h x, hchk h x])]
    exact uniformProb_prod_indep (fun s => sel h s = true) (fun k => err h k = true)
  have hmarg : uniformProb (σ × K) (fun x => R.fires h x = true)
      = uniformProb σ (fun s => sel h s = true) := by
    have h1 : uniformProb (σ × K) (fun x => (sel h x.1 = true) ∧ True)
        = uniformProb σ (fun s => sel h s = true) * uniformProb K (fun _ => True) :=
      uniformProb_prod_indep (fun s => sel h s = true) (fun _ => True)
    rw [uniformProb_congr (q := fun x : σ × K => (sel h x.1 = true) ∧ True)
      (fun x => by rw [hfires h x]; simp), h1, uniformProb_true, mul_one]
  rw [hjoint, hmarg]
  exact mul_le_mul_of_nonneg_left (hbound h hc) (uniformProb_nonneg _)

end Round

/-- **The `ε_chk` value, from the landed light-client bound.** A round whose
checker is the v0 light client — draw one Fiat–Shamir schedule, check the
folded aggregate — has checker error at most `n · (err⋆(δ) + 1/|F|)`, the
deployable headline of `Selvage/LightClientSound.lean`. Every hypothesis of
that theorem is carried here verbatim; nothing is weakened.

**The two transport obligations, stated as hypotheses and NOT discharged:**

* `hT1` **[AUDIT-chk-corrupt]** — the audit's corruption predicate must be
  *δ-far-falseness of some link*, not "the trace fails the relation". A word
  δ-close to a satisfying codeword sits OUTSIDE `lightClientSound`'s hypothesis,
  so an audit layer that defines `Round.corrupt` as relation-failure has a gap
  the bound does not cover. Here it appears as the light client's own `hfalse`;
  what remains open is the DEFINITIONAL choice in `Round.corrupt` at the
  deployment, and that it is the same `δ` in both places.
* `hT2` **[AUDIT-chk-anchor]** — the audited event must be anchored at the
  HONEST fold of the committed words (`foldWords`), which is where
  `lightClientSound`'s event lives. The gap between that and the prover's own
  recommitments is exactly `ε_bind`, so the decomposition is consistent
  *because* `AuditParams` prices `ε_bind` separately — and it is inconsistent
  for any deployment that folds `ε_bind` away.

Neither obligation is discharged in this file; both are semantic identifications
between the audit layer's `Round` and the light client's chain vocabulary, and
they belong to the deployment that builds the `Round`. -/
theorem chkErr_bound_of_lightClient
    {Root ι : Type*} {F : Type} [Field F] [Fintype F] [Nonempty ι] [Fintype ι]
    [DecidableEq ι] [DecidableEq F] {r : ℕ}
    (foldRoot : Root → F → Root → Root)
    {C : Submodule F (ι → F)} {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    {ws : List (ι → F)} {f₀ : ι → F} {δ dC Bstar : ℝ} {errstar : ℝ → ℝ}
    {err : (Fin ch.length → F) → Bool}
    (halign : Aligned A₀ ch)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hδ0 : 0 < δ) (hδB : δ < 1 - Bstar) (hδC : δ < dC / 2)
    (herr0 : 0 ≤ errstar δ) (hlen : ws.length = ch.length)
    (hT1 : ∃ p ∈ ch.zip ws, ∀ v ∈ C, relDist p.2 v ≤ δ →
        ¬ AccClaim.Satisfies C p.1.claim v)
    (hT2 : ∀ γv : Fin ch.length → F, (err γv = true) ↔
        ∃ w, relDist (foldWords (padSched γv) f₀ ws) w ≤ δ ∧
          AccClaim.Satisfies C (aggregate foldRoot (padSched γv) A₀ ch) w) :
    uniformProb (Fin ch.length → F) (fun γv => err γv = true)
      ≤ (ch.length : ℝ) * (errstar δ + 1 / (Fintype.card F : ℝ)) := by
  rw [uniformProb_congr hT2]
  exact lightClientSound foldRoot halign hdC hMCA hδ0 hδB hδC herr0 hlen hT1

/-! ## 8. Residuals — what is NOT closed here

* **[AUDIT-chk-corrupt]** / **[AUDIT-chk-anchor]** — the two transport
  obligations above. Hypotheses, not theorems; they are discharged by the
  deployment that defines `Round.corrupt` and `Round.chkErr`, and a deployment
  that defines either of them the natural-looking way (relation-failure;
  the prover's own recommitment) does NOT discharge them.
* **`ε_bind`** — `BindLeg` is a named hypothesis with no realizer in this
  vocabulary. It is `[ACC-extract]` in the light-client vocabulary, and
  `Selvage/ZkExtraction.lean`'s `extractChain_committed_seam` closes a composed
  binding seam at unique decoding on the ZK flank — nearer to hand than a fresh
  proof, but not the same statement.
* **`ε_beacon`** — `BeaconLeg` is a named hypothesis. `BeaconRefutation` proves
  the term is load-bearing and that the honest value for a fully grindable
  beacon is `p`; the file does NOT derive `ε_beacon ≤ p · Pr[G ≥ 2]` from a
  beacon model, and in particular does not derive `ε_beacon ≤ α·p` for a
  longest-chain beacon at adversarial stake `α`. That derivation needs a
  beacon-model layer this file does not have.
* **Fresh coins across rounds.** `expOver` averages over INDEPENDENT uniform
  draws, one per round. The adversary is fully adaptive; the WORLD's per-round
  randomness is assumed i.i.d. uniform. A beacon whose draws are correlated
  across rounds is outside the sequential theorem — and correlated draws are
  exactly what a grindable beacon has, which is why `ε_beacon` is priced at the
  per-round layer where the conditional statement lives.
* **Infinite horizon.** `sequential_bound` is proved at every finite horizon
  `n`, uniformly in `n`. The limit statement `E[C_τ] ≤ 1/q` follows from the
  monotone limit of a bound that does not depend on `n`; that passage is not
  formalized, because nothing downstream needs it — a deployment runs a finite
  number of rounds.
* **The ledger term.** `roundCost`'s `Q_ledger` is a parameter. The
  Boyle–Komargodski–Vafa `Ω(log n / log log n)` lower bound on it is cited, not
  formalized. `ledger_paid_in_full` only refuses the sentence "sampling makes
  the ledger cheap"; it does not prove the ledger is expensive.
* **Tightness of `1/q`.** Not proved here. `AuditWitness` shows the PER-ROUND
  bound is attained; the sequential constant is not shown unimprovable.
* **The spatial burst.** A single-path trace check on width-`N` layers forces
  `ε_chk ≥ 1 − 1/N`, so `q ≤ p/N − ε_bind − ε_beacon`. `AuditParams` can
  express this — `εchk` is a free parameter — but nothing here derives the
  `1 − 1/N` floor from a checker model, and nothing composes it with the
  temporal concentration.
* **The commitment `c_t` is not a first-class object.** It is folded into the
  history: `Round.corrupt`, `Round.fires` and `Round.alarms` read `List Ω`, and
  everything decided before the beacon emits — the commitment included — is
  determined by that. This is what makes `BeaconLeg`'s `∀ h` the spec's
  `ess inf … | F_{t−1}, c_t`, and it is also a simplification: a model wanting
  to say something about the commitment ITSELF (its opening, its equivocation
  witness) cannot say it here, and would have to widen `Round`.
* **`ChkLeg`'s product form.** `Pr[fire ∧ chkErr] ≤ Pr[fire]·ε_chk` is an
  assumption about the beacon and the checker being independent. It is
  discharged by `Round.chkLeg_of_product` only when the coin space LITERALLY
  factors; a deployment whose checker reads the beacon owes it directly.
* **`ε_chk > 0` unconditionally.** If one-way functions exist, no checker has
  `ε_chk = 0` (the HLvA floor). Cited; not formalized. The
  `AuditWitness` instance is a MODEL with a perfect checker, not a claim that
  one exists.
-/

/-- info: 'Minidregg.Selvage.Round.detect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.detect
/-- info: 'Minidregg.Selvage.Round.mart_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.mart_step
/-- info: 'Minidregg.Selvage.expOver.le_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expOver.le_of_step
/-- info: 'Minidregg.Selvage.Round.sequential_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.sequential_bound
/-- info: 'Minidregg.Selvage.Round.leakage_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.leakage_bound
/-- info: 'Minidregg.Selvage.Round.sequential_bound_of_legs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.sequential_bound_of_legs
/-- info: 'Minidregg.Selvage.Round.missDecomp_of_failClosed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Round.missDecomp_of_failClosed
/-- info: 'Minidregg.Selvage.Round.chkLeg_of_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.chkLeg_of_product
/-- info: 'Minidregg.Selvage.chkErr_bound_of_lightClient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms chkErr_bound_of_lightClient
/-- info: 'Minidregg.Selvage.ledger_paid_in_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ledger_paid_in_full
/-- info: 'Minidregg.Selvage.AuditWitness.bound_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AuditWitness.bound_attained
/-- info: 'Minidregg.Selvage.BeaconRefutation.grind_beats_beaconless_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BeaconRefutation.grind_beats_beaconless_bound
/-- info: 'Minidregg.Selvage.BeaconRefutation.beaconless_leg_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BeaconRefutation.beaconless_leg_false
/-- info: 'Minidregg.Selvage.BeaconRefutation.grind_honest_q_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BeaconRefutation.grind_honest_q_eq_zero
/-- info: 'Minidregg.Selvage.FailOpenRefutation.missDecomp_false' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms FailOpenRefutation.missDecomp_false
/-- info: 'Minidregg.Selvage.FailOpenRefutation.failOpen_no_legs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FailOpenRefutation.failOpen_no_legs
/-- info: 'Minidregg.Selvage.FailOpenRefutation.honest_q_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FailOpenRefutation.honest_q_nonpos
/-- info: 'Minidregg.Selvage.AuditWitness.sequential_fired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AuditWitness.sequential_fired
/-- info: 'Minidregg.Selvage.AuditWitness.count_after_one_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AuditWitness.count_after_one_round
/-- info: 'Minidregg.Selvage.BeaconRefutation.other_legs_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BeaconRefutation.other_legs_hold

end Minidregg.Selvage
