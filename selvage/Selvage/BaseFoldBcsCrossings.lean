/-
# Selvage.BaseFoldBcsCrossings — the RP/RF crossing through the capacity event,
# and the deployed Poseidon2 boundary with every term visible

`BaseFoldBcsCapacityEvent` (queue item 1) priced the eager/deferred coupling's
exact bad event at `paddedCapacityError W = 2·W²/|Cap|` on the work space
`Fin W → Rate × Cap`, and charged it into the strict ROM/sampling ledger BY
UNION BOUND on top of `romError W`, whose first summand is the same
`2·W²/p⁸`.  Item 1 warned that this pays the capacity event twice.  This
module makes the identification and stops the double payment.

**The identification (proved).**  `capacity_summand_identified`:
`paddedCapacityError W = 2·W²/p⁸` as real numbers, so
`romError W = switchError W + paddedCapacityError W` exactly
(`romError_eq_switch_add_capacity`), with `switchError W = W²/p¹⁶` the
random-permutation/random-function switching cost.  The two summands are
distinct quantities (`switchError_lt_paddedCapacityError`), and item 1's
`strictRomSamplingCapacityError` is EXACTLY the honest ledger plus one extra
capacity term (`strictRomSamplingCapacityError_double_counts`).

**Why the summands are the same number but not the same event, and what the
ledger keeps.**  `romError` is the error expression of the still-open
`romConstructionTarget` (`hrom`), a proposition about the ideal-permutation
real world versus the lazy-RO ideal world; nothing inside an assumed `hrom`
can be identified with a proved event.  Item 1's event lives on the eager
hybrid's work space.  The honest move is therefore to DECOMPOSE the padded
class of `hrom` into hops on explicit sample spaces, and let item 1's event be
the capacity hop.  The ledger keeps `paddedCapacityError` (proved, item 1)
and `switchError` (named), and no longer carries `romError` as an opaque
premise for the padded receipt class:

    real (uniform `Equiv.Perm`)            [RP-RF-switch]        switchError W
      ≈ total function (uniform function)  [RF-lazy-sampling]    exact
      = lazy function (work space)         [RF-lazy-eager]       off ¬collision
      ≈ eager hybrid (work space)          item 1 (PROVED)       off ¬collision
      ≈ deferred ideal (work space)        [DEFERRED-ideal-exact] exact (PROVED,
      = idealRun (ideal coin space)          `BaseFoldBcsDeferredIdeal`)

The two `¬collision` hops share ONE bad event on ONE sample space, so the
identical-until-bad lemma charges `paddedCapacityError W` ONCE across both
(`lazyProb_sub_deferredProb_abs_le`).  Under the three named hops the padded
class of `hrom` is DERIVED with its capacity summand realized by item 1's
event (`paddedRomBound_of_crossings`).

**The deployed Poseidon2 boundary.**  `Poseidon2PermutationIdeal gap` is the
tree's `[PERM-ideal]` floor for THIS profile: the source-derived `permutePair`
world (deterministic; its acceptance is a `uniformProb Unit`) is within
`gap W` of the uniform-permutation world for every padded receipt
distinguisher.  It is a `def : Prop`, never an axiom, never asserted.  The
whole deployed ledger is then one expression with every term visible:

    crossingsError gap W q = gap W + switchError W + paddedCapacityError W + q/p

and `deployedPaddedAcceptedRawLedger` composes it with the raw-IOR terms:
algebraic `m·3/|E|` + miss `(1-τ)^q` + retained Merkle equivocation +
rejection `q/p` + switch + capacity (once) + Poseidon2 gap.

Covered scope: the fixed padded receipt schedule (construction queries only).
Not covered (named, with ATLAS fields on each): the switching lemma itself,
lazy-sampling equivalence of a uniform total function, and the lazy/eager
pointwise agreement off the collision event.  The deferred/ideal
marginalization is closed in `Selvage.BaseFoldBcsDeferredIdeal`.  Nothing
here idealizes deployed Poseidon2.
-/

import Selvage.BaseFoldBcsCapacityEvent

namespace Minidregg.Selvage

/-! ## Identical-until-bad, as a counting lemma -/

/-- Two events that agree wherever a bad event fails differ in probability by
at most the bad event's probability.  This is the only probabilistic glue
needed to pay one bad event once across several hops on one sample space. -/
theorem uniformProb_abs_sub_le_of_agree_off_bad {C : Type} [Fintype C]
    {left right bad : C → Prop}
    (hagree : ∀ c, ¬ bad c → (left c ↔ right c)) :
    |uniformProb C left - uniformProb C right| ≤ uniformProb C bad := by
  have hleft :
      uniformProb C left ≤ uniformProb C right + uniformProb C bad := by
    refine le_trans (uniformProb_mono (q := fun c => right c ∨ bad c) ?_)
      (uniformProb_or_le right bad)
    intro c hc
    by_cases hb : bad c
    · exact Or.inr hb
    · exact Or.inl ((hagree c hb).1 hc)
  have hright :
      uniformProb C right ≤ uniformProb C left + uniformProb C bad := by
    refine le_trans (uniformProb_mono (q := fun c => left c ∨ bad c) ?_)
      (uniformProb_or_le left bad)
    intro c hc
    by_cases hb : bad c
    · exact Or.inr hb
    · exact Or.inl ((hagree c hb).2 hc)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ## The total random-function world -/

section FunctionWorld

variable {Rate Cap : Type}

/-- Answers of the world whose primitive is a total function `P`.
Constructions squeeze the sponge over `P`; forward queries evaluate `P`; an
inverse query is not a function of `P` and fails closed. -/
def functionAnswer? [AddCommGroup Rate] (P : Rate × Cap → Rate × Cap)
    (iv : Rate × Cap) : SpQuery Rate Cap → Option (SpAnswer Rate Cap)
  | .constr x xs => some (.rate (sponge P iv (x :: xs)))
  | .fwd s => some (.block (P s))
  | .inv _ => none

/-- The adaptive run against a total function, failing closed on the first
inverse query. -/
def functionRun [AddCommGroup Rate] {q : Nat} (P : Rate × Cap → Rate × Cap)
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap) :
    Option (List (SpAnswer Rate Cap)) :=
  (List.finRange q).foldl
    (fun acc _ => acc.bind fun ans =>
      (functionAnswer? P iv (D.move ans)).map fun answer => ans ++ [answer])
    (some [])

/-- Acceptance in the total-function world. -/
def functionAccept [AddCommGroup Rate] {q : Nat}
    (P : Rate × Cap → Rate × Cap) (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) : Prop :=
  match functionRun P D iv with
  | some ans => D.out ans = true
  | none => False

/-- `Pr_P[D accepts]` over a uniformly random TOTAL function on the full
state — the random-function side of the RP/RF switch. -/
noncomputable def functionProb [AddCommGroup Rate] [Fintype Rate] [Fintype Cap]
    [DecidableEq Rate] [DecidableEq Cap] {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap) : Real :=
  uniformProb (Rate × Cap → Rate × Cap) fun P => functionAccept P D iv

/-- Distinguishers that issue only construction queries within their round
budget.  The padded BaseFold receipt distinguisher is one. -/
def ConstructionOnly {q : Nat} (D : Distinguisher Rate Cap q) : Prop :=
  ∀ ans : List (SpAnswer Rate Cap), ans.length < q →
    ∃ x xs, D.move ans = .constr x xs

theorem functionRun_foldl_eq_realRun_foldl [AddCommGroup Rate] {q : Nat}
    (P Pinv : Rate × Cap → Rate × Cap) (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) (hconstr : ConstructionOnly D) :
    ∀ (rounds : List (Fin q)) (ans : List (SpAnswer Rate Cap)),
      ans.length + rounds.length ≤ q →
        rounds.foldl
            (fun acc _ => acc.bind fun ans =>
              (functionAnswer? P iv (D.move ans)).map fun answer =>
                ans ++ [answer])
            (some ans) =
          some (rounds.foldl
            (fun ans _ => ans ++ [realAnswer P Pinv iv (D.move ans)]) ans) := by
  intro rounds
  induction rounds with
  | nil =>
      intro ans _
      rfl
  | cons round rounds ih =>
      intro ans hlen
      rw [List.length_cons] at hlen
      obtain ⟨x, xs, hmove⟩ := hconstr ans (by omega)
      rw [List.foldl_cons, List.foldl_cons]
      have hstep :
          (some ans).bind (fun ans =>
            (functionAnswer? P iv (D.move ans)).map fun answer =>
              ans ++ [answer]) =
            some (ans ++ [realAnswer P Pinv iv (D.move ans)]) := by
        rw [Option.bind_some, hmove]
        rfl
      rw [hstep]
      exact ih _ (by rw [List.length_append, List.length_singleton]; omega)

/-- For a construction-only distinguisher the total-function run at a
permutation is literally the landed real run; the inverse direction is never
consulted. -/
theorem functionRun_perm_eq_realRun [AddCommGroup Rate] [Fintype Rate]
    [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (hconstr : ConstructionOnly D) (π : Equiv.Perm (Rate × Cap)) :
    functionRun (⇑π) D iv = some (realRun D iv π) := by
  unfold functionRun realRun
  exact functionRun_foldl_eq_realRun_foldl (⇑π) (⇑π.symm) D iv hconstr
    (List.finRange q) [] (by simp)

/-- The ideal-permutation real world IS the total-function world restricted
to permutations: same run, same verdict, permutation coins. -/
theorem realProb_eq_uniformProb_perm_functionAccept [AddCommGroup Rate]
    [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (hconstr : ConstructionOnly D) :
    realProb D iv =
      uniformProb (Equiv.Perm (Rate × Cap)) fun π =>
        functionAccept (⇑π) D iv := by
  unfold realProb
  apply uniformProb_congr
  intro π
  unfold functionAccept
  rw [functionRun_perm_eq_realRun D iv hconstr π]

end FunctionWorld

/-! ## The lazily sampled random-function world on the work space -/

section LazyFunctionWorld

variable {Rate Cap : Type}

/-- State of the lazily sampled random-function world: a primitive table, the
public answers, and the unconsumed work vector.  There is no construction RO
and no programming: every fresh primitive edge takes the next work pair. -/
structure LazyFunctionState (Rate Cap : Type) where
  primitive : Oracle (Rate × Cap) (Rate × Cap)
  ans : List (SpAnswer Rate Cap)
  remaining : List (Rate × Cap)

/-- One public round against the lazy table.  A construction absorbs every
block through the landed `lazyAbsorb` (one work pair per block, replaying
hits); a forward query consumes one pair; an inverse query fails closed. -/
noncomputable def lazyFunctionStep [AddCommGroup Rate] {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (st : LazyFunctionState Rate Cap) (_round : Fin q) :
    Option (LazyFunctionState Rate Cap) :=
  match D.move st.ans with
  | .constr x xs =>
      let need := xs.length + 1
      let used := st.remaining.take need
      if used.length = need then
        (lazyAbsorb st.primitive iv (x :: xs) used).map fun result =>
          ⟨result.2, st.ans ++ [.rate result.1.1], st.remaining.drop need⟩
      else none
  | .fwd s =>
      match st.remaining with
      | coin :: rest =>
          some ⟨(st.primitive.respond s coin).2,
            st.ans ++ [.block (st.primitive.respond s coin).1], rest⟩
      | [] => none
  | .inv _ => none

/-- The lazy random-function run on one fixed work vector. -/
noncomputable def lazyFunctionRun [AddCommGroup Rate] {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin work → Rate × Cap) : Option (LazyFunctionState Rate Cap) :=
  (List.finRange q).foldl
    (fun acc round => acc.bind fun st => lazyFunctionStep D iv st round)
    (some ⟨Oracle.empty, [], List.ofFn coins⟩)

/-- Acceptance of the lazy random-function world on the work space. -/
noncomputable def lazyFunctionAccept [AddCommGroup Rate] {q work : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (coins : Fin work → Rate × Cap) : Prop :=
  match lazyFunctionRun D iv coins with
  | some st => D.out st.ans = true
  | none => False

end LazyFunctionWorld

end Minidregg.Selvage

/-! ## The padded BaseFold receipt class -/

namespace Minidregg.Selvage.BaseFoldBcsCrossings

open Minidregg.Selvage
open BabyBearExt4
open Minidregg.Selvage.BaseFoldPoseidon2
open Minidregg.Selvage.BaseFoldBcsFiatShamir
open Minidregg.Selvage.BaseFoldBcsQuerySampling
open Minidregg.Selvage.BaseFoldBcsQuerySamplingJoint
open Minidregg.Selvage.BaseFoldBcsPadding
open Minidregg.Selvage.BaseFoldBcsRunSchedule
open Minidregg.Selvage.BaseFoldBcsStrictRomLedger
open Minidregg.Selvage.BaseFoldBcsCapacityEvent

set_option autoImplicit false

noncomputable section

/-! ### The identification of the capacity summand -/

/-- The random-permutation / random-function switching summand of
`romError`, isolated: `W²/|Rate × Cap|` with `|Rate × Cap| = p¹⁶`. -/
def switchError (work : Nat) : Real :=
  (work : Real) ^ 2 / ((modulus ^ 16 : Nat) : Real)

/-- ⭐ **The capacity summand, identified.**  Item 1's charged term IS the
first summand of `romError` as a real number: `2·W²/p⁸`.
Witness: `paddedCapacityError_pos` (nonzero at every positive work).
Falsifier: `switchError_lt_paddedCapacityError` (it is not the other
summand; the two cannot be confused). -/
theorem capacity_summand_identified (work : Nat) :
    paddedCapacityError work =
      2 * (work : Real) ^ 2 / ((modulus ^ 8 : Nat) : Real) := by
  unfold paddedCapacityError
  rw [BaseFoldPoseidon2Rom.capacity_card]

/-- `romError` is exactly the switch term plus item 1's capacity term. -/
theorem romError_eq_switch_add_capacity (work : Nat) :
    BaseFoldPoseidon2Rom.romError work =
      switchError work + paddedCapacityError work := by
  rw [capacity_summand_identified]
  unfold BaseFoldPoseidon2Rom.romError switchError
  ring

theorem paddedCapacityError_pos (work : Nat) (hwork : 0 < work) :
    0 < paddedCapacityError work := by
  rw [capacity_summand_identified]
  have hw : (0 : Real) < (work : Real) ^ 2 := pow_pos (Nat.cast_pos.mpr hwork) 2
  have hp : (0 : Real) < ((modulus ^ 8 : Nat) : Real) :=
    Nat.cast_pos.mpr (Nat.pow_pos (by norm_num [modulus]))
  exact div_pos (by linarith) hp

/-- The two summands of `romError` are different quantities: the switch term
is strictly smaller at every positive work. -/
theorem switchError_lt_paddedCapacityError (work : Nat) (hwork : 0 < work) :
    switchError work < paddedCapacityError work := by
  rw [capacity_summand_identified]
  unfold switchError
  have hw : (0 : Real) < (work : Real) ^ 2 := pow_pos (Nat.cast_pos.mpr hwork) 2
  have h8 : (0 : Real) < ((modulus ^ 8 : Nat) : Real) :=
    Nat.cast_pos.mpr (Nat.pow_pos (by norm_num [modulus]))
  have h16 : ((modulus ^ 8 : Nat) : Real) ≤ ((modulus ^ 16 : Nat) : Real) :=
    Nat.cast_le.mpr (Nat.pow_le_pow_right (by norm_num [modulus]) (by norm_num))
  calc (work : Real) ^ 2 / ((modulus ^ 16 : Nat) : Real)
      ≤ (work : Real) ^ 2 / ((modulus ^ 8 : Nat) : Real) :=
        div_le_div_of_nonneg_left hw.le h8 h16
    _ < 2 * (work : Real) ^ 2 / ((modulus ^ 8 : Nat) : Real) := by
        rw [div_lt_div_iff_of_pos_right h8]
        linarith

/-- **Every term of the deployed ledger, visible.**  Poseidon2 gap, the
permutation/function switch, item 1's capacity event (once), and the
fail-closed query-seed rejection. -/
def crossingsError (gap : Nat → Real) (work queryCount : Nat) : Real :=
  gap work + switchError work + paddedCapacityError work +
    (queryCount : Real) / (modulus : Real)

/-- With no Poseidon2 gap the crossings ledger is numerically the old strict
ROM/sampling ledger: `romError` was already switch + capacity. -/
theorem crossingsError_zero_gap (work queryCount : Nat) :
    crossingsError (fun _ => 0) work queryCount =
      strictRomSamplingError work queryCount := by
  unfold crossingsError strictRomSamplingError
  rw [romError_eq_switch_add_capacity]
  ring

/-- ⭐ **The double count, exhibited.**  Item 1's charged ledger is the honest
ledger plus one extra capacity term. -/
theorem strictRomSamplingCapacityError_double_counts (work queryCount : Nat) :
    strictRomSamplingCapacityError work queryCount =
      crossingsError (fun _ => 0) work queryCount + paddedCapacityError work := by
  unfold strictRomSamplingCapacityError
  rw [crossingsError_zero_gap]

/-! ### The worlds of the padded receipt distinguisher -/

variable {m queryCount : Nat}

/-- The fixed uniform work space of one padded receipt. -/
abbrev WorkCoins (statement : Statement m) (receipt : Receipt m queryCount) :
    Type :=
  Fin (paddedTranscriptPrimitiveWork statement receipt) → Rate × Cap

/-- Eager prefix-programmed acceptance (item 1's hybrid). -/
def eagerAccept (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : WorkCoins statement receipt) : Prop :=
  workHybridAccept Rate Cap
    (paddedConstructionDistinguisher statement receipt verdict) (0, 0) coins

def eagerProb (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Real :=
  uniformProb (WorkCoins statement receipt) (eagerAccept statement receipt verdict)

/-- Deferred ideal acceptance on the same work space. -/
def deferredAccept (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : WorkCoins statement receipt) : Prop :=
  deferredWorkAccept
    (paddedConstructionDistinguisher statement receipt verdict) (0, 0) coins

def deferredProb (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Real :=
  uniformProb (WorkCoins statement receipt)
    (deferredAccept statement receipt verdict)

/-- Lazy random-function acceptance on the same work space. -/
def lazyAccept (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (coins : WorkCoins statement receipt) : Prop :=
  lazyFunctionAccept
    (paddedConstructionDistinguisher statement receipt verdict) (0, 0) coins

def lazyProb (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Real :=
  uniformProb (WorkCoins statement receipt) (lazyAccept statement receipt verdict)

/-- The deployed world: the source-derived width-16 Poseidon2 permutation at
the generic sponge interface, zero IV.  No randomness. -/
def deployedAccept (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Prop :=
  functionAccept BaseFoldPoseidon2Rom.permutePair
    (paddedConstructionDistinguisher statement receipt verdict) (0, 0)

/-- The deployed world's acceptance as a probability on the one-point sample
space: exactly `1` or `0`. -/
def deployedIndicator (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Real :=
  uniformProb Unit fun _ => deployedAccept statement receipt verdict

open Classical in
theorem deployedIndicator_eq (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    deployedIndicator statement receipt verdict =
      if deployedAccept statement receipt verdict then 1 else 0 :=
  uniformProb_const Unit _

/-- The padded schedule never issues a primitive query. -/
theorem paddedConstructionDistinguisher_constructionOnly
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    ConstructionOnly (paddedConstructionDistinguisher statement receipt verdict) := by
  intro ans hlen
  rw [paddedConstructionDistinguisher_move_at_length statement receipt verdict
    ans hlen]
  obtain ⟨x, xs, hquery, _⟩ :=
    paddedConstructionQuerySchedule_is_constr statement receipt ⟨ans.length, hlen⟩
  exact ⟨x, xs, hquery⟩

/-- The landed real world of the padded distinguisher is the total-function
world sampled over permutations. -/
theorem paddedRealProb_eq_perm_functionAccept
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    realProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0) =
      uniformProb (Equiv.Perm (Rate × Cap)) fun π =>
        functionAccept (⇑π)
          (paddedConstructionDistinguisher statement receipt verdict) (0, 0) :=
  realProb_eq_uniformProb_perm_functionAccept _ _
    (paddedConstructionDistinguisher_constructionOnly statement receipt verdict)

/-! ### The eager/deferred hop, priced by item 1 -/

/-- Off item 1's event, eager acceptance is deferred acceptance of the
reindexed vector: item 1's bridge plus the landed run-level agreement. -/
theorem eagerAccept_iff_deferredAccept_reindex
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (coins : WorkCoins statement receipt)
    (hnocol : ¬ PaddedCapacityCollisionRun statement receipt verdict coins) :
    eagerAccept statement receipt verdict coins ↔
      deferredAccept statement receipt verdict
        (paddedSegmentReindex statement receipt coins) := by
  obtain ⟨eager, deferred, heager, hdeferred, hans⟩ :=
    paddedEagerDeferredRun_terminalFresh_agreement statement receipt verdict
      coins hsafe
      (paddedEagerTerminalFreshRun_of_noCapacityCollision statement receipt
        verdict coins hsafe hnocol)
  unfold eagerAccept deferredAccept workHybridAccept deferredWorkAccept
  simp [heager, hdeferred, hans]

/-- The segment reindexing is a measure-preserving bijection of the work
space, so the deferred probability may be read at the reindexed vector. -/
theorem deferredProb_eq_reindexed (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) :
    deferredProb statement receipt verdict =
      uniformProb (WorkCoins statement receipt) fun coins =>
        deferredAccept statement receipt verdict
          (paddedSegmentReindex statement receipt coins) :=
  (uniformProb_paddedSegmentReindex statement receipt
    (deferredAccept statement receipt verdict)).symm

/-- ⭐ **Eager ≈ deferred, priced by item 1.**  The first probability hop of
the crossing, on the work space, costing exactly the capacity term. -/
theorem eagerProb_sub_deferredProb_abs_le (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt) :
    |eagerProb statement receipt verdict - deferredProb statement receipt verdict|
      ≤ paddedCapacityError (paddedTranscriptPrimitiveWork statement receipt) := by
  rw [deferredProb_eq_reindexed]
  refine le_trans
    (uniformProb_abs_sub_le_of_agree_off_bad
      (bad := PaddedCapacityCollisionRun statement receipt verdict) ?_)
    (paddedCapacityCollisionRun_le_error statement receipt verdict)
  intro coins hnocol
  exact eagerAccept_iff_deferredAccept_reindex statement receipt verdict hsafe
    coins hnocol

/-! ### The named crossings, in the tree's convention: `def : Prop`, never an axiom -/

/-- **`[RP-RF-switch]`** — the random-permutation / random-function switching
lemma for the padded receipt distinguisher: the uniform-permutation world and
the uniform-total-function world differ by at most `switchError W = W²/p¹⁶`.
This is the standard `q(q−1)/2^{b+1}` switching bound with the pessimistic
constant, on the full 16-lane state.  NOT proved here.
Witness: `paddedRpRfSwitch_zero_rounds` (satisfiable — the zero-round slice).
Teeth: `RpRfSwitchToy.switch_is_load_bearing` (at a two-element state the
two worlds differ, so no version of this hypothesis with a zero term holds
in general).  Premise inhabitation: every padded receipt of every shape is a
valid argument; the real world is `paddedRealProb_eq_perm_functionAccept`. -/
def PaddedRpRfSwitch (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Prop :=
  |realProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0) -
      functionProb (paddedConstructionDistinguisher statement receipt verdict)
        (0, 0)|
    ≤ switchError (paddedTranscriptPrimitiveWork statement receipt)

/-- **`[RF-lazy-sampling]`** — lazy sampling of a uniform total function is
exact: the total-function acceptance probability equals the lazy-table
acceptance probability on the work space.  Each fresh primitive edge of a
construction takes one fresh uniform pair; replays consume no randomness.
NOT proved here (a pushforward argument along the adaptively selected fresh
keys; `uniformProb_pushforward_le` in `Selvage/Depth.lean` is the counting
kernel it needs).  Teeth: the equality is an EXACT identity, so any padded
receipt where `lazyProb ≠ functionProb` refutes it; none is claimed. -/
def PaddedLazyFunctionSampling (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Prop :=
  functionProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0) =
    lazyProb statement receipt verdict

/-- **`[RF-lazy-eager]`** — off item 1's exact capacity event, the lazy
random-function world and the eager prefix-programmed hybrid accept the same
work vectors.  Pointwise on the SAME sample space with the SAME bad event as
the eager/deferred hop, so the capacity term is paid once across both
(`lazyProb_sub_deferredProb_abs_le`).  NOT proved here: it needs the converse
of item 1's `TableRooted` (every RO entry is the programmed edge of a rooted
prefix) threaded through `paddedRound_bridge`; with it, a fresh primitive
edge always sits at a fresh RO prefix, so the programmed rate IS the work
rate coin.  Teeth: on the collision event the two worlds may differ (item 1's
`CapacityEventExample.collision_zero_capacity` closes a cycle the lazy table
does not), which is why the hypothesis is conditional. -/
def PaddedLazyEagerAgreeOffCollision (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Prop :=
  ∀ coins : WorkCoins statement receipt,
    ¬ PaddedCapacityCollisionRun statement receipt verdict coins →
      (lazyAccept statement receipt verdict coins ↔
        eagerAccept statement receipt verdict coins)

/-- **`[DEFERRED-ideal-exact]`** — the deferred work-space acceptance
probability equals the landed `idealProb` on the ideal coin space.  The
deferred run reads only the segment-head rate coin of each round
(`paddedDeferredWorkRun_head_semantics`), so this is a marginalization along
the injective segment-head map (`uniformProb_comp_injective` in
`Selvage/LightClientGrinding.lean`) plus the construction-only trace of
`idealRun`.  This is the `deferred_probability_exact` field of the landed
`PrefixHybridIdealOffBadWitness`.  PROVED for every padded receipt under the
routing premise in `Selvage.BaseFoldBcsDeferredIdeal`
(`paddedDeferredIdealExact`), which also inhabits that witness. -/
def PaddedDeferredIdealExact (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool) : Prop :=
  deferredProb statement receipt verdict =
    idealProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0)

/-- **`[POSEIDON2-perm-ideal]`** — the deployed-Poseidon2 boundary, the tree's
`[PERM-ideal]` floor at this profile.  The source-derived `permutePair` world
(deterministic) is within `gap W` of the uniformly random permutation world
for every padded receipt distinguisher of work `W`.  This is a NAMED
COMPUTATIONAL HYPOTHESIS about a fixed function, in the shape of
`[COMMIT-CR]`/`[FOLD-msis]`: a `def : Prop` carried as a premise, never
asserted, never an axiom.  Its number is cryptanalytic, not a theorem.
Witness: `poseidon2PermutationIdeal_one` (`gap := 1` holds vacuously — the
floor below which the hypothesis says nothing).  Teeth: `gap := 0` claims a
fixed function is a uniform permutation against every verdict; its refutation
is an explicit structural distinguisher for Poseidon2, which is exactly what
cryptanalysis of the deployed parameters would supply and what this file does
not claim to have. -/
def Poseidon2PermutationIdeal (gap : Nat → Real) : Prop :=
  ∀ {m queryCount : Nat} (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool),
    |deployedIndicator statement receipt verdict -
        realProb (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0)|
      ≤ gap (paddedTranscriptPrimitiveWork statement receipt)

/-! ### Paying the capacity event once -/

/-- ⭐ **Lazy ≈ deferred, capacity paid ONCE across two hops.**  Both hops
agree off the same event on the same space, so identical-until-bad charges
`paddedCapacityError W` a single time. -/
theorem lazyProb_sub_deferredProb_abs_le (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (hagree : PaddedLazyEagerAgreeOffCollision statement receipt verdict) :
    |lazyProb statement receipt verdict - deferredProb statement receipt verdict|
      ≤ paddedCapacityError (paddedTranscriptPrimitiveWork statement receipt) := by
  rw [deferredProb_eq_reindexed]
  refine le_trans
    (uniformProb_abs_sub_le_of_agree_off_bad
      (bad := PaddedCapacityCollisionRun statement receipt verdict) ?_)
    (paddedCapacityCollisionRun_le_error statement receipt verdict)
  intro coins hnocol
  exact (hagree coins hnocol).trans
    (eagerAccept_iff_deferredAccept_reindex statement receipt verdict hsafe
      coins hnocol)

/-- ⭐ **The padded class of `hrom`, derived through item 1's event.**  Under
the three named hops, the ideal-permutation advantage of the padded receipt
distinguisher is at most `romError W` — with its capacity summand realized
by `paddedCapacityCollisionRun_le` rather than assumed. -/
theorem paddedRomBound_of_crossings (statement : Statement m)
    (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (hswitch : PaddedRpRfSwitch statement receipt verdict)
    (hsampling : PaddedLazyFunctionSampling statement receipt verdict)
    (hagree : PaddedLazyEagerAgreeOffCollision statement receipt verdict)
    (hdeferred : PaddedDeferredIdealExact statement receipt verdict) :
    |realProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0) -
        idealProb (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0)|
      ≤ BaseFoldPoseidon2Rom.romError
          (paddedTranscriptPrimitiveWork statement receipt) := by
  rw [romError_eq_switch_add_capacity]
  have h1 :
      |realProb (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0) - lazyProb statement receipt verdict|
        ≤ switchError (paddedTranscriptPrimitiveWork statement receipt) := by
    unfold PaddedRpRfSwitch at hswitch
    unfold PaddedLazyFunctionSampling at hsampling
    rw [← hsampling]
    exact hswitch
  have h2 :
      |lazyProb statement receipt verdict -
          idealProb (paddedConstructionDistinguisher statement receipt verdict)
            (0, 0)|
        ≤ paddedCapacityError (paddedTranscriptPrimitiveWork statement receipt) := by
    unfold PaddedDeferredIdealExact at hdeferred
    rw [← hdeferred]
    exact lazyProb_sub_deferredProb_abs_le statement receipt verdict hsafe hagree
  calc
    |realProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0) -
        idealProb (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0)|
      ≤ |realProb (paddedConstructionDistinguisher statement receipt verdict)
            (0, 0) - lazyProb statement receipt verdict| +
          |lazyProb statement receipt verdict -
            idealProb (paddedConstructionDistinguisher statement receipt verdict)
              (0, 0)| := abs_sub_le _ _ _
    _ ≤ switchError (paddedTranscriptPrimitiveWork statement receipt) +
          paddedCapacityError (paddedTranscriptPrimitiveWork statement receipt) :=
        add_le_add h1 h2

/-! ### The deployed ledger, every term visible -/

/-- ⭐ **Deployed sponge advantage plus rejection, in one expression.**
Poseidon2 gap + switch + capacity (once) + `q/p`. -/
theorem deployed_rom_rejection_ledger (gap : Nat → Real)
    (hgap : Poseidon2PermutationIdeal gap)
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (hswitch : PaddedRpRfSwitch statement receipt verdict)
    (hsampling : PaddedLazyFunctionSampling statement receipt verdict)
    (hagree : PaddedLazyEagerAgreeOffCollision statement receipt verdict)
    (hdeferred : PaddedDeferredIdealExact statement receipt verdict) :
    |deployedIndicator statement receipt verdict -
        idealProb (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0)| +
      uniformProb (Fin queryCount → Digest) QuerySeedRejection
      ≤ crossingsError gap (paddedTranscriptPrimitiveWork statement receipt)
          queryCount := by
  have hg := hgap statement receipt verdict
  have hrom := paddedRomBound_of_crossings statement receipt verdict hsafe hswitch
    hsampling hagree hdeferred
  rw [romError_eq_switch_add_capacity] at hrom
  have hrej := querySeedRejection_le queryCount
  have htri := abs_sub_le (deployedIndicator statement receipt verdict)
    (realProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0))
    (idealProb (paddedConstructionDistinguisher statement receipt verdict) (0, 0))
  unfold crossingsError
  linarith

/-- Arithmetic composition rule: any raw-IOR false-accept bound adds the
crossings ledger without renaming or dropping a term. -/
theorem add_rawFailure_le_crossingsLedger
    {m queryCount : Nat} {tau rawFailure equivocation : Real}
    (rawBound :
      rawFailure ≤
        (m : Real) * (3 / Fintype.card E) +
          (1 - tau) ^ queryCount + equivocation)
    {gap : Nat → Real} {receiptWork : Nat} {advantage rejection : Real}
    (advantageAndRejection :
      advantage + rejection ≤ crossingsError gap receiptWork queryCount) :
    rawFailure + advantage + rejection ≤
      (m : Real) * (3 / Fintype.card E) +
        (1 - tau) ^ queryCount + equivocation +
          crossingsError gap receiptWork queryCount := by
  linarith

/-- ⭐ **The whole deployed ledger.**  Algebraic `m·3/|E|`, query miss
`(1−τ)^q`, retained Merkle equivocation, and the crossings ledger (Poseidon2
gap + switch + capacity once + `q/p`), for the padded `.pad1` profile.  Same
raw-IOR hypotheses as `strictPaddedAcceptedRawRomLedger`; `hrom` is replaced
by the named crossings and the deployed-Poseidon2 boundary. -/
theorem deployedPaddedAcceptedRawLedger
    {ell m queryCount : Nat}
    (gap : Nat → Real) (hgap : Poseidon2PermutationIdeal gap)
    (T : FoldingTower E (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript
      (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)))
    (hell : ell ≤ 28) (hmell : m ≤ ell)
    (z : Fin m → E) (H : E)
    (word : PowerTwoFriLevels ell 0 → E)
    (prover : (Nat → E) → Nat → Polynomial E)
    {tau : Real} (htau1 : tau ≤ 1)
    (htau : ∀ j : Fin m,
      tau ≤ 1 /
        (Fintype.card (PowerTwoFriLevels ell (j + 1)) : Real))
    (hword0 : st.word 0 (fun i => i.elim0) = word)
    (hfalse : ¬ BaseFoldExactClaim T z H word)
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (chi : Nat → E) (i : Nat), i < m →
      (prover chi i).degree < ((2 + 1 : Nat) : WithBot Nat))
    (statement : Statement m) (receipt : Receipt m queryCount)
    (verdict : List (SpAnswer Rate Cap) → Bool)
    (hsafe : PaddedFullMessageRoutingSafe statement receipt)
    (hswitch : PaddedRpRfSwitch statement receipt verdict)
    (hsampling : PaddedLazyFunctionSampling statement receipt verdict)
    (hagree : PaddedLazyEagerAgreeOffCollision statement receipt verdict)
    (hdeferred : PaddedDeferredIdealExact statement receipt verdict) :
    uniformProb
      ((Fin m → E) × AcceptedSeedFamily queryCount)
      (fun sample =>
        BaseFoldRawCommittedIorAccepts
          (fun n => BinaryMerkle.openingScheme hashSuite (ell - n)) T st
          z H prover queryCount sample.1
          (powerTwoCoherentSchedule hmell
            (acceptedSeedCoordinates hell sample.2))) +
      |deployedIndicator statement receipt verdict -
        idealProb (paddedConstructionDistinguisher statement receipt verdict)
          (0, 0)| +
      uniformProb (Fin queryCount → Digest) QuerySeedRejection
      ≤ (m : Real) * (3 / Fintype.card E) +
          (1 - tau) ^ queryCount +
          uniformProb
            ((Fin m → E) × QueryCoordinateFamily ell queryCount)
            (fun sample =>
              FriRawAdaptiveEquivocates
                (fun n => BinaryMerkle.openingScheme hashSuite (ell - n))
                T st sample.1 queryCount
                (powerTwoCoherentSchedule hmell sample.2)) +
          crossingsError gap (paddedTranscriptPrimitiveWork statement receipt)
            queryCount := by
  apply add_rawFailure_le_crossingsLedger
  · exact acceptedSeedRawCommittedIor_coherent_exact_sound
      T st hell hmell z H word prover htau1 htau hword0 hfalse hpm hdeg
  · exact deployed_rom_rejection_ledger gap hgap statement receipt verdict hsafe
      hswitch hsampling hagree hdeferred

/-! ### ATLAS fields for the named hypotheses -/

/-- `gap := 1` is inhabited: both sides are probabilities.  This is the
vacuous floor of `[POSEIDON2-perm-ideal]`, exhibited so the definition is
known satisfiable; it says nothing about deployed Poseidon2. -/
theorem poseidon2PermutationIdeal_one : Poseidon2PermutationIdeal fun _ => 1 := by
  unfold Poseidon2PermutationIdeal
  intro m queryCount statement receipt verdict
  have h0 := uniformProb_nonneg (C := Unit)
    (fun _ => deployedAccept statement receipt verdict)
  have h1 := uniformProb_le_one (C := Unit)
    (fun _ => deployedAccept statement receipt verdict)
  have h2 := uniformProb_nonneg (C := Equiv.Perm (Rate × Cap))
    (fun π => (paddedConstructionDistinguisher statement receipt verdict).out
      (realRun (paddedConstructionDistinguisher statement receipt verdict)
        (0, 0) π) = true)
  have h3 := uniformProb_le_one (C := Equiv.Perm (Rate × Cap))
    (fun π => (paddedConstructionDistinguisher statement receipt verdict).out
      (realRun (paddedConstructionDistinguisher statement receipt verdict)
        (0, 0) π) = true)
  unfold deployedIndicator realProb
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- A zero-round statement and receipt. -/
def emptyStatement : Statement 0 := ⟨0, fun i => i.elim0, 0⟩

def emptyReceipt : Receipt 0 0 :=
  ⟨fun i => i.elim0, fun i => i.elim0, 0, fun i => i.elim0, fun i => i.elim0⟩

/-- `[RP-RF-switch]` is satisfiable: at zero rounds both worlds are the
constant verdict on the empty transcript. -/
theorem paddedRpRfSwitch_zero_rounds (verdict : List (SpAnswer Rate Cap) → Bool) :
    PaddedRpRfSwitch emptyStatement emptyReceipt verdict := by
  classical
  unfold PaddedRpRfSwitch
  have hreal :
      realProb (paddedConstructionDistinguisher emptyStatement emptyReceipt
        verdict) (0, 0) =
        if (paddedConstructionDistinguisher emptyStatement emptyReceipt
          verdict).out [] = true then 1 else 0 := by
    unfold realProb
    haveI : Nonempty (Equiv.Perm (Rate × Cap)) := ⟨Equiv.refl _⟩
    rw [uniformProb_congr
      (q := fun _ => (paddedConstructionDistinguisher emptyStatement emptyReceipt
        verdict).out [] = true) (fun π => by simp [realRun])]
    exact uniformProb_const _ _
  have hfun :
      functionProb (paddedConstructionDistinguisher emptyStatement emptyReceipt
        verdict) (0, 0) =
        if (paddedConstructionDistinguisher emptyStatement emptyReceipt
          verdict).out [] = true then 1 else 0 := by
    unfold functionProb
    haveI : Nonempty (Rate × Cap → Rate × Cap) := ⟨id⟩
    rw [uniformProb_congr
      (q := fun _ => (paddedConstructionDistinguisher emptyStatement emptyReceipt
        verdict).out [] = true)
      (fun P => by unfold functionAccept; simp [functionRun])]
    exact uniformProb_const _ _
  rw [hreal, hfun, sub_self, abs_zero]
  unfold switchError
  positivity

end

/-! ### Teeth for `[RP-RF-switch]`: the switch term is load-bearing -/

namespace RpRfSwitchToy

/-- Two one-block constructions at the two distinct blocks of `ZMod 2`;
accept iff the squeezed rates agree.  Over a permutation of the two-element
state they never agree; over a random function they agree on the constant
functions. -/
def distinguisher : Distinguisher (ZMod 2) (Fin 1) 2 where
  move ans :=
    match ans with
    | [] => .constr 0 []
    | _ :: _ => .constr 1 []
  out ans :=
    match ans with
    | [.rate a, .rate b] => decide (a = b)
    | _ => false

theorem realRun_eq (π : Equiv.Perm (ZMod 2 × Fin 1)) :
    realRun distinguisher (0, 0) π =
      [.rate (π (0, 0)).1, .rate (π (1, 0)).1] := by
  unfold realRun
  rw [show List.finRange 2 = [0, 1] by decide]
  simp [distinguisher, realAnswer, sponge, spongeAbsorb, absorbStep]

theorem real_never_accepts (π : Equiv.Perm (ZMod 2 × Fin 1)) :
    ¬ (distinguisher.out (realRun distinguisher (0, 0) π) = true) := by
  rw [realRun_eq]
  simp only [distinguisher, decide_eq_true_eq]
  intro heq
  have hpair : π (0, 0) = π (1, 0) := Prod.ext heq (Subsingleton.elim _ _)
  have hzero : ((0 : ZMod 2), (0 : Fin 1)) = (1, 0) := π.injective hpair
  exact absurd (congrArg Prod.fst hzero) (by decide)

theorem realProb_zero : realProb distinguisher (0, 0) = 0 := by
  unfold realProb
  exact uniformProb_false real_never_accepts

def constantFunction : ZMod 2 × Fin 1 → ZMod 2 × Fin 1 := fun _ => (0, 0)

theorem constant_accepts : functionAccept constantFunction distinguisher (0, 0) := by
  unfold functionAccept functionRun
  rw [show List.finRange 2 = [0, 1] by decide]
  simp [distinguisher, functionAnswer?, sponge, spongeAbsorb, absorbStep,
    constantFunction]

theorem functionProb_pos : 0 < functionProb distinguisher (0, 0) := by
  unfold functionProb uniformProb
  haveI : Nonempty {P : ZMod 2 × Fin 1 → ZMod 2 × Fin 1 //
      functionAccept P distinguisher (0, 0)} :=
    ⟨⟨constantFunction, constant_accepts⟩⟩
  apply div_pos
  · exact_mod_cast Nat.card_pos
  · exact_mod_cast Fintype.card_pos

/-- The random-permutation / random-function gap is real: a zero switching
term is refuted at a two-element state. -/
theorem switch_is_load_bearing :
    realProb distinguisher (0, 0) ≠ functionProb distinguisher (0, 0) := by
  rw [realProb_zero]
  exact ne_of_lt functionProb_pos

end RpRfSwitchToy

#check @capacity_summand_identified
#check @romError_eq_switch_add_capacity
#check @switchError_lt_paddedCapacityError
#check @strictRomSamplingCapacityError_double_counts
#check @crossingsError
#check @paddedRealProb_eq_perm_functionAccept
#check @eagerProb_sub_deferredProb_abs_le
#check @PaddedRpRfSwitch
#check @PaddedLazyFunctionSampling
#check @PaddedLazyEagerAgreeOffCollision
#check @PaddedDeferredIdealExact
#check @Poseidon2PermutationIdeal
#check @lazyProb_sub_deferredProb_abs_le
#check @paddedRomBound_of_crossings
#check @deployed_rom_rejection_ledger
#check @deployedPaddedAcceptedRawLedger
#check @poseidon2PermutationIdeal_one
#check @paddedRpRfSwitch_zero_rounds
#check @RpRfSwitchToy.switch_is_load_bearing

/-- info: 'Minidregg.Selvage.uniformProb_abs_sub_le_of_agree_off_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformProb_abs_sub_le_of_agree_off_bad
/-- info: 'Minidregg.Selvage.realProb_eq_uniformProb_perm_functionAccept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realProb_eq_uniformProb_perm_functionAccept
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.capacity_summand_identified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms capacity_summand_identified
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.romError_eq_switch_add_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms romError_eq_switch_add_capacity
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.switchError_lt_paddedCapacityError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms switchError_lt_paddedCapacityError
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.strictRomSamplingCapacityError_double_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms strictRomSamplingCapacityError_double_counts
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.eagerProb_sub_deferredProb_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eagerProb_sub_deferredProb_abs_le
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.lazyProb_sub_deferredProb_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lazyProb_sub_deferredProb_abs_le
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.paddedRomBound_of_crossings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedRomBound_of_crossings
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.deployed_rom_rejection_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployed_rom_rejection_ledger
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.deployedPaddedAcceptedRawLedger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedPaddedAcceptedRawLedger
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.poseidon2PermutationIdeal_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms poseidon2PermutationIdeal_one
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.paddedRpRfSwitch_zero_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms paddedRpRfSwitch_zero_rounds
/-- info: 'Minidregg.Selvage.BaseFoldBcsCrossings.RpRfSwitchToy.switch_is_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RpRfSwitchToy.switch_is_load_bearing

end Minidregg.Selvage.BaseFoldBcsCrossings
