/-
# Selvage.SpongeIndiff — sponge indifferentiability: the LAST floor reduction,
# [FS-ROM] → (ideal permutation + proximity)

`Selvage/FiatShamir.lean` names `[FS-ROM]` as "the one named idealization": the
deployed sponge/hash realizes the lazy-sampling `Oracle` handler.
`Selvage/CollisionResistanceROM.lean` already moved the CR leg of `[COMMIT-CR]`
into the ROM with a number. This file builds the machinery that reduces
`[FS-ROM]` itself one floor down: the SPONGE construction over an ideal
permutation is indifferentiable from a random oracle up to the capacity bound
`O(q²/2^c)` — so the floor consolidates to (ideal permutation + proximity).

What lands here, PROVED:
* **The sponge** (`spongeAbsorb`/`sponge`): absorb rate-blocks into a
  `Rate × Cap` state through a permutation `P`, squeeze the final rate. The
  deployed candidate for `P` is `Compiler/AirHash.lean`'s `permExec`
  (Poseidon2-shape) — cited by NAME, not imported: the Selvage boundary
  (`scripts/check-import-boundary.sh`) forbids `Compiler` imports, so the
  sponge is parametric over `P` and the tie to `permExec` is instantiation.
* **The partial walk** (`walkFrom`): the sponge's absorb phase run THROUGH a
  partial permutation log — `Selvage/FiatShamir.lean`'s `Oracle` structure,
  reused verbatim, with two new handler laws (`Oracle.lookup_mem`,
  `Oracle.lookup_respond_some`, `Oracle.invert_respond`). `walkFrom_agrees`:
  on a log consistent with a total `P`, the walk IS `spongeAbsorb`.
* **The simulator** (`simFwd`/`simInv`, dispatched by `spongeSimulator`) — the
  standard indifferentiability simulator, genuinely maintaining consistency:
  ONE shared log for both query directions; forward queries that COMPLETE a
  rooted absorption path (`completion?` — the unique-path detector) are
  answered by PROGRAMMING the RO's value into the rate and a fresh coin into
  the capacity; unrooted forward queries and inverse queries answer fresh
  coins. Replay/frame/consistency laws come free from the LANDED handler laws
  (`respond_hit`, `respond_consistent`, `lookup_respond_self`) — the
  simulator is `Oracle.respond` with a computed value, not a new handler.
* **`walk_programs` — the programming keystone**: at the moment a fresh
  forward query completes rooted path `m`, the FULL sponge walk of `m`
  through the extended log succeeds and squeezes EXACTLY the programmed rate
  (the RO's answer at `m`). This is the real/ideal agreement at the
  construction interface, one step, machine-checked for every log, state, and
  message. `sponge_realizes_handler_step` restates it with the RO as the
  landed lazy-sampling handler and adds `respond_consistent`: a later
  construction query of `m` answers the SAME value — the exact seam
  `[FS-ROM]` names, closed one step at a time.
* **Path-uniqueness preservation** (`uniquePaths_simFwd`/`uniquePaths_simInv`
  via `uniquePaths_respond_freshOut`/`_freshKey`): the simulator's path
  bookkeeping stays UNIQUE after every step whose fresh capacity coin misses
  `capsOf` (every capacity the log or IV mentions) — the walk-decomposition
  lemma `walkFrom_respond_split` shows a new entry can only ever be the LAST
  step of a path, and only extend THE unique rooted prefix. This is the
  simulator's consistency-off-the-bad-event, per step, proved.
* **The capacity-collision bad event, PRICED** (`CapBad`, `capBad_bound`,
  `capBad_le`): fresh capacity coins pairwise collide or hit a fixed avoid
  set. Pairwise part = the LANDED `birthday_bound` (cited through the
  transport `capCollisionProb_eq`, not re-derived); hit part = a union bound
  over coordinates, per-coordinate the LANDED `uniformProb_coord_mem`
  (`Selvage/Sumcheck.lean`, its unused `Field` binder dropped there — cited, not
  re-derived). Total: `≤ q(q−1)/(2N) + q·|S|/N ≤ 2q²/N` for
  `|S| ≤ q + 1` — the `O(q²/2^c)` capacity bound with explicit constants.
  Tight at `q = 2` (`capBad_two_prob` = `1/N`, the bound's value there).
* **The game, STATED PRECISELY** (`SpongeIndifferentiable`,
  `SpongeIndiffGame` = `[SPONGE-indiff-game]`): a `q`-query adaptive
  distinguisher (the `SrProver` adaptivity shape) against REAL = (sponge over
  a uniformly random `Equiv.Perm`, the permutation both ways) vs IDEAL = (the
  lazy-sampling RO handler, the simulator); advantage `≤ 2q²/|Cap| + q²/|Blk|`
  (capacity bad event + permutation-vs-function switching). `q = 0` slice
  PROVED (`advantage_zero_queries`) — the game machinery computes.

## Covered scope, in the same sentence as the claim (the honest label)
The simulator, its programming correctness, its per-step path-uniqueness
preservation, and the fixed-set capacity-collision bound are PROVED here.
Follow-up modules through `SpongeIndiffOffBadRun` thread path uniqueness
through the actual adaptive `idealRun`, prove prefix causality for the evolving
`capsOf`, price its exact ideal-coin failure event by `q(2q+2)/|Cap|`, and
prove failure-or-final `UniquePaths`.  The newer construction-first lane makes
the previously missing operational semantics explicit: `SpongeIndiffWorkBudget`
formally refutes external query count as a primitive-work budget for arbitrary
multi-block messages; `SpongeIndiffPrefixProgramming` reconciles or programs
every nonempty prefix; `SpongeIndiffPrefixOutput` proves that a successful
construction returns exactly the lazy RO value of the full message; and
`SpongeIndiffPrefixWalk` proves that its returned primitive table actually
walks the complete message to that same state.  `SpongeIndiffWorkStream`
consumes one pair from a fixed uniform vector per primitive evaluation.
Distinct lazy samples commute extensionally
(`SpongeIndiffOracleReordering`), while `SpongeIndiffUniformCoupling` proves
that an actual work-space bijection plus pointwise event equivalence transports
uniform probability exactly.  `SpongeIndiffDeferredWork` supplies the matching
work-indexed deferred ideal interpreter: a construction consumes its whole
primitive-work segment while only its selected public RO coin is used, and a
concrete two-block construction/reveal run proves that the eager and deferred
public traces agree after a nontrivial permutation of the three work pairs.

Consequently the canonical unrestricted target is now the work-indexed
`SpongeIndiffWorkGame`, not this file's older `q`-indexed headline.  The latter
has honest budget meaning only on the explicitly proved
`SingleBlockConstruction` fragment.  The remaining theorem is sharply named:
generalize the exhibited eager/deferred coordinate move to an adaptive
same-space coupling, prove agreement away from its consistency/capacity bad
event, price that event on the work space, and perform the
random-permutation/random-function switch.  The atomic consistency event is
already exact: `SpongeIndiffPrefixConflict` proves a one-prefix construction
rejects iff the primitive edge and lazy RO had previously sampled unequal rate
values at that rooted prefix; either fresh side is conflict-free.
`SpongeIndiffPrefixFailure` lifts that atom through arbitrary message length:
every recursive `programPrefixes = none` is equivalent to malformed coin
lists, a direct sampled disagreement, or the exact failure of the updated
tail state.  Thus construction rejection is no longer an opaque error event;
the remaining work is to transport and price this exact adaptive event.
The construction already squeezes one rate element after a nonempty unpadded
message of any block length; the deployed padding/domain rule remains
`[SPONGE-padding]`.

## Keystones (ATLAS: satisfiable + teeth + premise inhabitation, BUILT)
`SpongeExample`: over `ZMod 2 × Fin 2`, the FIRST forward query at the IV
capacity is rate-completing with completed message `[a]` (computed through
`completion?_empty_iv`), the simulator programs `H [a]` into it, the walk
squeezes it back, the second identical query REPLAYS it, and path uniqueness
survives the step; teeth — two RO's differing at the completed message force
DIFFERENT simulator answers (`simFwd_reads_H`: the programming is
load-bearing), and the capacity-collision event is exhibited (`capBad_pair`),
has probability EXACTLY `1/N` at two queries (`capBad_two_prob` — the bound
ATTAINED, not slack), and is nonempty (`capBad_two_pos`).
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic
import Selvage.FiatShamir
import Selvage.CollisionResistanceROM
import Selvage.Sumcheck

namespace Minidregg.Selvage

/-! ## §0 Handler extensions — three more laws of the LANDED `Oracle`
(`Selvage/FiatShamir.lean`), in its namespace: membership of a successful lookup,
lookup preservation under `respond`, and value-inversion of a fresh respond.
Nothing here re-derives the handler; these are frame laws the sponge walk and
the simulator's inverse direction need. -/

section OracleExt

open Classical

variable {Q C : Type}

/-- A successful lookup exhibits its log entry. -/
theorem Oracle.lookup_mem {O : Oracle Q C} {k : Q} {t : C}
    (h : O.lookup k = some t) : (k, t) ∈ O.log := by
  unfold Oracle.lookup at h
  cases hf : O.log.find? (fun e => decide (e.1 = k)) with
  | none => rw [hf] at h; cases h
  | some e =>
      rw [hf, Option.map_some] at h
      have he : e ∈ O.log := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      have : e = (k, t) := Prod.ext (of_decide_eq_true hp) (Option.some.inj h)
      exact this ▸ he

/-- Responding never DESTROYS a recorded answer: any query already answered
keeps its answer (hit: the handler does not move; fresh: the frame law). -/
theorem Oracle.lookup_respond_some {O : Oracle Q C} {u : Q} {w : C}
    (h : O.lookup u = some w) (q : Q) (v : C) :
    (O.respond q v).2.lookup u = some w := by
  by_cases hqu : u = q
  · subst hqu
    rw [Oracle.respond_hit h v]
    exact h
  · rw [Oracle.lookup_respond_ne O hqu v]
    exact h

/-- Search the log by VALUE — the inverse direction of the partial
permutation the log denotes. -/
noncomputable def Oracle.lookupInv (O : Oracle Q C) (t : C) : Option (Q × C) :=
  O.log.find? fun e => decide (e.2 = t)

@[simp] lemma Oracle.lookupInv_empty (t : C) :
    (Oracle.empty : Oracle Q C).lookupInv t = none := rfl

/-- Value-inversion of a fresh respond: if `v` was not a recorded VALUE
before, then after `respond s v` the first (only) entry with value `v` is
`(s, v)` — the inverse direction of the partial permutation finds the right
preimage. -/
theorem Oracle.invert_respond {O : Oracle Q C} {s : Q} {v : C}
    (hfresh : O.lookup s = none) (hval : ∀ e ∈ O.log, e.2 ≠ v) :
    (O.respond s v).2.lookupInv v = some (s, v) := by
  unfold Oracle.lookupInv
  rw [Oracle.respond_fresh_log hfresh, List.find?_append]
  have h1 : (O.log.find? fun e => decide (e.2 = v)) = none := by
    rw [List.find?_eq_none]
    intro e he
    simpa using hval e he
  rw [h1, Option.none_or, List.find?_cons_of_pos (by simp)]

end OracleExt

variable {Rate Cap : Type} [AddCommGroup Rate]

/-! ## §1 The sponge — absorb through a permutation, squeeze the rate.

State `Rate × Cap` (rate `r`, capacity `c` in the usual `2^c` counting when
`Cap` has `2^c` elements). Absorbing a block ADDS it into the rate and
permutes; squeezing reads the final rate. The permutation parameter's deployed
candidate is `Compiler/AirHash.lean`'s `permExec` at the deployed Poseidon2
parameters (`[AIR-poseidon-params]`) — instantiation, not imported (Selvage
boundary). Padding and multi-block squeeze are `[SPONGE-padding]`. -/

/-- One absorption: add the block into the rate, permute. -/
def absorbStep (P : Rate × Cap → Rate × Cap) (s : Rate × Cap) (x : Rate) :
    Rate × Cap :=
  P (s.1 + x, s.2)

/-- The absorb phase: fold the message's blocks through `absorbStep`. -/
def spongeAbsorb (P : Rate × Cap → Rate × Cap) (iv : Rate × Cap)
    (m : List Rate) : Rate × Cap :=
  m.foldl (absorbStep P) iv

/-- **The sponge hash**: absorb all blocks, squeeze the final rate. -/
def sponge (P : Rate × Cap → Rate × Cap) (iv : Rate × Cap)
    (m : List Rate) : Rate :=
  (spongeAbsorb P iv m).1

lemma spongeAbsorb_append (P : Rate × Cap → Rate × Cap) (iv : Rate × Cap)
    (m₁ m₂ : List Rate) :
    spongeAbsorb P iv (m₁ ++ m₂) = spongeAbsorb P (spongeAbsorb P iv m₁) m₂ :=
  List.foldl_append

/-! ## §2 The partial walk — the absorb phase through a permutation LOG.

The two worlds share this spine: the REAL world's log is consistent with the
true permutation (`walkFrom_agrees`); the IDEAL world's log is the simulator's.
`walkFrom` succeeds only if every needed permutation call is recorded. -/

section Walk

/-- Walk the absorb phase through the log: at state `s` and block `x`, look up
`(s.1 + x, s.2)`; fail on any unrecorded call. -/
noncomputable def walkFrom (O : Oracle (Rate × Cap) (Rate × Cap)) :
    Rate × Cap → List Rate → Option (Rate × Cap)
  | s, [] => some s
  | s, x :: m =>
      match O.lookup (s.1 + x, s.2) with
      | some t => walkFrom O t m
      | none => none

variable {O : Oracle (Rate × Cap) (Rate × Cap)}

@[simp] lemma walkFrom_nil (s : Rate × Cap) : walkFrom O s [] = some s := rfl

lemma walkFrom_cons (s : Rate × Cap) (x : Rate) (m : List Rate) :
    walkFrom O s (x :: m) =
      match O.lookup (s.1 + x, s.2) with
      | some t => walkFrom O t m
      | none => none := rfl

lemma walkFrom_append (s : Rate × Cap) (m₁ m₂ : List Rate) :
    walkFrom O s (m₁ ++ m₂) = (walkFrom O s m₁).bind fun t => walkFrom O t m₂ := by
  induction m₁ generalizing s with
  | nil => rfl
  | cons x m₁ ih =>
      rw [List.cons_append, walkFrom_cons, walkFrom_cons]
      cases hl : O.lookup (s.1 + x, s.2) with
      | some t => exact ih t
      | none => rfl

/-- Monotonicity: a successful walk survives any `respond` (hit: the handler
does not move; fresh: old lookups are preserved). -/
lemma walkFrom_respond (q v : Rate × Cap) {m : List Rate} :
    ∀ {u t : Rate × Cap}, walkFrom O u m = some t →
      walkFrom (O.respond q v).2 u m = some t := by
  induction m with
  | nil => intro u t h; exact h
  | cons x m ih =>
      intro u t h
      rw [walkFrom_cons] at h ⊢
      cases hl : O.lookup (u.1 + x, u.2) with
      | none => rw [hl] at h; cases h
      | some w =>
          rw [hl] at h
          rw [Oracle.lookup_respond_some hl q v]
          exact ih h

/-- The walk's endpoint is the start or a recorded OUTPUT of the log. -/
lemma walkFrom_end_mem {m : List Rate} :
    ∀ {u w : Rate × Cap}, walkFrom O u m = some w →
      w = u ∨ w ∈ O.log.map Prod.snd := by
  induction m with
  | nil => intro u w h; exact Or.inl (Option.some.inj h).symm
  | cons x m ih =>
      intro u w h
      rw [walkFrom_cons] at h
      cases hl : O.lookup (u.1 + x, u.2) with
      | none => rw [hl] at h; cases h
      | some t =>
          rw [hl] at h
          rcases ih h with rfl | hmem
          · exact Or.inr (List.mem_map.mpr ⟨_, Oracle.lookup_mem hl, rfl⟩)
          · exact Or.inr hmem

/-- On a log CONSISTENT with a total permutation `P`, the walk computes the
sponge's absorb phase: the real world's primitive interface and the sponge
construction agree by definition, through any partial view. -/
lemma walkFrom_agrees {P : Rate × Cap → Rate × Cap}
    (hcons : ∀ k w, O.lookup k = some w → w = P k) {m : List Rate} :
    ∀ {u w : Rate × Cap}, walkFrom O u m = some w → spongeAbsorb P u m = w := by
  induction m with
  | nil => intro u w h; exact Option.some.inj h
  | cons x m ih =>
      intro u w h
      rw [walkFrom_cons] at h
      cases hl : O.lookup (u.1 + x, u.2) with
      | none => rw [hl] at h; cases h
      | some t =>
          rw [hl] at h
          show spongeAbsorb P (absorbStep P u x) m = w
          rw [show absorbStep P u x = t from (hcons _ _ hl).symm]
          exact ih h

end Walk

/-! ## §3 Rooted paths and the completion detector.

A capacity `c` is ROOTED in a log if some message's partial walk from the IV
reaches a state with capacity `c`. A forward query at a rooted capacity
COMPLETES an absorption: it is the last permutation call of the message
`m ++ [s.1 − b]` (where `(b, c)` is the rooted state) — exactly the calls the
honest sponge makes. `completion?` detects this; it programs only when the
path is UNIQUE (off the capacity-collision bad event it always is — §5). -/

section Paths

variable {O : Oracle (Rate × Cap) (Rate × Cap)}

/-- `p = (message, rate)` is a rooted path to capacity `c`: the partial walk
of `p.1` from the IV reaches `(p.2, c)`. -/
def IsPath (O : Oracle (Rate × Cap) (Rate × Cap)) (iv : Rate × Cap) (c : Cap)
    (p : List Rate × Rate) : Prop :=
  walkFrom O iv p.1 = some (p.2, c)

/-- Every rooted capacity has at most ONE path — the simulator's bookkeeping
invariant, maintained off the capacity-collision bad event (§5). -/
def UniquePaths (O : Oracle (Rate × Cap) (Rate × Cap)) (iv : Rate × Cap) :
    Prop :=
  ∀ (c : Cap) (p p' : List Rate × Rate),
    IsPath O iv c p → IsPath O iv c p' → p = p'

open Classical in
/-- The completed message of forward query `s`, if `s.2` is rooted by a UNIQUE
path `(m, b)`: the query absorbs one more block, `m ++ [s.1 − b]`. `none` when
unrooted (fresh random answer) or when several paths exist (only on the bad
event; the simulator then declines to program — the bound pays for it). -/
noncomputable def completion? (O : Oracle (Rate × Cap) (Rate × Cap))
    (iv s : Rate × Cap) : Option (List Rate) :=
  if h : ∃! p : List Rate × Rate, IsPath O iv s.2 p
  then some (h.choose.1 ++ [s.1 - h.choose.2])
  else none

lemma completion?_spec {iv s : Rate × Cap} {m : List Rate}
    (h : completion? O iv s = some m) :
    ∃ p₀ : List Rate × Rate, IsPath O iv s.2 p₀ ∧
      (∀ p, IsPath O iv s.2 p → p = p₀) ∧ m = p₀.1 ++ [s.1 - p₀.2] := by
  unfold completion? at h
  split at h
  · rename_i hex
    exact ⟨hex.choose, hex.choose_spec.1, fun p hp => hex.choose_spec.2 p hp,
      (Option.some.inj h).symm⟩
  · cases h

lemma completion?_eq_some {iv s : Rate × Cap} {p₀ : List Rate × Rate}
    (hp₀ : IsPath O iv s.2 p₀) (huniq : ∀ p, IsPath O iv s.2 p → p = p₀) :
    completion? O iv s = some (p₀.1 ++ [s.1 - p₀.2]) := by
  have hex : ∃! p : List Rate × Rate, IsPath O iv s.2 p :=
    ⟨p₀, hp₀, fun p hp => huniq p hp⟩
  unfold completion?
  rw [dif_pos hex]
  rw [huniq _ hex.choose_spec.1]

/-- In the EMPTY log the only rooted path is the empty message at the IV. -/
lemma isPath_empty {iv : Rate × Cap} {c : Cap} {p : List Rate × Rate}
    (h : IsPath Oracle.empty iv c p) : p = ([], iv.1) ∧ c = iv.2 := by
  obtain ⟨m, r⟩ := p
  cases m with
  | nil =>
      have h' : iv = (r, c) := Option.some.inj h
      subst h'
      exact ⟨rfl, rfl⟩
  | cons x m =>
      have h' : walkFrom Oracle.empty iv (x :: m) = none := by
        rw [walkFrom_cons, Oracle.lookup_empty]
      rw [IsPath, h'] at h
      cases h

theorem uniquePaths_empty (iv : Rate × Cap) : UniquePaths Oracle.empty iv :=
  fun _c _p _p' hp hp' => (isPath_empty hp).1.trans (isPath_empty hp').1.symm

/-- The FIRST forward query at the IV capacity is rate-completing, with
completed message the single block `s.1 − iv.1` — the base of the sponge/RO
agreement: single-block absorptions are programmed from the start. -/
lemma completion?_empty_iv {iv s : Rate × Cap} (h : s.2 = iv.2) :
    completion? Oracle.empty iv s = some [s.1 - iv.1] := by
  have hp₀ : IsPath Oracle.empty iv s.2 ([], iv.1) := by
    show some iv = some (iv.1, s.2)
    rw [h]
  have := completion?_eq_some hp₀ fun p hp => (isPath_empty hp).1
  simpa using this

lemma completion?_empty_ne {iv s : Rate × Cap} (h : s.2 ≠ iv.2) :
    completion? Oracle.empty iv s = none := by
  unfold completion?
  rw [dif_neg]
  rintro ⟨p, hp, -⟩
  exact h (isPath_empty hp).2

end Paths

/-! ## §4 The simulator — and the programming keystone.

The standard sponge-indifferentiability simulator (Bertoni–Daemen–Peeters–Van
Assche 2008 shape): one shared partial-permutation log for BOTH query
directions; a fresh forward query that completes rooted path `m` gets rate
`H m` (the RO programmed into the squeeze position) and a fresh capacity coin;
unrooted forward and all fresh inverse queries answer coins. Consistency is
NOT re-proved: the simulator IS `Oracle.respond` at a computed value, so the
landed handler laws carry replay, frame, and consistency verbatim. -/

section Simulator

open Classical

variable {O : Oracle (Rate × Cap) (Rate × Cap)}

/-- **Simulator, forward direction.** Programs `(H m, coin.2)` on a
rate-completing query, answers `coin` when unrooted; replays automatically on
a repeated query (`Oracle.respond`'s hit branch ignores the computed value). -/
noncomputable def simFwd (H : List Rate → Rate) (iv : Rate × Cap)
    (O : Oracle (Rate × Cap) (Rate × Cap)) (s coin : Rate × Cap) :
    (Rate × Cap) × Oracle (Rate × Cap) (Rate × Cap) :=
  O.respond s
    (match completion? O iv s with
      | some m => (H m, coin.2)
      | none => coin)

/-- **Simulator, inverse direction.** Replay a logged preimage by VALUE
search; else answer the fresh coin and record `coin ↦ t`, so a future forward
query at `coin` replays `t` (`simInv_lookup`). (If the coin collides with an
existing KEY — an input collision, paid by the bad event — the log is left
unchanged rather than corrupted: `respond`'s hit branch.) -/
noncomputable def simInv (O : Oracle (Rate × Cap) (Rate × Cap))
    (t coin : Rate × Cap) : (Rate × Cap) × Oracle (Rate × Cap) (Rate × Cap) :=
  match O.lookupInv t with
  | some e => (e.1, O)
  | none => (coin, (O.respond coin t).2)

/-- **The sponge simulator**, dispatched: `.inl` forward, `.inr` inverse —
one handler over signed permutation queries, one shared log, programming
through `H`. -/
noncomputable def spongeSimulator (H : List Rate → Rate) (iv : Rate × Cap)
    (O : Oracle (Rate × Cap) (Rate × Cap)) :
    (Rate × Cap) ⊕ (Rate × Cap) → (Rate × Cap) →
      (Rate × Cap) × Oracle (Rate × Cap) (Rate × Cap)
  | .inl s, coin => simFwd H iv O s coin
  | .inr t, coin => simInv O t coin

@[simp] lemma spongeSimulator_fwd (H : List Rate → Rate) (iv : Rate × Cap)
    (O : Oracle (Rate × Cap) (Rate × Cap)) (s coin : Rate × Cap) :
    spongeSimulator H iv O (.inl s) coin = simFwd H iv O s coin := rfl

@[simp] lemma spongeSimulator_inv (H : List Rate → Rate) (iv : Rate × Cap)
    (O : Oracle (Rate × Cap) (Rate × Cap)) (t coin : Rate × Cap) :
    spongeSimulator H iv O (.inr t) coin = simInv O t coin := rfl

/-- Replay: a repeated forward query returns the recorded answer, and the
handler does not move — free from `respond_hit`. -/
lemma simFwd_replay {iv s : Rate × Cap} {t : Rate × Cap}
    (h : O.lookup s = some t) (H : List Rate → Rate) (coin : Rate × Cap) :
    simFwd H iv O s coin = (t, O) := by
  unfold simFwd
  exact Oracle.respond_hit h _

/-- Programming: a fresh rate-completing query answers `(H m, coin.2)` — the
RO's value in the rate, a fresh coin in the capacity. -/
lemma simFwd_program {iv s : Rate × Cap} {m : List Rate}
    (hfresh : O.lookup s = none) (hm : completion? O iv s = some m)
    (H : List Rate → Rate) (coin : Rate × Cap) :
    (simFwd H iv O s coin).1 = (H m, coin.2) := by
  unfold simFwd
  rw [hm]
  exact Oracle.respond_fresh_fst hfresh _

lemma simFwd_program_log {iv s : Rate × Cap} {m : List Rate}
    (hfresh : O.lookup s = none) (hm : completion? O iv s = some m)
    (H : List Rate → Rate) (coin : Rate × Cap) :
    (simFwd H iv O s coin).2.log = O.log ++ [(s, (H m, coin.2))] := by
  unfold simFwd
  rw [hm]
  exact Oracle.respond_fresh_log hfresh _

/-- Unrooted: a fresh query at an unrooted capacity answers the coin. -/
lemma simFwd_unrooted {iv s : Rate × Cap}
    (hfresh : O.lookup s = none) (hm : completion? O iv s = none)
    (H : List Rate → Rate) (coin : Rate × Cap) :
    (simFwd H iv O s coin).1 = coin := by
  unfold simFwd
  rw [hm]
  exact Oracle.respond_fresh_fst hfresh _

/-- **Consistency**: asking the same forward query twice returns the same
answer, whatever the second step's coin or (re)computed completion — verbatim
`respond_consistent` of the landed handler. -/
lemma simFwd_selfconsistent (H : List Rate → Rate) (iv : Rate × Cap)
    (O : Oracle (Rate × Cap) (Rate × Cap)) (s coin coin' : Rate × Cap) :
    (simFwd H iv (simFwd H iv O s coin).2 s coin').1
      = (simFwd H iv O s coin).1 := by
  unfold simFwd
  exact Oracle.respond_consistent O s _ _

/-- **Teeth — the programming is load-bearing**: two RO's differing at the
completed message force DIFFERENT simulator answers. The simulator genuinely
READS `H`; it is not a fresh-coin handler with decoration. -/
theorem simFwd_reads_H {iv s : Rate × Cap} {m : List Rate}
    (hfresh : O.lookup s = none) (hm : completion? O iv s = some m)
    {H H' : List Rate → Rate} (hHH : H m ≠ H' m) (coin : Rate × Cap) :
    (simFwd H iv O s coin).1 ≠ (simFwd H' iv O s coin).1 := by
  rw [simFwd_program hfresh hm, simFwd_program hfresh hm]
  exact fun h => hHH (congrArg Prod.fst h)

omit [AddCommGroup Rate] in
/-- Inverse replay: a value already in the log returns its recorded preimage,
and the handler does not move. -/
lemma simInv_found {t coin : Rate × Cap} {e : (Rate × Cap) × (Rate × Cap)}
    (h : O.lookupInv t = some e) :
    simInv O t coin = (e.1, O) := by
  unfold simInv
  rw [h]

omit [AddCommGroup Rate] in
/-- Inverse fresh: an unseen value answers the coin and records `coin ↦ t`. -/
lemma simInv_fresh {t coin : Rate × Cap}
    (h : O.lookupInv t = none) :
    simInv O t coin = (coin, (O.respond coin t).2) := by
  unfold simInv
  rw [h]

omit [AddCommGroup Rate] in
/-- **Forward/inverse consistency, inverse first**: after a fresh inverse
query answered `coin`, the FORWARD query at `coin` replays `t` — the two
directions describe one partial permutation. -/
lemma simInv_lookup {t coin : Rate × Cap}
    (hf : O.lookupInv t = none)
    (hcoin : O.lookup coin = none) :
    (simInv O t coin).2.lookup coin = some t := by
  rw [simInv_fresh hf]
  show (O.respond coin t).2.lookup coin = some t
  rw [Oracle.lookup_respond_self, Oracle.respond_fresh_fst hcoin]

/-- **Forward/inverse consistency, forward first**: after a fresh forward
query answered `v` (with `v` not a previously recorded value), the INVERSE
query at `v` returns `s` — through `Oracle.invert_respond`. -/
theorem simInv_inverts {iv s : Rate × Cap} (H : List Rate → Rate)
    (coin coin' : Rate × Cap) (hfresh : O.lookup s = none)
    (hval : ∀ e ∈ O.log, e.2 ≠ (simFwd H iv O s coin).1) :
    (simInv (simFwd H iv O s coin).2 (simFwd H iv O s coin).1 coin').1 = s := by
  have hfind : (simFwd H iv O s coin).2.lookupInv (simFwd H iv O s coin).1
      = some (s, (simFwd H iv O s coin).1) := by
    unfold simFwd at hval ⊢
    rw [Oracle.respond_fresh_fst hfresh] at hval ⊢
    exact Oracle.invert_respond hfresh hval
  rw [simInv_found hfind]

/-- **`walk_programs` — the programming keystone.** If fresh forward query `s`
completes rooted path `m` (`completion? = some m`), then in the log extended
with ANY value `v` at `s`, the FULL walk of `m` succeeds and ends at `v`:
`m`'s prefix survives by monotonicity, and its last block lands exactly on the
new entry (`b + (s.1 − b) = s.1`). With `v = (H m, coin.2)` — the simulator's
programmed value — the sponge walk through the simulator's log SQUEEZES
EXACTLY the RO's answer at `m`: the real/ideal agreement at the construction
interface, one step, for every log, state, and message. -/
theorem walk_programs {iv s : Rate × Cap}
    (hfresh : O.lookup s = none) {m : List Rate}
    (hm : completion? O iv s = some m) (v : Rate × Cap) :
    walkFrom (O.respond s v).2 iv m = some v := by
  obtain ⟨p₀, hp₀, -, rfl⟩ := completion?_spec hm
  rw [walkFrom_append, walkFrom_respond s v hp₀]
  show walkFrom (O.respond s v).2 (p₀.2, s.2) [s.1 - p₀.2] = some v
  rw [walkFrom_cons]
  have hsc : ((((p₀.2, s.2) : Rate × Cap).1 + (s.1 - p₀.2),
      ((p₀.2, s.2) : Rate × Cap).2) : Rate × Cap) = s := by
    show ((p₀.2 + (s.1 - p₀.2), s.2) : Rate × Cap) = s
    have : p₀.2 + (s.1 - p₀.2) = s.1 := by abel
    rw [this]
  rw [hsc, Oracle.lookup_respond_self, Oracle.respond_fresh_fst hfresh]
  rfl

/-- The keystone at the simulator's own step: the walk of the completed
message through `simFwd`'s log is the programmed `(H m, coin.2)`. -/
theorem simFwd_walk {iv s : Rate × Cap}
    (hfresh : O.lookup s = none) {m : List Rate}
    (hm : completion? O iv s = some m) (H : List Rate → Rate)
    (coin : Rate × Cap) :
    walkFrom (simFwd H iv O s coin).2 iv m = some (H m, coin.2) := by
  unfold simFwd
  rw [hm]
  exact walk_programs hfresh hm _

end Simulator

/-! ## §5 Path-uniqueness preservation — the simulator's consistency OFF the
bad event, per step.

The bad event is a fresh capacity hitting `capsOf` — any capacity the log
(inputs AND outputs) or the IV mentions. Off it, a new entry can only be the
LAST step of a rooted path (`walkFrom_respond_split`: nothing continues from
the fresh output capacity), and can only extend THE unique rooted prefix — so
`UniquePaths` survives every simulator step, in both query directions. -/

section Preservation

open Classical

variable {O : Oracle (Rate × Cap) (Rate × Cap)}

/-- Every capacity the log mentions (entry inputs and outputs) plus the IV's —
the set a fresh capacity coin must MISS. -/
def capsOf (O : Oracle (Rate × Cap) (Rate × Cap)) (iv : Rate × Cap) :
    List Cap :=
  iv.2 :: ((O.log.map fun e => e.1.2) ++ O.log.map fun e => e.2.2)

omit [AddCommGroup Rate] in
lemma iv_cap_mem (O : Oracle (Rate × Cap) (Rate × Cap)) (iv : Rate × Cap) :
    iv.2 ∈ capsOf O iv :=
  List.mem_cons_self ..

omit [AddCommGroup Rate] in
lemma in_cap_mem {iv : Rate × Cap} {e : (Rate × Cap) × (Rate × Cap)}
    (he : e ∈ O.log) : e.1.2 ∈ capsOf O iv :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))

omit [AddCommGroup Rate] in
lemma out_cap_mem {iv : Rate × Cap} {e : (Rate × Cap) × (Rate × Cap)}
    (he : e ∈ O.log) : e.2.2 ∈ capsOf O iv :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩))

omit [AddCommGroup Rate] in
/-- A key whose capacity misses `capsOf` was never queried. -/
lemma lookup_cap_none {iv k : Rate × Cap} (hk : k.2 ∉ capsOf O iv) :
    O.lookup k = none := by
  rw [Oracle.lookup_eq_none]
  intro e he heq
  exact hk (heq ▸ in_cap_mem he)

/-- A rooted capacity is mentioned: paths only reach `capsOf`. -/
lemma isPath_cap_mem {iv : Rate × Cap} {c : Cap} {p : List Rate × Rate}
    (h : IsPath O iv c p) : c ∈ capsOf O iv := by
  rcases walkFrom_end_mem h with heq | hmem
  · have hc : c = iv.2 := congrArg Prod.snd heq
    rw [hc]
    exact iv_cap_mem O iv
  · obtain ⟨e, he, hee⟩ := List.mem_map.mp hmem
    have hc : c = e.2.2 := (congrArg Prod.snd hee).symm
    rw [hc]
    exact out_cap_mem he

/-- **Walk decomposition across one fresh `respond`**: a successful walk in
the extended log either already succeeded in the old log, or it splits at the
FIRST use of the new entry — an old-log prefix reaching the new entry's input,
then the entry, then a tail from its output. -/
lemma walkFrom_respond_split {s v : Rate × Cap}
    (hfresh : O.lookup s = none) {m : List Rate} :
    ∀ {u w : Rate × Cap}, walkFrom (O.respond s v).2 u m = some w →
      walkFrom O u m = some w ∨
        ∃ (m₁ : List Rate) (x : Rate) (m₂ : List Rate) (b : Rate × Cap),
          m = m₁ ++ x :: m₂ ∧ walkFrom O u m₁ = some b ∧
            ((b.1 + x, b.2) : Rate × Cap) = s ∧
            walkFrom (O.respond s v).2 v m₂ = some w := by
  induction m with
  | nil => intro u w h; exact Or.inl h
  | cons y m ih =>
      intro u w h
      rw [walkFrom_cons] at h
      by_cases hk : ((u.1 + y, u.2) : Rate × Cap) = s
      · have hlv : (O.respond s v).2.lookup (u.1 + y, u.2) = some v := by
          rw [hk, Oracle.lookup_respond_self, Oracle.respond_fresh_fst hfresh]
        rw [hlv] at h
        exact Or.inr ⟨[], y, m, u, rfl, rfl, hk, h⟩
      · rw [Oracle.lookup_respond_ne O hk v] at h
        cases hol : O.lookup (u.1 + y, u.2) with
        | none => rw [hol] at h; cases h
        | some t =>
            rw [hol] at h
            rcases ih h with hleft | ⟨m₁, x, m₂, b, hm, hb, hbs, htail⟩
            · left
              rw [walkFrom_cons, hol]
              exact hleft
            · right
              refine ⟨y :: m₁, x, m₂, b, by rw [hm, List.cons_append], ?_, hbs, htail⟩
              rw [walkFrom_cons, hol]
              exact hb

/-- **Preservation, fresh OUTPUT capacity** (the forward step): extending with
`s ↦ v` where `v.2` misses `capsOf` and `v.2 ≠ s.2` keeps paths unique. A new
path must end at the new entry (nothing continues from the fresh capacity `v.2`
— no input mentions it), and its prefix is THE unique rooted path to `s.2`. -/
theorem uniquePaths_respond_freshOut {iv s v : Rate × Cap}
    (hU : UniquePaths O iv) (hfresh : O.lookup s = none)
    (hv : v.2 ∉ capsOf O iv) (hvs : v.2 ≠ s.2) :
    UniquePaths (O.respond s v).2 iv := by
  have hchar : ∀ (c : Cap) (p : List Rate × Rate),
      IsPath (O.respond s v).2 iv c p →
        IsPath O iv c p ∨
          (c = v.2 ∧ ∃ p₀ : List Rate × Rate, IsPath O iv s.2 p₀ ∧
            p = (p₀.1 ++ [s.1 - p₀.2], v.1)) := by
    intro c p hp
    rcases walkFrom_respond_split hfresh hp with hleft | ⟨m₁, x, m₂, b, hm, hb, hbs, htail⟩
    · exact Or.inl hleft
    · cases m₂ with
      | cons y m₂' =>
          exfalso
          rw [walkFrom_cons] at htail
          have hnone : (O.respond s v).2.lookup (v.1 + y, v.2) = none := by
            rw [Oracle.lookup_eq_none]
            intro e he heq
            rw [Oracle.respond_fresh_log hfresh] at he
            rcases List.mem_append.mp he with hold | hnew
            · exact hv (congrArg Prod.snd heq ▸ in_cap_mem hold)
            · rw [List.mem_singleton] at hnew
              subst hnew
              exact hvs (congrArg Prod.snd heq).symm
          rw [hnone] at htail
          simp at htail
      | nil =>
          have hv' : v = (p.2, c) := Option.some.inj htail
          refine Or.inr ⟨(congrArg Prod.snd hv').symm, (m₁, b.1), ?_, ?_⟩
          · show walkFrom O iv m₁ = some (b.1, s.2)
            rw [← congrArg Prod.snd hbs]
            exact hb
          · have hx : x = s.1 - b.1 := by
              have h1 : b.1 + x = s.1 := congrArg Prod.fst hbs
              rw [← h1]
              abel
            refine Prod.ext ?_ (congrArg Prod.fst hv').symm
            rw [hm, hx]
  intro c p p' hp hp'
  rcases hchar c p hp with h1 | ⟨rfl, p₀, hp₀, rfl⟩
  · rcases hchar c p' hp' with h2 | ⟨hcv, -⟩
    · exact hU c p p' h1 h2
    · exact absurd (hcv ▸ isPath_cap_mem h1) hv
  · rcases hchar _ p' hp' with h2 | ⟨-, p₀', hp₀', rfl⟩
    · exact absurd (isPath_cap_mem h2) hv
    · rw [hU s.2 p₀ p₀' hp₀ hp₀']

/-- **Preservation, fresh KEY capacity** (the inverse step): extending with
`k ↦ t` where `k.2` misses `capsOf` keeps paths unique — no walk can even
REACH the new entry (its input capacity is mentioned nowhere), so the path set
is unchanged. -/
theorem uniquePaths_respond_freshKey {iv k t : Rate × Cap}
    (hU : UniquePaths O iv) (hk : k.2 ∉ capsOf O iv) :
    UniquePaths (O.respond k t).2 iv := by
  have hfresh : O.lookup k = none := lookup_cap_none hk
  have hchar : ∀ (c : Cap) (p : List Rate × Rate),
      IsPath (O.respond k t).2 iv c p → IsPath O iv c p := by
    intro c p hp
    rcases walkFrom_respond_split hfresh hp with hleft | ⟨m₁, x, m₂, b, -, hb, hbk, -⟩
    · exact hleft
    · exfalso
      have hb2 : b.2 = k.2 := by rw [← hbk]
      rcases walkFrom_end_mem hb with hbiv | hmem
      · refine hk ?_
        have hkiv : k.2 = iv.2 := by rw [← hb2, hbiv]
        rw [hkiv]
        exact iv_cap_mem O iv
      · obtain ⟨e, he, hee⟩ := List.mem_map.mp hmem
        have : e.2.2 = k.2 := by rw [hee]; exact hb2
        exact hk (this ▸ out_cap_mem he)
  intro c p p' hp hp'
  exact hU c p p' (hchar c p hp) (hchar c p' hp')

/-- The simulator's FORWARD step preserves path uniqueness whenever its fresh
capacity coin misses `capsOf` and the queried capacity (both branches program
capacity `coin.2`; replay leaves the log alone). -/
theorem uniquePaths_simFwd {iv s coin : Rate × Cap}
    (hU : UniquePaths O iv) (H : List Rate → Rate)
    (hcoin : coin.2 ∉ capsOf O iv) (hcs : coin.2 ≠ s.2) :
    UniquePaths (simFwd H iv O s coin).2 iv := by
  unfold simFwd
  cases hlk : O.lookup s with
  | some t =>
      rw [Oracle.respond_hit hlk]
      exact hU
  | none =>
      cases hc : completion? O iv s with
      | some m => exact uniquePaths_respond_freshOut hU hlk hcoin hcs
      | none => exact uniquePaths_respond_freshOut hU hlk hcoin hcs

/-- The simulator's INVERSE step preserves path uniqueness whenever its fresh
coin's capacity misses `capsOf` (replay and the degenerate key-collision
branch leave the log alone). -/
theorem uniquePaths_simInv {iv t coin : Rate × Cap}
    (hU : UniquePaths O iv) (hcoin : coin.2 ∉ capsOf O iv) :
    UniquePaths (simInv O t coin).2 iv := by
  unfold simInv
  cases hf : O.lookupInv t with
  | some e => exact hU
  | none => exact uniquePaths_respond_freshKey hU hcoin

end Preservation

/-! ## §6 The capacity-collision bad event, PRICED.

`q` fresh capacity coins go bad if two collide (birthday — the LANDED
`birthday_bound`, cited through a transport, never re-derived) or one hits a
fixed avoid set `S` (union bound over coordinates, each priced by the LANDED
`uniformProb_coord_mem` of `Selvage/Sumcheck.lean` — cited, not re-derived).
Covered scope,
mirroring `Selvage/CollisionResistanceROM.lean`: NON-ADAPTIVE — `S` is fixed
before the coins; the adaptively-grown `capsOf` needs the same
schedule-machinery named there as `[CR-ROM-adaptive]`, folded here into
`[SPONGE-indiff-game]`. -/

section BadEvent

variable {Cap : Type} [Fintype Cap]

/-- The capacity-collision bad event: two fresh capacity coins agree, or some
coin lands in the avoid set `S` (the IV plus the schedule's query capacities —
at most `q + 1` values for a `q`-query schedule). -/
def CapBad {qc : ℕ} (S : Finset Cap) (c : Fin qc → Cap) : Prop :=
  (∃ i j : Fin qc, i < j ∧ c i = c j) ∨ ∃ i, c i ∈ S

/-- Transport: capacity-coin collisions ARE the landed collision event at
range size `|Cap|` — so `birthday_bound` prices them, cited, not re-derived. -/
lemma capCollisionProb_eq (qc : ℕ) :
    uniformProb (Fin qc → Cap) (fun c => ∃ i j : Fin qc, i < j ∧ c i = c j)
      = collisionProb qc (Fintype.card Cap) := by
  classical
  unfold collisionProb
  rw [← uniformProb_equiv
    (Equiv.arrowCongr (Equiv.refl (Fin qc)) (Fintype.equivFin Cap)) Collides]
  refine uniformProb_congr fun c => ⟨?_, ?_⟩
  · rintro ⟨i, j, hij, hc⟩
    exact ⟨i, j, hij, congrArg (⇑(Fintype.equivFin Cap)) hc⟩
  · rintro ⟨i, j, hij, hc⟩
    refine ⟨i, j, hij, (Fintype.equivFin Cap).injective ?_⟩
    exact hc

/-- Union bound: some coordinate hits `S` with probability `≤ q·|S|/|Cap|` —
per coordinate, the LANDED `uniformProb_coord_mem` (`Selvage/Sumcheck.lean`). -/
lemma capHit_le (qc : ℕ) (S : Finset Cap) :
    uniformProb (Fin qc → Cap) (fun c => ∃ i, c i ∈ S)
      ≤ (qc : ℝ) * (S.card : ℝ) / (Fintype.card Cap : ℝ) := by
  refine le_trans (uniformProb_exists_le (C := Fin qc → Cap) (m := qc)
    fun (i : Fin qc) (c : Fin qc → Cap) => c i ∈ S) ?_
  calc ∑ i : Fin qc, uniformProb (Fin qc → Cap) (fun c => c i ∈ S)
      ≤ ∑ _i : Fin qc, (S.card : ℝ) / (Fintype.card Cap : ℝ) :=
        Finset.sum_le_sum fun i _ => uniformProb_coord_mem i S
    _ = (qc : ℝ) * ((S.card : ℝ) / (Fintype.card Cap : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (qc : ℝ) * (S.card : ℝ) / (Fintype.card Cap : ℝ) := by ring

/-- **The bad-event bound, sharp form**: `Pr[CapBad] ≤ q(q−1)/(2N) + q·|S|/N`
over `N = |Cap|` — birthday (CITED: `birthday_bound`) plus the hit bound. -/
theorem capBad_bound (qc : ℕ) (S : Finset Cap) :
    uniformProb (Fin qc → Cap) (CapBad S)
      ≤ (qc : ℝ) * ((qc : ℝ) - 1) / (2 * (Fintype.card Cap : ℝ))
        + (qc : ℝ) * (S.card : ℝ) / (Fintype.card Cap : ℝ) := by
  have h1 : uniformProb (Fin qc → Cap) (CapBad S)
      ≤ uniformProb (Fin qc → Cap) (fun c => ∃ i j : Fin qc, i < j ∧ c i = c j)
        + uniformProb (Fin qc → Cap) (fun c => ∃ i, c i ∈ S) :=
    uniformProb_or_le _ _
  refine le_trans h1 (add_le_add ?_ (capHit_le qc S))
  rw [capCollisionProb_eq]
  exact birthday_bound qc (Fintype.card Cap)

/-- **The capacity bound, headline form**: for any avoid set of size at most
`q + 1` (IV + the schedule's query capacities), `Pr[CapBad] ≤ 2q²/|Cap|` —
the `O(q²/2^c)` of the sponge-indifferentiability literature, with the
pessimistic explicit constant `2`. -/
theorem capBad_le (qc : ℕ) (S : Finset Cap) (hS : S.card ≤ qc + 1) :
    uniformProb (Fin qc → Cap) (CapBad S)
      ≤ 2 * (qc : ℝ) ^ 2 / (Fintype.card Cap : ℝ) := by
  refine le_trans (capBad_bound qc S) ?_
  have hs : (S.card : ℝ) ≤ (qc : ℝ) + 1 := by exact_mod_cast hS
  have hq : (0 : ℝ) ≤ (qc : ℝ) := Nat.cast_nonneg _
  have hqq : (qc : ℝ) ≤ (qc : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos qc with h | h
    · subst h; norm_num
    · have h1 : (1 : ℝ) ≤ (qc : ℝ) := by exact_mod_cast h
      nlinarith
  have key : (qc : ℝ) * ((qc : ℝ) - 1) / 2 + (qc : ℝ) * (S.card : ℝ)
      ≤ 2 * (qc : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs hq]
  have hinv : (0 : ℝ) ≤ 1 / (Fintype.card Cap : ℝ) :=
    one_div_nonneg.mpr (Nat.cast_nonneg _)
  calc (qc : ℝ) * ((qc : ℝ) - 1) / (2 * (Fintype.card Cap : ℝ))
        + (qc : ℝ) * (S.card : ℝ) / (Fintype.card Cap : ℝ)
      = ((qc : ℝ) * ((qc : ℝ) - 1) / 2 + (qc : ℝ) * (S.card : ℝ))
          * (1 / (Fintype.card Cap : ℝ)) := by ring
    _ ≤ (2 * (qc : ℝ) ^ 2) * (1 / (Fintype.card Cap : ℝ)) :=
        mul_le_mul_of_nonneg_right key hinv
    _ = 2 * (qc : ℝ) ^ 2 / (Fintype.card Cap : ℝ) := by ring

omit [Fintype Cap] in
/-- **Teeth — the bad event is exhibited**: two equal capacity coins are a
capacity collision. -/
theorem capBad_pair (S : Finset Cap) (v : Cap) :
    CapBad S (fun _ : Fin 2 => v) :=
  Or.inl ⟨0, 1, by decide, rfl⟩

/-- **Teeth — the two-query probability, EXACTLY**: with an empty avoid set,
`Pr[CapBad] = 1/|Cap|` at `q = 2` — the landed `collisionProb_two`, and
precisely the value of `capBad_bound` there: the bound is ATTAINED, not
slack. -/
theorem capBad_two_prob :
    uniformProb (Fin 2 → Cap) (CapBad (∅ : Finset Cap))
      = 1 / (Fintype.card Cap : ℝ) := by
  have hev : uniformProb (Fin 2 → Cap) (CapBad (∅ : Finset Cap))
      = uniformProb (Fin 2 → Cap) (fun c => ∃ i j : Fin 2, i < j ∧ c i = c j) :=
    uniformProb_congr fun c =>
      ⟨fun h => h.elim id (fun ⟨_, hi⟩ => absurd hi (Finset.notMem_empty _)),
        Or.inl⟩
  rw [hev, capCollisionProb_eq, BirthdayExample.collisionProb_two]

/-- The bad event is POSSIBLE (nonvacuous bound) for any real capacity. -/
theorem capBad_two_pos (h : 0 < Fintype.card Cap) :
    0 < uniformProb (Fin 2 → Cap) (CapBad (∅ : Finset Cap)) := by
  rw [capBad_two_prob]
  exact div_pos one_pos (by exact_mod_cast h)

end BadEvent

/-! ## §7 The two worlds, and `[SPONGE-indiff-game]` — stated precisely.

REAL: a uniformly random permutation `π : Equiv.Perm (Rate × Cap)` (the ideal
permutation — `[PERM-ideal]` prices its deployed instantiation by `permExec`),
the distinguisher sees the sponge over `π` and both directions of `π`. IDEAL:
the lazy-sampling RO handler (`Selvage/FiatShamir.lean`'s `Oracle`, at query type
`List Rate` — literally the `[FS-ROM]` object) and the simulator. Adaptivity
is the `SrProver` shape: the next query is a function of past answers. -/

section Game

variable {Rate Cap : Type} [AddCommGroup Rate] [Fintype Rate] [Fintype Cap]
  [DecidableEq Rate] [DecidableEq Cap]

/-- A distinguisher query: the construction on a NONEMPTY message `x :: xs`
(the sponge without padding realizes no empty-message oracle — padding is
`[SPONGE-padding]`), or the primitive, either direction. -/
inductive SpQuery (Rate Cap : Type) where
  | constr (x : Rate) (xs : List Rate)
  | fwd (s : Rate × Cap)
  | inv (t : Rate × Cap)

/-- An answer: a squeezed rate block, or a primitive block. -/
inductive SpAnswer (Rate Cap : Type) where
  | rate (h : Rate)
  | block (b : Rate × Cap)

/-- A `q`-query indifferentiability distinguisher — adaptive (each query a
function of past answers, the `SrProver` shape), with a Boolean verdict. -/
structure Distinguisher (Rate Cap : Type) (q : ℕ) where
  /-- The next query, from the answers so far. -/
  move : List (SpAnswer Rate Cap) → SpQuery Rate Cap
  /-- The verdict, from all `q` answers. -/
  out : List (SpAnswer Rate Cap) → Bool

/-- The REAL world's answer: the sponge over `P` for construction queries,
`P`/`Pinv` for the primitive. -/
def realAnswer (P Pinv : Rate × Cap → Rate × Cap) (iv : Rate × Cap) :
    SpQuery Rate Cap → SpAnswer Rate Cap
  | .constr x xs => .rate (sponge P iv (x :: xs))
  | .fwd s => .block (P s)
  | .inv t => .block (Pinv t)

/-- The REAL run: `q` adaptive queries against `(sponge π, π, π⁻¹)`. -/
def realRun {q : ℕ} (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (π : Equiv.Perm (Rate × Cap)) : List (SpAnswer Rate Cap) :=
  (List.finRange q).foldl
    (fun ans _ => ans ++ [realAnswer (⇑π) (⇑π.symm) iv (D.move ans)]) []

/-- `Pr_π[D accepts]` in the REAL world — `π` uniform over `Equiv.Perm`, the
ideal-permutation model. -/
noncomputable def realProb {q : ℕ} (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) : ℝ :=
  uniformProb (Equiv.Perm (Rate × Cap)) fun π => D.out (realRun D iv π) = true

/-- The IDEAL world's running state: the RO handler (the `[FS-ROM]` object —
`Selvage/FiatShamir.lean`'s `Oracle` at query type `List Rate`), the simulator's
log, and the answers so far. -/
structure IdealState (Rate Cap : Type) where
  /-- The lazy-sampling random oracle. -/
  ro : Oracle (List Rate) Rate
  /-- The simulator's shared forward log. -/
  sim : Oracle (Rate × Cap) (Rate × Cap)
  /-- Answers delivered so far. -/
  ans : List (SpAnswer Rate Cap)

/-- The simulator's forward step with the RO as a HANDLER (not a total
function): a rate-completing query queries the RO at the completed message
(possibly extending its log with the step's rate coin) and programs the
answer; unrooted queries answer the block coin. Branch-wise this is `simFwd`
at `H := fun m => (ro.respond m rc).1` (`simFwdRO_answer`). -/
noncomputable def simFwdRO (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (os : Oracle (Rate × Cap) (Rate × Cap)) (s : Rate × Cap) (rc : Rate)
    (bc : Rate × Cap) :
    (Rate × Cap) × Oracle (List Rate) Rate × Oracle (Rate × Cap) (Rate × Cap) :=
  match completion? os iv s with
  | some m =>
      ((os.respond s ((ro.respond m rc).1, bc.2)).1, (ro.respond m rc).2,
        (os.respond s ((ro.respond m rc).1, bc.2)).2)
  | none => ((os.respond s bc).1, ro, (os.respond s bc).2)

omit [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap] in
/-- The handler-threaded forward step answers exactly as `simFwd` at the RO's
respond function — the game simulator IS the §4 simulator. -/
lemma simFwdRO_answer (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (os : Oracle (Rate × Cap) (Rate × Cap)) (s : Rate × Cap) (rc : Rate)
    (bc : Rate × Cap) :
    (simFwdRO iv ro os s rc bc).1
      = (simFwd (fun m => (ro.respond m rc).1) iv os s bc).1 := by
  unfold simFwdRO simFwd
  cases hc : completion? os iv s <;> rfl

/-- One IDEAL step: construction queries go to the RO handler; forward
primitive queries to `simFwdRO`; inverse primitive queries to `simInv`. Each
step carries one rate coin (for the RO) and one block coin (for the
simulator). -/
noncomputable def idealStep {q : ℕ} (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) (coins : Fin q → Rate × (Rate × Cap))
    (st : IdealState Rate Cap) (j : Fin q) : IdealState Rate Cap :=
  match D.move st.ans with
  | .constr x xs =>
      ⟨(st.ro.respond (x :: xs) (coins j).1).2, st.sim,
        st.ans ++ [.rate (st.ro.respond (x :: xs) (coins j).1).1]⟩
  | .fwd s =>
      let r := simFwdRO iv st.ro st.sim s (coins j).1 (coins j).2
      ⟨r.2.1, r.2.2, st.ans ++ [.block r.1]⟩
  | .inv t =>
      ⟨st.ro, (simInv st.sim t (coins j).2).2,
        st.ans ++ [.block (simInv st.sim t (coins j).2).1]⟩

/-- The IDEAL run: `q` adaptive queries against `(RO, simulator)`, from empty
handler and empty log. -/
noncomputable def idealRun {q : ℕ} (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) (coins : Fin q → Rate × (Rate × Cap)) :
    IdealState Rate Cap :=
  (List.finRange q).foldl (idealStep D iv coins) ⟨Oracle.empty, Oracle.empty, []⟩

/-- `Pr_coins[D accepts]` in the IDEAL world — coins one `(rate, block)` pair
per step, lazily consumed by the two handlers. -/
noncomputable def idealProb {q : ℕ} (D : Distinguisher Rate Cap q)
    (iv : Rate × Cap) : ℝ :=
  uniformProb (Fin q → Rate × (Rate × Cap)) fun coins =>
    D.out (idealRun D iv coins).ans = true

/-- A constant event has probability `1` or `0` on a nonempty space. -/
lemma uniformProb_const (C : Type) [Fintype C] [Nonempty C] (p : Prop)
    [Decidable p] : uniformProb C (fun _ => p) = if p then 1 else 0 := by
  unfold uniformProb
  by_cases hp : p
  · rw [if_pos hp, Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => hp),
      Nat.card_eq_fintype_card,
      div_self (by exact_mod_cast Fintype.card_ne_zero)]
  · rw [if_neg hp]
    haveI : IsEmpty {c : C // p} := ⟨fun x => hp x.2⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]

/-- **The zero-query slice, PROVED**: with no queries the two worlds are
indistinguishable — the game machinery computes, the statement below is not
vacuously unsatisfiable. -/
theorem advantage_zero_queries (D : Distinguisher Rate Cap 0)
    (iv : Rate × Cap) : realProb D iv = idealProb D iv := by
  haveI : Nonempty (Equiv.Perm (Rate × Cap)) := ⟨Equiv.refl _⟩
  haveI : Nonempty (Fin 0 → Rate × (Rate × Cap)) := ⟨fun i => i.elim0⟩
  have hreal : ∀ π : Equiv.Perm (Rate × Cap), realRun D iv π = [] := fun π => by
    simp [realRun]
  have hideal : ∀ coins : Fin 0 → Rate × (Rate × Cap),
      (idealRun D iv coins).ans = [] := fun coins => by
    simp [idealRun]
  unfold realProb idealProb
  calc uniformProb (Equiv.Perm (Rate × Cap))
        (fun π => D.out (realRun D iv π) = true)
      = uniformProb (Equiv.Perm (Rate × Cap)) (fun _ => D.out [] = true) :=
        uniformProb_congr fun π => by rw [hreal π]
    _ = if D.out [] = true then 1 else 0 := uniformProb_const _ _
    _ = uniformProb (Fin 0 → Rate × (Rate × Cap)) (fun _ => D.out [] = true) :=
        (uniformProb_const _ _).symm
    _ = uniformProb (Fin 0 → Rate × (Rate × Cap))
          (fun coins => D.out (idealRun D iv coins).ans = true) :=
        uniformProb_congr fun coins => by rw [hideal coins]

theorem spongeIndiff_zero (D : Distinguisher Rate Cap 0) (iv : Rate × Cap) :
    |realProb D iv - idealProb D iv| ≤ 0 := by
  rw [advantage_zero_queries D iv, sub_self, abs_zero]

end Game

/-- **Sponge indifferentiability, parametric in the error**: every `q`-query
adaptive distinguisher's advantage between (sponge over a random permutation,
the permutation) and (the lazy-sampling RO, the simulator) is at most `ε q`. -/
def SpongeIndifferentiable (Rate Cap : Type) [AddCommGroup Rate]
    [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    (iv : Rate × Cap) (ε : ℕ → ℝ) : Prop :=
  ∀ (q : ℕ) (D : Distinguisher Rate Cap q),
    |realProb D iv - idealProb D iv| ≤ ε q

/-- **`[SPONGE-indiff-game]` — the legacy query-indexed target, STATED, not
proved.** The sponge over an ideal permutation is indifferentiable from the RO
at the capacity bound: advantage `≤ 2q²/|Cap| + q²/|Rate × Cap|`. The first term is
the capacity-collision bad event — PRICED above (`capBad_le`); the second is
the standard permutation-vs-function switching cost (`q(q−1)/2^{b+1} ≤
q²/2^b` over the full block). What its proof needs that this file already
has: `walk_programs` (real/ideal agreement at each completing step),
`uniquePaths_simFwd`/`uniquePaths_simInv` (the bookkeeping invariant per
step), `capBad_le` (the fixed-set price). The follow-up modules named in the
header close the adaptive `capsOf` causality/cardinality argument and final
path-uniqueness classifier on the exact `idealRun` coin space, currently at
the honest but slightly looser `q(2q+2)/|Cap|` price.  Because an arbitrary
construction query can absorb more than one primitive block, `q` is not a
valid unrestricted primitive budget; `SpongeIndiffWorkBudget` proves the
counterexample and states `SpongeIndiffWorkGame` as the canonical replacement.
This legacy statement has the intended budget reading only for
`SingleBlockConstruction`.  NOT an axiom, NOT `True` — a real quantified
statement retained for compatibility while the work-indexed off-bad coupling
and permutation/function switch remain open. -/
def SpongeIndiffGame (Rate Cap : Type) [AddCommGroup Rate]
    [Fintype Rate] [Fintype Cap] [DecidableEq Rate] [DecidableEq Cap]
    (iv : Rate × Cap) : Prop :=
  SpongeIndifferentiable Rate Cap iv fun q =>
    2 * (q : ℝ) ^ 2 / (Fintype.card Cap : ℝ)
      + (q : ℝ) ^ 2 / (Fintype.card (Rate × Cap) : ℝ)

section Seam

variable {Rate Cap : Type} [AddCommGroup Rate]

/-- **The `[FS-ROM]` seam, one step, PROVED.** At a fresh rate-completing
forward query: (i) the sponge walk of the completed message `m` through the
simulator's extended log squeezes EXACTLY the RO handler's answer at `m`
(`walk_programs`), and (ii) any LATER construction query of `m` replays that
same answer (`respond_consistent` of the landed handler). The sponge-over-
the-simulator and the lazy-sampling RO — the two sides of `[FS-ROM]` — agree
on `m`, machine-checked; extending this agreement along a whole adaptive run
is exactly `[SPONGE-indiff-game]`. -/
theorem sponge_realizes_handler_step (iv : Rate × Cap)
    (ro : Oracle (List Rate) Rate) (os : Oracle (Rate × Cap) (Rate × Cap))
    {s : Rate × Cap} (hfresh : os.lookup s = none) {m : List Rate}
    (hm : completion? os iv s = some m) (rc rc' : Rate) (bc : Rate × Cap) :
    walkFrom (simFwdRO iv ro os s rc bc).2.2 iv m
        = some ((ro.respond m rc).1, bc.2) ∧
      (((simFwdRO iv ro os s rc bc).2.1).respond m rc').1
        = (ro.respond m rc).1 := by
  constructor
  · unfold simFwdRO
    rw [hm]
    exact walk_programs hfresh hm _
  · unfold simFwdRO
    rw [hm]
    exact ro.respond_consistent m rc rc'

end Seam

/-! ## §8 Keystones — BUILT over `ZMod 2 × Fin 2`, the smallest sponge. -/

namespace SpongeExample

/-- Rate `ZMod 2`, capacity `Fin 2`, IV `(0, 0)`. -/
def iv₂ : ZMod 2 × Fin 2 := (0, 0)

/-- *The sponge computes*: two blocks through the identity permutation. -/
example : sponge (id : ZMod 2 × Fin 2 → ZMod 2 × Fin 2) iv₂ [1, 1] = 0 := by
  decide

/-- *Satisfiable — the first query completes*: on the empty log, the forward
query `(1, 0)` at the IV capacity is rate-completing with message `[1]`. -/
theorem first_completion :
    completion? Oracle.empty iv₂ ((1 : ZMod 2), (0 : Fin 2)) = some [1] := by
  have h := completion?_empty_iv (iv := iv₂) (s := ((1 : ZMod 2), (0 : Fin 2))) rfl
  simpa using h

/-- *The simulator programs it*: the answer is `(H [1], coin.2)` — the RO's
value at the completed message, in the squeeze position. -/
theorem first_programs (H : List (ZMod 2) → ZMod 2) (coin : ZMod 2 × Fin 2) :
    (simFwd H iv₂ Oracle.empty (1, 0) coin).1 = (H [1], coin.2) :=
  simFwd_program (Oracle.lookup_empty _) first_completion H coin

/-- *The walk squeezes it back*: the sponge of `[1]` through the simulator's
log IS `H [1]` — the construction and the primitive agree. -/
theorem first_walk (H : List (ZMod 2) → ZMod 2) (coin : ZMod 2 × Fin 2) :
    walkFrom (simFwd H iv₂ Oracle.empty (1, 0) coin).2 iv₂ [1]
      = some (H [1], coin.2) :=
  simFwd_walk (Oracle.lookup_empty _) first_completion H coin

/-- *Consistency on the concrete sequence*: the SECOND identical query replays
the first answer, whatever its coin. -/
theorem second_replays (H : List (ZMod 2) → ZMod 2)
    (coin coin' : ZMod 2 × Fin 2) :
    (simFwd H iv₂ (simFwd H iv₂ Oracle.empty (1, 0) coin).2 (1, 0) coin').1
      = (simFwd H iv₂ Oracle.empty (1, 0) coin).1 :=
  simFwd_selfconsistent H iv₂ Oracle.empty (1, 0) coin coin'

/-- *Teeth — the RO is load-bearing on the instance*: the all-`0` and all-`1`
oracles force different simulator answers to the same query. -/
theorem programs_differ (coin : ZMod 2 × Fin 2) :
    (simFwd (fun _ => 0) iv₂ Oracle.empty (1, 0) coin).1
      ≠ (simFwd (fun _ => 1) iv₂ Oracle.empty (1, 0) coin).1 :=
  simFwd_reads_H (Oracle.lookup_empty _) first_completion
    (by decide : (0 : ZMod 2) ≠ 1) coin

/-- *The invariant survives the step*: with a capacity-fresh coin (capacity
`1 ∉ capsOf = [0]`), path uniqueness is preserved. -/
theorem first_preserves (H : List (ZMod 2) → ZMod 2) (r : ZMod 2) :
    UniquePaths (simFwd H iv₂ Oracle.empty (1, 0) (r, 1)).2 iv₂ :=
  uniquePaths_simFwd (uniquePaths_empty iv₂) H
    (show (1 : Fin 2) ∉ capsOf Oracle.empty iv₂ by decide)
    (show (1 : Fin 2) ≠ (0 : Fin 2) by decide)

/-- *Inverse-then-forward consistency on the instance*: a fresh inverse query
answered by the coin makes the forward query at the coin replay it. -/
theorem inv_then_fwd (t coin : ZMod 2 × Fin 2) :
    (simInv Oracle.empty t coin).2.lookup coin = some t :=
  simInv_lookup rfl (Oracle.lookup_empty _)

/-- *The capacity-collision bad event, exhibited and priced on the instance*:
`Pr[CapBad] = 1/2` at two queries over `Fin 2` capacities — the §6 bound's
exact value there. -/
theorem capBad_half :
    uniformProb (Fin 2 → Fin 2) (CapBad (∅ : Finset (Fin 2))) = 1 / 2 := by
  rw [capBad_two_prob]
  norm_num

example : CapBad (∅ : Finset (Fin 2)) (fun _ : Fin 2 => 0) := capBad_pair ∅ 0

end SpongeExample

/-! ## §9 Residual ledger — prose, not stubs.

**What CLOSED here.** (1) The sponge and its partial walk, with the real
world's reading (`walkFrom_agrees`). (2) THE SIMULATOR — the genuine
construction: one shared log, RO-programming on rate-completing queries
(`completion?`, unique-path–guarded), consistency inherited verbatim from the
landed handler laws, forward/inverse coherence both ways (`simInv_lookup`,
`simInv_inverts`). (3) `walk_programs` — the programming keystone: the sponge
walk of a completed message through the simulator's log squeezes exactly the
RO's answer, for every log/state/message; `sponge_realizes_handler_step`
re-renders it against the landed lazy-sampling handler with replay. (4)
Path-uniqueness preservation per step, BOTH directions, off capacity-freshness
(`uniquePaths_simFwd`, `uniquePaths_simInv`, via the walk-decomposition lemma).
(5) The capacity-collision bad event PRICED: `capBad_bound` (sharp),
`capBad_le` (`≤ 2q²/|Cap|`), birthday CITED from
`Selvage/CollisionResistanceROM.lean`, tight at `q = 2`. (6) The game — both
worlds and the advantage statement — STATED precisely, with the `q = 0` slice
proved.

**`[SPONGE-indiff-game]`** — the genuinely-remaining mass, named as the real
`Prop` `SpongeIndiffGame`. The follow-up run modules now close the evolving
capacity schedule, its exact ideal-coin probability transport, and final
path uniqueness (failure price `q(2q+2)/|Cap|`). Concretely owed: (i) fold
`walk_programs` into a run invariant saying every completed construction path
agrees with the RO handler; (ii) identical-until-bad, coupling that ideal run
to a random-function transcript; (iii) the random-permutation/random-function
switch (`q²/|Blk|`); and (iv) sharpen the landed adaptive capacity price to the
headline `2q²/|Cap|`. This is standard game-hopping
(Bertoni–Daemen–Peeters–Van Assche 2008) awaiting formalization mass.

**`[SPONGE-padding]`** — single-rate-block squeeze, nonempty unpadded
messages; the deployed injective padding rule and multi-block squeeze are
instantiation, owed with `[AIR-poseidon-params]`.

**`[PERM-ideal]`** — the NEW floor this file consolidates onto: the deployed
permutation (`Compiler/AirHash.lean`'s `permExec` at the deployed Poseidon2
parameters — cited by name; the Selvage import boundary keeps it out of this
tree) behaves as a uniformly random `Equiv.Perm` — the real world's coin. This
replaces `[FS-ROM]`'s monolithic "the sponge realizes the handler": once
`[SPONGE-indiff-game]` closes, `[FS-ROM]` = `[PERM-ideAL]` + this file's
theorems + MRH composition (the composition theorem is folded into the game
residual — the game statement is already the composable form). The floor then
reads: **ideal permutation + proximity**.

## Ledger

* `sponge`/`spongeAbsorb`/`walkFrom`(+laws)/`walkFrom_agrees` — the
  construction and its partial-log spine.
* `IsPath`/`UniquePaths`/`completion?`(+spec/empty) — rooted paths and the
  completion detector.
* `simFwd`/`simInv`/`spongeSimulator`(+replay/program/unrooted/consistency/
  inverse laws)/`simFwd_reads_H` — THE simulator, teeth included.
* `walk_programs`/`simFwd_walk`/`sponge_realizes_handler_step` — the
  programming keystone; the `[FS-ROM]` seam closed one step at a time.
* `capsOf`/`walkFrom_respond_split`/`uniquePaths_respond_freshOut`/
  `uniquePaths_respond_freshKey`/`uniquePaths_simFwd`/`uniquePaths_simInv` —
  consistency off the bad event, per step, both directions.
* `CapBad`/`capBad_bound`/`capBad_le`(+`capCollisionProb_eq` transport,
  `capBad_two_prob` tightness) — the `O(q²/2^c)` capacity price, birthday
  cited.
* `Distinguisher`/`realRun`/`realProb`/`IdealState`/`simFwdRO`/`idealRun`/
  `idealProb`/`SpongeIndifferentiable`/`SpongeIndiffGame` — the game, stated;
  `advantage_zero_queries` the proved slice.
* Keystones — `SpongeExample.*`: the concrete two-query run of the simulator
  (completion computed, programming, walk-back, replay, teeth, invariant,
  inverse coherence) and the priced bad event, exact at `1/2`.
* Residuals — `[SPONGE-indiff-game]` is the legacy single-block/query-count
  target; the unrestricted residual is the `SpongeIndiffWorkGame` adaptive
  off-bad work-space coupling plus the permutation/function switch,
  `[SPONGE-padding]`,
  `[PERM-ideal]` (the new floor) — all prose above, none a `True` stub. -/

#check @walk_programs
#check @sponge_realizes_handler_step
#check @uniquePaths_simFwd
#check @capBad_le
#check @SpongeIndiffGame

/-- info: 'Minidregg.Selvage.walk_programs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms walk_programs
/-- info: 'Minidregg.Selvage.sponge_realizes_handler_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sponge_realizes_handler_step
/-- info: 'Minidregg.Selvage.uniquePaths_respond_freshOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniquePaths_respond_freshOut
/-- info: 'Minidregg.Selvage.capBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capBad_le
/-- info: 'Minidregg.Selvage.advantage_zero_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms advantage_zero_queries

end Minidregg.Selvage
