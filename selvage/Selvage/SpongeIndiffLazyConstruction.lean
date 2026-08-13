/-
# Selvage.SpongeIndiffLazyConstruction — execute construction through a lazy table

The landed ideal game answers `.constr` directly from its RO and leaves the
simulator table unchanged.  An identical-until-bad proof additionally needs a
hidden primitive table populated by every absorbed construction block.  This
module supplies that missing operational object.

`lazyAbsorb` consumes exactly one candidate primitive answer per message
block, replaying existing table entries and extending fresh ones through the
same `Oracle.respond` laws used everywhere else.  `coupledConstruction` then
joins that primitive execution to one lazy RO answer and fails closed unless
the final squeezed rate is exactly the RO answer.  No probability or
permutation-distribution claim is made here; freshness, collision pricing, and
the later transcript coupling remain separate.
-/
import Selvage.SpongeIndiffWorkBudget

namespace Minidregg.Selvage

section LazyConstruction

variable {Rate Cap : Type} [AddCommGroup Rate]

/-- Execute a sponge absorption against a lazy primitive table.  The list of
candidate primitive answers must have exactly the message length; handler hits
replay and therefore ignore the corresponding candidate coin. -/
noncomputable def lazyAbsorb
    (primitive : Oracle (Rate × Cap) (Rate × Cap)) (state : Rate × Cap) :
    List Rate → List (Rate × Cap) →
      Option ((Rate × Cap) × Oracle (Rate × Cap) (Rate × Cap))
  | [], [] => some (state, primitive)
  | [], _ :: _ => none
  | _ :: _, [] => none
  | x :: xs, coin :: coins =>
      let reply := primitive.respond (state.1 + x, state.2) coin
      lazyAbsorb reply.2 reply.1 xs coins

@[simp] theorem lazyAbsorb_nil
    (primitive : Oracle (Rate × Cap) (Rate × Cap)) (state : Rate × Cap) :
    lazyAbsorb primitive state [] [] = some (state, primitive) := rfl

@[simp] theorem lazyAbsorb_nil_extra
    (primitive : Oracle (Rate × Cap) (Rate × Cap)) (state coin : Rate × Cap)
    (coins : List (Rate × Cap)) :
    lazyAbsorb primitive state [] (coin :: coins) = none := rfl

@[simp] theorem lazyAbsorb_missing
    (primitive : Oracle (Rate × Cap) (Rate × Cap)) (state : Rate × Cap)
    (x : Rate) (xs : List Rate) :
    lazyAbsorb primitive state (x :: xs) [] = none := rfl

/-- Successful construction execution consumed exactly one primitive coin per
absorbed message block. -/
theorem lazyAbsorb_some_length_eq
    (primitive : Oracle (Rate × Cap) (Rate × Cap)) (state : Rate × Cap) :
    ∀ {message : List Rate} {coins : List (Rate × Cap)} {result},
      lazyAbsorb primitive state message coins = some result →
        message.length = coins.length := by
  intro message
  induction message generalizing primitive state with
  | nil =>
      intro coins result h
      cases coins with
      | nil => rfl
      | cons coin coins => simp at h
  | cons x xs ih =>
      intro coins result h
      cases coins with
      | nil => simp at h
      | cons coin coins =>
          simp only [lazyAbsorb] at h
          let reply := primitive.respond (state.1 + x, state.2) coin
          have htail :
              lazyAbsorb reply.2 reply.1 xs coins = some result := by
            simpa [reply] using h
          have hlen := ih (primitive := reply.2) (state := reply.1) htail
          simp [hlen]

/-- One-block execution is exactly one handler response. -/
theorem lazyAbsorb_singleton
    (primitive : Oracle (Rate × Cap) (Rate × Cap)) (state coin : Rate × Cap)
    (x : Rate) :
    lazyAbsorb primitive state [x] [coin] =
      some (primitive.respond (state.1 + x, state.2) coin) := by
  simp [lazyAbsorb]

/-- On a logged primitive input, a one-block construction replays the table
entry and leaves the table unchanged. -/
theorem lazyAbsorb_singleton_replay
    (primitive : Oracle (Rate × Cap) (Rate × Cap)) (state coin value : Rate × Cap)
    (x : Rate)
    (hlookup : primitive.lookup (state.1 + x, state.2) = some value) :
    lazyAbsorb primitive state [x] [coin] = some (value, primitive) := by
  rw [lazyAbsorb_singleton, Oracle.respond_hit hlookup]

/-- On a fresh primitive input, a one-block construction records exactly its
candidate coin. -/
theorem lazyAbsorb_singleton_fresh
    (primitive : Oracle (Rate × Cap) (Rate × Cap)) (state coin : Rate × Cap)
    (x : Rate)
    (hfresh : primitive.lookup (state.1 + x, state.2) = none) :
    lazyAbsorb primitive state [x] [coin] =
      some (coin, (primitive.respond (state.1 + x, state.2) coin).2) := by
  rw [lazyAbsorb_singleton]
  have hreply : primitive.respond (state.1 + x, state.2) coin =
      (coin, (primitive.respond (state.1 + x, state.2) coin).2) :=
    Prod.ext (Oracle.respond_fresh_fst hfresh coin) rfl
  rw [hreply]

variable [DecidableEq Rate]

/-- Successful coupled construction state.  Both handlers are returned so the
next adaptive query observes their exact updated tables. -/
structure CoupledConstructionResult (Rate Cap : Type) where
  answer : Rate
  ro : Oracle (List Rate) Rate
  primitive : Oracle (Rate × Cap) (Rate × Cap)

/-- Execute one nonempty construction query in the hidden lazy primitive
hybrid.  The RO is sampled/replayed once at the full message; the primitive
table executes every block; the step succeeds only when both rates agree. -/
noncomputable def coupledConstruction
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message : List Rate) (rateCoin : Rate)
    (blockCoins : List (Rate × Cap)) : Option (CoupledConstructionResult Rate Cap) :=
  if message.isEmpty then none
  else
    let roReply := ro.respond message rateCoin
    match lazyAbsorb primitive iv message blockCoins with
    | none => none
    | some (finalState, primitive') =>
        if finalState.1 = roReply.1 then
          some ⟨roReply.1, roReply.2, primitive'⟩
        else none

/-- A successful coupled step has an exact coin count. -/
theorem coupledConstruction_some_length_eq
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message : List Rate) (rateCoin : Rate)
    (blockCoins : List (Rate × Cap)) {result}
    (h : coupledConstruction iv ro primitive message rateCoin blockCoins =
      some result) :
    message.length = blockCoins.length := by
  by_cases hempty : message.isEmpty = true
  · simp [coupledConstruction, hempty] at h
  · cases hlazy : lazyAbsorb primitive iv message blockCoins with
    | none => simp [coupledConstruction, hempty, hlazy] at h
    | some pair => exact lazyAbsorb_some_length_eq primitive iv hlazy

/-- A successful coupled step records the full message at exactly the returned
answer in its RO state. -/
theorem coupledConstruction_lookup
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message : List Rate) (rateCoin : Rate)
    (blockCoins : List (Rate × Cap)) {result}
    (h : coupledConstruction iv ro primitive message rateCoin blockCoins =
      some result) :
    result.ro.lookup message = some result.answer := by
  by_cases hempty : message.isEmpty = true
  · simp [coupledConstruction, hempty] at h
  · cases hlazy : lazyAbsorb primitive iv message blockCoins with
    | none => simp [coupledConstruction, hempty, hlazy] at h
    | some pair =>
        obtain ⟨finalState, primitive'⟩ := pair
        by_cases heq : finalState.1 = (ro.respond message rateCoin).1
        · have hresult :
              (CoupledConstructionResult.mk
                (ro.respond message rateCoin).1
                (ro.respond message rateCoin).2 primitive') = result := by
            exact Option.some.inj (by
              simpa [coupledConstruction, hempty, hlazy, heq] using h)
          rw [← hresult]
          exact Oracle.lookup_respond_self ro message rateCoin
        · simp [coupledConstruction, hempty, hlazy, heq] at h

end LazyConstruction

/-! ## Concrete two-block construction-first execution -/

namespace SpongeLazyConstructionExample

def iv : ZMod 2 × Fin 4 := (0, 0)

def message : List (ZMod 2) := [1, 1]

def blockCoins : List (ZMod 2 × Fin 4) := [(0, 1), (1, 2)]

/-- The hidden primitive runner actually executes both absorbed blocks and
returns the second candidate's rate. -/
theorem two_block_lazy_absorb :
    lazyAbsorb Oracle.empty iv message blockCoins =
      some ((1, 2),
        (Oracle.empty.respond (1, 0) (0, 1)).2.respond (1, 1) (1, 2) |>.2) := by
  simp [lazyAbsorb, iv, message, blockCoins, Oracle.respond_fresh_fst,
    Oracle.lookup_respond_ne]

/-- The coupled construction accepts when the RO answer equals that exact
two-block squeeze. -/
theorem two_block_coupled_accepts :
    ∃ result, coupledConstruction iv Oracle.empty Oracle.empty message 1 blockCoins =
      some result ∧ result.answer = 1 := by
  simp [coupledConstruction, lazyAbsorb, iv, message, blockCoins,
    Oracle.respond_fresh_fst, Oracle.lookup_respond_ne]

noncomputable def coupledResult : CoupledConstructionResult (ZMod 2) (Fin 4) :=
  ⟨1, (Oracle.empty.respond message 1).2,
    ((Oracle.empty.respond (1, 0) (0, 1)).2.respond (1, 1) (1, 2)).2⟩

/-- Exact state returned by the concrete accepted construction. -/
theorem two_block_coupled_exact :
    coupledConstruction iv Oracle.empty Oracle.empty message 1 blockCoins =
      some coupledResult := by
  unfold coupledConstruction
  rw [show message.isEmpty = false by decide]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [two_block_lazy_absorb]
  simp only
  rw [Oracle.respond_fresh_fst (Oracle.lookup_empty message)]
  simp [coupledResult]

theorem two_block_coupled_exact_literals :
    coupledConstruction iv Oracle.empty Oracle.empty
      ([1, 1] : List (ZMod 2)) 1 [(0, 1), (1, 2)] = some coupledResult := by
  simpa [message, blockCoins] using two_block_coupled_exact

/-- Changing only the RO rate coin makes the same primitive execution reject,
so the agreement check is load-bearing. -/
theorem two_block_wrong_ro_rejected :
    coupledConstruction iv Oracle.empty Oracle.empty message 0 blockCoins = none := by
  simp [coupledConstruction, lazyAbsorb, iv, message, blockCoins,
    Oracle.respond_fresh_fst, Oracle.lookup_respond_ne]

end SpongeLazyConstructionExample

/-- info: 'Minidregg.Selvage.lazyAbsorb_some_length_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lazyAbsorb_some_length_eq
/-- info: 'Minidregg.Selvage.coupledConstruction_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coupledConstruction_lookup
/-- info: 'Minidregg.Selvage.SpongeLazyConstructionExample.two_block_wrong_ro_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeLazyConstructionExample.two_block_wrong_ro_rejected

end Minidregg.Selvage
