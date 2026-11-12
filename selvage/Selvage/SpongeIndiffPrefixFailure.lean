/-
# Selvage.SpongeIndiffPrefixFailure — exact recursive construction failures

The singleton kernel identifies an already-sampled RO/primitive disagreement.
This module lifts that atom through the full recursive construction interpreter.
`PrefixProgramFailure` mirrors `programPrefixes` exactly: malformed coin shapes
fail immediately; an existing edge fails at this prefix on disagreement or in
the recursively updated tail; a fresh edge can fail only in its tail.

The main theorem is an iff for arbitrary message length and arbitrary coin-list
shape.  Consequently an `Option.none` result is never opaque: it is either
malformed input or a dynamically attributed prefix consistency failure.
-/
import Selvage.SpongeIndiffPrefixConflict

namespace Minidregg.Selvage

section PrefixFailure

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- Proof-level mirror of every fail-closed branch in `programPrefixes`. -/
noncomputable def PrefixProgramFailure
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    List Rate → List Rate → List Cap → Prop
  | [], [], [] => False
  | [], _, _ => True
  | _ :: _, [], _ => True
  | _ :: _, _, [] => True
  | block :: message, rateCoin :: rateCoins,
      capacityCoin :: capacityCoins =>
      let nextPrefix := seen ++ [block]
      let key : Rate × Cap := (state.1 + block, state.2)
      match primitive.lookup key with
      | some edgeValue =>
          let roReply := ro.respond nextPrefix edgeValue.1
          edgeValue.1 ≠ roReply.1 ∨
            (edgeValue.1 = roReply.1 ∧
              PrefixProgramFailure roReply.2 primitive edgeValue nextPrefix
                message rateCoins capacityCoins)
      | none =>
          let roReply := ro.respond nextPrefix rateCoin
          let programmed : Rate × Cap := (roReply.1, capacityCoin)
          let primitiveReply := primitive.respond key programmed
          PrefixProgramFailure roReply.2 primitiveReply.2 primitiveReply.1
            nextPrefix message rateCoins capacityCoins

/-- Every recursive failure classifier branch is exact: no interpreter
failure lacks a reason, and no classified reason can accompany success. -/
theorem programPrefixes_none_iff_failure
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    ∀ (message rateCoins : List Rate) (capacityCoins : List Cap),
      programPrefixes ro primitive state seen message rateCoins capacityCoins =
          none ↔
        PrefixProgramFailure ro primitive state seen message rateCoins
          capacityCoins := by
  intro message
  induction message generalizing ro primitive state seen with
  | nil =>
      intro rateCoins capacityCoins
      cases rateCoins <;> cases capacityCoins <;>
        simp [programPrefixes, PrefixProgramFailure]
  | cons block message ih =>
      intro rateCoins capacityCoins
      cases rateCoins with
      | nil => simp [programPrefixes, PrefixProgramFailure]
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [programPrefixes, PrefixProgramFailure]
          | cons capacityCoin capacityCoins =>
              simp only [programPrefixes, PrefixProgramFailure]
              cases hedge : primitive.lookup (state.1 + block, state.2) with
              | some edgeValue =>
                  simp only
                  let roReply := ro.respond (seen ++ [block]) edgeValue.1
                  by_cases hagree : edgeValue.1 = roReply.1
                  · rw [if_pos hagree]
                    change
                      (programPrefixes roReply.2 primitive edgeValue
                          (seen ++ [block]) message rateCoins capacityCoins =
                            none ↔
                        edgeValue.1 ≠ roReply.1 ∨
                          (edgeValue.1 = roReply.1 ∧
                            PrefixProgramFailure roReply.2 primitive edgeValue
                              (seen ++ [block]) message rateCoins capacityCoins))
                    constructor
                    · intro hnone
                      exact Or.inr ⟨hagree,
                        (ih (ro := roReply.2) (primitive := primitive)
                          (state := edgeValue) (seen := seen ++ [block])
                          rateCoins capacityCoins).mp hnone⟩
                    · rintro (hdisagree | ⟨_, hfailure⟩)
                      · exact False.elim (hdisagree hagree)
                      · exact (ih (ro := roReply.2) (primitive := primitive)
                          (state := edgeValue) (seen := seen ++ [block])
                          rateCoins capacityCoins).mpr hfailure
                  · rw [if_neg hagree]
                    change
                      (none = none ↔
                        edgeValue.1 ≠ roReply.1 ∨
                          (edgeValue.1 = roReply.1 ∧
                            PrefixProgramFailure roReply.2 primitive edgeValue
                              (seen ++ [block]) message rateCoins capacityCoins))
                    exact ⟨fun _ => Or.inl hagree, fun _ => rfl⟩
              | none =>
                  simp only
                  let roReply := ro.respond (seen ++ [block]) rateCoin
                  let programmed : Rate × Cap := (roReply.1, capacityCoin)
                  let primitiveReply :=
                    primitive.respond (state.1 + block, state.2) programmed
                  simpa [roReply, programmed, primitiveReply] using
                    (ih (ro := roReply.2) (primitive := primitiveReply.2)
                      (state := primitiveReply.1)
                      (seen := seen ++ [block]) rateCoins capacityCoins)

omit [DecidableEq Rate] in
/-- At an already-present edge, direct inequality with `Oracle.respond` is
exactly the proof-relevant sampled-table conflict from the singleton kernel. -/
theorem prefixConflict_iff_respond_disagrees
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) (block : Rate)
    (edgeValue : Rate × Cap)
    (hedge : primitive.lookup (state.1 + block, state.2) = some edgeValue) :
    PrefixConflict ro primitive state seen block ↔
      edgeValue.1 ≠ (ro.respond (seen ++ [block]) edgeValue.1).1 := by
  unfold PrefixConflict
  cases hro : ro.lookup (seen ++ [block]) with
  | none =>
      have hreply :
          (ro.respond (seen ++ [block]) edgeValue.1).1 = edgeValue.1 :=
        Oracle.respond_fresh_fst hro edgeValue.1
      rw [hreply]
      constructor
      · rintro ⟨value, roValue, _, hroValue, _⟩
        cases hroValue
      · intro hne
        exact False.elim (hne rfl)
  | some roValue =>
      have hreply :
          (ro.respond (seen ++ [block]) edgeValue.1).1 = roValue :=
        congrArg Prod.fst (Oracle.respond_hit hro edgeValue.1)
      rw [hreply]
      constructor
      · rintro ⟨value, value', hvalue, hvalue', hne⟩
        have hv : value = edgeValue :=
          Option.some.inj (hvalue.symm.trans hedge)
        have hv' : value' = roValue :=
          (Option.some.inj hvalue').symm
        simpa [hv, hv'] using hne
      · intro hne
        exact ⟨edgeValue, roValue, hedge, rfl, hne⟩

end PrefixFailure

/-- info: 'Minidregg.Selvage.programPrefixes_none_iff_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programPrefixes_none_iff_failure
/-- info: 'Minidregg.Selvage.prefixConflict_iff_respond_disagrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefixConflict_iff_respond_disagrees

end Minidregg.Selvage
