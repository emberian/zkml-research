/-
# Selvage.SpongeIndiffPrefixWalk — successful programming materializes the walk

`programPrefixes` returns a final primitive table and state.  The output theorem
already identifies the returned rate with the full-message lazy RO lookup.
This module proves the complementary construction fact: the final primitive
table actually contains the whole programmed/hit path, and walking the input
message from the supplied starting state reaches exactly the returned state.

The proof is insensitive to later log extension.  A first edge—whether it was
already present or freshly programmed—survives every recursive prefix step by
the landed oracle frame law.  Thus the theorem covers arbitrary nonempty
multi-block construction and primitive-first reconciliation, not merely the
two-block executable witness.
-/
import Selvage.SpongeIndiffPrefixOutput

namespace Minidregg.Selvage

section PrefixWalk

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- Successful prefix programming preserves every answer already present in
the starting primitive table. -/
theorem programPrefixes_preserves_lookup
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    ∀ {message rateCoins : List Rate} {capacityCoins : List Cap} {result}
      {key value : Rate × Cap},
      programPrefixes ro primitive state seen message rateCoins capacityCoins =
        some result →
      primitive.lookup key = some value →
      result.primitive.lookup key = some value := by
  intro message
  induction message generalizing ro primitive state seen with
  | nil =>
      intro rateCoins capacityCoins result key value hrun hlookup
      cases rateCoins <;> cases capacityCoins <;>
        simp [programPrefixes] at hrun
      subst result
      exact hlookup
  | cons x xs ih =>
      intro rateCoins capacityCoins result key value hrun hlookup
      cases rateCoins with
      | nil => simp [programPrefixes] at hrun
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [programPrefixes] at hrun
          | cons capacityCoin capacityCoins =>
              simp only [programPrefixes] at hrun
              cases hedge : primitive.lookup (state.1 + x, state.2) with
              | some edgeValue =>
                  rw [hedge] at hrun
                  simp only at hrun
                  by_cases hagree :
                      edgeValue.1 =
                        (ro.respond (seen ++ [x]) edgeValue.1).1
                  · rw [if_pos hagree] at hrun
                    exact ih
                      (ro := (ro.respond (seen ++ [x]) edgeValue.1).2)
                      (primitive := primitive) (state := edgeValue)
                      (seen := seen ++ [x]) hrun hlookup
                  · rw [if_neg hagree] at hrun
                    contradiction
              | none =>
                  rw [hedge] at hrun
                  let roReply := ro.respond (seen ++ [x]) rateCoin
                  let programmed : Rate × Cap := (roReply.1, capacityCoin)
                  let primitiveReply :=
                    primitive.respond (state.1 + x, state.2) programmed
                  have htail :
                      programPrefixes roReply.2 primitiveReply.2
                        primitiveReply.1 (seen ++ [x]) xs rateCoins
                        capacityCoins = some result := by
                    simpa [roReply, programmed, primitiveReply] using hrun
                  have hlookup' :
                      primitiveReply.2.lookup key = some value := by
                    exact Oracle.lookup_respond_some hlookup
                      (state.1 + x, state.2) programmed
                  exact ih (ro := roReply.2) (primitive := primitiveReply.2)
                    (state := primitiveReply.1) (seen := seen ++ [x])
                    htail hlookup'

/-- The final primitive table returned by successful prefix programming walks
the whole remaining message from the supplied starting state to the exact
returned state. -/
theorem programPrefixes_final_walk
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    ∀ {message rateCoins : List Rate} {capacityCoins : List Cap} {result},
      programPrefixes ro primitive state seen message rateCoins capacityCoins =
        some result →
      walkFrom result.primitive state message = some result.state := by
  intro message
  induction message generalizing ro primitive state seen with
  | nil =>
      intro rateCoins capacityCoins result hrun
      cases rateCoins <;> cases capacityCoins <;>
        simp [programPrefixes] at hrun
      subst result
      rfl
  | cons x xs ih =>
      intro rateCoins capacityCoins result hrun
      cases rateCoins with
      | nil => simp [programPrefixes] at hrun
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [programPrefixes] at hrun
          | cons capacityCoin capacityCoins =>
              simp only [programPrefixes] at hrun
              cases hedge : primitive.lookup (state.1 + x, state.2) with
              | some edgeValue =>
                  rw [hedge] at hrun
                  simp only at hrun
                  by_cases hagree :
                      edgeValue.1 =
                        (ro.respond (seen ++ [x]) edgeValue.1).1
                  · rw [if_pos hagree] at hrun
                    have hfirst :
                        result.primitive.lookup (state.1 + x, state.2) =
                          some edgeValue :=
                      programPrefixes_preserves_lookup
                        (ro.respond (seen ++ [x]) edgeValue.1).2 primitive
                        edgeValue (seen ++ [x]) hrun hedge
                    have htail := ih
                      (ro := (ro.respond (seen ++ [x]) edgeValue.1).2)
                      (primitive := primitive) (state := edgeValue)
                      (seen := seen ++ [x]) hrun
                    rw [walkFrom_cons, hfirst]
                    simp only
                    exact htail
                  · rw [if_neg hagree] at hrun
                    contradiction
              | none =>
                  rw [hedge] at hrun
                  let roReply := ro.respond (seen ++ [x]) rateCoin
                  let programmed : Rate × Cap := (roReply.1, capacityCoin)
                  let primitiveReply :=
                    primitive.respond (state.1 + x, state.2) programmed
                  have htailRun :
                      programPrefixes roReply.2 primitiveReply.2
                        primitiveReply.1 (seen ++ [x]) xs rateCoins
                        capacityCoins = some result := by
                    simpa [roReply, programmed, primitiveReply] using hrun
                  have hedgeReply :
                      primitiveReply.2.lookup (state.1 + x, state.2) =
                        some primitiveReply.1 :=
                    Oracle.lookup_respond_self primitive
                      (state.1 + x, state.2) programmed
                  have hfirst :
                      result.primitive.lookup (state.1 + x, state.2) =
                        some primitiveReply.1 :=
                    programPrefixes_preserves_lookup roReply.2
                      primitiveReply.2 primitiveReply.1 (seen ++ [x])
                      htailRun hedgeReply
                  have htail := ih (ro := roReply.2)
                    (primitive := primitiveReply.2)
                    (state := primitiveReply.1) (seen := seen ++ [x])
                    htailRun
                  rw [walkFrom_cons, hfirst]
                  simp only
                  exact htail

/-- Public construction starts at the IV, so a successful construction's
final primitive table realizes the entire public message exactly. -/
theorem programConstruction_final_walk
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message rateCoins : List Rate) (capacityCoins : List Cap) {result}
    (hrun : programConstruction iv ro primitive message rateCoins
      capacityCoins = some result) :
    walkFrom result.primitive iv message = some result.state := by
  unfold programConstruction at hrun
  split at hrun
  · contradiction
  · exact programPrefixes_final_walk ro primitive iv [] hrun

/-- One theorem packages the complete construction semantics: the final table
walks the entire nonempty message to the returned state, and the state's rate
is exactly the full-message lazy RO response. -/
theorem programConstruction_realizes_ro
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message rateCoins : List Rate) (capacityCoins : List Cap) {result}
    (hrun : programConstruction iv ro primitive message rateCoins
      capacityCoins = some result) :
    walkFrom result.primitive iv message = some result.state ∧
      result.ro.lookup message = some result.state.1 :=
  ⟨programConstruction_final_walk iv ro primitive message rateCoins
      capacityCoins hrun,
    programConstruction_final_lookup iv ro primitive message rateCoins
      capacityCoins hrun⟩

end PrefixWalk

/-- info: 'Minidregg.Selvage.programPrefixes_final_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms programPrefixes_final_walk
/-- info: 'Minidregg.Selvage.programConstruction_final_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programConstruction_final_walk
/-- info: 'Minidregg.Selvage.programConstruction_realizes_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programConstruction_realizes_ro

end Minidregg.Selvage
