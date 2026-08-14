/-
# Selvage.SpongeIndiffPrefixFresh — fresh primitive paths expose the last coin

Construction messages may intentionally share proper prefixes, so requiring
every prefix RO query to be fresh would be both false and unnecessary.  The
load-bearing eager condition is narrower: every primitive edge traversed by
the current construction is fresh, while only the complete public message
must still be fresh in the RO.  Under exactly those conditions, successful
prefix programming returns the final supplied rate coin.
-/
import Selvage.SpongeIndiffPrefixProgramming

namespace Minidregg.Selvage

section PrefixFresh

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- The last supplied rate coin, with the group zero used only for the
malformed empty-list case. -/
def lastRateCoin : List Rate → Rate
  | [] => 0
  | [rate] => rate
  | _ :: next :: rest => lastRateCoin (next :: rest)

/-- Recursive execution predicate saying that every primitive edge selected
by this construction path is absent immediately before it is programmed.
RO prefix hits are deliberately allowed. -/
noncomputable def PrimitivePathFresh
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    List Rate → List Rate → List Cap → Prop
  | [], [], [] => True
  | [], _, _ => False
  | _ :: _, [], _ => False
  | _ :: _, _, [] => False
  | block :: message, rateCoin :: rateCoins,
      capacityCoin :: capacityCoins =>
      let nextPrefix := seen ++ [block]
      let key : Rate × Cap := (state.1 + block, state.2)
      primitive.lookup key = none ∧
        let roReply := ro.respond nextPrefix rateCoin
        let programmed : Rate × Cap := (roReply.1, capacityCoin)
        let primitiveReply := primitive.respond key programmed
        PrimitivePathFresh roReply.2 primitiveReply.2 primitiveReply.1
          nextPrefix message rateCoins capacityCoins

/-- A recursively fresh, well-shaped path always executes successfully. -/
theorem programPrefixes_some_of_primitivePathFresh
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    ∀ {message rateCoins : List Rate} {capacityCoins : List Cap},
      PrimitivePathFresh ro primitive state seen message rateCoins
          capacityCoins →
        ∃ result, programPrefixes ro primitive state seen message rateCoins
          capacityCoins = some result := by
  intro message
  induction message generalizing ro primitive state seen with
  | nil =>
      intro rateCoins capacityCoins hfresh
      cases rateCoins <;> cases capacityCoins <;>
        simp [PrimitivePathFresh, programPrefixes] at hfresh ⊢
  | cons block message ih =>
      intro rateCoins capacityCoins hfresh
      cases rateCoins with
      | nil => simp [PrimitivePathFresh] at hfresh
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [PrimitivePathFresh] at hfresh
          | cons capacityCoin capacityCoins =>
              let nextPrefix := seen ++ [block]
              let key : Rate × Cap := (state.1 + block, state.2)
              let roReply := ro.respond nextPrefix rateCoin
              let programmed : Rate × Cap := (roReply.1, capacityCoin)
              let primitiveReply := primitive.respond key programmed
              change primitive.lookup key = none ∧
                PrimitivePathFresh roReply.2 primitiveReply.2
                  primitiveReply.1 nextPrefix message rateCoins
                    capacityCoins at hfresh
              obtain ⟨hedge, htailFresh⟩ := hfresh
              obtain ⟨result, htailRun⟩ := ih
                (ro := roReply.2) (primitive := primitiveReply.2)
                (state := primitiveReply.1) (seen := nextPrefix) htailFresh
              refine ⟨result, ?_⟩
              simp only [programPrefixes]
              rw [show (state.1 + block, state.2) = key by rfl, hedge]
              simpa [nextPrefix, key, roReply, programmed, primitiveReply]
                using htailRun

/-- On a nonempty fresh primitive path, freshness of the complete RO message
is sufficient for the returned rate to be the final supplied rate coin.
Proper prefix RO hits remain allowed. -/
theorem programPrefixes_fresh_final_rate
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    ∀ {message rateCoins : List Rate} {capacityCoins : List Cap} {result},
      message ≠ [] →
      PrimitivePathFresh ro primitive state seen message rateCoins
          capacityCoins →
      ro.lookup (seen ++ message) = none →
      programPrefixes ro primitive state seen message rateCoins capacityCoins =
          some result →
      result.state.1 = lastRateCoin rateCoins := by
  intro message
  induction message generalizing ro primitive state seen with
  | nil =>
      intro rateCoins capacityCoins result hnonempty
      contradiction
  | cons block message ih =>
      intro rateCoins capacityCoins result _ hfresh hro hrun
      cases rateCoins with
      | nil => simp [PrimitivePathFresh] at hfresh
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [PrimitivePathFresh] at hfresh
          | cons capacityCoin capacityCoins =>
              let nextPrefix := seen ++ [block]
              let key : Rate × Cap := (state.1 + block, state.2)
              let roReply := ro.respond nextPrefix rateCoin
              let programmed : Rate × Cap := (roReply.1, capacityCoin)
              let primitiveReply := primitive.respond key programmed
              change primitive.lookup key = none ∧
                PrimitivePathFresh roReply.2 primitiveReply.2
                  primitiveReply.1 nextPrefix message rateCoins
                    capacityCoins at hfresh
              obtain ⟨hedge, htailFresh⟩ := hfresh
              have htailRun :
                  programPrefixes roReply.2 primitiveReply.2 primitiveReply.1
                    nextPrefix message rateCoins capacityCoins = some result := by
                simp only [programPrefixes] at hrun
                rw [show (state.1 + block, state.2) = key by rfl, hedge] at hrun
                simpa [nextPrefix, key, roReply, programmed, primitiveReply]
                  using hrun
              cases message with
              | nil =>
                  cases rateCoins with
                  | nil =>
                      cases capacityCoins with
                      | nil =>
                          simp only [programPrefixes] at htailRun
                          injection htailRun with hresult
                          subst result
                          have hroPrefix : ro.lookup nextPrefix = none := by
                            simpa [nextPrefix] using hro
                          have hroReplyFresh : roReply.1 = rateCoin := by
                            dsimp [roReply]
                            exact Oracle.respond_fresh_fst hroPrefix rateCoin
                          have hprimitiveReply :
                              primitiveReply.1 = programmed := by
                            dsimp [primitiveReply]
                            exact Oracle.respond_fresh_fst hedge programmed
                          rw [hprimitiveReply]
                          simpa [programmed, lastRateCoin] using hroReplyFresh
                      | cons capacityCoin' capacityCoins =>
                          simp [PrimitivePathFresh] at htailFresh
                  | cons rateCoin' rateCoins =>
                      simp [PrimitivePathFresh] at htailFresh
              | cons next rest =>
                  cases rateCoins with
                  | nil => simp [PrimitivePathFresh] at htailFresh
                  | cons nextRate restRates =>
                      cases capacityCoins with
                      | nil => simp [PrimitivePathFresh] at htailFresh
                      | cons nextCapacity restCapacities =>
                          have hmessageNe :
                              nextPrefix ++ (next :: rest) ≠ nextPrefix := by
                            intro equal
                            have hlength := congrArg List.length equal
                            simp at hlength
                          have hroTail :
                              roReply.2.lookup
                                (nextPrefix ++ (next :: rest)) = none := by
                            dsimp [roReply]
                            rw [Oracle.lookup_respond_ne ro hmessageNe rateCoin]
                            simpa [nextPrefix, List.append_assoc] using hro
                          have hfinal := ih
                            (ro := roReply.2)
                            (primitive := primitiveReply.2)
                            (state := primitiveReply.1)
                            (seen := nextPrefix)
                            (rateCoins := nextRate :: restRates)
                            (capacityCoins := nextCapacity :: restCapacities)
                            (result := result) (by simp) htailFresh hroTail
                              htailRun
                          simpa [lastRateCoin] using hfinal

/-- Public construction wrapper for the fresh-path output theorem. -/
theorem programConstruction_fresh_final_rate
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message rateCoins : List Rate) (capacityCoins : List Cap)
    (hnonempty : message ≠ [])
    (hfresh : PrimitivePathFresh ro primitive iv [] message rateCoins
      capacityCoins)
    (hro : ro.lookup message = none) :
    ∃ result,
      programConstruction iv ro primitive message rateCoins capacityCoins =
          some result ∧
        result.state.1 = lastRateCoin rateCoins := by
  obtain ⟨result, hrun⟩ :=
    programPrefixes_some_of_primitivePathFresh ro primitive iv [] hfresh
  have hrate := programPrefixes_fresh_final_rate ro primitive iv [] hnonempty
    hfresh (by simpa using hro) hrun
  refine ⟨result, ?_, hrate⟩
  simp [programConstruction, hnonempty, hrun]

#check @programPrefixes_some_of_primitivePathFresh
#check @programPrefixes_fresh_final_rate
#check @programConstruction_fresh_final_rate

/-- info: 'Minidregg.Selvage.programPrefixes_some_of_primitivePathFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programPrefixes_some_of_primitivePathFresh
/-- info: 'Minidregg.Selvage.programPrefixes_fresh_final_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programPrefixes_fresh_final_rate
/-- info: 'Minidregg.Selvage.programConstruction_fresh_final_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programConstruction_fresh_final_rate

end PrefixFresh

end Minidregg.Selvage
