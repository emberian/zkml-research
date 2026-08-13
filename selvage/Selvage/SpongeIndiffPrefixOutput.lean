/-
# Selvage.SpongeIndiffPrefixOutput — successful construction returns the RO value

`programPrefixes` reconciles or programs every nonempty message prefix.  This
module proves the load-bearing output theorem: whenever the interpreter
succeeds on a nonempty suffix, its final state's rate is exactly the response
logged for the full prefix.  Consequently `programConstruction` answers with
the lazy RO value of the complete public message, in both construction-first
and primitive-first executions.
-/
import Selvage.SpongeIndiffPrefixProgramming

namespace Minidregg.Selvage

section PrefixOutput

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- Successful nonempty prefix programming logs the final state's rate at the
full `seen ++ message` query. -/
theorem programPrefixes_final_lookup
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    ∀ {message rateCoins : List Rate} {capacityCoins : List Cap} {result},
      message ≠ [] →
      programPrefixes ro primitive state seen message rateCoins capacityCoins =
        some result →
      result.ro.lookup (seen ++ message) = some result.state.1 := by
  intro message
  induction message generalizing ro primitive state seen with
  | nil =>
      intro rateCoins capacityCoins result hnonempty
      contradiction
  | cons x xs ih =>
      intro rateCoins capacityCoins result hnonempty hrun
      cases rateCoins with
      | nil => simp [programPrefixes] at hrun
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [programPrefixes] at hrun
          | cons capacityCoin capacityCoins =>
              simp only [programPrefixes] at hrun
              cases hlookup : primitive.lookup (state.1 + x, state.2) with
              | some value =>
                  rw [hlookup] at hrun
                  simp only at hrun
                  by_cases hagree :
                      value.1 = (ro.respond (seen ++ [x]) value.1).1
                  · rw [if_pos hagree] at hrun
                    cases xs with
                    | nil =>
                        cases rateCoins with
                        | nil =>
                            cases capacityCoins with
                            | nil =>
                                simp only [programPrefixes] at hrun
                                injection hrun with hresult
                                subst result
                                have hself := Oracle.lookup_respond_self ro
                                  (seen ++ [x]) value.1
                                exact hself.trans (congrArg some hagree.symm)
                            | cons capacityCoin' capacityCoins =>
                                simp [programPrefixes] at hrun
                        | cons rateCoin' rateCoins =>
                            simp [programPrefixes] at hrun
                    | cons y ys =>
                        have htail := ih
                          (ro := (ro.respond (seen ++ [x]) value.1).2)
                          (primitive := primitive) (state := value)
                          (seen := seen ++ [x]) (by simp) hrun
                        simpa [List.append_assoc] using htail
                  · rw [if_neg hagree] at hrun
                    contradiction
              | none =>
                  rw [hlookup] at hrun
                  simp only at hrun
                  let roReply := ro.respond (seen ++ [x]) rateCoin
                  let programmed : Rate × Cap := (roReply.1, capacityCoin)
                  let primitiveReply :=
                    primitive.respond (state.1 + x, state.2) programmed
                  have htail :
                      programPrefixes roReply.2 primitiveReply.2
                        primitiveReply.1 (seen ++ [x]) xs rateCoins
                        capacityCoins = some result := by
                    simpa [roReply, programmed, primitiveReply] using hrun
                  cases xs with
                  | nil =>
                      cases rateCoins with
                      | nil =>
                          cases capacityCoins with
                          | nil =>
                              simp only [programPrefixes] at htail
                              injection htail with hresult
                              subst result
                              have hself := Oracle.lookup_respond_self ro
                                (seen ++ [x]) rateCoin
                              have hprogrammed : primitiveReply.1 = programmed := by
                                exact Oracle.respond_fresh_fst hlookup programmed
                              have hrate : primitiveReply.1.1 = roReply.1 := by
                                rw [hprogrammed]
                              simpa [roReply, hrate] using hself
                          | cons capacityCoin' capacityCoins =>
                              simp [programPrefixes] at htail
                      | cons rateCoin' rateCoins =>
                          simp [programPrefixes] at htail
                  | cons y ys =>
                      have hrecursive := ih
                        (ro := roReply.2) (primitive := primitiveReply.2)
                        (state := primitiveReply.1) (seen := seen ++ [x])
                        (by simp) htail
                      simpa [List.append_assoc] using hrecursive

/-- Public construction is a nonempty wrapper, so its returned rate is exactly
the full-message RO lookup. -/
theorem programConstruction_final_lookup
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message rateCoins : List Rate) (capacityCoins : List Cap) {result}
    (hrun : programConstruction iv ro primitive message rateCoins
      capacityCoins = some result) :
    result.ro.lookup message = some result.state.1 := by
  unfold programConstruction at hrun
  split at hrun
  · contradiction
  · have hnonempty : message ≠ [] := by
      intro hempty
      subst message
      contradiction
    simpa using programPrefixes_final_lookup ro primitive iv [] hnonempty hrun

end PrefixOutput

/-- info: 'Minidregg.Selvage.programPrefixes_final_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms programPrefixes_final_lookup
/-- info: 'Minidregg.Selvage.programConstruction_final_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms programConstruction_final_lookup

end Minidregg.Selvage
