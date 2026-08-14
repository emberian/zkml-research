/-
# Selvage.SpongeIndiffPrefixFresh — fresh primitive paths expose the last coin

Construction messages may intentionally share proper prefixes, so requiring
every prefix RO query to be fresh would be both false and unnecessary.  The
load-bearing eager condition is narrower: every primitive edge traversed by
the current construction is fresh, while only the complete public message
must still be fresh in the RO.  Under exactly those conditions, successful
prefix programming returns the final supplied rate coin.
-/
import Selvage.SpongeIndiffWorkStream

namespace Minidregg.Selvage

section PrefixFresh

variable {Rate Cap : Type} [AddCommGroup Rate] [DecidableEq Rate]

/-- The last supplied rate coin, with the group zero used only for the
malformed empty-list case. -/
def lastRateCoin : List Rate → Rate
  | [] => 0
  | [rate] => rate
  | _ :: next :: rest => lastRateCoin (next :: rest)

omit [DecidableEq Rate] in
@[simp] theorem lastRateCoin_append_singleton (rates : List Rate)
    (rate : Rate) :
    lastRateCoin (rates ++ [rate]) = rate := by
  induction rates with
  | nil => rfl
  | cons first rates =>
      cases rates <;> simp_all [lastRateCoin]

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

/-- Prefix programming preserves freshness of any RO query which is not a
prefix of the full message being programmed.  This is the frame lemma that
allows a prefix-free public schedule to derive complete-message freshness
without forbidding intentional proper-prefix sharing. -/
theorem programPrefixes_preserves_ro_fresh_of_not_prefix
    (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (state : Rate × Cap) (seen : List Rate) :
    ∀ {message rateCoins : List Rate} {capacityCoins : List Cap} {result}
      {target : List Rate},
      programPrefixes ro primitive state seen message rateCoins capacityCoins =
          some result →
      ro.lookup target = none →
      ¬ (target <+: seen ++ message) →
      result.ro.lookup target = none := by
  intro message
  induction message generalizing ro primitive state seen with
  | nil =>
      intro rateCoins capacityCoins result target hrun hfresh _
      cases rateCoins <;> cases capacityCoins <;>
        simp [programPrefixes] at hrun
      subst result
      exact hfresh
  | cons block message ih =>
      intro rateCoins capacityCoins result target hrun hfresh hnotPrefix
      cases rateCoins with
      | nil => simp [programPrefixes] at hrun
      | cons rateCoin rateCoins =>
          cases capacityCoins with
          | nil => simp [programPrefixes] at hrun
          | cons capacityCoin capacityCoins =>
              let nextPrefix := seen ++ [block]
              have hcurrentPrefix :
                  nextPrefix <+: seen ++ (block :: message) := by
                refine ⟨message, ?_⟩
                simp [nextPrefix, List.append_assoc]
              have htargetNe : target ≠ nextPrefix := by
                intro equal
                apply hnotPrefix
                rw [equal]
                exact hcurrentPrefix
              have htailMessage :
                  nextPrefix ++ message = seen ++ (block :: message) := by
                simp [nextPrefix, List.append_assoc]
              have hnotTail : ¬ (target <+: nextPrefix ++ message) := by
                intro hprefix
                apply hnotPrefix
                rw [← htailMessage]
                exact hprefix
              simp only [programPrefixes] at hrun
              cases hedge : primitive.lookup (state.1 + block, state.2) with
              | some edgeValue =>
                  rw [hedge] at hrun
                  simp only at hrun
                  by_cases hagree :
                      edgeValue.1 =
                        (ro.respond nextPrefix edgeValue.1).1
                  · rw [if_pos hagree] at hrun
                    have hfresh' :
                        (ro.respond nextPrefix edgeValue.1).2.lookup target =
                          none := by
                      rw [Oracle.lookup_respond_ne ro htargetNe edgeValue.1]
                      exact hfresh
                    exact ih
                      (ro := (ro.respond nextPrefix edgeValue.1).2)
                      (primitive := primitive) (state := edgeValue)
                      (seen := nextPrefix) hrun hfresh' hnotTail
                  · rw [if_neg hagree] at hrun
                    contradiction
              | none =>
                  rw [hedge] at hrun
                  let roReply := ro.respond nextPrefix rateCoin
                  let programmed : Rate × Cap := (roReply.1, capacityCoin)
                  let primitiveReply :=
                    primitive.respond (state.1 + block, state.2) programmed
                  have htailRun :
                      programPrefixes roReply.2 primitiveReply.2
                        primitiveReply.1 nextPrefix message rateCoins
                          capacityCoins = some result := by
                    simpa [nextPrefix, roReply, programmed, primitiveReply]
                      using hrun
                  have hfresh' : roReply.2.lookup target = none := by
                    dsimp [roReply]
                    rw [Oracle.lookup_respond_ne ro htargetNe rateCoin]
                    exact hfresh
                  exact ih (ro := roReply.2)
                    (primitive := primitiveReply.2)
                    (state := primitiveReply.1) (seen := nextPrefix)
                    htailRun hfresh' hnotTail

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

/-- Public construction wrapper for RO freshness framing. -/
theorem programConstruction_preserves_ro_fresh_of_not_prefix
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (primitive : Oracle (Rate × Cap) (Rate × Cap))
    (message rateCoins : List Rate) (capacityCoins : List Cap) {result}
    {target : List Rate}
    (hrun : programConstruction iv ro primitive message rateCoins
      capacityCoins = some result)
    (hfresh : ro.lookup target = none)
    (hnotPrefix : ¬ (target <+: message)) :
    result.ro.lookup target = none := by
  unfold programConstruction at hrun
  split at hrun
  · contradiction
  · simpa using
      (programPrefixes_preserves_ro_fresh_of_not_prefix ro primitive iv []
        hrun hfresh (by simpa using hnotPrefix))

/-- The adaptive prefix-hybrid step exposes the same final rate coin under the
fresh-path predicate. -/
theorem prefixHybridStep_constr_of_primitivePathFresh {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (roundCoins : Fin q → PrefixHybridCoins Rate Cap)
    (state : PrefixHybridState Rate Cap) (j : Fin q)
    (x : Rate) (xs rateCoins : List Rate) (capacityCoins : List Cap)
    (hquery : D.move state.ans = .constr x xs)
    (hcoins : roundCoins j = .construction rateCoins capacityCoins)
    (hcounts : rateCoins.length = (x :: xs).length ∧
      capacityCoins.length = (x :: xs).length)
    (hfresh : PrimitivePathFresh state.ro state.primitive iv [] (x :: xs)
      rateCoins capacityCoins)
    (hro : state.ro.lookup (x :: xs) = none) :
    ∃ next,
      prefixHybridStep D iv roundCoins state j = .ok next ∧
        next.ans = state.ans ++ [.rate (lastRateCoin rateCoins)] := by
  obtain ⟨result, hprogram, hrate⟩ :=
    programConstruction_fresh_final_rate iv state.ro state.primitive
      (x :: xs) rateCoins capacityCoins (by simp) hfresh hro
  let next : PrefixHybridState Rate Cap :=
    ⟨result.ro, result.primitive,
      state.ans ++ [.rate result.state.1],
      state.work + (x :: xs).length⟩
  refine ⟨next, ?_, ?_⟩
  · unfold prefixHybridStep
    rw [hquery, hcoins]
    dsimp only
    rw [if_pos hcounts, hprogram]
  · simp [next, hrate]

/-- The fixed work-stream adapter preserves the fresh-path output theorem for
an exact construction segment. -/
theorem workHybridStep_constr_of_primitivePathFresh {q : Nat}
    (D : Distinguisher Rate Cap q) (iv : Rate × Cap)
    (state : WorkHybridState Rate Cap) (j : Fin q)
    (x : Rate) (xs : List Rate)
    (hquery : D.move state.core.ans = .constr x xs)
    (henough : xs.length + 1 ≤ state.remaining.length)
    (hfresh : PrimitivePathFresh state.core.ro state.core.primitive iv []
      (x :: xs)
      ((state.remaining.take (xs.length + 1)).map Prod.fst)
      ((state.remaining.take (xs.length + 1)).map Prod.snd))
    (hro : state.core.ro.lookup (x :: xs) = none) :
    ∃ next,
      workHybridStep D iv state j = .ok next ∧
        next.core.ans = state.core.ans ++
          [.rate (lastRateCoin
            ((state.remaining.take (xs.length + 1)).map Prod.fst))] := by
  have hlength :
      (state.remaining.take (xs.length + 1)).length = xs.length + 1 := by
    rw [List.length_take]
    omega
  have hcounts :
      ((state.remaining.take (xs.length + 1)).map Prod.fst).length =
          (x :: xs).length ∧
        ((state.remaining.take (xs.length + 1)).map Prod.snd).length =
          (x :: xs).length := by
    constructor <;>
      simp only [List.length_map, hlength, List.length_cons]
  obtain ⟨coreNext, hcore, hans⟩ :=
    prefixHybridStep_constr_of_primitivePathFresh D iv
      (fun _ => .construction
        ((state.remaining.take (xs.length + 1)).map Prod.fst)
        ((state.remaining.take (xs.length + 1)).map Prod.snd))
      state.core j x xs
      ((state.remaining.take (xs.length + 1)).map Prod.fst)
      ((state.remaining.take (xs.length + 1)).map Prod.snd)
      hquery rfl hcounts hfresh hro
  refine ⟨⟨coreNext, state.remaining.drop (xs.length + 1)⟩, ?_, hans⟩
  unfold workHybridStep
  dsimp only
  rw [hquery]
  simp only [SpQuery.primitiveCalls]
  rw [if_pos hlength]
  simp only [SpQuery.prefixCoins]
  rw [hcore]

#check @programPrefixes_some_of_primitivePathFresh
#check @programPrefixes_fresh_final_rate
#check @programPrefixes_preserves_ro_fresh_of_not_prefix
#check @programConstruction_fresh_final_rate
#check @programConstruction_preserves_ro_fresh_of_not_prefix
#check @prefixHybridStep_constr_of_primitivePathFresh
#check @workHybridStep_constr_of_primitivePathFresh

/-- info: 'Minidregg.Selvage.programPrefixes_some_of_primitivePathFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programPrefixes_some_of_primitivePathFresh
/-- info: 'Minidregg.Selvage.programPrefixes_fresh_final_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programPrefixes_fresh_final_rate
/-- info: 'Minidregg.Selvage.programPrefixes_preserves_ro_fresh_of_not_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programPrefixes_preserves_ro_fresh_of_not_prefix
/-- info: 'Minidregg.Selvage.programConstruction_fresh_final_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programConstruction_fresh_final_rate
/-- info: 'Minidregg.Selvage.programConstruction_preserves_ro_fresh_of_not_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms programConstruction_preserves_ro_fresh_of_not_prefix
/-- info: 'Minidregg.Selvage.prefixHybridStep_constr_of_primitivePathFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefixHybridStep_constr_of_primitivePathFresh
/-- info: 'Minidregg.Selvage.workHybridStep_constr_of_primitivePathFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms workHybridStep_constr_of_primitivePathFresh

end PrefixFresh

end Minidregg.Selvage
