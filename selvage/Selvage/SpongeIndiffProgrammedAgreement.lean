/-
# Selvage.SpongeIndiffProgrammedAgreement — the temporal programming boundary

The ideal sponge game answers construction queries directly from the lazy
random oracle.  Consequently a construction-first query can have an RO answer
before the simulator log contains the corresponding primitive path.  This
module records that fact as an executable counterexample, ruling out the
tempting but false invariant that every sampled construction answer is already
programmed into the simulator.

The positive theorem states the direction the eventual game hop may use: if a
message was answered earlier and a later fresh forward primitive query
completes its path, `simFwdRO` programs exactly that recorded answer and does
not resample it.  This is a temporal/deferred-programming invariant, not an
identical-until-bad or random-permutation/random-function switching theorem.
-/
import Selvage.SpongeIndiffOffBadRun

namespace Minidregg.Selvage

section Agreement

variable {Rate Cap : Type} [AddCommGroup Rate]

/-- A particular nonempty construction message is represented by both the RO
and a completed simulator path with the same squeezed rate value. -/
def MessageProgrammed (ro : Oracle (List Rate) Rate)
    (sim : Oracle (Rate × Cap) (Rate × Cap)) (iv : Rate × Cap)
    (m : List Rate) : Prop :=
  ∃ h c, ro.lookup m = some h ∧ walkFrom sim iv m = some (h, c)

/-- The deliberately too-strong invariant: every sampled RO answer already
has a matching completed simulator path.  Construction-first execution below
formally refutes it for the landed ideal game. -/
def EveryRoAnswerProgrammed (ro : Oracle (List Rate) Rate)
    (sim : Oracle (Rate × Cap) (Rate × Cap)) (iv : Rate × Cap) : Prop :=
  ∀ m h, ro.lookup m = some h → ∃ c, walkFrom sim iv m = some (h, c)

/-- **Deferred programming.**  If `m` was sampled earlier, then a fresh
forward query which completes `m` programs the already-recorded answer.  The
rate coin supplied to this later step is ignored by the RO replay branch. -/
theorem simFwdRO_programs_previously_answered
    (iv : Rate × Cap) (ro : Oracle (List Rate) Rate)
    (sim : Oracle (Rate × Cap) (Rate × Cap)) {s : Rate × Cap}
    {m : List Rate} {h : Rate}
    (hlookup : ro.lookup m = some h)
    (hfresh : sim.lookup s = none)
    (hcompletion : completion? sim iv s = some m)
    (rateCoin : Rate) (blockCoin : Rate × Cap) :
    (simFwdRO iv ro sim s rateCoin blockCoin).2.1 = ro ∧
      (simFwdRO iv ro sim s rateCoin blockCoin).1 = (h, blockCoin.2) ∧
      walkFrom (simFwdRO iv ro sim s rateCoin blockCoin).2.2 iv m =
        some (h, blockCoin.2) := by
  unfold simFwdRO
  rw [hcompletion]
  simp only
  rw [Oracle.respond_hit hlookup]
  constructor
  · rfl
  constructor
  · exact Oracle.respond_fresh_fst hfresh _
  · exact walk_programs hfresh hcompletion _

end Agreement

/-! ## Smallest construction-first witness -/

namespace SpongeProgrammedAgreementExample

def iv : ZMod 2 × Fin 3 := (0, 0)

def constructionOne : Distinguisher (ZMod 2) (Fin 3) 1 where
  move _ := .constr 1 []
  out _ := true

def coins : Fin 1 → ZMod 2 × (ZMod 2 × Fin 3) :=
  fun _ => (1, (0, 1))

noncomputable def afterConstruction : IdealState (ZMod 2) (Fin 3) :=
  idealStep constructionOne iv coins ⟨Oracle.empty, Oracle.empty, []⟩ 0

/-- The construction query really samples and records its RO answer. -/
theorem afterConstruction_lookup :
    afterConstruction.ro.lookup [1] = some 1 := by
  change ((Oracle.empty.respond [1] (1 : ZMod 2)).2.lookup [1]) = some 1
  rw [Oracle.lookup_respond_self, Oracle.respond_fresh_fst (Oracle.lookup_empty [1])]

/-- A construction query does not touch the primitive simulator log. -/
theorem afterConstruction_sim : afterConstruction.sim = Oracle.empty := rfl

/-- **Counterexample.**  Immediately after a construction-first query, its
RO answer is not yet represented by any simulator path.  Hence the stronger
"all answers are already programmed" invariant cannot underlie the game hop. -/
theorem construction_first_not_every_answer_programmed :
    ¬ EveryRoAnswerProgrammed afterConstruction.ro afterConstruction.sim iv := by
  intro hall
  obtain ⟨c, hwalk⟩ := hall [1] 1 afterConstruction_lookup
  rw [afterConstruction_sim, walkFrom_cons, Oracle.lookup_empty] at hwalk
  cases hwalk

/-- The first primitive forward query at the IV capacity completes exactly
the previously answered singleton construction message. -/
theorem first_completion :
    completion? (Oracle.empty : Oracle (ZMod 2 × Fin 3) (ZMod 2 × Fin 3))
      iv (1, 0) = some [1] := by
  simpa using completion?_empty_iv
    (iv := iv) (s := ((1 : ZMod 2), (0 : Fin 3))) rfl

/-- **Temporal convergence witness.**  Once that later primitive query is
made, the path is programmed with the exact earlier RO answer—even though the
later rate coin is different. -/
theorem construction_first_later_programmed :
    let ro := (Oracle.empty.respond ([1] : List (ZMod 2)) (1 : ZMod 2)).2
    let step := simFwdRO iv ro Oracle.empty (1, 0) 0 (0, 1)
    MessageProgrammed step.2.1 step.2.2 iv [1] := by
  dsimp only
  have hlookup :
      (Oracle.empty.respond ([1] : List (ZMod 2)) (1 : ZMod 2)).2.lookup [1] =
        some 1 := by
    rw [Oracle.lookup_respond_self,
      Oracle.respond_fresh_fst (Oracle.lookup_empty [1])]
  have h := simFwdRO_programs_previously_answered iv
    (Oracle.empty.respond ([1] : List (ZMod 2)) (1 : ZMod 2)).2 Oracle.empty
    (s := ((1 : ZMod 2), (0 : Fin 3))) (m := ([1] : List (ZMod 2)))
    (h := (1 : ZMod 2)) hlookup (Oracle.lookup_empty (1, 0))
    first_completion 0 (0, 1)
  refine ⟨1, 1, ?_, ?_⟩
  · rw [h.1]
    exact hlookup
  · exact h.2.2

end SpongeProgrammedAgreementExample

/-- info: 'Minidregg.Selvage.simFwdRO_programs_previously_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simFwdRO_programs_previously_answered
/-- info: 'Minidregg.Selvage.SpongeProgrammedAgreementExample.construction_first_not_every_answer_programmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeProgrammedAgreementExample.construction_first_not_every_answer_programmed
/-- info: 'Minidregg.Selvage.SpongeProgrammedAgreementExample.construction_first_later_programmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpongeProgrammedAgreementExample.construction_first_later_programmed

end Minidregg.Selvage
