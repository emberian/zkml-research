/-
# Selvage.OracleLogLinkedTarget — repair the final deployed-ZK target before
proving it

`Selvage.OracleLogLinked` leaves a prose residual: build an `OracleLogReduction`
for `accReductionBcsShiftedLinked` over the aligned deployed statement set.
Taken literally, that existential is vacuous.  The linked reduction is
parameterized by the *whole designated word family* `wv`, its source witness
type is that same family, and the proposed statement set asserts that `wv`
already witnesses every link.  Consequently the constant extractor `wv`
makes the source-failure event empty, without reading a log or using the
verifier.

This module records that diagnosis as a theorem and states the repaired target:
the extractor is required to be definitionally the linked log-read extractor.
The repaired target also carries the hypotheses actually needed by the fresh
horn (`dC` minimum distance and `δstar ≤ dC/2`), which the prose residual did
not list.

This module is the statement boundary: the final assembly can grow here
without weakening the extractor constraint.
-/
import Selvage.OracleLogLinked

namespace Minidregg.Selvage

section LinkedTarget

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F))
  (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m) (wv : Fin ch.length → Fin m → F)

/-- The linked reduction, named locally to keep the repaired target readable. -/
noncomputable abbrev linkedReduction : Reduction :=
  accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos hδone S dom d q wv

/-- The log-read increment at the *linked* reduction.  The upstream
`logIncrement` is typed at the unlinked reduction, so it cannot serve as the
algorithm pinned by the repaired target. -/
noncomputable def linkedLogIncrement {s : ℕ}
    (o : SrOutput (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (L : OracleLog
      (SrMove (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s) F)
    (i : Fin ch.length) : Option (Fin m → F) :=
  (L.answerOf (o.query i.castSucc)).map fun ρ =>
    ρ⁻¹ • (bcsWord dom d q (o.πs i.succ) - bcsWord dom d q (o.πs i.castSucc))

/-- The only extractor admitted by the repaired target: read each designated
challenge from the query log and recover the corresponding consecutive-root
difference, defaulting to zero on the fresh horn. -/
noncomputable def linkedShiftedLogExtractor (s : ℕ) :
    StraightlineOracleExtractor
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s :=
  fun o L i =>
    (linkedLogIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q wv o L i).getD 0

/-- On the fresh horn the linked log extractor has no challenge to read and
returns the specified default, zero. -/
theorem linkedShiftedLogExtractor_eq_zero_of_unqueried {s : ℕ}
    (o : SrOutput
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s)
    (L : OracleLog
      (SrMove (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv) s) F)
    (i : Fin ch.length)
    (h : L.answerOf (o.query i.castSucc) = none) :
    linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q wv
      s o L i = 0 := by
  unfold linkedShiftedLogExtractor linkedLogIncrement
  rw [h]
  rfl

/-- The deployed aligned statement set described by
`[ORACLE-LOG-linked-resid]`: the base claim is exactly satisfied and the
caller-fixed designation witnesses every link through the statement's own
channel. -/
def linkedStatementSet :
    Set (Stmt (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)) :=
  {st | AccClaim.Satisfies C st.x st.y ∧
    ∀ i, LinkAligned C st.x ch i (wv i)}

/-- Membership in the proposed deployed statement set already supplies the
entire source witness `wv`.  This is the key fact behind the unrestricted
existential's vacuity. -/
theorem linked_relaxedMem_of_statementSet
    {st : Stmt (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)}
    (hst : st ∈ linkedStatementSet C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    RelaxedMem
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv).R
      δ st.idx st.x st.y wv := by
  refine ⟨st.y, ⟨hst.1, hst.2⟩, ?_⟩
  rw [fracHamming_self]
  exact hδ

/-- Exact base satisfaction plus aligned extracted links is sufficient for
source relaxed membership, independently of the designated family. -/
theorem linked_relaxedMem_of_links
    {st : Stmt (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)}
    {w : Fin ch.length → Fin m → F}
    (hbase : AccClaim.Satisfies C st.x st.y)
    (hlinks : ∀ i, LinkAligned C st.x ch i (w i))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    RelaxedMem
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv).R
      δ st.idx st.x st.y w := by
  refine ⟨st.y, ⟨hbase, hlinks⟩, ?_⟩
  rw [fracHamming_self]
  exact hδ

/-- Over the deployed statement set, source-relaxed-membership failure can
only be failure of at least one extracted link. -/
theorem linked_source_failure_has_bad_link
    {st : Stmt (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)}
    (hst : st ∈ linkedStatementSet C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
    {w : Fin ch.length → Fin m → F} {δ : ℝ} (hδ : 0 ≤ δ)
    (hfail : ¬ RelaxedMem
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv).R
      δ st.idx st.x st.y w) :
    ∃ i : Fin ch.length, ¬ LinkAligned C st.x ch i (w i) := by
  classical
  by_contra hnone
  push Not at hnone
  exact hfail (linked_relaxedMem_of_links C foldRoot ch hm hch δs hδpos hδone
    S dom d q wv hst.1 hnone hδ)

omit [Fintype F] in
/-- If zero is not an aligned witness for a link, at least one of that link's
targets is nonzero.  This is the case split used by the fresh-horn fibre. -/
theorem exists_nonzero_target_of_zero_not_linkAligned
    {A₀ : AccClaim Root F (Fin m) r} (i : Fin ch.length)
    (hbad : ¬ LinkAligned C A₀ ch i (0 : Fin m → F)) :
    ∃ j : Fin r, (ch.get i).claim.targets j ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  apply hbad
  refine ⟨C.zero_mem, fun j => ?_⟩
  rw [map_zero, hnone j]

/-- **The old unrestricted existence shape is vacuous.**  A constant extractor
returning the word family captured by the reduction has zero error over the
proposed deployed statement set.  It reads no oracle log, uses no binding, and
does not inspect verifier acceptance.  This theorem is a negative audit result,
not the deployed-ZK closure. -/
noncomputable def knownWitnessOracleLogReduction :
    OracleLogReduction
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
      (linkedStatementSet C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
      (fun _ => 0) where
  extractLog := fun _s _o _L => wv
  sound_log := by
    intro s tq δ hδ P
    refine le_trans (le_of_eq (uniformProb_false fun coins hev => ?_)) ?_
    · obtain ⟨hz, hfail, -⟩ := hev
      exact hfail (linked_relaxedMem_of_statementSet C foldRoot ch hm hch δs
        hδpos hδone S dom d q wv hz hδ.1.le)
    · simp

/-- The corrected final target.  Existence alone is insufficient; the
`OracleLogReduction` must carry the exact log-read extractor above. -/
def LinkedAdaptiveIncrementSound (errstar : ℝ → ℝ) : Prop :=
  ∃ olr : OracleLogReduction
      (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
      (linkedStatementSet C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
      (accRbrError F errstar),
    ∀ s, olr.extractLog s =
      linkedShiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q wv s

/-- **[ORACLE-LOG-linked-target] — the exact non-vacuous obligation.**  These
are the hypotheses used by the two horns:

* `d ≤ t`, injective opened positions, and `wv` in the committed RS code pin
  the hit-horn increment;
* minimum distance `dC` and `δstar ≤ dC/2` give the fresh-horn unique-decoding
  pin;
* nonnegative `errstar` embeds the sharp `1/|F|` slot price in
  `accRbrError = errstar + 1/|F|`.

Unlike the old existential, this proposition cannot be discharged by replacing
the log extractor with the known designation family. -/
def DeployedZKAdaptiveSoundLinkedTarget (dC : ℝ) (errstar : ℝ → ℝ) : Prop :=
  d ≤ t →
  Function.Injective (dom ∘ q) →
  (∀ i, wv i ∈ reedSolomonCode dom d) →
  (∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v) →
  δs ≤ dC / 2 →
  (∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ) →
  LinkedAdaptiveIncrementSound C foldRoot ch hm hch δs hδpos hδone S dom d q wv errstar

/-- Any inhabitant of the corrected target exposes equality with the intended
log algorithm.  This tiny projection is the statement's tooth: downstream
code never receives an arbitrary existential extractor. -/
theorem linkedTarget_pins_extractor {errstar : ℝ → ℝ}
    (h : LinkedAdaptiveIncrementSound C foldRoot ch hm hch δs hδpos hδone S
      dom d q wv errstar) :
    ∃ olr : OracleLogReduction
        (linkedReduction C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
        (linkedStatementSet C foldRoot ch hm hch δs hδpos hδone S dom d q wv)
        (accRbrError F errstar),
      ∀ s, olr.extractLog s = linkedShiftedLogExtractor C foldRoot ch hm hch
        δs hδpos hδone S dom d q wv s :=
  h

end LinkedTarget

/-! ## The extractor constraint has teeth -/

namespace OracleLogLinkedTargetExample

open RSExample LCExample AccExample ZkHidingExample ZkExtractionExample
  CommitExample AccRbrBcsExample AccRbrBcsShiftedExample AccSoundRbrExample
  AccRbrInstanceExample OracleLogProgramExample OracleLogLinkedExample

/-- A well-typed linked output used only to distinguish the constant-known-
witness extractor from the required log reader. -/
noncomputable def targetOutF5 : SrOutput accReductionBcsShiftedLinked_F5 0 :=
  ⟨⟨(), genesis, xWord⟩, fun _ => msgOf xWord, fun _ => Fin.elim0, msEx⟩

/-- With an empty log, the required extractor returns zero at link zero. -/
theorem targetLogReader_zero_F5 :
    linkedShiftedLogExtractor
        (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
        (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
        S₅ dom₅ 2 qPair msEx 0 targetOutF5 [] (0 : Fin 2) = 0 := by
  apply linkedShiftedLogExtractor_eq_zero_of_unqueried
  exact OracleLog.answerOf_nil _

/-- **Teeth for the repaired statement:** the zero-error constant extractor
that witnesses the old existential does *not* satisfy the new extractor
constraint.  On the empty log it returns `msEx 0`, while the specified log
reader returns zero; those words are distinct, kernel-checked. -/
theorem knownWitness_not_logExtractor_F5 :
    ¬ ∀ s,
      (knownWitnessOracleLogReduction
        (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
        (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
        S₅ dom₅ 2 qPair msEx).extractLog s =
      linkedShiftedLogExtractor
        (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
        (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
        S₅ dom₅ 2 qPair msEx s := by
  intro h
  have heq := congrFun (congrFun (congrFun (h 0) targetOutF5) []) (0 : Fin 2)
  change msEx 0 = linkedShiftedLogExtractor
    (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair msEx 0 targetOutF5 [] (0 : Fin 2) at heq
  rw [targetLogReader_zero_F5] at heq
  exact (by decide : msEx 0 ≠ 0) heq

end OracleLogLinkedTargetExample

/-! ## Fresh-horn mathematical kernel

The game-level fibre proof will condition on every coin except one fresh final
challenge.  The lemma below is its only code-theoretic content: for a fixed
last word, two challenges whose aggregate claims are both δ-satisfied give two
nearby codewords; unique decoding identifies them, and one nonzero link target
makes the aggregate target channel injective in that challenge.
-/

section FreshKernel

variable {Root ι : Type*} {F : Type} [Field F] [DecidableEq F] [Fintype ι]
  [Nonempty ι] {r : ℕ}

/-- Replace one chain challenge in a schedule. -/
def scheduleAt (γs : ℕ → F) (k : ℕ) (ρ : F) : ℕ → F :=
  Function.update γs k ρ

/-- **Fresh-horn unique-draw pin.**  At a link with a nonzero target, at most
one value of its fresh challenge can make the aggregate δ-satisfiable near one
fixed output word in the unique-decoding regime. -/
theorem freshAggregateChallenge_injective
    {C : Submodule F (ι → F)} (foldRoot : Root → F → Root → Root)
    {A₀ : AccClaim Root F ι r} {ch : Chain Root F ι r}
    (γs : ℕ → F) (k : Fin ch.length) (y : ι → F) {δ dC : ℝ}
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hδC : δ < dC / 2) (j : Fin r)
    (htarget : (ch.get k).claim.targets j ≠ 0) :
    ∀ {ρ₁ ρ₂ : F},
      (∃ z : ι → F,
        AccClaim.Satisfies C
          (aggregate foldRoot (scheduleAt γs (k : ℕ) ρ₁) A₀ ch) z ∧
        relDist y z ≤ δ) →
      (∃ z : ι → F,
        AccClaim.Satisfies C
          (aggregate foldRoot (scheduleAt γs (k : ℕ) ρ₂) A₀ ch) z ∧
        relDist y z ≤ δ) →
      ρ₁ = ρ₂ := by
  intro ρ₁ ρ₂ hρ₁ hρ₂
  obtain ⟨z₁, hz₁, hy₁⟩ := hρ₁
  obtain ⟨z₂, hz₂, hy₂⟩ := hρ₂
  have hzeq : z₁ = z₂ :=
    codeword_eq_of_close_of_close hdC hz₁.1 hz₂.1 hδC hy₁ hy₂
  subst z₂
  have ht₁ := hz₁.2 j
  have ht₂ := hz₂.2 j
  rw [show (aggregate foldRoot (scheduleAt γs (k : ℕ) ρ₁) A₀ ch).weights =
      A₀.weights from aggregate_weights foldRoot _ _ _] at ht₁
  rw [show (aggregate foldRoot (scheduleAt γs (k : ℕ) ρ₂) A₀ ch).weights =
      A₀.weights from aggregate_weights foldRoot _ _ _] at ht₂
  have ht₁' := ht₁.trans
    (aggregate_targets foldRoot (scheduleAt γs (k : ℕ) ρ₁) A₀ ch j)
  have ht₂' := ht₂.trans
    (aggregate_targets foldRoot (scheduleAt γs (k : ℕ) ρ₂) A₀ ch j)
  have hs :
      (∑ i : Fin ch.length,
          scheduleAt γs (k : ℕ) ρ₁ (i : ℕ) * (ch.get i).claim.targets j) =
        ∑ i : Fin ch.length,
          scheduleAt γs (k : ℕ) ρ₂ (i : ℕ) * (ch.get i).claim.targets j := by
    exact add_left_cancel (ht₁'.symm.trans ht₂')
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ k),
      ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ k)] at hs
  have hoff :
      (∑ i ∈ Finset.univ.erase k,
          scheduleAt γs (k : ℕ) ρ₁ (i : ℕ) * (ch.get i).claim.targets j) =
        ∑ i ∈ Finset.univ.erase k,
          scheduleAt γs (k : ℕ) ρ₂ (i : ℕ) * (ch.get i).claim.targets j := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    have hv : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    rw [scheduleAt, scheduleAt, Function.update_of_ne hv,
      Function.update_of_ne hv]
  rw [hoff] at hs
  have hmul : ρ₁ * (ch.get k).claim.targets j =
      ρ₂ * (ch.get k).claim.targets j := by
    simpa [scheduleAt, Function.update_self] using add_left_cancel hs
  exact mul_right_cancel₀ htarget hmul

end FreshKernel

/-- info: 'Minidregg.Selvage.linked_relaxedMem_of_statementSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linked_relaxedMem_of_statementSet
/-- info: 'Minidregg.Selvage.knownWitnessOracleLogReduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms knownWitnessOracleLogReduction
/-- info: 'Minidregg.Selvage.linkedTarget_pins_extractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linkedTarget_pins_extractor
/-- info: 'Minidregg.Selvage.OracleLogLinkedTargetExample.knownWitness_not_logExtractor_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms OracleLogLinkedTargetExample.knownWitness_not_logExtractor_F5
/-- info: 'Minidregg.Selvage.freshAggregateChallenge_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms freshAggregateChallenge_injective

end Minidregg.Selvage
