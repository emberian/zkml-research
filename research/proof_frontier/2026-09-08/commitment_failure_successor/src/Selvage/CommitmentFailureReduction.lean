/- Observed finite-log Failure reduces to actual prefix-fixed targets and
fresh response collisions. Executable witnesses inspect only retained entries. -/
import Selvage.CommitmentFreshTrace
import Selvage.ArityEightScheduleSupplied

namespace Minidregg.Selvage.CommitmentFreshTrace
open scoped Classical
variable {Value : Type} {Q N R : ℕ}

/-- A checkpoint consists of all entries before some fresh-query cut. Its
root has been declared by every later fresh query, before that query's coin. -/
def CheckpointOrigin (A : Strategy Value Q N R) (c : Fin Q → Fin N)
    (P : EfficientRootOpening.Log Value (Fin N)) (root : Fin N) : Prop :=
  ∃ (k : ℕ) (hk : k ≤ Q),
    (∀ e, e ∈ P ↔ e ∈ prefixLog A k hk (friPrefix c k hk)) ∧
    ∀ t : Fin Q, k ≤ t.val → root ∈ A.roots t (friPrefix c t (by omega))

/-- Only actually observed entries may be charged to the fresh-response tape. -/
def LogCovered (A : Strategy Value Q N R) (c : Fin Q → Fin N)
    (L : EfficientRootOpening.Log Value (Fin N)) : Prop :=
  ∀ e ∈ L, e ∈ entries A c

/-- Log coverage supplies actual hash-call validity for the canonical cache;
this is derived from the existing handler's fresh-query response equality. -/
theorem covered_cached_valid (A : Strategy Value Q N R) (hf : Fresh A)
    (c : Fin Q → Fin N) (dflt : Fin N) (L : EfficientRootOpening.Log Value (Fin N))
    (hL : LogCovered A c L) :
    ∀ e ∈ L, e.2 = EfficientRootOpening.evaluate (cachedSuite A c dflt) e.1 := by
  intro e he
  obtain ⟨t,ht⟩ := (mem_entries_iff A c e).mp (hL e he)
  rw [←ht]
  exact (cachedSuite_entry A hf c dflt t).symm

/-- An observed collision supplies two distinct fresh-query indices. -/
theorem response_collision_cover (A : Strategy Value Q N R) (c : Fin Q → Fin N)
    (L : EfficientRootOpening.Log Value (Fin N)) (hL : LogCovered A c L)
    (hb : EfficientRootOpening.ResponseCollision L) : Collides c := by
  obtain ⟨e,he,e',he',hresp,hne⟩ := hb
  obtain ⟨i,hi⟩ := (mem_entries_iff A c e).mp (hL e he)
  obtain ⟨j,hj⟩ := (mem_entries_iff A c e').mp (hL e' he')
  apply collides_of_ne (i := i) (j := j)
  · intro h
    apply hne
    rw [←hi,←hj,h]
  · simpa only [←hi,←hj,entry] using hresp

/-- A late entry occurs after the checkpoint cut, so its root or child target
was already fixed by the prefix seen before its fresh response. -/
theorem late_target_cover (A : Strategy Value Q N R) (c : Fin Q → Fin N)
    (P L : EfficientRootOpening.Log Value (Fin N)) (root : Fin N)
    (hP : CheckpointOrigin A c P root) (hL : LogCovered A c L)
    (hb : EfficientRootOpening.LateTarget P L root) :
    ∃ t, c t ∈ targets A t (friPrefix c t (by omega)) := by
  obtain ⟨k,hk,hmem,hroot⟩ := hP
  obtain ⟨e,he,hnot,htarget⟩ := hb
  obtain ⟨t,ht⟩ := (mem_entries_iff A c e).mp (hL e he)
  have hkt : k ≤ t.val := by
    by_contra h
    apply hnot
    apply (hmem e).mpr
    exact (mem_prefixLog_iff A c k hk e).mpr ⟨t,by omega,ht⟩
  refine ⟨t,?_⟩
  rcases htarget with hr | ⟨ep,hep,hchild⟩
  · have hh := hroot t hkt
    have hc : c t = root := by simpa only [←ht,entry] using hr
    simp only [targets,List.mem_append]
    exact Or.inr (hc ▸ hh)
  · obtain ⟨s,hs,hse⟩ := (mem_prefixLog_iff A c k hk ep).mp ((hmem ep).mp hep)
    have hp : ep ∈ prefixLog A t (by omega) (friPrefix c t (by omega)) :=
      (mem_prefixLog_iff A c t (by omega) ep).mpr ⟨s,by omega,hse⟩
    have hc : c t ∈ EfficientRootOpening.children ep.1 := by simpa only [←ht,entry] using hchild
    simp only [targets,List.mem_append]
    exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨ep,hp,hc⟩))

theorem checkpoint_bad_cover (A : Strategy Value Q N R) (c : Fin Q → Fin N)
    (P L : EfficientRootOpening.Log Value (Fin N)) (root : Fin N)
    (hP : CheckpointOrigin A c P root) (hL : LogCovered A c L)
    (hb : EfficientRootOpening.Bad P L root) : Bad A c := by
  rcases hb with h | h
  · exact Or.inl (response_collision_cover A c L hL h)
  · exact Or.inr (late_target_cover A c P L root hP hL h)

/-- The exact collision pair is returned, with no oracle calls or semantic
search over unobserved alternative openings. -/
def collisionWitness [DecidableEq Value] (L : EfficientRootOpening.Log Value (Fin N)) :
    Option ((EfficientRootOpening.Query Value (Fin N) × Fin N) ×
      (EfficientRootOpening.Query Value (Fin N) × Fin N)) :=
  (L.product L).find? (fun p => decide (p.1.2 = p.2.2 ∧ p.1.1 ≠ p.2.1))

theorem collisionWitness_sound [DecidableEq Value] (L : EfficientRootOpening.Log Value (Fin N))
    {p} (hp : collisionWitness L = some p) :
    p.1 ∈ L ∧ p.2 ∈ L ∧ p.1.2 = p.2.2 ∧ p.1.1 ≠ p.2.1 := by
  have hm := List.mem_of_find?_eq_some hp
  have ht := List.find?_some hp
  exact ⟨(List.mem_product.mp hm).1,(List.mem_product.mp hm).2,of_decide_eq_true ht⟩

theorem collisionWitness_none_iff [DecidableEq Value] (L : EfficientRootOpening.Log Value (Fin N)) :
    collisionWitness L = none ↔ ¬EfficientRootOpening.ResponseCollision L := by
  constructor
  · intro hnone hb
    obtain ⟨e,he,e',he',hresp,hne⟩ := hb
    have hf := List.find?_eq_none.mp hnone (e,e') (List.mem_product.mpr ⟨he,he'⟩)
    exact hf (by simp [hresp,hne])
  · intro hn
    apply List.find?_eq_none.mpr
    intro p hp ht
    have hm := List.mem_product.mp hp
    have hh : p.1.2 = p.2.2 ∧ p.1.1 ≠ p.2.1 := of_decide_eq_true ht
    exact hn ⟨p.1,hm.1,p.2,hm.2,hh⟩

/-- Under actual hash-call validity, the returned pair is a typed-hash
collision. This includes leaf-versus-node collisions, unlike separate-only CR. -/
theorem collisionWitness_typed [DecidableEq Value]
    (H : BinaryMerkle.HashSuite Value (Fin N)) (L : EfficientRootOpening.Log Value (Fin N))
    (hvalid : ∀ e ∈ L, e.2 = EfficientRootOpening.evaluate H e.1)
    {p} (hp : collisionWitness L = some p) :
    p.1.1 ≠ p.2.1 ∧ EfficientRootOpening.evaluate H p.1.1 = EfficientRootOpening.evaluate H p.2.1 := by
  obtain ⟨h₁,h₂,he,hne⟩ := collisionWitness_sound L hp
  exact ⟨hne,(hvalid p.1 h₁).symm.trans (he.trans (hvalid p.2 h₂))⟩

/-- The retained collision witness is a real typed-hash collision in this
finite fresh-query game, without a separate hash-consistency premise. -/
theorem covered_collision_typed [DecidableEq Value]
    (A : Strategy Value Q N R) (hf : Fresh A) (c : Fin Q → Fin N) (dflt : Fin N)
    (L : EfficientRootOpening.Log Value (Fin N)) (hL : LogCovered A c L)
    {p} (hp : collisionWitness L = some p) :
    p.1.1 ≠ p.2.1 ∧ EfficientRootOpening.evaluate (cachedSuite A c dflt) p.1.1 =
      EfficientRootOpening.evaluate (cachedSuite A c dflt) p.2.1 :=
  collisionWitness_typed _ L (covered_cached_valid A hf c dflt L hL) hp

/-- At most this many retained entry pairs are searched; extraction makes no new hash query. -/
theorem collision_candidates (L : EfficientRootOpening.Log Value (Fin N)) :
    (L.product L).length = L.length^2 := by
  induction L with
  | nil => simp [List.product]
  | cons e L ih =>
    simp only [List.product,List.length_flatMap,List.length_map]
    simp
    ring

def lateWitness [DecidableEq Value] (P L : EfficientRootOpening.Log Value (Fin N)) (root : Fin N) :
    Option (EfficientRootOpening.Query Value (Fin N) × Fin N) :=
  L.find? (fun e => decide (e ∉ P) &&
    (decide (e.2 = root) || P.any (fun p => decide (e.2 ∈ EfficientRootOpening.children p.1))))

theorem lateWitness_sound [DecidableEq Value] (P L : EfficientRootOpening.Log Value (Fin N))
    (root : Fin N) {e} (he : lateWitness P L root = some e) :
    e ∈ L ∧ e ∉ P ∧ EfficientRootOpening.Target P root e.2 := by
  have hm := List.mem_of_find?_eq_some he
  have ht := List.find?_some he
  exact ⟨hm,by simpa [EfficientRootOpening.Target,List.any_eq_true] using ht⟩

theorem lateWitness_none_iff [DecidableEq Value]
    (P L : EfficientRootOpening.Log Value (Fin N)) (root : Fin N) :
    lateWitness P L root = none ↔ ¬EfficientRootOpening.LateTarget P L root := by
  simp [lateWitness,List.find?_eq_none,EfficientRootOpening.LateTarget,
    EfficientRootOpening.Target,List.any_eq_true]

section Schedule
variable {F : Type} [Field F] [DecidableEq F] {m : ℕ}

/-- Concrete origin certificates for the actual roots used by every supplied round. -/
def Origins (A : Strategy F Q N R) (c : Fin Q → Fin N)
    (st : ArityEight.Schedule.Checkpoints F (Fin N)) (r : Fin m → F) : Prop :=
  (∀ n (hn : n ≤ m),
    CheckpointOrigin A c (st.word n (friPrefix r n hn)).1 (st.word n (friPrefix r n hn)).2) ∧
  (∀ j : Fin m,
    CheckpointOrigin A c (st.input j (friPrefix r j (by omega))).1
      (st.input j (friPrefix r j (by omega))).2)

omit [Field F] [DecidableEq F] in
/-- The observed finite multi-round Failure is covered by the trace's
collision/target event. No global probability premise is introduced. -/
theorem schedule_failure_cover (A : Strategy F Q N R) (c : Fin Q → Fin N)
    (st : ArityEight.Schedule.Checkpoints F (Fin N)) (r : Fin m → F)
    (L : EfficientRootOpening.Log F (Fin N)) (hO : Origins A c st r) (hL : LogCovered A c L)
    (hF : ArityEight.Schedule.Failure st L r) : Bad A c := by
  obtain ⟨j,h | h | h⟩ := hF
  · exact checkpoint_bad_cover A c _ L _ (hO.1 j (by omega)) hL h
  · exact checkpoint_bad_cover A c _ L _ (hO.2 j) hL h
  · exact checkpoint_bad_cover A c _ L _ (hO.1 (j+1) (by omega)) hL h

omit [Field F] [DecidableEq F] in
/-- The formerly unpriced observed Failure now has a classical fresh-query
bound when its actual checkpoints and retained entries come from this trace. -/
theorem schedule_failure_probability [NeZero N] (A : Strategy F Q N R)
    (st : (Fin Q → Fin N) → ArityEight.Schedule.Checkpoints F (Fin N))
    (r : (Fin Q → Fin N) → Fin m → F) (logs : (Fin Q → Fin N) → EfficientRootOpening.Log F (Fin N))
    (hO : ∀ c, Origins A c (st c) (r c)) (hL : ∀ c, LogCovered A c (logs c)) :
    uniformProb (Fin Q → Fin N) (fun c => ArityEight.Schedule.Failure (st c) (logs c) (r c)) ≤
      ((3*(Q:ℝ)^2+Q)/2+R*Q)/N :=
  le_trans (uniformProb_mono fun c h => schedule_failure_cover A c (st c) (r c) (logs c) (hO c) (hL c) h)
    (bad_probability A)

omit [Field F] [DecidableEq F] in
/-- Same bound through the existing Oracle handler's actual response log.
Freshness is used by the proved handler equality, not asserted as independence prose. -/
theorem oracle_schedule_failure_probability [NeZero N] (A : Strategy F Q N R) (hf : Fresh A)
    (st : (Fin Q → Fin N) → ArityEight.Schedule.Checkpoints F (Fin N))
    (r : (Fin Q → Fin N) → Fin m → F) (logs : (Fin Q → Fin N) → EfficientRootOpening.Log F (Fin N))
    (hO : ∀ c, Origins A c (st c) (r c))
    (hL : ∀ c e, e ∈ logs c → e ∈ oracleLog A c) :
    uniformProb (Fin Q → Fin N) (fun c => ArityEight.Schedule.Failure (st c) (logs c) (r c)) ≤
      ((3*(Q:ℝ)^2+Q)/2+R*Q)/N := by
  apply schedule_failure_probability A st r logs hO
  intro c e he
  simpa only [oracleLog_eq_entries A hf c] using hL c e he

end Schedule
end Minidregg.Selvage.CommitmentFreshTrace

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.covered_cached_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.covered_cached_valid

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.response_collision_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.response_collision_cover

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.late_target_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.late_target_cover

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.checkpoint_bad_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.checkpoint_bad_cover

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.collisionWitness_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.collisionWitness_sound

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.collisionWitness_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.collisionWitness_none_iff

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.collisionWitness_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.collisionWitness_typed

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.covered_collision_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.covered_collision_typed

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.collision_candidates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.collision_candidates

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.lateWitness_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.lateWitness_sound

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.lateWitness_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.lateWitness_none_iff

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.schedule_failure_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.schedule_failure_cover

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.schedule_failure_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.schedule_failure_probability

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.oracle_schedule_failure_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.oracle_schedule_failure_probability
