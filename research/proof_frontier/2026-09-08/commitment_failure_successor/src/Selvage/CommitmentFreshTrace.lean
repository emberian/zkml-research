/- Classical fresh-query trace accounting for checkpoint opening extraction.
Queries and declared roots use only earlier digest responses. This module
uses the existing Oracle handler and birthday kernel, not a FS/QROM claim. -/
import Selvage.ArityEightSchedule
import Selvage.EfficientRootOpening
import Selvage.CollisionResistanceROM

namespace Minidregg.Selvage.CommitmentFreshTrace
open scoped Classical

/-- A query and all roots already declared before its response may depend on
prior responses. R is a bound on the retained declared-root list. -/
structure Strategy (Value : Type) (Q N R : ℕ) where
  query : ∀ t : Fin Q, (Fin t.val → Fin N) → EfficientRootOpening.Query Value (Fin N)
  roots : ∀ t : Fin Q, (Fin t.val → Fin N) → List (Fin N)
  roots_le : ∀ t p, (roots t p).length ≤ R

variable {Value : Type} {Q N R : ℕ}

def entry (A : Strategy Value Q N R) (c : Fin Q → Fin N) (t : Fin Q) :
    EfficientRootOpening.Query Value (Fin N) × Fin N :=
  (A.query t (friPrefix c t (by omega)),c t)

def prefixLog (A : Strategy Value Q N R) (n : ℕ) (hn : n ≤ Q) (p : Fin n → Fin N) :
    EfficientRootOpening.Log Value (Fin N) :=
  List.ofFn fun t : Fin n => (A.query ⟨t.val,by omega⟩ (friPrefix p t (by omega)),p t)

def entries (A : Strategy Value Q N R) (c : Fin Q → Fin N) : EfficientRootOpening.Log Value (Fin N) :=
  List.ofFn (entry A c)

/-- Earlier node children, current query children, and previously declared
roots. The response to the current query is not available to this function. -/
def targets (A : Strategy Value Q N R) (t : Fin Q) (p : Fin t.val → Fin N) : List (Fin N) :=
  (prefixLog A t (by omega) p).flatMap (fun e => EfficientRootOpening.children e.1) ++
    EfficientRootOpening.children (A.query t p) ++ A.roots t p

def Bad (A : Strategy Value Q N R) (c : Fin Q → Fin N) : Prop :=
  Collides c ∨ ∃ t, c t ∈ targets A t (friPrefix c t (by omega))

/-- Every counted query is fresh along every response tape. Repeated actual
calls must be represented by their existing cached entry, not a new coin. -/
def Fresh (A : Strategy Value Q N R) : Prop :=
  ∀ c : Fin Q → Fin N, Function.Injective (fun t => (entry A c t).1)

/-- Actual response list of the existing lazy-sampling Oracle handler. -/
noncomputable def oracleLog (A : Strategy Value Q N R) (c : Fin Q → Fin N) :
    EfficientRootOpening.Log Value (Fin N) :=
  (entries A c).map Prod.fst |>.zip (oracleRun Oracle.empty (entries A c)).2

/-- Adaptive prefix queries are answered by their own coins in the actual
handler, once all counted queries are proved fresh. -/
theorem oracle_answers (A : Strategy Value Q N R) (hf : Fresh A) (c : Fin Q → Fin N) :
    (oracleRun Oracle.empty (entries A c)).2 = List.ofFn c := by
  apply Eq.trans (oracleRun_fresh _ _ ?_ (fun e _ => Oracle.lookup_empty e.1))
  · rw [entries,List.map_ofFn]
    rfl
  · simpa [entries,List.map_ofFn] using List.nodup_ofFn.mpr (hf c)

theorem oracleLog_eq_entries (A : Strategy Value Q N R) (hf : Fresh A) (c : Fin Q → Fin N) :
    oracleLog A c = entries A c := by
  rw [oracleLog,oracle_answers A hf c]
  have hc : List.ofFn c = (entries A c).map Prod.snd := by
    rw [entries,List.map_ofFn]
    rfl
  rw [hc,List.zip_map']
  simp

/-- Exact checkpoint-prefix membership, retaining original typed query/response pairs. -/
theorem mem_prefixLog_iff (A : Strategy Value Q N R) (c : Fin Q → Fin N)
    (n : ℕ) (hn : n ≤ Q) (e : EfficientRootOpening.Query Value (Fin N) × Fin N) :
    e ∈ prefixLog A n hn (friPrefix c n hn) ↔
      ∃ t : Fin Q, t.val < n ∧ entry A c t = e := by
  constructor
  · intro he
    obtain ⟨t,ht⟩ := List.mem_ofFn.mp he
    exact ⟨⟨t.val,by omega⟩,t.isLt,ht⟩
  · rintro ⟨t,ht,he⟩
    exact List.mem_ofFn.mpr ⟨⟨t.val,ht⟩,he⟩

theorem mem_entries_iff (A : Strategy Value Q N R) (c : Fin Q → Fin N)
    (e : EfficientRootOpening.Query Value (Fin N) × Fin N) :
    e ∈ entries A c ↔ ∃ t, entry A c t = e := List.mem_ofFn

theorem children_length_le (q : EfficientRootOpening.Query Value (Fin N)) :
    (EfficientRootOpening.children q).length ≤ 2 := by
  cases q <;> simp [EfficientRootOpening.children]

/-- Every typed node query contributes at most two child targets. -/
theorem children_log_length_le (L : EfficientRootOpening.Log Value (Fin N)) :
    (L.flatMap (fun e => EfficientRootOpening.children e.1)).length ≤ 2*L.length := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    have h := children_length_le e.1
    omega

theorem targets_length_le (A : Strategy Value Q N R) (t : Fin Q) (p : Fin t.val → Fin N) :
    (targets A t p).length ≤ 2*(t.val+1)+R := by
  have hp := children_log_length_le (prefixLog A t (by omega) p)
  have hc := children_length_le (A.query t p)
  have hr := A.roots_le t p
  have hl : (prefixLog A t (by omega) p).length = t.val := List.length_ofFn
  rw [hl] at hp
  simp only [targets,List.length_append]
  omega

/-- Existing forward log lookup returns the retained answer whenever all
records for that query agree. -/
theorem answerOf_of_mem_unique {K C : Type} (L : OracleLog K C) (k : K) (v : C)
    (hm : (k,v) ∈ L) (hu : ∀ e ∈ L, e.1 = k → e.2 = v) :
    OracleLog.answerOf L k = some v := by
  induction L with
  | nil => simp at hm
  | cons e L ih =>
    by_cases hk : e.1 = k
    · have hv := hu e (List.mem_cons_self ..) hk
      have he : e = (k,v) := Prod.ext hk hv
      rw [he,OracleLog.answerOf_cons_self]
    · have ht : (k,v) ∈ L := by
        rcases List.mem_cons.mp hm with he | he
        · exact False.elim (hk (congrArg Prod.fst he).symm)
        · exact he
      have hh := ih ht (fun e he => hu e (List.mem_cons_of_mem _ he))
      simpa only [OracleLog.answerOf_cons_of_ne (Ne.symm hk)] using hh

/-- A full typed HashSuite completion of the actual finite cache. All absent
queries receive the same public default; only logged calls matter to this reduction. -/
noncomputable def cachedSuite (A : Strategy Value Q N R) (c : Fin Q → Fin N) (dflt : Fin N) :
    BinaryMerkle.HashSuite Value (Fin N) where
  leaf v := (OracleLog.answerOf (entries A c) (.leaf v)).getD dflt
  node a b := (OracleLog.answerOf (entries A c) (.node a b)).getD dflt

theorem evaluate_cachedSuite (A : Strategy Value Q N R) (c : Fin Q → Fin N) (dflt : Fin N)
    (q : EfficientRootOpening.Query Value (Fin N)) :
    EfficientRootOpening.evaluate (cachedSuite A c dflt) q =
      (OracleLog.answerOf (entries A c) q).getD dflt := by cases q <;> rfl

/-- The completed suite exactly replays every actual fresh query response. -/
theorem cachedSuite_entry (A : Strategy Value Q N R) (hf : Fresh A)
    (c : Fin Q → Fin N) (dflt : Fin N) (t : Fin Q) :
    EfficientRootOpening.evaluate (cachedSuite A c dflt) (entry A c t).1 = c t := by
  rw [evaluate_cachedSuite]
  have hm : ((entry A c t).1,c t) ∈ entries A c := List.mem_ofFn.mpr ⟨t,rfl⟩
  have hh := answerOf_of_mem_unique (entries A c) (entry A c t).1 (c t) hm (by
    intro e he hq
    obtain ⟨i,hi⟩ := (mem_entries_iff A c e).mp he
    have ht : i = t := hf c (by simpa only [hi] using hq)
    simp only [←hi,ht,entry])
  rw [hh]
  rfl

/-- Distinct fresh queries cannot outnumber the actual retained call records
covering them. Repeated verifier calls can reuse the same fresh cache entry. -/
theorem fresh_count_le_calls [DecidableEq Value] (A : Strategy Value Q N R) (hf : Fresh A)
    (c : Fin Q → Fin N) (L : EfficientRootOpening.Log Value (Fin N))
    (hcover : ∀ e ∈ entries A c, e ∈ L) : Q ≤ L.length := by
  have hn : (entries A c).Nodup := List.nodup_ofFn.mpr (by
    intro i j h
    exact hf c (congrArg Prod.fst h))
  have hs : (entries A c).toFinset ⊆ L.toFinset := by
    intro e he
    exact List.mem_toFinset.mpr (hcover e (List.mem_toFinset.mp he))
  calc
    Q = (entries A c).toFinset.card := by rw [List.toFinset_card_of_nodup hn]; exact List.length_ofFn.symm
    _ ≤ L.toFinset.card := Finset.card_le_card hs
    _ ≤ L.length := List.toFinset_card_le L

section Probability
variable [NeZero N]

/-- Prefix-conditioning over an arbitrary nonempty finite alphabet. This is
the same existing split-coordinate argument, without a field restriction on digests. -/
theorem uniform_prefix_event_le {C : Type} [Fintype C] (dflt : C)
    (t : Fin Q) (p : (Fin t.val → C) → C → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hp : ∀ pfx, uniformProb C (p pfx) ≤ ε) :
    uniformProb (Fin Q → C) (fun c => p (friPrefix c t (by omega)) (c t)) ≤ ε := by
  let e := splitCoord (β := C) t
  have he := uniformProb_equiv e (fun x => p (friPrefix (e.symm x) t (by omega)) x.2)
  have hh : uniformProb (Fin Q → C) (fun c => p (friPrefix c t (by omega)) (c t)) =
      uniformProb (({i : Fin Q // i ≠ t} → C) × C)
        (fun x => p (friPrefix (e.symm x) t (by omega)) x.2) := by
    rw [←he]
    apply uniformProb_congr
    intro c
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hh]
  apply uniformProb_prod_le hε
  intro a
  have hc : ∀ b : C, friPrefix (e.symm (a,b)) t (by omega) =
      friPrefix (e.symm (a,dflt)) t (by omega) := by
    intro b
    funext i
    unfold friPrefix
    have hi : (⟨i.val,by omega⟩ : Fin Q) ≠ t := by
      intro h
      exact (Nat.ne_of_lt i.isLt) (congrArg Fin.val h)
    exact (splitCoord_symm_apply_of_ne (a,b) hi).trans (splitCoord_symm_apply_of_ne (a,dflt) hi).symm
  calc
    _ = uniformProb C (p (friPrefix (e.symm (a,dflt)) t (by omega))) :=
      uniformProb_congr fun b => by rw [hc b]
    _ ≤ ε := hp _

/-- One fresh response hits only a bounded prefix-fixed target list. -/
theorem target_hit_le (A : Strategy Value Q N R) (t : Fin Q) :
    uniformProb (Fin Q → Fin N) (fun c => c t ∈ targets A t (friPrefix c t (by omega))) ≤
      ((2*(t.val+1)+R:ℕ):ℝ)/N := by
  apply uniform_prefix_event_le (0 : Fin N) t (fun p b => b ∈ targets A t p) (by positivity)
  intro p
  have hm : uniformProb (Fin N) (fun b => b ∈ targets A t p) =
      uniformProb (Fin N) (fun b => b ∈ (targets A t p).toFinset) :=
    uniformProb_congr fun b => by simp
  rw [hm,uniformProb_mem_finset,Fintype.card_fin]
  have hn := le_trans (List.toFinset_card_le (targets A t p)) (targets_length_le A t p)
  gcongr

/-- The exact target-count sum, before dividing by digest cardinality. -/
theorem target_sum (Q R : ℕ) :
    (∑ t : Fin Q, ((2*(t.val+1)+R:ℕ):ℝ)) = (Q:ℝ)*(Q+1)+R*Q := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- Classical adaptive fresh-query trace bound. The birthday term is reused
from CollisionResistanceROM; only prefix-fixed roots/children are charged as targets. -/
theorem bad_probability (A : Strategy Value Q N R) :
    uniformProb (Fin Q → Fin N) (Bad A) ≤
      ((3*(Q:ℝ)^2+Q)/2+R*Q)/N := by
  have hhit : uniformProb (Fin Q → Fin N)
      (fun c => ∃ t, c t ∈ targets A t (friPrefix c t (by omega))) ≤
      ((Q:ℝ)*(Q+1)+R*Q)/N := by
    calc
      _ ≤ ∑ t : Fin Q, uniformProb (Fin Q → Fin N)
          (fun c => c t ∈ targets A t (friPrefix c t (by omega))) := uniformProb_exists_le _
      _ ≤ ∑ t : Fin Q, ((2*(t.val+1)+R:ℕ):ℝ)/N := Finset.sum_le_sum fun t _ => target_hit_le A t
      _ = _ := by rw [←Finset.sum_div,target_sum]
  have hcol := birthday_bound Q N
  have hs := uniformProb_or_le (C := Fin Q → Fin N) Collides
    (fun c => ∃ t, c t ∈ targets A t (friPrefix c t (by omega)))
  change uniformProb (Fin Q → Fin N) (Bad A) ≤ _ at hs
  change uniformProb (Fin Q → Fin N) Collides ≤ _ at hcol
  calc
    _ ≤ (Q:ℝ)*(Q-1)/(2*N)+((Q:ℝ)*(Q+1)+R*Q)/N := hs.trans (add_le_add hcol hhit)
    _ = _ := by ring

end Probability
end Minidregg.Selvage.CommitmentFreshTrace

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.oracle_answers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.oracle_answers

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.oracleLog_eq_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.oracleLog_eq_entries

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.mem_prefixLog_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.mem_prefixLog_iff

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.mem_entries_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.mem_entries_iff

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.children_length_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.children_length_le

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.children_log_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.children_log_length_le

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.targets_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.targets_length_le

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.answerOf_of_mem_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.answerOf_of_mem_unique

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.evaluate_cachedSuite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.evaluate_cachedSuite

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.cachedSuite_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.cachedSuite_entry

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.fresh_count_le_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.fresh_count_le_calls

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.uniform_prefix_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.uniform_prefix_event_le

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.target_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.target_hit_le

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.target_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.target_sum

/-- info: 'Minidregg.Selvage.CommitmentFreshTrace.bad_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.CommitmentFreshTrace.bad_probability
