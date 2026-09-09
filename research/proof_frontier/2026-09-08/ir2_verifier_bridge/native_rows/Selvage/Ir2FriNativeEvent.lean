/- Native query-event correspondence for the concrete IR2 schedule.
Packed-root extraction remains an external input to these global Words. -/
import Selvage.Ir2FriNativeRows

namespace Minidregg.Selvage.Ir2Fri
open BabyBearExt4 Ir2FriSchedule
open scoped Classical
noncomputable section

/-- The parent row actually selected by shifting the full seventeen-bit raw query. -/
def rawParentRow (j : Fin 5) (raw : Fin (2^17)) : Index (j+1) :=
  ⟨raw.val / 2^(stage (j+1)),by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(stage (j+1)))).mpr
    rw [←pow_add]
    have hs : 17-stage (j+1)+stage (j+1) = 17 := by
      have h := stage_le (j+1)
      omega
    rw [hs]
    exact raw.isLt⟩

/-- The selected native parent coordinate is the existing coherent runtime index. -/
theorem nativeParentIndex_rawParentRow (j : Fin 5) (raw : Fin (2^17)) :
    nativeParentIndex j (rawParentRow j raw) = runtimeIndex (j+1) raw := rfl

/-- Literal native interpolation query checks on the prefix-fixed global words.
The initial equality is the native carried-input equality before the first fold. -/
def NativeQueryAccepts (s : Words) (r : Fin 5 → Ext4) (q : ℕ)
    (raw : Fin q → Fin (2^17)) : Prop :=
  (∀ a, initialMask s (sourceIndex (raw a))) ∧
  ∀ j : Fin 5, ∀ a,
    s.wordAt r (j+1) (by omega) (nativeParentIndex j (rawParentRow j (raw a))) =
      P3Barycentric.native (nativeRowNodes j (rawParentRow j (raw a)))
        (fun c => s.wordAt r j (by omega) (nativeRowSourceIndex j (rawParentRow j (raw a)) c))
        (r j)

/-- Statement-first acceptance contract for the actual native row checks. -/
def NativeQueryEventContract : Prop := ∀ (s : Words) (r : Fin 5 → Ext4) (q : ℕ)
    (raw : Fin q → Fin (2^17)),
  NativeQueryAccepts s r q raw ↔ QueryAccepts (initialMask s) (stepMasks s r) q raw

/-- Native interpolation at the raw selected parent is the model's literal block. -/
theorem native_raw_row_eq_block (s : Words) (r : Fin 5 → Ext4) (j : Fin 5)
    (raw : Fin (2^17)) :
    P3Barycentric.native (nativeRowNodes j (rawParentRow j raw))
      (fun c => s.wordAt r j (by omega) (nativeRowSourceIndex j (rawParentRow j raw) c)) (r j) =
      blockAt s j r (runtimeIndex (j+1) raw) := by
  rw [native_eq_foldStep,nativeParentIndex_rawParentRow]
  rfl

/-- Exact event equivalence: the model's fold equality is no longer an adapter premise. -/
theorem native_query_iff_counted : NativeQueryEventContract := by
  intro s r q raw
  unfold NativeQueryAccepts QueryAccepts stepMasks
  simp only [native_raw_row_eq_block,nativeParentIndex_rawParentRow]

/-- Actual global zero words provide a positive-query acceptance witness. -/
def nativeEventZeroWords : Words where
  input _ := 0
  word _ _ _ := 0

/-- The native predicate is satisfiable for arbitrary challenges and positive batch sizes. -/
theorem native_event_zero_accepts (r : Fin 5 → Ext4) (q : ℕ) (raw : Fin q → Fin (2^17)) :
    NativeQueryAccepts nativeEventZeroWords r q raw := by
  refine ⟨fun _ => rfl,?_⟩
  intro j a
  change (0:Ext4) = P3Barycentric.native (nativeRowNodes j (rawParentRow j (raw a))) (fun _ => 0) (r j)
  symm
  simpa using P3Barycentric.native_of_polynomial (nativeRowNodes j (rawParentRow j (raw a)))
    (0 : Polynomial Ext4) (by simp) (r j)

/-- Different actual input values make the required carried-input check fail. -/
def nativeEventMismatchedWords : Words where
  input _ := 1
  word _ _ _ := 0

/-- Teeth: valid zero native interpolation rows cannot erase an input mismatch. -/
theorem native_event_initial_falsifier (r : Fin 5 → Ext4) :
    ¬NativeQueryAccepts nativeEventMismatchedWords r 38 (fun _ => 0) := by
  intro h
  have hzero : (0:Ext4) = 1 := h.1 0
  exact zero_ne_one hzero

/-- Native acceptance and the event contract are inhabited at the observed 38 queries. -/
theorem native_event_premises_inhabited : ∃ (s : Words) (r : Fin 5 → Ext4)
    (raw : Fin 38 → Fin (2^17)), NativeQueryAccepts s r 38 raw ∧ NativeQueryEventContract :=
  ⟨nativeEventZeroWords,fun _ => 0,fun _ => 0,native_event_zero_accepts _ _ _,native_query_iff_counted⟩

end
end Minidregg.Selvage.Ir2Fri

/-- info: 'Minidregg.Selvage.Ir2Fri.nativeParentIndex_rawParentRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.nativeParentIndex_rawParentRow

/-- info: 'Minidregg.Selvage.Ir2Fri.native_raw_row_eq_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_raw_row_eq_block

/-- info: 'Minidregg.Selvage.Ir2Fri.native_query_iff_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_query_iff_counted

/-- info: 'Minidregg.Selvage.Ir2Fri.native_event_zero_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_event_zero_accepts

/-- info: 'Minidregg.Selvage.Ir2Fri.native_event_initial_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_event_initial_falsifier

/-- info: 'Minidregg.Selvage.Ir2Fri.native_event_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.Ir2Fri.native_event_premises_inhabited

