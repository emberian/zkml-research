/-
# Selvage.OracleLogSatisfiable — bounded satisfiability witnesses for the original
oracle-log obligations

`OracleLogProgram` and `adaptiveIncrement_sound_via_log` are false at the
intended `accRbrError` price on the landed F₅ instance
(`oracleLogProgram_accRbrError_false` and `adaptiveViaLog_accRbrError_false`).
This module does not weaken or bypass those negative results.  It closes only
the separate ATLAS satisfiability question: both proposition shapes do have
inhabitants at the universal slack price `ε = 1`.

The witnesses deliberately claim no deployment-grade soundness.  Their content
is structural: the program event is a probability and hence at most one; the
shifted reduction has `k = ch.length + 1`, so its `(tq + k) * 1` budget is at
least one; and the reduction's extractor is exactly the stated log extractor.
-/
import Selvage.OracleLogProgram

namespace Minidregg.Selvage

/-! ## The per-slot proposition is satisfiable at the universal bound -/

section Program

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m)

/-- The original per-slot proposition has an inhabitant at `εslot = 1`.
This is the sharp universal probability bound, not the refuted
`accRbrError`-priced claim. -/
theorem oracleLogProgram_one :
    OracleLogProgram C foldRoot ch hm hch δs hδpos hδone S dom d q
      (fun _ => 1) := by
  intro s tq P i j δ hδ
  exact uniformProb_le_one _

end Program

/-! ## The extraction proposition is satisfiable at the universal bound -/

section Extraction

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m)

/-- An `OracleLogReduction` whose extractor is exactly the shifted log
extractor and whose per-slot price is the universal bound one.  Since the
shifted reduction has at least one round, every soundness event fits inside
the resulting `(tq + k) * 1` budget. -/
noncomputable def shiftedOracleLogReduction_one :
    OracleLogReduction
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q)
      Set.univ (fun _ => 1) where
  extractLog := shiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S
    dom d q
  sound_log := by
    intro s tq δ hδ P
    refine (uniformProb_le_one _).trans ?_
    change 1 ≤ ((tq : ℝ) + ((ch.length + 1 : ℕ) : ℝ)) * 1
    norm_num only [mul_one, Nat.cast_add, Nat.cast_one]
    have htq : 0 ≤ (tq : ℝ) := Nat.cast_nonneg tq
    have hlen : 0 ≤ (ch.length : ℝ) := Nat.cast_nonneg ch.length
    linarith

/-- The original extraction proposition has an inhabitant at `εlog = 1`,
with its extractor-pinning clause satisfied definitionally.  This establishes
satisfiability only; the intended `accRbrError` instance remains refuted. -/
theorem adaptiveIncrement_sound_via_log_one :
    adaptiveIncrement_sound_via_log C foldRoot ch hm hch δs hδpos hδone S
      dom d q (fun _ => 1) := by
  refine ⟨shiftedOracleLogReduction_one C foldRoot ch hm hch δs hδpos hδone S
    dom d q, ?_⟩
  intro s o L i w h
  change (logIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q o L i).getD 0 = w
  rw [h]
  rfl

end Extraction

end Minidregg.Selvage
