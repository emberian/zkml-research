/-
# Dregg2.Crypto.Deriv.PaddedAbsence — `CERTIFICATES.md` P4 (Padded Complement = Substring Absence)
and P6 Instance-Level Separation + P6∘P4 Composition.

## What is proved

1. **P4 (`CERTIFICATES.md` §2 L3 & §5 P4):**
   * `slice w i j := (w.take j).drop i` and `padded r := .cat (.star any) (.cat r (.star any))`.
   * `slice_eq_factor_iff` — `s` is a slice of `w` iff `w = u ++ s ++ v` for some `u, v`.
   * `derives_any_true` & `derives_star_any` — `any = .sym .tt` accepts every `Value` (all
     constructors, record and non-record alike), so `.star any` accepts every word.
   * `absent_iff_padded_complement` — `(∀ i j, ¬ derives (slice w i j) r = true) ↔
     derives w (.neg (.cat (.star any) (.cat r (.star any)))) = true`
     (and `absent_matches_iff_padded_complement` in `Matches` form).
   * `whole_word_complement_is_not_absence` — concrete falsifier showing `derives w (.neg r) = true`
     does NOT imply substring absence (while `.neg (padded r)` rejects `w`).
2. **P6 Instance-Level Separation (`CERTIFICATES.md` §5 P6):**
   * `dfa_bound_sound` — content-bound DFA verifier soundness.
   * `splice_verifierKernel_separation` — constructs an actual `DfaVerifierKernel` instance
     (`spliceUnboundKernel`, `extractable := True`, firing `dfa_verify_sound` on `Dfa.Reference`)
     whose `verify` ignores the record, and proves that NO `DfaBoundVerifierKernel` on
     `Dfa.Reference.idScheme` sharing that record-ignoring `verify` (with `interpret = id`) can
     inhabit `extractable`.
3. **P6∘P4 Bridge (`dfa_bound_padded_absence_or_collides`):**
   * Composes `DfaBoundVerifierKernel` + `TableDfa` + `absent_matches_iff_padded_complement`: an
     accepted content-bound proof over a `TableDfa` recognizing `derives · (.neg (padded r))` for
     `record` concludes that EITHER no slice of `record` matches `r`, OR the extracted word is a
     concrete commitment collision with `record`.
   * `dfa_bound_padded_absence_witness` jointly inhabits all premises and fires the bridge on a
     concrete `Value` word.

Pure. Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `#guard`.
-/
import Dregg2.Crypto.Deriv.Core
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Crypto.Deriv.TableDfa
import Dregg2.Crypto.Dfa
import Dregg2.Tactics

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.Dfa

/-! ## §1. P4 — Substring Absence Equals Padded Complement (`CERTIFICATES.md` §2 L3, §5 P4) -/

/-- Contiguous slice `w[i..j)` of a word of `Value` frames. -/
def slice (w : List Value) (i j : ℕ) : List Value :=
  (w.take j).drop i

/-- Padded regex `Σ* · r · Σ*`, matching any word containing a contiguous factor matching `r`. -/
def padded (r : PredRE) : PredRE :=
  .cat (.star PredRE.any) (.cat r (.star PredRE.any))

/-- **`slice_eq_factor_iff`**: `s` is a slice `slice w i j` iff `s` is a contiguous factor
`u ++ s ++ v = w`. Works for all `i, j` (including `i ≥ j`, where `slice w i j = []`). -/
theorem slice_eq_factor_iff (w s : List Value) :
    (∃ i j : ℕ, s = slice w i j) ↔ (∃ u v : List Value, u ++ s ++ v = w) := by
  constructor
  · rintro ⟨i, j, rfl⟩
    refine ⟨(w.take j).take i, w.drop j, ?_⟩
    unfold slice
    rw [List.take_append_drop, List.take_append_drop]
  · rintro ⟨u, v, huv⟩
    refine ⟨u.length, u.length + s.length, ?_⟩
    unfold slice
    rw [← huv, ← List.length_append, List.take_left, List.drop_left]

/-- `PredRE.any = .sym .tt` accepts every single `Value` (every constructor: `.int`, `.dig`,
`.sym`, `.record`). -/
theorem derives_any_true (a : Value) : derives [a] PredRE.any = true := rfl

/-- `.star PredRE.any` accepts every word `w : List Value`. -/
theorem derives_star_any (w : List Value) : derives w (.star PredRE.any) = true := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    rw [derives_star_cons]
    have hder : der a PredRE.any = .ε := rfl
    rw [hder, derives_cat]
    exact ⟨[], as, rfl, rfl, ih⟩

/-- `derives w (padded r) = true` iff some contiguous slice `slice w i j` satisfies `derives · r`. -/
theorem derives_padded_iff (w : List Value) (r : PredRE) :
    derives w (padded r) = true ↔ ∃ i j : ℕ, derives (slice w i j) r = true := by
  unfold padded
  rw [derives_cat]
  constructor
  · rintro ⟨u, w', huw', _, hrest⟩
    rw [derives_cat] at hrest
    obtain ⟨s, v, hsv, hsr, _⟩ := hrest
    have hfac : u ++ s ++ v = w := by rw [List.append_assoc, hsv, huw']
    obtain ⟨i, j, hsij⟩ := (slice_eq_factor_iff w s).mpr ⟨u, v, hfac⟩
    exact ⟨i, j, hsij ▸ hsr⟩
  · rintro ⟨i, j, hsr⟩
    obtain ⟨u, v, huv⟩ := (slice_eq_factor_iff w (slice w i j)).mp ⟨i, j, rfl⟩
    refine ⟨u, slice w i j ++ v, by simpa [List.append_assoc] using huv, derives_star_any u, ?_⟩
    rw [derives_cat]
    exact ⟨slice w i j, v, rfl, hsr, derives_star_any v⟩

/-- **`absent_iff_padded_complement` (`CERTIFICATES.md` P4)**:
`r` matches no contiguous slice of `w` iff `w` derives `¬(Σ* · r · Σ*)`. -/
theorem absent_iff_padded_complement (w : List Value) (r : PredRE) :
    (∀ i j : ℕ, ¬ derives (slice w i j) r = true) ↔
      derives w (.neg (.cat (.star PredRE.any) (.cat r (.star PredRE.any)))) = true := by
  change (∀ i j : ℕ, ¬ derives (slice w i j) r = true) ↔ derives w (.neg (padded r)) = true
  rw [derives_neg, Bool.not_eq_true', Bool.eq_false_iff]
  constructor
  · intro hall hpad
    obtain ⟨i, j, hij⟩ := (derives_padded_iff w r).mp hpad
    exact hall i j hij
  · intro hnot i j hij
    exact hnot ((derives_padded_iff w r).mpr ⟨i, j, hij⟩)

/-- **`absent_matches_iff_padded_complement`**: denotational (`Matches`) form of P4. -/
theorem absent_matches_iff_padded_complement (w : List Value) (r : PredRE) :
    (∀ i j : ℕ, ¬ Matches (slice w i j) r) ↔ derives w (.neg (padded r)) = true := by
  unfold padded
  rw [← absent_iff_padded_complement w r]
  constructor
  · intro h i j hd
    exact h i j ((PredRE.correctness (slice w i j) r).mp hd)
  · intro h i j hm
    exact h i j ((PredRE.correctness (slice w i j) r).mpr hm)

/-- **`whole_word_complement_is_not_absence` (P4 Falsifier)**:
whole-word complement `.neg r` ACCEPTS a 2-frame word `[v9, v7]` that contains a matching slice
`slice [v9, v7] 1 2 = [v7]`, whereas `.neg (padded r)` REJECTS it. -/
theorem whole_word_complement_is_not_absence :
    ∃ (w : List Value) (r : PredRE),
      derives w (.neg r) = true ∧
      (∃ i j : ℕ, derives (slice w i j) r = true) ∧
      derives w (.neg (padded r)) = false := by
  let v7 : Value := .record [("k", .sym 7)]
  let v9 : Value := .record [("k", .sym 9)]
  let w : List Value := [v9, v7]
  let r : PredRE := .sym (.symEq "k" 7)
  refine ⟨w, r, by decide, ⟨1, 2, by decide⟩, by decide⟩

/-! ## §2. P6 Strengthening — `DfaVerifierKernel` vs `DfaBoundVerifierKernel` Instance Separation -/

/-- **`dfa_bound_sound` (`CERTIFICATES.md` P6)**: content-bound DFA verifier soundness, extracting
an accepting run whose word commits to the disclosed commitment `c`. -/
theorem dfa_bound_sound {State Sym D Proof Input : Type} {S : ContentScheme Sym D}
    [K : DfaBoundVerifierKernel State Sym D S Proof Input]
    (hext : K.extractable (Input := Input)) (stmt : Input) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ w : List Sym, S.commit w = (K.interpret stmt).c ∧
      ∃ trace : List (Step State Sym),
        DfaAccepts (K.interpret stmt).δ (K.interpret stmt).q₀ (K.interpret stmt).accept trace ∧
        traceWord trace = w :=
  dfa_bound_verify_sound (K := K) hext stmt proof haccept

/-- The `Dfa.Reference` automaton packaged as a `Dfa.Statement Nat Nat`. -/
def refStatement : Dfa.Statement Nat Nat :=
  { δ := Dfa.Reference.δ, q₀ := Dfa.Reference.q₀, accept := Dfa.Reference.accept }

/-- Record-ignoring DFA verification oracle: decides whether `tr` is an accepting run of the
automaton in `stmt` and ignores any record/commitment. -/
noncomputable def spliceVerify (stmt : Dfa.Statement Nat Nat) (tr : List (Step Nat Nat)) : Bool :=
  open Classical in
  decide (DfaAccepts stmt.δ stmt.q₀ stmt.accept tr)

theorem spliceVerify_eq_true_iff (stmt : Dfa.Statement Nat Nat) (tr : List (Step Nat Nat)) :
    spliceVerify stmt tr = true ↔ DfaAccepts stmt.δ stmt.q₀ stmt.accept tr := by
  classical
  unfold spliceVerify
  exact decide_eq_true_iff

/-- Concrete unbound `DfaVerifierKernel` whose `verify` ignores the record (`extractable := True`). -/
@[instance_reducible] noncomputable def spliceUnboundKernel :
    DfaVerifierKernel Nat Nat (List (Step Nat Nat)) where
  verify := spliceVerify
  extractable := True
  extract := fun _ stmt tr h => ⟨⟨tr⟩, (spliceVerify_eq_true_iff stmt tr).mp h⟩

/-- **`splice_verifierKernel_separation` (`CERTIFICATES.md` P6 Instance-Level Falsifier)**:
1. `spliceUnboundKernel` is a genuine `DfaVerifierKernel` (`extractable := True`) whose `verify`
   accepts `Dfa.Reference.aabTrace` and fires the OLD `dfa_verify_sound`;
2. NO `DfaBoundVerifierKernel Nat Nat (List Nat) Dfa.Reference.idScheme (List (Step Nat Nat))`
   with `interpret = id` sharing that record-ignoring `verify` (`fun stmt tr => spliceVerify
   stmt.toStatement tr`) can inhabit `extractable`! -/
theorem splice_verifierKernel_separation :
    (spliceUnboundKernel.extractable ∧
      spliceUnboundKernel.verify refStatement Dfa.Reference.aabTrace = true ∧
      ∃ trace : List (Step Nat Nat),
        DfaAccepts refStatement.δ refStatement.q₀ refStatement.accept trace) ∧
    (∀ K : DfaBoundVerifierKernel Nat Nat (List Nat) Dfa.Reference.idScheme (List (Step Nat Nat)),
      K.interpret = id →
      K.verify = (fun stmt tr => spliceVerify stmt.toStatement tr) →
      ¬ K.extractable) := by
  refine ⟨?_, ?_⟩
  · have hacc : spliceUnboundKernel.verify refStatement Dfa.Reference.aabTrace = true :=
      (spliceVerify_eq_true_iff refStatement Dfa.Reference.aabTrace).mpr Dfa.Reference.aab_accepts
    exact ⟨trivial, hacc,
      dfa_verify_sound (K := spliceUnboundKernel) trivial refStatement Dfa.Reference.aabTrace hacc⟩
  · intro K hinterp hver hext
    let stmtZ : BoundStatement Nat Nat (List Nat) :=
      { toStatement := refStatement, c := [0x7a] }
    have hacc : K.verify stmtZ Dfa.Reference.aabTrace = true := by
      rw [hver]
      exact (spliceVerify_eq_true_iff refStatement Dfa.Reference.aabTrace).mpr
        Dfa.Reference.aab_accepts
    obtain ⟨circuit, hsat, hcomm⟩ := K.extract hext stmtZ Dfa.Reference.aabTrace hacc
    rw [hinterp] at hsat hcomm
    have hsep := Dfa.Reference.splice_fails_bound_of_sep Dfa.Reference.idScheme [0x7a] (by
      intro tr htr hc
      obtain ⟨_, _, _, _, _, _, hvalid, _⟩ := htr
      have hw : traceWord tr = [0x7a] := hc
      cases tr with
      | nil => simp at hw
      | cons s rest =>
        simp only [traceWord_cons, List.cons.injEq] at hw
        have hv := hvalid s List.mem_cons_self
        unfold stepValid Dfa.Reference.δ at hv
        rw [hw.1] at hv
        rcases hv with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega)
    exact hsep.2 ⟨circuit, hsat, hcomm⟩

/-! ## §3. P6∘P4 Bridge — Content-Bound `TableDfa` Proof Implies Substring Absence or Collision -/

/-- Helper: threading `td.runState` across a valid, chained trace recovers `last.next`. -/
private theorem tableDfa_runState_of_trace {State Sym : Type} (td : TableDfa State Sym) :
    ∀ (trace : List (Step State Sym)) (first last : Step State Sym),
      trace.head? = some first →
      trace.getLast? = some last →
      (∀ s ∈ trace, stepValid td.δ s) →
      chained trace →
      td.runState first.state (traceWord trace) = last.next
  | [], _, _, hhead, _, _, _ => by simp at hhead
  | [s], first, last, hhead, hlast, hvalid, _ => by
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hhead; subst hlast
      have hv : s.next = td.step s.state s.sym := hvalid s List.mem_cons_self
      simp [TableDfa.runState, traceWord, hv]
  | s₁ :: s₂ :: rest, first, last, hhead, hlast, hvalid, hch => by
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      have hv₁ : s₁.next = td.step s₁.state s₁.sym := hvalid s₁ List.mem_cons_self
      have hlink : s₂.state = s₁.next := hch.1
      have hch' : chained (s₂ :: rest) := hch.2
      have hlast' : (s₂ :: rest).getLast? = some last := by
        simpa [List.getLast?_cons_cons] using hlast
      have hvalid' : ∀ s ∈ s₂ :: rest, stepValid td.δ s :=
        fun s hs => hvalid s (List.mem_cons_of_mem _ hs)
      have ih := tableDfa_runState_of_trace td (s₂ :: rest) s₂ last rfl hlast' hvalid' hch'
      simp only [traceWord_cons, TableDfa.runState]
      rw [← hv₁, ← hlink]
      exact ih

/-- Any `DfaAccepts` run of a `TableDfa`'s deterministic transition relation `td.δ` certifies
`td.accepts (traceWord trace)`. -/
theorem dfaAccepts_tableDfa_imp_accepts {State Sym : Type} (td : TableDfa State Sym)
    (trace : List (Step State Sym))
    (h : DfaAccepts td.δ td.start td.accept trace) :
    td.accepts (traceWord trace) := by
  obtain ⟨first, last, hhead, hlast, hstart, hacc, hvalid, hch⟩ := h
  unfold TableDfa.accepts
  rw [← hstart, tableDfa_runState_of_trace td trace first last hhead hlast hvalid hch]
  exact hacc

/-- **`dfa_bound_padded_absence_or_collides` (P6∘P4 Composition)**:
Given an accepted `DfaBoundVerifierKernel` proof for a `TableDfa` `td` recognizing
`derives · (.neg (padded r))` and a `record : List Value` committing to the disclosed `c`,
EITHER no contiguous slice of `record` matches `r` (`∀ i j, ¬ Matches (slice record i j) r`),
OR there exists a distinct word `w' ≠ record` colliding with `record` under `S.commit`. -/
theorem dfa_bound_padded_absence_or_collides
    {State D Proof Input : Type} {S : ContentScheme Value D}
    [K : DfaBoundVerifierKernel State Value D S Proof Input]
    (hext : K.extractable (Input := Input))
    (td : TableDfa State Value) (r : PredRE)
    (hagree : ∀ w : List Value, td.accepts w ↔ derives w (.neg (padded r)) = true)
    (stmt : Input) (proof : Proof)
    (haccept : K.verify stmt proof = true)
    (hδ : (K.interpret stmt).δ = td.δ)
    (hq₀ : (K.interpret stmt).q₀ = td.start)
    (hacc : (K.interpret stmt).accept = td.accept)
    (record : List Value) (hrec : S.commit record = (K.interpret stmt).c) :
    (∀ i j : ℕ, ¬ Matches (slice record i j) r) ∨
      (∃ w' : List Value, w' ≠ record ∧ S.commit w' = S.commit record) := by
  obtain ⟨trace, htr, hcase⟩ :=
    dfa_bound_identifies_record_or_collides (K := K) hext stmt proof haccept record hrec
  rcases hcase with hword | ⟨hne, hcoll⟩
  · left
    rw [hδ, hq₀, hacc] at htr
    have htd : td.accepts (traceWord trace) := dfaAccepts_tableDfa_imp_accepts td trace htr
    rw [hword] at htd
    exact (absent_matches_iff_padded_complement record r).mpr ((hagree record).mp htd)
  · right
    exact ⟨traceWord trace, hne, hcoll⟩

/-! ### Non-Vacuity Witness Firing ALL Premises of `dfa_bound_padded_absence_or_collides` -/

/-- Canonical derivative `TableDfa` for any `PredRE`. -/
def derTableDfa (R : PredRE) : TableDfa PredRE Value :=
  { step := fun s a => der a s, start := R, accept := fun s => null s = true }

private theorem derTableDfa_runState_null (R : PredRE) :
    ∀ (q : PredRE) (w : List Value), null ((derTableDfa R).runState q w) = derives w q
  | _, [] => rfl
  | q, a :: as => derTableDfa_runState_null R (der a q) as

theorem derTableDfa_accepts_iff (R : PredRE) (w : List Value) :
    (derTableDfa R).accepts w ↔ derives w R = true := by
  unfold TableDfa.accepts derTableDfa
  exact Eq.congr_left (derTableDfa_runState_null R R w)

/-- Identity content scheme over `List Value`. -/
def valueIdScheme : ContentScheme Value (List Value) := ⟨id⟩

/-- Reference bound verifier kernel over `Value` with identity commitment. -/
@[instance_reducible] noncomputable def valueBoundRefKernel :
    DfaBoundVerifierKernel PredRE Value (List Value) valueIdScheme (List (Step PredRE Value)) where
  interpret := id
  verify := fun stmt tr =>
    open Classical in
    decide (DfaAccepts stmt.δ stmt.q₀ stmt.accept tr ∧ traceWord tr = stmt.c)
  extractable := True
  extract := by
    classical
    intro _ stmt tr h
    have ⟨hacc, hw⟩ := of_decide_eq_true h
    exact ⟨⟨tr⟩, hacc, hw⟩

private theorem runTrace_traceWord {State Sym : Type} (td : TableDfa State Sym) :
    ∀ (q : State) (w : List Sym), traceWord (td.runTrace q w) = w
  | _, [] => rfl
  | q, a :: as => by
      simp only [TableDfa.runTrace, traceWord_cons, runTrace_traceWord td (td.step q a) as]

/-- **Non-vacuity witness (`dfa_bound_padded_absence_witness`)**:
jointly inhabits ALL premises of `dfa_bound_padded_absence_or_collides` on the concrete record
`[v9, v9]` and forbidden pattern `.sym (.symEq "k" 7)`, firing the theorem to conclude that
no contiguous slice of `[v9, v9]` matches `.sym (.symEq "k" 7)`. -/
theorem dfa_bound_padded_absence_witness :
    let v9 : Value := .record [("k", .sym 9)]
    let r : PredRE := .sym (.symEq "k" 7)
    let record : List Value := [v9, v9]
    ∀ i j : ℕ, ¬ Matches (slice record i j) r := by
  classical
  let v9 : Value := .record [("k", .sym 9)]
  let r : PredRE := .sym (.symEq "k" 7)
  let record : List Value := [v9, v9]
  let td : TableDfa PredRE Value := derTableDfa (.neg (padded r))
  let stmt : BoundStatement PredRE Value (List Value) :=
    { δ := td.δ, q₀ := td.start, accept := td.accept, c := record }
  let proof : List (Step PredRE Value) := td.runTrace td.start record
  have hder : derives record (.neg (padded r)) = true := by decide
  have htd_acc : td.accepts record := (derTableDfa_accepts_iff (.neg (padded r)) record).mpr hder
  have hdfa : DfaAccepts td.δ td.start td.accept proof :=
    (TableDfa.tableRun_dfaAccepts td v9 [v9]).mpr htd_acc
  have hword : traceWord proof = record := runTrace_traceWord td td.start record
  have hverify : valueBoundRefKernel.verify stmt proof = true := by
    unfold valueBoundRefKernel
    exact decide_eq_true ⟨hdfa, hword⟩
  rcases dfa_bound_padded_absence_or_collides (K := valueBoundRefKernel) trivial td r
      (derTableDfa_accepts_iff (.neg (padded r))) stmt proof hverify rfl rfl rfl record rfl with
      habs | ⟨w', hne, hcoll⟩
  · exact habs
  · exact False.elim (hne hcoll)

/-! ## §4. Axiom Hygiene (`#assert_all_clean` + `#guard_msgs in #print axioms`) -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.slice_eq_factor_iff,
  Dregg2.Crypto.Deriv.derives_any_true,
  Dregg2.Crypto.Deriv.derives_star_any,
  Dregg2.Crypto.Deriv.derives_padded_iff,
  Dregg2.Crypto.Deriv.absent_iff_padded_complement,
  Dregg2.Crypto.Deriv.absent_matches_iff_padded_complement,
  Dregg2.Crypto.Deriv.whole_word_complement_is_not_absence,
  Dregg2.Crypto.Deriv.dfa_bound_sound,
  Dregg2.Crypto.Deriv.splice_verifierKernel_separation,
  Dregg2.Crypto.Deriv.dfaAccepts_tableDfa_imp_accepts,
  Dregg2.Crypto.Deriv.dfa_bound_padded_absence_or_collides,
  Dregg2.Crypto.Deriv.dfa_bound_padded_absence_witness
]

/-- info: 'Dregg2.Crypto.Deriv.slice_eq_factor_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms slice_eq_factor_iff
/-- info: 'Dregg2.Crypto.Deriv.derives_any_true' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms derives_any_true
/-- info: 'Dregg2.Crypto.Deriv.derives_star_any' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms derives_star_any
/-- info: 'Dregg2.Crypto.Deriv.absent_iff_padded_complement' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms absent_iff_padded_complement
/-- info: 'Dregg2.Crypto.Deriv.absent_matches_iff_padded_complement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_matches_iff_padded_complement
/-- info: 'Dregg2.Crypto.Deriv.whole_word_complement_is_not_absence' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms whole_word_complement_is_not_absence
/-- info: 'Dregg2.Crypto.Deriv.dfa_bound_sound' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms dfa_bound_sound
/-- info: 'Dregg2.Crypto.Deriv.splice_verifierKernel_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms splice_verifierKernel_separation
/-- info: 'Dregg2.Crypto.Deriv.dfa_bound_padded_absence_or_collides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dfa_bound_padded_absence_or_collides
/-- info: 'Dregg2.Crypto.Deriv.dfa_bound_padded_absence_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dfa_bound_padded_absence_witness

end Dregg2.Crypto.Deriv
