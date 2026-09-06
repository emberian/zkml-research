/-
Statement-first: one descriptor, arbitrary root-carried public contexts, and one
global state-restoration ROM. A false accepted full-word receipt after t queries
has price (t+(m+1))*gatePrice d m for delta in (0,1/n), where n is
the public word width used by the existing gateReduction. The local realizer
is the existing gateRbr at the context already carried by the queried root.

The query-complete multi-output theorem below uses that SAME generic reduction.
No descriptor-specific reduction is copied for EMA. Fixed-context query and
verification transport is explicit. Full words are public; no hiding, QROM,
runtime publication schedule, or concrete hash realization is claimed.

ATLAS: the adapter supplies an actual changed-state EMA receipt satisfying all
premises, a complete nine-query sampled transcript, and failed-premise siblings.
The generic empty-log theorem makes query completeness load-bearing.
-/
import Compiler.CommittedTerminalFiatShamir
import Mathlib.Logic.Equiv.Fin.Basic

namespace Minidregg.Compiler.ContextualGate

open Minidregg.Selvage
open Minidregg.Compiler.CommittedTerminalFiatShamir
open Minidregg.Compiler.CommittedTerminalRealizer
open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

variable {C : Type} [DecidableEq C]

def commit (c : C) {n : Nat} (w : Fin n → BabyBear) : C × (Fin n → BabyBear) := (c,w)

noncomputable def contextReduction (base : C) (d : ConstraintDescriptor BabyBear)
    (m : Nat) {n : Nat} (hn : 0 < n) : Reduction :=
  { gateReduction (commit base) d (bitCorner m) hn with
    R := fun _ rt w _ => commit rt.1 w = rt ∧ descriptorHolds d (traceOf w)
    verify := fun _ rt w πs ρs => gateVerify (commit rt.1) d (bitCorner m) rt w πs ρs }

variable {base : C} {d : ConstraintDescriptor BabyBear} {m n : Nat} {hn : 0 < n}
local notation "R" => contextReduction base d m hn

private noncomputable def encFor
    (fit : d.gates.length + d.zeros.length ≤ 2^m) (wv : Nat → BabyBear) :=
  residualEmbedding d wv fit

private noncomputable def localRbr
    (fit : d.gates.length + d.zeros.length ≤ 2^m) (c : C) :
    RbrKnowledgeSoundness (gateReduction (commit c) d (bitCorner m) hn) :=
  gateRbr (commit c) d (bitCorner m) (encFor fit) (fun _ _ => rfl) hn

private def localStmt (st : Stmt R) :
    Stmt (gateReduction (commit st.x.1) d (bitCorner m) hn) :=
  ⟨st.idx, st.x, st.y⟩

private noncomputable def contextKState
    (fit : d.gates.length + d.zeros.length ≤ 2^m) : KStateFn R where
  state := fun δ st tr w => (localRbr fit st.x.1).kstate.state δ (localStmt st) tr w
  empty_iff := by
    intro δ hδ st w
    exact (localRbr fit st.x.1).kstate.empty_iff δ hδ (localStmt st) w
  prover_monotone := by
    intro δ hδ st rs w hlen h π
    exact (localRbr fit st.x.1).kstate.prover_monotone δ hδ (localStmt st) rs w hlen h π
  full_iff := by
    intro δ hδ st πs ρs w
    exact (localRbr fit st.x.1).kstate.full_iff δ hδ (localStmt st) πs ρs w

noncomputable def contextRbr (fit : d.gates.length + d.zeros.length ≤ 2^m) :
    RbrKnowledgeSoundness R where
  kstate := contextKState fit
  extract := fun _ _ w => w
  err := fun i _ _ => gateErr d i
  extractTime := fun _ => 0
  extract_sound := by
    intro δ hδ st i rs hlen π
    exact (localRbr fit st.x.1).extract_sound δ hδ (localStmt st) i rs hlen π

theorem context_receipt_sound (fit : d.gates.length + d.zeros.length ≤ 2^m) :
    FsStraightlineKnowledgeSoundness R Set.univ
      (fun _s t _δ => ((t : ℝ) + ((m+1 : Nat) : ℝ)) * gatePrice d m) :=
  fsKeystone_proved.sound R (contextRbr fit) Set.univ
    (fun _ => gatePrice d m) (fun _ _ => gatePrice_nonneg d)
    (fun i _ _ _ _ => gateErr_le_gatePrice d i)

def toFixed (c : C) (q : SrMove R 0) :
    SrMove (gateReduction (commit c) d (bitCorner m) hn) 0 :=
  ⟨⟨q.stmt.idx, q.stmt.x, q.stmt.y⟩, q.pfx⟩

def fromFixed (c : C) (q : SrMove (gateReduction (commit c) d (bitCorner m) hn) 0) :
    SrMove R 0 := ⟨⟨q.stmt.idx, q.stmt.x, q.stmt.y⟩, q.pfx⟩

theorem fixed_query_roundtrip (c : C)
    (q : SrMove (gateReduction (commit c) d (bitCorner m) hn) 0) :
    toFixed c (fromFixed (base:=base) c q) = q := by cases q; rfl

theorem context_query_roundtrip (c : C) (q : SrMove R 0) :
    fromFixed c (toFixed c q) = q := by cases q; rfl

def queryBytes (rootBytes : C × (Fin n → BabyBear) → List UInt8)
    (q : SrMove R 0) : List UInt8 :=
  encodeMove (commit base) d (bitCorner m) hn rootBytes (toFixed base q)

theorem query_bytes_match_fixed_encoder
    (rootBytes : C × (Fin n → BabyBear) → List UInt8)
    (c : C) (q : SrMove R 0) :
    queryBytes rootBytes q =
      encodeMove (commit c) d (bitCorner m) hn rootBytes (toFixed c q) := rfl

theorem query_bytes_injective
    (rootBytes : C × (Fin n → BabyBear) → List UInt8)
    (hroot : Function.Injective rootBytes) : Function.Injective (queryBytes (base:=base) (d:=d) (m:=m) (hn:=hn) rootBytes) := by
  intro a b h
  have he := encodeMove_injective (commit base) d (bitCorner m) hn rootBytes hroot h
  have hr := congrArg (fromFixed (base:=base) base) he
  simpa only [context_query_roundtrip] using hr

def output (rc : FsReceipt (C × (Fin n → BabyBear)) n m) : SrOutput R 0 :=
  ⟨⟨(), rc.root, rc.word⟩, rc.messages, fun _ => fun z => Fin.elim0 z, ()⟩

theorem fixed_acceptance_transport (c : C) (O : SrMove R 0 → Ext6L)
    (rc : FsReceipt (C × (Fin n → BabyBear)) n m)
    (hc : rc.root.1 = c)
    (hf : fiatShamir (gateReduction (commit c) d (bitCorner m) hn) 0
      (fun q => O (fromFixed c q)) (rc.output (commit c) d (bitCorner m) hn) =
      some ((), fun _ => ())) :
    fiatShamir R 0 O (output rc) = some ((), fun _ => ()) := by
  unfold fiatShamir at hf ⊢
  change gateVerify (commit rc.root.1) d (bitCorner m) rc.root rc.word
    rc.messages (fun i => O ((output rc).query i)) = _
  rw [hc]
  exact hf

theorem sound_reading (fit : d.gates.length + d.zeros.length ≤ 2^m)
    (s t : Nat) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (P : SrProver R s) :
    uniformProb ((Fin t → (R).Chal) × (Fin (R).k → (R).Chal))
      (fun coins =>
        let o := P.out ((srTrace P coins.1).map Prod.snd)
        ¬ (R).R o.stmt.idx o.stmt.x o.stmt.y () ∧
          fiatShamir R s (fsOracle o (srFinalChal P coins.1 coins.2)) o ≠ none) ≤
      ((t : ℝ) + ((m+1 : Nat) : ℝ)) * gatePrice d m := by
  obtain ⟨E, hE⟩ := context_receipt_sound (base:=base) (hn:=hn) fit
  refine le_trans (le_of_eq (uniformProb_congr fun coins => ?_)) (hE s t δ hδ P)
  dsimp only
  constructor
  · rintro ⟨hfalse, hacc⟩
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hacc
    refine ⟨Set.mem_univ _, ?_, v.1, v.2, hv, ?_⟩
    · intro hrel
      exact hfalse ((relaxedMem_iff hn (R).R hδ _ _ _).mp hrel)
    · exact ⟨v.2, trivial, by rw [fracHamming_self]; exact le_of_lt hδ.1⟩
  · rintro ⟨-, hrel, x', y', hv, -⟩
    refine ⟨?_, ?_⟩
    · intro hR
      exact hrel ((relaxedMem_iff hn (R).R hδ _ _ _).mpr hR)
    · rw [hv]
      exact Option.some_ne_none _

/-! Query-complete collection over the same generic reduction. All prover and
verifier oracle queries are included in t; final-log completeness does not
assert before-publication runtime ordering. The selector is query-bounded,
with no computation-time or private-witness extraction claim. -/

abbrev Moves := List (R).Chal → SrMove R 0
abbrev Outputs (M : Nat) := Fin M → List (R).Chal → SrOutput R 0

def withOutput (P : SrProver R 0) (f : List (R).Chal → SrOutput R 0) : SrProver R 0 :=
  { P with out := f }

theorem output_change_preserves_log {t : Nat} (P : SrProver R 0)
    (f : List (R).Chal → SrOutput R 0) (coins : Fin t → (R).Chal) :
    srTrace (withOutput P f) coins = srTrace P coins := rfl

/-- The application has already performed every verification query in the
same transcript, including the final-prefix checks of every published output. -/
def AllOutputQueriesLogged {M : Nat} (t : Nat) (P : SrProver R 0)
    (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M) : Prop :=
  ∀ (coins : Fin t → (R).Chal) (j : Fin M) (i : Fin (R).k),
    ∃ e ∈ srTrace P coins, e.1 = (outputs j ((srTrace P coins).map Prod.snd)).query i

noncomputable def loggedOracle {t : Nat} (P : SrProver R 0)
    (coins : Fin t → (R).Chal) (q : SrMove R 0) : (R).Chal := by
  classical
  exact ((srTrace P coins).find? (fun e => decide (e.1 = q))).map Prod.snd |>.getD ext6Zero

theorem final_challenge_is_logged {M t : Nat} (P : SrProver R 0) (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M)
    (closed : AllOutputQueriesLogged t P outputs) (coins : Fin t → (R).Chal)
    (fallback : Fin (R).k → (R).Chal) (j : Fin M) (i : Fin (R).k) :
    srFinalChal (withOutput P (outputs j)) coins fallback i =
      loggedOracle P coins ((outputs j ((srTrace P coins).map Prod.snd)).query i) := by
  classical
  obtain ⟨e, he, hq⟩ := closed coins j i
  have hn : (srTrace P coins).find?
      (fun e => decide (e.1 = (outputs j ((srTrace P coins).map Prod.snd)).query i)) ≠ none := by
    intro hnone
    have hx := (List.find?_eq_none.mp hnone) e he
    exact hx (by simpa using hq)
  obtain ⟨entry, hentry⟩ := Option.ne_none_iff_exists'.mp hn
  unfold srFinalChal
  rw [output_change_preserves_log]
  dsimp only [withOutput]
  rw [hentry]
  simp only [loggedOracle, hentry, Option.map_some, Option.getD_some]

def BadLoggedOutput {t : Nat} (P : SrProver R 0) (f : List (R).Chal → SrOutput R 0)
    (coins : Fin t → (R).Chal) : Prop :=
  let o := f ((srTrace P coins).map Prod.snd)
  ¬ (R).R o.stmt.idx o.stmt.x o.stmt.y () ∧
    fiatShamir R 0 (loggedOracle P coins) o ≠ none

/-- Extra final coins are unused in this query-complete experiment. Keeping
them in the sample type permits direct comparison to the existing ROM game. -/
theorem one_logged_output_bound (fit : d.gates.length + d.zeros.length ≤ 2^m)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ))) {M t : Nat} (P : SrProver R 0) (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M)
    (closed : AllOutputQueriesLogged t P outputs) (j : Fin M) :
    uniformProb ((Fin t → (R).Chal) × (Fin (R).k → (R).Chal))
      (fun coins => BadLoggedOutput P (outputs j) coins.1) ≤
      ((t : ℝ) + ((m+1 : Nat) : ℝ)) * gatePrice d m := by
  have hb := sound_reading fit 0 t hδ (withOutput P (outputs j))
  refine le_trans (le_of_eq (uniformProb_congr fun coins => ?_)) hb
  let o := outputs j ((srTrace P coins.1).map Prod.snd)
  have hc : srFinalChal (withOutput P (outputs j)) coins.1 coins.2 =
      fun i => loggedOracle P coins.1 (o.query i) :=
    funext (fun i => final_challenge_is_logged P outputs closed coins.1 coins.2 j i)
  have hv : fiatShamir R 0
      (fsOracle o (srFinalChal (withOutput P (outputs j)) coins.1 coins.2)) o =
      fiatShamir R 0 (loggedOracle P coins.1) o := by
    rw [fiatShamir_fsOracle]
    unfold fiatShamir
    rw [hc]
  change (¬ (R).R o.stmt.idx o.stmt.x o.stmt.y () ∧
    fiatShamir R 0 (loggedOracle P coins.1) o ≠ none) ↔
    (¬ (R).R o.stmt.idx o.stmt.x o.stmt.y () ∧
      fiatShamir R 0
        (fsOracle o (srFinalChal (withOutput P (outputs j)) coins.1 coins.2)) o ≠ none)
  rw [hv]

def rebuildLog (P : SrProver R 0) (responses : List (R).Chal) : List (SrMove R 0 × (R).Chal) :=
  responses.foldl (fun log ρ => log ++ [(P.move (log.map Prod.snd), ρ)]) []

theorem rebuild_append (P : SrProver R 0) (responses : List (R).Chal) (ρ : (R).Chal) :
    rebuildLog P (responses ++ [ρ]) =
      rebuildLog P responses ++ [(P.move ((rebuildLog P responses).map Prod.snd), ρ)] := by
  simp only [rebuildLog, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rebuild_actual_log {t : Nat} (P : SrProver R 0) (coins : Fin t → (R).Chal) :
    rebuildLog P ((srTrace P coins).map Prod.snd) = srTrace P coins := by
  have hi : ∀ (cs : List (R).Chal) (log : List (SrMove R 0 × (R).Chal)),
      rebuildLog P (log.map Prod.snd) = log →
      rebuildLog P ((runFrom P log cs).map Prod.snd) = runFrom P log cs := by
    intro cs
    induction cs with
    | nil => intro log h; exact h
    | cons ρ cs ih =>
      intro log h
      rw [runFrom_cons]
      apply ih
      simp only [stepOnce, List.map_append, List.map_cons, List.map_nil, rebuild_append, h]
  rw [srTrace_eq_runFrom]
  exact hi (List.ofFn coins) [] rfl

noncomputable def responseOracle (P : SrProver R 0)
    (responses : List (R).Chal) (q : SrMove R 0) : (R).Chal := by
  classical
  exact ((rebuildLog P responses).find? (fun e => decide (e.1 = q))).map Prod.snd |>.getD ext6Zero

theorem response_oracle_matches {t : Nat} (P : SrProver R 0) (coins : Fin t → (R).Chal) :
    responseOracle P ((srTrace P coins).map Prod.snd) = loggedOracle P coins := by
  funext q
  simp only [responseOracle, rebuild_actual_log, loggedOracle]

def ResponseBad (P : SrProver R 0) (f : List (R).Chal → SrOutput R 0)
    (responses : List (R).Chal) : Prop :=
  let o := f responses
  ¬ (R).R o.stmt.idx o.stmt.x o.stmt.y () ∧
    fiatShamir R 0 (responseOracle P responses) o ≠ none

theorem response_bad_matches {t : Nat} (P : SrProver R 0)
    (f : List (R).Chal → SrOutput R 0) (coins : Fin t → (R).Chal) :
    ResponseBad P f ((srTrace P coins).map Prod.snd) ↔ BadLoggedOutput P f coins := by
  simp only [ResponseBad, BadLoggedOutput, response_oracle_matches]

noncomputable def selectedIndex {M : Nat} (hM : 0 < M) (P : SrProver R 0)
    (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M) (responses : List (R).Chal) : Fin M := by
  classical
  exact if h : ∃ j, ResponseBad P (outputs j) responses then Classical.choose h else ⟨0, hM⟩

theorem selected_index_bad {M : Nat} (hM : 0 < M) (P : SrProver R 0)
    (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M) (responses : List (R).Chal)
    (h : ∃ j, ResponseBad P (outputs j) responses) :
    ResponseBad P (outputs (selectedIndex hM P outputs responses)) responses := by
  classical
  simpa only [selectedIndex, dif_pos h] using Classical.choose_spec h

noncomputable def selectedOutput {M : Nat} (hM : 0 < M) (P : SrProver R 0)
    (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M) (responses : List (R).Chal) : SrOutput R 0 :=
  outputs (selectedIndex hM P outputs responses) responses

theorem selection_queries_still_logged {M t : Nat} (hM : 0 < M) (P : SrProver R 0)
    (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M) (closed : AllOutputQueriesLogged t P outputs) :
    AllOutputQueriesLogged t P (fun _j : Fin 1 => selectedOutput hM P outputs) := by
  intro coins _j i
  exact closed coins (selectedIndex hM P outputs ((srTrace P coins).map Prod.snd)) i

theorem any_bad_selects_bad {M t : Nat} (hM : 0 < M) (P : SrProver R 0)
    (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M) (coins : Fin t → (R).Chal)
    (bad : ∃ j, BadLoggedOutput P (outputs j) coins) :
    BadLoggedOutput P (selectedOutput hM P outputs) coins := by
  obtain ⟨j, hj⟩ := bad
  have hresponse : ∃ j, ResponseBad P (outputs j) ((srTrace P coins).map Prod.snd) :=
    ⟨j, (response_bad_matches P (outputs j) coins).mpr hj⟩
  have hs := selected_index_bad hM P outputs ((srTrace P coins).map Prod.snd) hresponse
  change ResponseBad P (selectedOutput hM P outputs) ((srTrace P coins).map Prod.snd) at hs
  exact (response_bad_matches P (selectedOutput hM P outputs) coins).mp hs

theorem all_logged_outputs_bound (fit : d.gates.length + d.zeros.length ≤ 2^m)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ))) {M t : Nat} (hM : 0 < M) (P : SrProver R 0)
    (outputs : Outputs (base:=base) (d:=d) (m:=m) (hn:=hn) M) (closed : AllOutputQueriesLogged t P outputs) :
    uniformProb ((Fin t → (R).Chal) × (Fin (R).k → (R).Chal))
      (fun coins => ∃ j : Fin M, BadLoggedOutput P (outputs j) coins.1) ≤
      ((t : ℝ) + ((m+1 : Nat) : ℝ)) * gatePrice d m := by
  refine le_trans (uniformProb_mono (fun coins h => any_bad_selects_bad hM P outputs coins.1 h))
    (one_logged_output_bound fit hδ P (fun _j : Fin 1 => selectedOutput hM P outputs)
      (selection_queries_still_logged hM P outputs closed) 0)

theorem trace_entry_query {t : Nat} (P : SrProver R 0) (coins : Fin t → (R).Chal)
    (j : Fin t) :
    ((srTrace P coins)[j.val]'(by rw [srTrace_length]; exact j.isLt)).1 =
      P.move (((srTrace P coins).take j.val).map Prod.snd) := by
  have hidx : (List.finRange t).take (j.val + 1) = (List.finRange t).take j.val ++ [j] := by
    rw [List.take_succ_eq_append_getElem (by simp)]
    simp
  have hf := srTrace_take P coins (Nat.succ_le_of_lt j.isLt)
  rw [hidx, List.foldl_append, List.foldl_cons, List.foldl_nil,
    ← srTrace_take P coins (Nat.le_of_lt j.isLt)] at hf
  rw [List.take_succ_eq_append_getElem (by rw [srTrace_length]; exact j.isLt), stepFn_eq] at hf
  have he := List.singleton_inj.mp (List.append_cancel_left hf)
  exact congrArg Prod.fst he

def plannedVerifier {t : Nat} (ht : 0 < t) (queries : Fin t → SrMove R 0)
    (out : SrOutput R 0) : SrProver R 0 where
  move := fun responses => queries ⟨responses.length % t, Nat.mod_lt _ ht⟩
  out := fun _ => out

theorem planned_entry_query {t : Nat} (ht : 0 < t) (queries : Fin t → SrMove R 0)
    (out : SrOutput R 0) (coins : Fin t → (R).Chal) (j : Fin t) :
    ((srTrace (plannedVerifier ht queries out) coins)[j.val]'
      (by rw [srTrace_length]; exact j.isLt)).1 = queries j := by
  rw [trace_entry_query]
  simp only [plannedVerifier, List.length_map, List.length_take, srTrace_length,
    Nat.min_eq_left (Nat.le_of_lt j.isLt), Nat.mod_eq_of_lt j.isLt]

noncomputable def verificationQueries {M : Nat} (outputs : Fin M → SrOutput R 0) :
    Fin (M * (R).k) → SrMove R 0 := fun z =>
  let ji : Fin M × Fin (R).k := finProdFinEquiv.symm z
  (outputs ji.1).query ji.2

noncomputable def completeVerifier {M : Nat} (hM : 0 < M) (outputs : Fin M → SrOutput R 0) :
    SrProver R 0 :=
  plannedVerifier (Nat.mul_pos hM (R).k_pos) (verificationQueries outputs) (outputs ⟨0, hM⟩)

theorem planned_verifier_logs_all {M : Nat} (hM : 0 < M)
    (outputs : Fin M → SrOutput R 0) :
    AllOutputQueriesLogged (M * (R).k) (completeVerifier hM outputs) (fun j _ => outputs j) := by
  intro coins j i
  let z : Fin (M * (R).k) := finProdFinEquiv (j, i)
  let entry := (srTrace (completeVerifier hM outputs) coins)[z.val]'
    (by rw [srTrace_length]; exact z.isLt)
  refine ⟨entry, List.getElem_mem _, ?_⟩
  have he := planned_entry_query (Nat.mul_pos hM (R).k_pos)
    (verificationQueries outputs) (outputs ⟨0, hM⟩) coins z
  simpa only [verificationQueries, z, Equiv.symm_apply_apply] using he

theorem empty_log_not_complete (P : SrProver R 0) (out : SrOutput R 0) :
    ¬ AllOutputQueriesLogged 0 P (fun _j : Fin 1 => fun _ => out) := by
  intro h
  obtain ⟨e, he, _⟩ := h (fun z => Fin.elim0 z) 0 ⟨0, (R).k_pos⟩
  simp [srTrace] at he

theorem zero_sampled_trace_values {t : Nat} (P : SrProver R 0) :
    ∀ e ∈ srTrace P (fun _ : Fin t => ext6Zero), e.2 = ext6Zero := by
  classical
  have hi : ∀ (cs : List (R).Chal) (log : List (SrMove R 0 × (R).Chal)),
      (∀ ρ ∈ cs, ρ = ext6Zero) → (∀ e ∈ log, e.2 = ext6Zero) →
      ∀ e ∈ runFrom P log cs, e.2 = ext6Zero := by
    intro cs
    induction cs with
    | nil => intro log _ hlog; exact hlog
    | cons ρ cs ih =>
      intro log hcs hlog
      rw [runFrom_cons]
      apply ih
      · intro x hx
        exact hcs x (List.mem_cons_of_mem _ hx)
      · intro e he
        simp only [stepOnce, List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hlog e he
        · dsimp only
          cases hf : log.find? (fun e => decide (e.1 = P.move (log.map Prod.snd))) with
          | none => exact hcs ρ List.mem_cons_self
          | some entry => exact hlog entry (List.mem_of_find?_eq_some hf)
  rw [srTrace_eq_runFrom]
  apply hi
  · intro x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    exact hi.symm
  · intro e he
    simp at he

theorem zero_sampled_oracle {t : Nat} (P : SrProver R 0) :
    loggedOracle P (fun _ : Fin t => ext6Zero) = fun _ => ext6Zero := by
  classical
  funext q
  unfold loggedOracle
  cases hf : (srTrace P (fun _ : Fin t => ext6Zero)).find? (fun e => decide (e.1 = q)) with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, Option.getD_some]
    exact zero_sampled_trace_values P entry (List.mem_of_find?_eq_some hf)

end Minidregg.Compiler.ContextualGate

/-- info: 'Minidregg.Compiler.ContextualGate.context_receipt_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.context_receipt_sound

/-- info: 'Minidregg.Compiler.ContextualGate.fixed_query_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.fixed_query_roundtrip

/-- info: 'Minidregg.Compiler.ContextualGate.context_query_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.context_query_roundtrip

/-- info: 'Minidregg.Compiler.ContextualGate.query_bytes_match_fixed_encoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.query_bytes_match_fixed_encoder

/-- info: 'Minidregg.Compiler.ContextualGate.query_bytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.query_bytes_injective

/-- info: 'Minidregg.Compiler.ContextualGate.fixed_acceptance_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.fixed_acceptance_transport

/-- info: 'Minidregg.Compiler.ContextualGate.sound_reading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.sound_reading

/-- info: 'Minidregg.Compiler.ContextualGate.output_change_preserves_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.output_change_preserves_log

/-- info: 'Minidregg.Compiler.ContextualGate.final_challenge_is_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.final_challenge_is_logged

/-- info: 'Minidregg.Compiler.ContextualGate.one_logged_output_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.one_logged_output_bound

/-- info: 'Minidregg.Compiler.ContextualGate.rebuild_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.rebuild_append

/-- info: 'Minidregg.Compiler.ContextualGate.rebuild_actual_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.rebuild_actual_log

/-- info: 'Minidregg.Compiler.ContextualGate.response_oracle_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.response_oracle_matches

/-- info: 'Minidregg.Compiler.ContextualGate.response_bad_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.response_bad_matches

/-- info: 'Minidregg.Compiler.ContextualGate.selected_index_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.selected_index_bad

/-- info: 'Minidregg.Compiler.ContextualGate.selection_queries_still_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.selection_queries_still_logged

/-- info: 'Minidregg.Compiler.ContextualGate.any_bad_selects_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.any_bad_selects_bad

/-- info: 'Minidregg.Compiler.ContextualGate.all_logged_outputs_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.all_logged_outputs_bound

/-- info: 'Minidregg.Compiler.ContextualGate.trace_entry_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.trace_entry_query

/-- info: 'Minidregg.Compiler.ContextualGate.planned_entry_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.planned_entry_query

/-- info: 'Minidregg.Compiler.ContextualGate.planned_verifier_logs_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.planned_verifier_logs_all

/-- info: 'Minidregg.Compiler.ContextualGate.empty_log_not_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.empty_log_not_complete

/-- info: 'Minidregg.Compiler.ContextualGate.zero_sampled_trace_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.zero_sampled_trace_values

/-- info: 'Minidregg.Compiler.ContextualGate.zero_sampled_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ContextualGate.zero_sampled_oracle
