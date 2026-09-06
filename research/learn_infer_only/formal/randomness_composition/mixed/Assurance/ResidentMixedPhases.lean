/-
Statement-first: actual Stage0 and EMA public full-word receipts share ONE
program-tagged cache. Stage0 runs first; EMA's entire strategy and all its plans
may depend on Stage0's complete response history. Query-complete schedules give
an any-bad bound ((t0+14)*4160+(t1+9)*161)/p^6 with t0+t1 total queries.
There is no per-receipt factor and no hidden charging of the global budget twice.
This is a classical uniform-Ext6 ROM theorem for this explicit phase controller;
arbitrary interleaving, correlated preloaded service history, byte-uniform hash
sampling, and runtime publication timing are outside its statement.
-/
import Compiler.DisjointOraclePhases
import Assurance.ResidentMultiReceiptSchedule
import Assurance.ResidentEmaAdaptive

namespace Minidregg.Assurance.ResidentMixedPhases
open Classical
open Minidregg.Selvage
open Minidregg.Compiler
open Minidregg.Compiler.CommittedTerminalFiatShamir
open Minidregg.Compiler.CommittedTerminalRealizer
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable abbrev R₀ := ResidentAdaptiveContext.adaptiveReduction
noncomputable abbrev R₁ := ResidentEmaAdaptive.R
abbrev Q₀ := SrMove R₀ 0
abbrev Q₁ := SrMove R₁ 0
abbrev Coins₀ (t : Nat) := (Fin t → Ext6L) × (Fin 14 → Ext6L)
abbrev Coins₁ (t : Nat) := (Fin t → Ext6L) × (Fin 9 → Ext6L)

/-- One uniformly sampled vector supplies the entire positional query budget.
The 14+9 auxiliary coordinates are unused fallback coins from the inherited
soundness games; query completeness prevents them becoming free verifier queries. -/
abbrev GlobalCoins (t₀ t₁ : Nat) := (Fin (t₀+t₁) → Ext6L) ×
  ((Fin 14 → Ext6L) × (Fin 9 → Ext6L))

def splitQueryCoins (t₀ t₁ : Nat) : (Fin (t₀+t₁) → Ext6L) ≃
    (Fin t₀ → Ext6L) × (Fin t₁ → Ext6L) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Ext6L)).trans
    (Equiv.sumArrowEquivProdArrow (Fin t₀) (Fin t₁) Ext6L)

def splitGlobalCoins (t₀ t₁ : Nat) : GlobalCoins t₀ t₁ ≃ Coins₀ t₀ × Coins₁ t₁ :=
  (Equiv.prodCongr (splitQueryCoins t₀ t₁) (Equiv.refl _)).trans
    (Equiv.prodProdProdComm _ _ _ _)

theorem global_coin_positions {t₀ t₁ : Nat} (c : GlobalCoins t₀ t₁)
    (i : Fin t₀) (j : Fin t₁) :
    (splitGlobalCoins t₀ t₁ c).1.1 i=c.1 (Fin.castAdd t₁ i) ∧
    (splitGlobalCoins t₀ t₁ c).2.1 j=c.1 (Fin.natAdd t₀ j) := by
  exact ⟨rfl,rfl⟩

theorem uniform_global_coin_transport {t₀ t₁ : Nat} (event : Coins₀ t₀ × Coins₁ t₁ → Prop) :
    uniformProb (GlobalCoins t₀ t₁) (fun c=>event (splitGlobalCoins t₀ t₁ c))=
      uniformProb (Coins₀ t₀ × Coins₁ t₁) event :=
  uniformProb_equiv (splitGlobalCoins t₀ t₁) event

noncomputable def trace {t₀ t₁ : Nat} (P₀ : SrProver R₀ 0)
    (P₁ : List Ext6L → SrProver R₁ 0) (c₀ : Fin t₀ → Ext6L) (c₁ : Fin t₁ → Ext6L) :=
  DisjointOraclePhases.mixedTrace P₀.move (fun h=> (P₁ h).move) (List.ofFn c₀) (List.ofFn c₁)
noncomputable def oracle {t₀ t₁ : Nat} (P₀ : SrProver R₀ 0)
    (P₁ : List Ext6L → SrProver R₁ 0) (c₀ : Fin t₀ → Ext6L) (c₁ : Fin t₁ → Ext6L)
    (q : Q₀ ⊕ Q₁) : Ext6L := DisjointOraclePhases.answer (trace P₀ P₁ c₀ c₁) q ext6Zero

theorem actual_trace_coupling {t₀ t₁ : Nat} (P₀ : SrProver R₀ 0)
    (P₁ : List Ext6L → SrProver R₁ 0) (c₀ : Fin t₀ → Ext6L) (c₁ : Fin t₁ → Ext6L) :
    trace P₀ P₁ c₀ c₁ =
      DisjointOraclePhases.liftLeft (srTrace P₀ c₀) ++
      DisjointOraclePhases.liftRight (srTrace (r:=R₁) (P₁ ((srTrace P₀ c₀).map Prod.snd)) c₁) := by
  unfold trace
  rw [DisjointOraclePhases.mixed_trace_coupling,DisjointOraclePhases.run_is_srTrace]
  dsimp only
  exact congrArg (fun L : List (Q₁ × Ext6L)=>
    (DisjointOraclePhases.liftLeft (C:=Ext6L) (Q₁:=Q₁) (srTrace P₀ c₀) : List ((Q₀ ⊕ Q₁) × Ext6L)) ++
      DisjointOraclePhases.liftRight (C:=Ext6L) (Q₀:=Q₀) L)
    (DisjointOraclePhases.run_is_srTrace (P₁ ((srTrace P₀ c₀).map Prod.snd)) c₁)

theorem actual_query_count {t₀ t₁ : Nat} (P₀ : SrProver R₀ 0)
    (P₁ : List Ext6L → SrProver R₁ 0) (c₀ : Fin t₀ → Ext6L) (c₁ : Fin t₁ → Ext6L) :
    (trace P₀ P₁ c₀ c₁).length=t₀+t₁ := by
  unfold trace;rw [DisjointOraclePhases.mixed_query_budget];simp

theorem byte_addresses_injective : Function.Injective ResidentEmaAdaptive.programQueryBytes :=
  ResidentEmaAdaptive.program_query_bytes_injective

theorem stage0_oracle_transport {t₀ t₁ : Nat} (P₀ : SrProver R₀ 0)
    (P₁ : List Ext6L → SrProver R₁ 0) (c₀ : Fin t₀ → Ext6L) (c₁ : Fin t₁ → Ext6L) :
    (fun q=>oracle P₀ P₁ c₀ c₁ (.inl q))=ResidentMultiReceiptSchedule.loggedOracle P₀ c₀ := by
  funext q
  unfold oracle
  rw [actual_trace_coupling]
  have ha := (DisjointOraclePhases.tagged_answers (srTrace P₀ c₀)
    (srTrace (r:=R₁) (P₁ ((srTrace P₀ c₀).map Prod.snd)) c₁) ext6Zero).1 q
  trans DisjointOraclePhases.answer (srTrace P₀ c₀) q ext6Zero
  · exact ha
  exact DisjointOraclePhases.answer_eq_getD _ q ext6Zero

theorem ema_oracle_transport {t₀ t₁ : Nat} (P₀ : SrProver R₀ 0)
    (P₁ : List Ext6L → SrProver R₁ 0) (c₀ : Fin t₀ → Ext6L) (c₁ : Fin t₁ → Ext6L) :
    (fun q=>oracle P₀ P₁ c₀ c₁ (.inr q))=
      ContextualGate.loggedOracle (P₁ ((srTrace P₀ c₀).map Prod.snd)) c₁ := by
  funext q
  unfold oracle
  rw [actual_trace_coupling]
  have ha := (DisjointOraclePhases.tagged_answers (srTrace P₀ c₀)
    (srTrace (r:=R₁) (P₁ ((srTrace P₀ c₀).map Prod.snd)) c₁) ext6Zero).2 q
  trans DisjointOraclePhases.answer (srTrace (r:=R₁) (P₁ ((srTrace P₀ c₀).map Prod.snd)) c₁) q ext6Zero
  · exact ha
  exact DisjointOraclePhases.answer_eq_getD _ q ext6Zero

/-- Expected contexts and opened plans are public. Their original wrappers
check the actual descriptor-specific program tags and bindings. -/
noncomputable def AnyBad {hash : List UInt8 → Digest} {M₀ M₁ t₀ t₁ : Nat}
    (P₀ : SrProver R₀ 0) (P₁ : List Ext6L → SrProver R₁ 0)
    (expected : Fin M₀ → List Ext6L → ResidentReleaseContext.Context)
    (receipts₀ : Fin M₀ → List Ext6L → FsReceipt ResidentReleaseContext.Root 4131 13)
    (plans : List Ext6L → Fin M₁ → List Ext6L → ResidentEmaCell.OpenedPlan hash)
    (receipts₁ : List Ext6L → Fin M₁ → List Ext6L → ResidentEmaRelease.Receipt)
    (c : Coins₀ t₀ × Coins₁ t₁) : Prop :=
  let h₀ := (srTrace P₀ c.1.1).map Prod.snd
  let h₁ := (srTrace (r:=R₁) (P₁ h₀) c.2.1).map Prod.snd
  let O := oracle P₀ P₁ c.1.1 c.2.1
  (∃ j,ResidentAdaptiveContext.wrapperCheck (expected j h₀) (fun q=>O (.inl q)) (receipts₀ j h₀)=true ∧
      ¬ResidentReleaseContext.Forced (expected j h₀)) ∨
  (∃ j,ResidentEmaAdaptive.wrapperCheck (plans h₀ j h₁) (fun q=>O (.inr q)) (receipts₁ h₀ j h₁)=true ∧
      ¬ResidentEmaCell.LogicalStep (plans h₀ j h₁))

/-- Two real descriptor bounds coupled to one cache, with separate charged
phase lengths. All verifier addresses of every collected receipt are included.
No independent-oracle assumption is a premise. -/
theorem any_bad_mixed_receipt_bound {hash : List UInt8 → Digest} {M₀ M₁ t₀ t₁ : Nat}
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1/(153 : ℝ))) (hM₀ : 0<M₀) (hM₁ : 0<M₁)
    (P₀ : SrProver R₀ 0) (P₁ : List Ext6L → SrProver R₁ 0)
    (expected : Fin M₀ → List Ext6L → ResidentReleaseContext.Context)
    (receipts₀ : Fin M₀ → List Ext6L → FsReceipt ResidentReleaseContext.Root 4131 13)
    (plans : List Ext6L → Fin M₁ → List Ext6L → ResidentEmaCell.OpenedPlan hash)
    (receipts₁ : List Ext6L → Fin M₁ → List Ext6L → ResidentEmaRelease.Receipt)
    (closed₀ : ResidentMultiReceiptSchedule.AllOutputQueriesLogged t₀ P₀ (fun j h=>ResidentAdaptiveContext.output (receipts₀ j h)))
    (closed₁ : ∀ h₀,ContextualGate.AllOutputQueriesLogged t₁ (P₁ h₀)
      (fun j h₁=>ResidentEmaAdaptive.receiptOutput (receipts₁ h₀ j h₁))) :
    uniformProb (Coins₀ t₀ × Coins₁ t₁)
      (AnyBad P₀ P₁ expected receipts₀ plans receipts₁) ≤
      (((t₀ : ℝ)+14)*4160+((t₁ : ℝ)+9)*161) / ((2013265921 : ℝ)^6) := by
  have left := ResidentMultiReceiptSchedule.all_logged_bad_arithmetic_bound hM₀ P₀ expected receipts₀ closed₀
  rw [ResidentAdaptiveContext.adaptive_price_numeric] at left
  have right := fun h₀=>ResidentEmaAdaptive.all_logged_bad_steps_bound hδ hM₁ (P₁ h₀)
    (plans h₀) (receipts₁ h₀) (closed₁ h₀)
  have bound := DisjointOraclePhases.two_phase_union_bound _ _ left
    (fun c₀ : Coins₀ t₀=>right ((srTrace P₀ c₀.1).map Prod.snd)) (by positivity)
  convert bound using 1
  · apply uniformProb_congr
    intro c
    unfold AnyBad
    dsimp only
    rw [stage0_oracle_transport,ema_oracle_transport]
    rfl
  · ring

/-- The actual byte encoder is injective over the combined typed query domain;
therefore a SINGLE byte-addressed cache gives exactly these typed answers. -/
theorem byte_cache_transport {t₀ t₁ : Nat} (P₀ : SrProver R₀ 0)
    (P₁ : List Ext6L → SrProver R₁ 0) (c₀ : Fin t₀ → Ext6L) (c₁ : Fin t₁ → Ext6L)
    (q : Q₀ ⊕ Q₁) :
    DisjointOraclePhases.answer
      ((trace P₀ P₁ c₀ c₁).map (fun e=>(ResidentEmaAdaptive.programQueryBytes e.1,e.2)))
      (ResidentEmaAdaptive.programQueryBytes q) ext6Zero=oracle P₀ P₁ c₀ c₁ q :=
  DisjointOraclePhases.encoded_answer_transport _ byte_addresses_injective _ q ext6Zero

theorem accepted_program_tags {hash : List UInt8 → Digest} (expected : ResidentReleaseContext.Context)
    (p : ResidentEmaCell.OpenedPlan hash) (O₀ : Q₀ → Ext6L) (O₁ : Q₁ → Ext6L)
    (rc₀ : FsReceipt ResidentReleaseContext.Root 4131 13) (rc₁ : ResidentEmaRelease.Receipt)
    (h₀ : ResidentAdaptiveContext.wrapperCheck expected O₀ rc₀=true)
    (h₁ : ResidentEmaAdaptive.wrapperCheck p O₁ rc₁=true) :
    rc₀.root.1.program=0 ∧ rc₁.root.1.program=1 := by
  have root₀ := ResidentReleaseContext.context_binding expected _ rc₀ h₀
  have linked₀ := ResidentReleaseContext.accepted_linked expected _ rc₀ h₀
  have pair₁ := ResidentEmaRelease.checked_context p _ rc₁ h₁
  constructor
  · rw [root₀];exact linked₀.2.2.2.2.1
  · rw [pair₁.1];exact pair₁.2.1

/-- Same actual receipts inhabit the two complete local schedules and both
wrappers under their own shared sampled cache. The two program tags differ;
the global trace contains fourteen Stage0 plus nine EMA queries. -/
theorem mixed_two_receipts_premise_inhabited :
    ∃ (rc₀ : FsReceipt ResidentReleaseContext.Root 4131 13) (rc₁ : ResidentEmaRelease.Receipt),
      let P₀ := ResidentMultiReceiptSchedule.completeVerifier (M:=1) (by decide)
        (fun _=>ResidentAdaptiveContext.output rc₀)
      let P₁ := ContextualGate.completeVerifier (M:=1) (by decide)
        (fun _=>ResidentEmaAdaptive.receiptOutput rc₁)
      let O := oracle P₀ (fun _=>P₁) (fun _ : Fin 14=>ext6Zero) (fun _ : Fin 9=>ext6Zero)
      ResidentMultiReceiptSchedule.AllOutputQueriesLogged 14 P₀
        (fun _j : Fin 1=>fun _=>ResidentAdaptiveContext.output rc₀) ∧
      ContextualGate.AllOutputQueriesLogged 9 P₁
        (fun _j : Fin 1=>fun _=>ResidentEmaAdaptive.receiptOutput rc₁) ∧
      ResidentAdaptiveContext.wrapperCheck (ResidentReleaseContext.honestContext 1 2)
        (fun q=>O (.inl q)) rc₀=true ∧
      ResidentEmaAdaptive.wrapperCheck (ResidentEmaWitness.p ResidentEmaWitness.publicHash)
        (fun q=>O (.inr q)) rc₁=true ∧
      rc₀.root.1.program=0 ∧ rc₁.root.1.program=1 ∧
      (trace P₀ (fun _=>P₁) (fun _ : Fin 14=>ext6Zero) (fun _ : Fin 9=>ext6Zero)).length=23 := by
  obtain ⟨rc₀,h₀,_⟩ := ResidentAdaptiveContext.honest_wrapper_inhabited (fun _=>ext6Zero)
  obtain ⟨rc₁,h₁,_,_,_⟩ := ResidentEmaAdaptive.same_receipt_inhabited (fun _=>ext6Zero)
  have tags := accepted_program_tags _ _ _ _ rc₀ rc₁ h₀ h₁
  refine ⟨rc₀,rc₁,ResidentMultiReceiptSchedule.planned_verifier_logs_all (by decide) _,
    ContextualGate.planned_verifier_logs_all (by decide) _,?_,?_,tags.1,tags.2,?_⟩
  · rw [stage0_oracle_transport,ResidentMultiReceiptSchedule.zero_sampled_oracle]
    exact h₀
  · rw [ema_oracle_transport,ContextualGate.zero_sampled_oracle]
    exact h₁
  · exact actual_query_count _ _ _ _

/-- Dropping the tag can reuse a first-program response for the other program.
This is a cache falsifier, not a claim that the actual injective encoder aliases. -/
theorem omitted_tag_breaks_coupling :
    DisjointOraclePhases.answer ([(0,false)] : List (Nat × Bool)) 0 true=false ∧
    DisjointOraclePhases.answer ([] : List (Nat × Bool)) 0 true=true := by decide

theorem zero_ema_budget_fails (P : SrProver R₁ 0) (rc : ResidentEmaRelease.Receipt) :
    ¬ContextualGate.AllOutputQueriesLogged 0 P
      (fun _j : Fin 1=>fun _=>ResidentEmaAdaptive.receiptOutput rc) :=
  ResidentEmaAdaptive.empty_query_log_fails P rc

theorem one_global_coin_receipt_bound {hash : List UInt8 → Digest} {M₀ M₁ t₀ t₁ : Nat}
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) (1/(153 : ℝ))) (hM₀ : 0<M₀) (hM₁ : 0<M₁)
    (P₀ : SrProver R₀ 0) (P₁ : List Ext6L → SrProver R₁ 0)
    (expected : Fin M₀ → List Ext6L → ResidentReleaseContext.Context)
    (receipts₀ : Fin M₀ → List Ext6L → FsReceipt ResidentReleaseContext.Root 4131 13)
    (plans : List Ext6L → Fin M₁ → List Ext6L → ResidentEmaCell.OpenedPlan hash)
    (receipts₁ : List Ext6L → Fin M₁ → List Ext6L → ResidentEmaRelease.Receipt)
    (closed₀ : ResidentMultiReceiptSchedule.AllOutputQueriesLogged t₀ P₀ (fun j h=>ResidentAdaptiveContext.output (receipts₀ j h)))
    (closed₁ : ∀ h₀,ContextualGate.AllOutputQueriesLogged t₁ (P₁ h₀)
      (fun j h₁=>ResidentEmaAdaptive.receiptOutput (receipts₁ h₀ j h₁))) :
    uniformProb (GlobalCoins t₀ t₁)
      (fun c=>AnyBad P₀ P₁ expected receipts₀ plans receipts₁ (splitGlobalCoins t₀ t₁ c)) ≤
      (((t₀ : ℝ)+14)*4160+((t₁ : ℝ)+9)*161) / ((2013265921 : ℝ)^6) := by
  rw [uniform_global_coin_transport]
  exact any_bad_mixed_receipt_bound hδ hM₀ hM₁ P₀ P₁ expected receipts₀ plans receipts₁ closed₀ closed₁

end Minidregg.Assurance.ResidentMixedPhases

/-- info: 'Minidregg.Assurance.ResidentMixedPhases.global_coin_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.global_coin_positions
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.uniform_global_coin_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.uniform_global_coin_transport
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.actual_trace_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.actual_trace_coupling
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.actual_query_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.actual_query_count
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.byte_addresses_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.byte_addresses_injective
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.stage0_oracle_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.stage0_oracle_transport
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.ema_oracle_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.ema_oracle_transport
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.any_bad_mixed_receipt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.any_bad_mixed_receipt_bound
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.byte_cache_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.byte_cache_transport
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.accepted_program_tags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.accepted_program_tags
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.mixed_two_receipts_premise_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.mixed_two_receipts_premise_inhabited
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.omitted_tag_breaks_coupling' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.omitted_tag_breaks_coupling
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.zero_ema_budget_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.zero_ema_budget_fails
/-- info: 'Minidregg.Assurance.ResidentMixedPhases.one_global_coin_receipt_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Assurance.ResidentMixedPhases.one_global_coin_receipt_bound
