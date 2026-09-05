/-
# Selvage.HeteroCompositionSuccinct — census upgrade 4: `HeteroComposition.KnowledgeSound`
at a system whose proof is NOT the witness

`zkml-research/notes/unit-witness-census.md` §7 item 4 asks for a `ProofSystem` built from
`accReductionBcs` with `Proof := SrOutput r s`, `Verify := fiatShamir r s O`, `Wit := r.W`,
`Rel := r.R`, and `KnowledgeSound` proved from `accFsSound_bcs`'s extractor — so that
`rung_sound`/`ivc_tower_sound` (zero consumers at `9db15e7`) rest on a real extractor.

## What the statement change actually meets

`HeteroComposition.KnowledgeSound S := ∀ x π, S.Verify x π = true → ∃ w, S.Rel x w` is a
**perfect** statement: every accepting proof, at every statement, has a witness. It reads no
error — in `HeteroComposition.lean`, `ProofSystem.err` is read by the obligation
`ComposeErrorBound` (`:235`) and by no theorem: `KnowledgeSound`, `rung_sound`,
`ivc_tower_sound` never mention it. `accFsSound_bcs` is a **counting** statement: for every SR prover the
uniform probability of `(accept ∧ extractor fails)` is `≤ (t + k)·accRbrError`, and at the
landed F₅ instance that number is `(t + 2)/5 > 0`. The two meet in exactly one place —
error zero — and this file is built around that fact:

* **`fsProofSystem`** — the FS-compiled argument as a `ProofSystem`, for EVERY `Reduction`
  and oracle: `Proof := SrOutput r s` (the FS proof string — statement, `k` messages, `k`
  salts, carried target witness), `Verify := decide (FsAccepts …)` where `FsAccepts` is the
  FS verifier's acceptance ∧ the decider's check of the carried witness (Def B.2's
  acceptance event, verbatim), `Wit := r.W`, `Rel := R_{≤δ}` — the δ-RELAXED source relation,
  which is what Def B.2's extractor lands in; the census's `Rel := r.R` is its `δ`-free
  fibre and coincides with it whenever `A` is a subsingleton (`carriedFsSystem_rel_iff`).
* **`knowledgeSound_of_fs_zero`** — the bridge: straightline FS knowledge soundness at
  error `0` (for zero-query adversaries) yields `KnowledgeSound (fsProofSystem …)` at EVERY
  oracle. Proof: the 0-move prover that outputs the given proof string, and the fact that a
  uniform probability of `0` over a nonempty finite coin space is an EMPTY event.
* **`accBcsProofSystem` / `AccRbrBcsExample.accBcsSystem_F5`** — the census's system,
  built. Satisfiable: the honest committed transcript (`bcs_state_alive`'s data) is
  accepted at the oracle answering `1` (the landed schedule `γbase = (1, 1)`). Rejecting: a
  message whose columns do not open is refused. Error pinned at `(b + 2)/5`.
* ⚑ **`AccRbrBcsExample.accBcsSystem_F5_not_knowledgeSound`** — the census's target
  statement is **FALSE**, not merely unproved: at the SAME oracle that accepts the honest
  transcript, a genesis claiming `q2(xWord) = 3` (no witness for ANY `w` — the first
  conjunct of `R` does not read `w`, and `R_{≤1/32}` cannot move `xWord`) has an accepted
  proof string: send `oneWord` twice, and the fold `xWord + oneWord + oneWord` meets the
  folded target `3 + 0 + 1 = 4`. This is the `1/|F|` round event of `accRbrError`, fired at
  the `ProofSystem` seam. No oracle-relative argument at positive error inhabits the
  perfect `KnowledgeSound`; the two existing inhabitants (`AccRbrFold.lean:1073`, `:1078`)
  are error-zero deciders, and that is the only kind possible.
* **`FsKnowledgeSoundRO` / `fsKnowledgeSoundRO_of_fs` / `rung_sound_ro`** — the statement
  that IS true at positive error: the probability, over the SR game's coins, that the
  adversary's proof string is accepted at the game's oracle while its statement has NO
  witness, is `≤ εfs` — and the rung theorem at that error, for oracle-uniform embedding
  families, via `bwd`. At F₅: `accBcsSystem_F5_knowledgeSoundRO` at `(b + 2)/5`.
* **`carriedFsSystem`** — the census's request at the witness type where the extractor
  EXISTS at error zero (`AccRbrFoldExtract.foldCarried_fs_sound`): `KnowledgeSound` PROVED
  two ways — through the bridge (`carriedFsSystem_knowledgeSound_of_fs`) and with the
  extractor NAMED (`carried_srExtract_sound`: Construction B.5 on the un-fold,
  `srExtract (foldCarriedRbr …)`, outputs a relaxed genesis opening on every accepting
  proof string). `Proof = SrOutput ≠ Wit` by type; the extractor is not the identity
  (`ToyFold.toy_srExtract_ne_id`). Not succinct — `AccRbrFoldExtract`'s scope note stands.
* **`relDecider` / `relDeciderEmbedding` / `ToyFold.toy_rung`** — `rung_sound`'s FIRST
  consumer at a system whose knowledge soundness is a theorem about an extractor rather
  than `fun _ π h => ⟨π, …⟩`; and `AccRbrBcsExample.rung_hypothesis_load_bearing`: at the
  acc F₅ system the rung's CONCLUSION fails on an accepted proof — `hB` is load-bearing.

## Named, not closed

* `[HETERO-succinct]` — a `KnowledgeSound` inhabitant that is succinct. Refuted at every
  positive error (above); at error zero the only inhabitant with a real extractor carries
  `T + 1` openings. Open.
* `[HETERO-err-tower]` — `ivc_tower_sound` at positive error (`TowerSoundRO`). `n = 1` is
  `rung_sound_ro`'s shape; `n ≥ 2` is NOT a union bound: the proof `bwd` hands back for
  rung `n − 1` is an existential, not an adversary the game bounds. Open — and it is exactly
  the extractor-efficiency clause IVC soundness needs.
* `HeteroComposition.KnowledgeSound` itself: to consume a positive-error argument it must
  read `err` and quantify over the oracle — the `FsKnowledgeSoundRO` shape. Not modified
  here (file boundary); named.

Design record: `zkml-research/notes/hetero-succinct-upgrade.md`.
-/
import Selvage.AccRbrBcs
import Selvage.AccRbrFoldExtract

namespace Minidregg.Selvage

/-! ## The FS-compiled argument as a `ProofSystem` -/

/-- **Acceptance of the compiled argument** at oracle `O` and proximity `δ`: the proof
string names the statement, the FS verifier outputs a target instance, and the carried
target witness `w'` is in `R'_{≤δ}` there — Def B.2's acceptance event, read at a fixed
total oracle. -/
def FsAccepts (r : Reduction) (s : ℕ) (O : SrMove r s → r.Chal) (δ : ℝ)
    (x : Stmt r) (o : SrOutput r s) : Prop :=
  o.stmt = x ∧ ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
    fiatShamir r s O o = some (x', y') ∧ RelaxedMem r.R' δ x.idx x' y' o.w'

open Classical in
/-- **The Fiat–Shamir transform of a reduction, as `HeteroComposition`'s object.**
`Proof` is the FS proof string, `Verify` decides `FsAccepts`, `Wit` is the reduction's
witness type, `Rel` is the δ-relaxed source relation (what Def B.2 extracts). `err` is
carried data: `KnowledgeSound` reads no error, and this file shows why that matters. -/
noncomputable def fsProofSystem (r : Reduction) (s : ℕ) (O : SrMove r s → r.Chal)
    (δ : ℝ) (ε : ℝ) (hε : 0 ≤ ε) : ProofSystem where
  Stmt := Stmt r
  Wit := r.W
  Proof := SrOutput r s
  Rel := fun x w => RelaxedMem r.R δ x.idx x.x x.y w
  Verify := fun x o => decide (FsAccepts r s O δ x o)
  err := ε
  err_nonneg := hε

theorem fsProofSystem_verify_iff (r : Reduction) (s : ℕ) (O : SrMove r s → r.Chal)
    (δ ε : ℝ) (hε : 0 ≤ ε) (x : Stmt r) (o : SrOutput r s) :
    (fsProofSystem r s O δ ε hε).Verify x o = true ↔ FsAccepts r s O δ x o := by
  classical
  exact decide_eq_true_iff

theorem fsProofSystem_rel_iff (r : Reduction) (s : ℕ) (O : SrMove r s → r.Chal)
    (δ ε : ℝ) (hε : 0 ≤ ε) (x : Stmt r) (w : r.W) :
    (fsProofSystem r s O δ ε hε).Rel x w ↔ RelaxedMem r.R δ x.idx x.x x.y w :=
  Iff.rfl

/-! ## The bridge at error zero -/

/-- The 0-move state-restoration prover that outputs `o` whatever it is told. -/
def constProver (r : Reduction) (s : ℕ) (o : SrOutput r s) : SrProver r s where
  move := fun _ => ⟨o.stmt, []⟩
  out := fun _ => o

/-- **The bridge**: straightline FS knowledge soundness at error `0` for zero-query
adversaries (at some `δ ∈ (0, δ*)`) gives `HeteroComposition.KnowledgeSound` of the compiled
system at EVERY oracle. The witness is the FS extractor's output on the single transcript
`(o, ρs := O ∘ o.query, [])`. Counting: a uniform probability of `0` over a nonempty finite
coin space is an empty event (`uniformProb_pos_of_witness`), and the 0-move prover reaches
every `(o, ρs)`: its trace is `[]` and its final challenges are the fresh coins, both by
computation (`List.finRange 0 = []`), and `fiatShamir_congr` moves the verdict from the
canonical oracle `fsOracle o ρs` to `O`. -/
theorem knowledgeSound_of_fs_zero (r : Reduction) (s : ℕ) (O : SrMove r s → r.Chal)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (εfs : ℕ → ℕ → ℝ → ℝ)
    (hfs : FsStraightlineKnowledgeSoundness r Set.univ εfs) (hzero : εfs s 0 δ = 0)
    (ε : ℝ) (hε : 0 ≤ ε) : KnowledgeSound (fsProofSystem r s O δ ε hε) := by
  intro x o hacc
  rw [fsProofSystem_verify_iff] at hacc
  obtain ⟨hstmt, x', y', hver, hR'⟩ := hacc
  subst hstmt
  obtain ⟨E, hE⟩ := hfs
  have hP := hE s 0 δ hδ (constProver r s o)
  rw [hzero] at hP
  by_contra hno
  refine absurd hP (not_le.mpr ?_)
  refine uniformProb_pos_of_witness (Fin.elim0, fun i => O (o.query i)) ?_
  simp only [constProver]
  refine ⟨Set.mem_univ _, ?_, x', y', ?_, hR'⟩
  · intro hw
    exact hno ⟨_, hw⟩
  · rw [← hver]
    exact fiatShamir_congr o fun i => fsOracle_query o _ i

/-! ## The statement that is true at positive error -/

/-- **Knowledge-soundness failure** of a `ProofSystem` at one `(statement, proof)`: accepted,
and no witness at all. `KnowledgeSound S ↔ ∀ x π, ¬ KsFailure S x π`. -/
def KsFailure (S : ProofSystem) (x : S.Stmt) (π : S.Proof) : Prop :=
  S.Verify x π = true ∧ ∀ w, ¬ S.Rel x w

theorem knowledgeSound_iff_no_ksFailure (S : ProofSystem) :
    KnowledgeSound S ↔ ∀ x π, ¬ KsFailure S x π := by
  constructor
  · rintro h x π ⟨hacc, hno⟩
    obtain ⟨w, hw⟩ := h x π hacc
    exact hno w hw
  · intro h x π hacc
    by_contra hno
    exact h x π ⟨hacc, fun w hw => hno ⟨w, hw⟩⟩

theorem ksFailure_fs_iff (r : Reduction) (s : ℕ) (O : SrMove r s → r.Chal)
    (δ ε : ℝ) (hε : 0 ≤ ε) (x : Stmt r) (o : SrOutput r s) :
    KsFailure (fsProofSystem r s O δ ε hε) x o ↔
      FsAccepts r s O δ x o ∧ ¬ ∃ w, RelaxedMem r.R δ x.idx x.x x.y w := by
  rw [KsFailure, fsProofSystem_verify_iff, not_exists]
  rfl

/-- **Knowledge soundness in the ROM game, at the `ProofSystem` seam**: for every SR prover,
the probability over the game's coins that its output is accepted at the game's own
oracle (`fsOracle o ρs`) while its statement has NO witness in `R_{≤δ}` is at most `εfs`.
This is `KsFailure (fsProofSystem r s (fsOracle o ρs) δ …) o.stmt o` under `uniformProb`
(`ksFailure_fs_iff`) — the shape `HeteroComposition.KnowledgeSound` would need to have for
a positive-error argument to inhabit it. -/
def FsKnowledgeSoundRO (r : Reduction) (δ : ℝ) (εfs : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∀ (s t : ℕ) (P : SrProver r s),
    uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal)) (fun coins =>
      let log := srTrace P coins.1
      let o := P.out (log.map Prod.snd)
      let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
      FsAccepts r s (fsOracle o ρs) δ o.stmt o ∧
        ¬ ∃ w, RelaxedMem r.R δ o.stmt.idx o.stmt.x o.stmt.y w)
      ≤ εfs s t δ

/-- Straightline FS knowledge soundness implies the ROM-game statement: "no witness at all"
is a sub-event of "the extractor's output is not a witness" (`uniformProb_mono`). -/
theorem fsKnowledgeSoundRO_of_fs (r : Reduction) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (εfs : ℕ → ℕ → ℝ → ℝ)
    (hfs : FsStraightlineKnowledgeSoundness r Set.univ εfs) :
    FsKnowledgeSoundRO r δ εfs := by
  intro s t P
  obtain ⟨E, hE⟩ := hfs
  refine le_trans (uniformProb_mono ?_) (hE s t δ hδ P)
  intro coins h
  obtain ⟨⟨-, x', y', hver, hR'⟩, hno⟩ := h
  exact ⟨Set.mem_univ _, fun hw => hno ⟨_, hw⟩, x', y', hver, hR'⟩

/-- **The rung at positive error** — `rung_sound`'s content for the FS-compiled system, in
the ROM game: for an oracle-uniform family of embeddings of `A` into the compiled system,
the probability that the adversary's proof string is accepted at the game's oracle while
the `A`-statement it embeds has NO accepting `A`-proof is `≤ εfs`. The step is `bwd`, as in
`rung_sound`; the error is the game's, as `rung_sound` cannot say. -/
theorem rung_sound_ro (A : ProofSystem) (r : Reduction) (δ : ℝ) (εfs : ℕ → ℕ → ℝ → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (e : ∀ (s : ℕ) (O : SrMove r s → r.Chal),
      VerifierEmbedding A (fsProofSystem r s O δ ε hε))
    (hB : FsKnowledgeSoundRO r δ εfs) :
    ∀ (s t : ℕ) (P : SrProver r s),
      uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal)) (fun coins =>
        let log := srTrace P coins.1
        let o := P.out (log.map Prod.snd)
        let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
        (fsProofSystem r s (fsOracle o ρs) δ ε hε).Verify o.stmt o = true ∧
          ∃ x : A.Stmt, (e s (fsOracle o ρs)).encStmt x = o.stmt ∧
            ¬ ∃ πA, A.Verify x πA = true)
        ≤ εfs s t δ := by
  intro s t P
  refine le_trans (uniformProb_mono ?_) (hB s t P)
  intro coins h
  obtain ⟨hacc, x, hx, hno⟩ := h
  refine ⟨(fsProofSystem_verify_iff _ _ _ _ _ _ _ _).mp hacc, ?_⟩
  rintro ⟨w, hw⟩
  apply hno
  obtain ⟨πA, -, hA⟩ := (e s _).bwd x w (by
    show RelaxedMem r.R δ ((e s _).encStmt x).idx ((e s _).encStmt x).x
      ((e s _).encStmt x).y w
    rw [hx]
    exact hw)
  exact ⟨πA, hA⟩

/-- `[HETERO-err-tower]` — `ivc_tower_sound` at positive error: for a self-embedding family
of the compiled system, `n` rungs at error `n · εfs`.

ATLAS keystone fields:
* satisfiable: `n = 0` is `uniformProb_nonneg`-trivial (the event demands `x = o.stmt`
  with no accepting proof, contradicting acceptance); `n = 1` is `rung_sound_ro`'s shape.
* teeth: at error `0` this is `ivc_tower_sound` on `knowledgeSound_of_fs_zero`; at positive
  error and `n ≥ 2` the proof `bwd` returns for rung `n − 1` is an EXISTENTIAL, not an
  adversary the SR game prices — so the union bound over rungs is not available in this
  model. That is the extractor-efficiency clause of IVC, named.
* premise-inhabitation: `SelfEmbedding` families exist for the identity carrier
  (`relDeciderEmbedding` below is one-way; a self-embedding is `[COMPOSE-fixedpoint]`). -/
def TowerSoundRO (r : Reduction) (δ : ℝ) (εfs : ℕ → ℕ → ℝ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (e : ∀ (s : ℕ) (O : SrMove r s → r.Chal), SelfEmbedding (fsProofSystem r s O δ ε hε)) :
    Prop :=
  ∀ (n s t : ℕ) (P : SrProver r s),
    uniformProb ((Fin t → r.Chal) × (Fin r.k → r.Chal)) (fun coins =>
      let log := srTrace P coins.1
      let o := P.out (log.map Prod.snd)
      let ρs : Fin r.k → r.Chal := srFinalChal P coins.1 coins.2
      (fsProofSystem r s (fsOracle o ρs) δ ε hε).Verify o.stmt o = true ∧
        ∃ x : Stmt r, (e s (fsOracle o ρs)).encStmt^[n] x = o.stmt ∧
          ¬ ∃ π₀, (fsProofSystem r s (fsOracle o ρs) δ ε hε).Verify x π₀ = true)
      ≤ (n : ℝ) * εfs s t δ

/-! ## The decider of a relation, and the identity carrier into it -/

open Classical in
/-- The DECIDER of `B`'s relation as a `ProofSystem`: the proof IS a witness, checked
directly. This is the shape of both existing `KnowledgeSound` inhabitants
(`plainCommitSystem`, `foldSystem`) and of `verifierRelationSystem`'s source; it is the
`A` that any `B` proves the relation of. -/
noncomputable def relDecider (B : ProofSystem) : ProofSystem where
  Stmt := B.Stmt
  Wit := B.Wit
  Proof := B.Wit
  Rel := B.Rel
  Verify := fun x w => decide (B.Rel x w)
  err := 0
  err_nonneg := le_refl 0

/-- The identity carrier `relDecider B → B`: `fwd` and `bwd` are `decide`'s two directions.
`canonicalEmbedding`'s shape, read from `B`'s side. -/
noncomputable def relDeciderEmbedding (B : ProofSystem) :
    VerifierEmbedding (relDecider B) B where
  encStmt := id
  encProof := id
  fwd := fun _ _ h => by classical exact of_decide_eq_true h
  bwd := fun _ w h => ⟨w, rfl, by classical exact decide_eq_true h⟩

/-! ## The census's system: `accReductionBcs`, Fiat–Shamir'd -/

section AccBcs

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

/-- **The census's `ProofSystem`** (§7 item 4), built: `fsProofSystem` at
`accReductionBcs` — proof string = roots + opened columns + opening proofs + carried
witness; `Verify` = every opening verifies ∧ the folded word is `δ`-close to satisfying
the aggregate; `Wit = Fin ch.length → Fin m → F`; `Rel = R_{≤δ}` (genesis satisfied ∧ each
link aligned, up to `δ` on the genesis word). `err` = the FS number `accFsSound_bcs` proves
at query budget `b`, `(b + k)·accRbrError F errstar δ` — a fact about the SR game
(`accBcs_knowledgeSoundRO`), NOT about `KnowledgeSound`, which this system does not have
(`AccRbrBcsExample.accBcsSystem_F5_not_knowledgeSound`). -/
noncomputable def accBcsProofSystem (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) (errstar : ℝ → ℝ)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) δs) (b s : ℕ)
    (O : SrMove (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q) s → F) :
    ProofSystem :=
  fsProofSystem (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q) s O δ
    (((b : ℝ) + (ch.length : ℝ)) * accRbrError F errstar δ)
    (mul_nonneg (by positivity) (accRbrError_nonneg (hstar δ hδ)))

/-- **What `accFsSound_bcs` gives at the `ProofSystem` seam**: knowledge soundness in the
ROM game at `(b + k)·accRbrError` — proven parameters only, the mutual-CA floor consumed
as hypotheses exactly as `accFsSound_bcs` consumes it. -/
theorem accBcs_knowledgeSoundRO (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) {dC Bstar : ℝ}
    (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) δs) :
    FsKnowledgeSoundRO (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q) δ
      (fun _s b δ => ((b : ℝ) + (ch.length : ℝ)) * accRbrError F errstar δ) :=
  fsKnowledgeSoundRO_of_fs _ hδ _
    (accFsSound_bcs C foldRoot ch hm hch δs hδpos hδone S dom d q errstar hdC hMCA
      hBstar hdC2 hstar Set.univ)

end AccBcs

/-! ## A counting lemma: below `1/n`, the δ-ball is a point -/

/-- Fractional Hamming distance below `1/n` forces equality: the disagreement count is a
natural number strictly below `1`. -/
theorem eq_of_fracHamming_lt_inv {A : Type} {n : ℕ} (hn : 0 < n) {u v : Fin n → A}
    {δ : ℝ} (hδ : δ < 1 / (n : ℝ)) (h : fracHamming u v ≤ δ) : u = v := by
  classical
  unfold fracHamming at h
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlt : (Nat.card {i : Fin n // u i ≠ v i} : ℝ) < 1 := by
    have := lt_of_le_of_lt h hδ
    rwa [div_lt_div_iff_of_pos_right hn'] at this
  have hzero : Nat.card {i : Fin n // u i ≠ v i} = 0 := by
    have : Nat.card {i : Fin n // u i ≠ v i} < 1 := by exact_mod_cast hlt
    omega
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff] at hzero
  funext i
  by_contra hne
  exact hzero.false ⟨i, hne⟩

/-! ## Keystones at the landed F₅ BCS instance -/

namespace AccRbrBcsExample

open RSExample AccExample LCExample ZkHidingExample AccExtractChainExample
  ZkExtractionExample CommitExample AccSoundRbrExample

/-- The oracle answering `1` at every query. It realizes the landed honest schedule
`γbase = (1, 1)` — AND it is the lucky oracle of the refutation below. One oracle, both
poles. -/
def oneOracle : SrMove accReductionBcs_F5 0 → ZMod 5 := fun _ => 1

/-- The census's system at the landed instance: `accReductionBcs_F5`, salt size `0`,
`δ = 1/32` (inside the instance's `δ* = 1/16`), query budget `b`. -/
noncomputable def accBcsSystem_F5 (b : ℕ) (O : SrMove accReductionBcs_F5 0 → ZMod 5) :
    ProofSystem :=
  accBcsProofSystem (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num) S₅ dom₅ 2 qPair
    (fun _ => 0) (fun _ _ => le_refl 0) (δ := 1 / 32)
    (by rw [Set.mem_Ioo]; constructor <;> norm_num) b 0 O

/-- **The error field computes**: `(b + 2)/5` — `accRbrError_zero_five` through `k = 2`. -/
theorem accBcsSystem_F5_err (b : ℕ) (O : SrMove accReductionBcs_F5 0 → ZMod 5) :
    (accBcsSystem_F5 b O).err = ((b : ℝ) + 2) * (1 / 5) := by
  show ((b : ℝ) + (goodChain.length : ℝ)) * accRbrError (ZMod 5) (fun _ => 0) (1 / 32) = _
  rw [accRbrError_zero_five, show goodChain.length = 2 from rfl]
  norm_num

/-- **The ROM-game number at F₅**: `(b + 2)·(1/5)`, from `bcs_fs_fired`. -/
theorem accBcsSystem_F5_knowledgeSoundRO :
    FsKnowledgeSoundRO accReductionBcs_F5 (1 / 32)
      (fun _s b δ => ((b : ℝ) + (accReductionBcs_F5.k : ℝ))
        * accRbrError (ZMod 5) (fun _ => 0) δ) :=
  fsKnowledgeSoundRO_of_fs _
    (by
      rw [Set.mem_Ioo]
      exact ⟨by norm_num, by show (1 : ℝ) / 32 < 1 / 16; norm_num⟩)
    _ bcs_fs_fired

/-- **Why the census's route does not fire**: the bridge needs the FS error at zero
queries to be `0`; here it is `2/5`. -/
theorem accBcs_fs_error_ne_zero :
    (((0 : ℕ) : ℝ) + (accReductionBcs_F5.k : ℝ)) * accRbrError (ZMod 5) (fun _ => 0) (1 / 32)
      ≠ 0 := by
  rw [accRbrError_zero_five, show accReductionBcs_F5.k = 2 from rfl]
  norm_num

/-! ### Satisfiable: the honest committed transcript is accepted -/

/-- The honest FS proof string: the landed genesis, the honest committed round messages
(`msgBcs`), plain FS (no salts), the masked words as the carried witness. -/
noncomputable def honestOut : SrOutput accReductionBcs_F5 0 :=
  ⟨stBcs_F5, msgBcs, fun _ => Fin.elim0, fun k => msEx k⟩

/-- **SATISFIABLE**: the honest proof string is accepted at `oneOracle` — `bcs_state_alive`
read through `full_iff`, with the derived challenges the landed `γbase = (1, 1)`. -/
theorem honest_accepted (b : ℕ) :
    (accBcsSystem_F5 b oneOracle).Verify stBcs_F5 honestOut = true := by
  unfold accBcsSystem_F5 accBcsProofSystem
  rw [fsProofSystem_verify_iff]
  obtain ⟨x', y', hver, hR'⟩ := (accRbrBcs_F5.kstate.full_iff (1 / 32)
    (by
      rw [Set.mem_Ioo]
      exact ⟨by norm_num, by show (1 : ℝ) / 32 < 1 / 16; norm_num⟩)
    stBcs_F5 msgBcs (fun k => γbase (k : ℕ)) (fun k => msEx k)).mp bcs_state_alive
  refine ⟨rfl, x', y', ?_, hR'⟩
  rw [← hver]
  show accReductionBcs_F5.verify () genesis xWord msgBcs (fun _ => 1)
    = accReductionBcs_F5.verify () genesis xWord msgBcs (fun k => γbase (k : ℕ))
  congr 1
  funext k
  exact (show ∀ j : Fin 2, (1 : ZMod 5) = γbase (j : ℕ) by decide) k

/-! ### Refutable: a message whose columns do not open is rejected -/

/-- A message attributing `oneWord`'s columns to the root committing `xWord`. -/
def badMsg : BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2 :=
  ⟨S₅.commit xWord, fun j => oneWord (qPair j), fun _ => ()⟩

theorem badMsg_not_opens : ¬ ColsOpen S₅ qPair badMsg := by
  show ¬ ∀ j : Fin 2, xWord (qPair j) = oneWord (qPair j)
  decide

/-- The proof string carrying `badMsg` in every round. -/
noncomputable def badOut : SrOutput accReductionBcs_F5 0 :=
  ⟨stBcs_F5, fun _ => badMsg, fun _ => Fin.elim0, fun k => msEx k⟩

theorem badOut_fs_none : fiatShamir accReductionBcs_F5 0 oneOracle badOut = none := by
  classical
  show (if ∀ i : Fin 2, ColsOpen S₅ qPair badMsg then _ else none) = none
  rw [if_neg]
  intro h
  exact badMsg_not_opens (h 0)

/-- **REFUTABLE**: the verifier rejects it, at every budget. -/
theorem badOut_rejected (b : ℕ) :
    (accBcsSystem_F5 b oneOracle).Verify stBcs_F5 badOut = false := by
  unfold accBcsSystem_F5 accBcsProofSystem fsProofSystem
  rw [decide_eq_false_iff_not]
  rintro ⟨-, x', y', hver, -⟩
  rw [badOut_fs_none] at hver
  cases hver

/-! ### ⚑ `KnowledgeSound` is FALSE here — the lucky oracle -/

/-- A genesis claim with NO witness: `q2(xWord) = 3`, while `q2 xWord = 2`. -/
def luckyGenesis : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 := ⟨0, fun _ => (q2, 3)⟩

noncomputable def luckySt : Stmt accReductionBcs_F5 := ⟨(), luckyGenesis, xWord⟩

/-- The cheating round message: `oneWord` honestly committed and opened (`q2 oneWord = 1`,
where `claim₀` asks for `0`). -/
def luckyMsg : BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2 :=
  ⟨S₅.commit oneWord, fun j => oneWord (qPair j), fun j => S₅.openAt oneWord (qPair j)⟩

theorem luckyMsg_opens : ColsOpen S₅ qPair luckyMsg :=
  fun j => S₅.verifyOpen_commit oneWord (qPair j)

theorem luckyMsg_word : bcsWord dom₅ 2 qPair luckyMsg = oneWord :=
  recoverFromColumns_sound dom₅ le_rfl qPair_inj oneWord_mem fun _ => rfl

/-- The lucky proof string: the witness-less statement, `luckyMsg` in both rounds. -/
noncomputable def luckyOut : SrOutput accReductionBcs_F5 0 :=
  ⟨luckySt, fun _ => luckyMsg, fun _ => Fin.elim0, fun _ => oneWord⟩

theorem luckyOut_fs :
    fiatShamir accReductionBcs_F5 0 oneOracle luckyOut =
      some (aggregate linRoot (padSched fun _ : Fin 2 => (1 : ZMod 5)) luckyGenesis
          goodChain,
        foldWords (padSched fun _ : Fin 2 => (1 : ZMod 5)) xWord
          (List.ofFn fun _ : Fin 2 => bcsWord dom₅ 2 qPair luckyMsg)) := by
  classical
  show (if ∀ i : Fin 2, ColsOpen S₅ qPair luckyMsg then _ else none) = _
  rw [if_pos fun _ => luckyMsg_opens]
  rfl

/-- The fold `xWord + oneWord + oneWord` meets the folded target `3 + 1·0 + 1·1 = 4`:
`2 + 1 + 1 = 4` in `ZMod 5`. The `1/|F|` event of `accRbrError`, on the nose. -/
theorem lucky_fold_satisfies :
    ∀ i : Fin 1,
      (aggregate linRoot (padSched fun _ : Fin 2 => (1 : ZMod 5)) luckyGenesis
        goodChain).weights i
        (foldWords (padSched fun _ : Fin 2 => (1 : ZMod 5)) xWord [oneWord, oneWord])
      = (aggregate linRoot (padSched fun _ : Fin 2 => (1 : ZMod 5)) luckyGenesis
          goodChain).targets i := by
  decide

/-- **The lucky proof string is ACCEPTED** at the honest oracle. -/
theorem lucky_accepted (b : ℕ) :
    (accBcsSystem_F5 b oneOracle).Verify luckySt luckyOut = true := by
  unfold accBcsSystem_F5 accBcsProofSystem
  rw [fsProofSystem_verify_iff]
  refine ⟨rfl, _, _, luckyOut_fs, ?_⟩
  have hofn : (List.ofFn fun _ : Fin 2 => bcsWord dom₅ 2 qPair luckyMsg)
      = [oneWord, oneWord] := by
    rw [luckyMsg_word]
    rfl
  rw [hofn]
  refine ⟨_, ⟨Submodule.mem_top, lucky_fold_satisfies⟩, ?_⟩
  rw [fracHamming_self]
  norm_num

/-- **The lucky statement has NO witness**, in `R_{≤1/32}`: the ball of radius `1/32 < 1/4`
around `xWord` is `{xWord}`, and `q2 xWord = 2 ≠ 3`. The first conjunct of `R` does not
read `w`. -/
theorem lucky_no_witness (w : Fin 2 → Fin 4 → ZMod 5) :
    ¬ RelaxedMem accReductionBcs_F5.R (1 / 32) () luckyGenesis xWord w := by
  rintro ⟨ystar, ⟨⟨-, hq⟩, -⟩, hclose⟩
  have hy : xWord = ystar := eq_of_fracHamming_lt_inv (by norm_num) (by norm_num) hclose
  subst hy
  exact absurd (hq 0) (by decide)

/-- ⚑⚑ **The census's target statement is FALSE**: `accBcsSystem_F5 b oneOracle` — the
`ProofSystem` §7 item 4 specifies, at the landed instance, at the oracle that accepts the
honest transcript — is NOT `KnowledgeSound`, for every budget `b`. The `1/|F|` round event
is a real accepting proof string of a witness-less statement, and `KnowledgeSound` has no
error slot to charge it to. -/
theorem accBcsSystem_F5_not_knowledgeSound (b : ℕ) :
    ¬ KnowledgeSound (accBcsSystem_F5 b oneOracle) := by
  intro h
  obtain ⟨w, hw⟩ := h luckySt luckyOut (lucky_accepted b)
  exact lucky_no_witness w hw

/-- **`rung_sound`'s hypothesis is load-bearing**: at the acc F₅ system, with the identity
carrier in place, the rung's CONCLUSION fails on an accepted proof — there is no
`relDecider`-proof (no witness) for `luckySt`. `rung_sound` cannot be instantiated here
(`accBcsSystem_F5_not_knowledgeSound`), and this is why. -/
theorem rung_hypothesis_load_bearing (b : ℕ) :
    (accBcsSystem_F5 b oneOracle).Verify
        ((relDeciderEmbedding (accBcsSystem_F5 b oneOracle)).encStmt luckySt) luckyOut
      = true ∧
    ¬ ∃ πA, (relDecider (accBcsSystem_F5 b oneOracle)).Verify luckySt πA = true :=
  ⟨lucky_accepted b, fun ⟨πA, h⟩ =>
    lucky_no_witness πA (by classical exact of_decide_eq_true h)⟩

end AccRbrBcsExample

/-! ## The carried fold: the inhabitant with a real extractor -/

section Carried

variable {R : Type} [Ring R] {W C : Type} [AddCommGroup W] [AddCommGroup C]
  [Module R W] [Module R C]
  (S : FoldCommitScheme R W C) (T : ℕ) (hT : 0 < T) (Kh : Type)
  [Fintype Kh] [Nonempty Kh] (chalVal : Kh → R) (b₀ : ℝ)

/-- **The carried fold, Fiat–Shamir'd, as a `ProofSystem`** at error `0` — the number
`foldCarried_fs_sound` proves. `Proof` = the FS string (genesis commitment, `T` absorbed
commitments, salts, the carried `(running opening, T absorbed openings)`); `Wit` =
`W × (Fin T → W)`; `Rel` = the relaxed genesis opening (`carriedFsSystem_rel_iff`). -/
noncomputable def carriedFsSystem (s : ℕ)
    (O : SrMove (foldReductionCarried S T hT Kh chalVal b₀) s → Kh) : ProofSystem :=
  fsProofSystem (foldReductionCarried S T hT Kh chalVal b₀) s O (1 / 2) 0 le_rfl

/-- Here `Rel` IS the census's `r.R`: the proximity alphabet is `Unit`, so `R_{≤δ} = R`. -/
theorem carriedFsSystem_rel_iff (s : ℕ)
    (O : SrMove (foldReductionCarried S T hT Kh chalVal b₀) s → Kh)
    (x : Stmt (foldReductionCarried S T hT Kh chalVal b₀)) (w : W × (Fin T → W)) :
    (carriedFsSystem S T hT Kh chalVal b₀ s O).Rel x w ↔
      S.ShortOpens (S.budget b₀ (2 * T)) x.x w.1 :=
  relaxedMem_of_subsingleton _ (by norm_num) _ _ _ _

/-- **Construction B.5 preserves the carried state, index by index**: from the full-transcript
state at `w'`, the backward composition `wAt` at index `i` is in the state of the length-`i`
prefix — `foldExtract_state` iterated, no probability anywhere. -/
theorem wAt_carried_state (hchal : ∀ c, chalVal c ∈ S.chalSet)
    (st : Stmt (foldReductionCarried S T hT Kh chalVal b₀)) (rounds : List (C × Kh))
    (w' : W × (Fin T → W))
    (hw : FoldCarriedStateProp S T Kh chalVal b₀ st.x rounds w') (hlen : rounds.length ≤ T) :
    ∀ i, i ≤ rounds.length →
      FoldCarriedStateProp S T Kh chalVal b₀ st.x (rounds.take i)
        (wAt (foldCarriedRbr S T hT Kh chalVal b₀ hchal) st rounds w' i) := by
  suffices h : ∀ j i, rounds.length - i = j → i ≤ rounds.length →
      FoldCarriedStateProp S T Kh chalVal b₀ st.x (rounds.take i)
        (wAt (foldCarriedRbr S T hT Kh chalVal b₀ hchal) st rounds w' i) from
    fun i hi => h _ i rfl hi
  intro j
  induction j with
  | zero =>
    intro i hj hi
    have hi' : i = rounds.length := by omega
    subst hi'
    rw [wAt_of_le _ _ _ _ le_rfl, List.take_length]
    exact hw
  | succ j ih =>
    intro i hj hi
    have hlt : i < rounds.length := by omega
    rw [wAt_of_lt _ _ _ _ hlt]
    have hstep := ih (i + 1) (by omega) (by omega)
    have hiT : i < T := lt_of_lt_of_le hlt hlen
    have htake : rounds.take (i + 1) = rounds.take i ++ [rounds[i]] :=
      (List.take_append_getElem hlt).symm
    rw [htake] at hstep ⊢
    have hlen' : (rounds.take i).length = i := by
      rw [List.length_take]
      exact min_eq_left (le_of_lt hlt)
    exact foldExtract_state S T hT Kh chalVal b₀ hchal st ⟨i, hiT⟩ (rounds.take i) hlen'
      (rounds[i]).1 (rounds[i]).2 _ hstep

/-- **The NAMED extractor, sound on every accepting proof string**: the straightline FS
extractor of the carried fold, `srExtract (foldCarriedRbr …)` — Construction B.5 on the
un-fold `(Y, Ys) ↦ (Y − ρᵢ • Ysᵢ, Ys)` — outputs a `budget b₀ (2T)`-short opening of the
genesis whenever `carriedFsSystem` accepts. Deterministic, error `0`, at every oracle. -/
theorem carried_srExtract_sound (hchal : ∀ c, chalVal c ∈ S.chalSet) (s : ℕ)
    (O : SrMove (foldReductionCarried S T hT Kh chalVal b₀) s → Kh)
    (x : Stmt (foldReductionCarried S T hT Kh chalVal b₀))
    (o : SrOutput (foldReductionCarried S T hT Kh chalVal b₀) s)
    (hacc : (carriedFsSystem S T hT Kh chalVal b₀ s O).Verify x o = true) :
    (carriedFsSystem S T hT Kh chalVal b₀ s O).Rel x
      (srExtract (foldCarriedRbr S T hT Kh chalVal b₀ hchal) s o
        (fun i => O (o.query i)) []) := by
  unfold carriedFsSystem at hacc ⊢
  rw [fsProofSystem_verify_iff] at hacc
  obtain ⟨hstmt, x', y', hver, hR'⟩ := hacc
  subst hstmt
  obtain ⟨hx, -⟩ := Prod.mk.inj (Option.some.inj hver)
  subst hx
  rw [relaxedMem_of_subsingleton _ (by norm_num)] at hR'
  obtain ⟨⟨hcom, hnrm⟩, hopen⟩ := hR'
  have hfull : FoldCarriedStateProp S T Kh chalVal b₀ o.stmt.x
      (List.ofFn fun i => (o.πs i, O (o.query i))) o.w' := by
    refine ⟨hcom, ?_, ?_⟩
    · rw [List.length_ofFn, show 2 * T - T = T by omega]
      exact hnrm
    · intro j hj
      simpa only [List.getElem_ofFn, Fin.eta] using hopen j
  have h0 := wAt_carried_state S T hT Kh chalVal b₀ hchal o.stmt _ o.w' hfull
    (by rw [List.length_ofFn]) 0 (Nat.zero_le _)
  rw [List.take_zero] at h0
  obtain ⟨hc, hn, -⟩ := h0
  rw [chalFoldList_nil] at hc
  rw [List.length_nil, Nat.sub_zero] at hn
  rw [fsProofSystem_rel_iff, relaxedMem_of_subsingleton _ (by norm_num)]
  exact ⟨hc, hn⟩

/-- **`KnowledgeSound`, with the extractor named**: `carried_srExtract_sound` supplies the
witness. -/
theorem carriedFsSystem_knowledgeSound (hchal : ∀ c, chalVal c ∈ S.chalSet) (s : ℕ)
    (O : SrMove (foldReductionCarried S T hT Kh chalVal b₀) s → Kh) :
    KnowledgeSound (carriedFsSystem S T hT Kh chalVal b₀ s O) :=
  fun x o hacc => ⟨_, carried_srExtract_sound S T hT Kh chalVal b₀ hchal s O x o hacc⟩

/-- **`KnowledgeSound`, the census's route**: through the bridge from
`foldCarried_fs_sound`'s error-`0` FS statement — the same conclusion, extractor hidden in
the FS theorem's existential. -/
theorem carriedFsSystem_knowledgeSound_of_fs (hchal : ∀ c, chalVal c ∈ S.chalSet) (s : ℕ)
    (O : SrMove (foldReductionCarried S T hT Kh chalVal b₀) s → Kh) :
    KnowledgeSound (carriedFsSystem S T hT Kh chalVal b₀ s O) :=
  knowledgeSound_of_fs_zero _ s O
    (by
      rw [Set.mem_Ioo]
      exact ⟨by norm_num, by show (1 : ℝ) / 2 < 1; norm_num⟩)
    _ (foldCarried_fs_sound S T hT Kh chalVal b₀ hchal Set.univ) rfl 0 le_rfl

/-- **`rung_sound`'s first consumer with a real extractor**: an accepting FS proof string of
the carried fold yields a proof the `T + 1`-openings decider accepts. The embedding is the
identity carrier; the content is `hB`, which is now `carried_srExtract_sound`, not
`fun _ π h => ⟨π, …⟩`. -/
theorem carried_rung (hchal : ∀ c, chalVal c ∈ S.chalSet) (s : ℕ)
    (O : SrMove (foldReductionCarried S T hT Kh chalVal b₀) s → Kh)
    (x : Stmt (foldReductionCarried S T hT Kh chalVal b₀))
    (π : SrOutput (foldReductionCarried S T hT Kh chalVal b₀) s)
    (hacc : (carriedFsSystem S T hT Kh chalVal b₀ s O).Verify x π = true) :
    ∃ πA, (relDecider (carriedFsSystem S T hT Kh chalVal b₀ s O)).Verify x πA = true :=
  rung_sound (relDeciderEmbedding _)
    (carriedFsSystem_knowledgeSound S T hT Kh chalVal b₀ hchal s O) x π hacc

end Carried

/-! ## Keystones at the toy fold -/

namespace ToyFold

/-- The carried fold at the toy point, one absorption, budget `0`. -/
noncomputable abbrev toyCarried : Reduction :=
  foldReductionCarried toy 1 one_pos (Fin 3) chalVal3 0

/-- The oracle answering challenge index `2` (decode `chalVal3 2 = +1`) everywhere. -/
noncomputable def twoOracle : SrMove toyCarried 0 → Fin 3 := fun _ => 2

/-- The toy carried fold's compiled system. -/
noncomputable def toySystem : ProofSystem :=
  carriedFsSystem toy 1 one_pos (Fin 3) chalVal3 0 0 twoOracle

/-- Genesis commitment `0`. -/
noncomputable def toySt : Stmt toyCarried := ⟨(), 0, fun _ => ()⟩

/-- The honest proof string: absorb `commit e₀`, carry `(e₀, e₀)` — the running opening of
the one-fold `0 + 1·commit e₀` and the absorbed opening. -/
noncomputable def toyHonestOut : SrOutput toyCarried 0 :=
  ⟨toySt, fun _ => intCommit 97 A97 e01, fun _ => Fin.elim0, (e01, fun _ => e01)⟩

/-- **SATISFIABLE**: the honest proof string is accepted. -/
theorem toy_honest_accepted : toySystem.Verify toySt toyHonestOut = true := by
  unfold toySystem carriedFsSystem
  rw [fsProofSystem_verify_iff]
  refine ⟨rfl, _, _, rfl, ?_⟩
  rw [relaxedMem_of_subsingleton _ (by norm_num)]
  refine ⟨⟨?_, ?_⟩, fun j => ⟨rfl, ?_⟩⟩
  · show intCommit 97 A97 e01 = chalFoldList chalVal3 (0 : Fin 1 → ZMod 97)
      (List.ofFn fun _ : Fin 1 => (intCommit 97 A97 e01, (2 : Fin 3)))
    simp only [List.ofFn_succ, List.ofFn_zero]
    decide
  · show supNorm e01 ≤ toy.budget 0 1
    rw [toy_budget, supNorm, show supNat e01 = 1 from by decide]
    norm_num
  · show supNorm e01 ≤ toy.B
    rw [supNorm, show supNat e01 = 1 from by decide]
    exact le_refl _

/-- A proof string carrying `0` as the absorbed opening of `commit e₀`. -/
noncomputable def toyBadOut : SrOutput toyCarried 0 :=
  ⟨toySt, fun _ => intCommit 97 A97 e01, fun _ => Fin.elim0, (e01, fun _ => 0)⟩

/-- **REFUTABLE**: the decider's check of the carried absorbed opening rejects it
(`commit 0 = 0 ≠ 1 = commit e₀`). -/
theorem toy_bad_rejected : toySystem.Verify toySt toyBadOut = false := by
  unfold toySystem carriedFsSystem fsProofSystem
  rw [decide_eq_false_iff_not]
  rintro ⟨-, x', y', hver, hR'⟩
  obtain ⟨hx, -⟩ := Prod.mk.inj (Option.some.inj hver)
  subst hx
  rw [relaxedMem_of_subsingleton _ (by norm_num)] at hR'
  have h : toy.commit (0 : Fin 2 → ℤ) = intCommit 97 A97 e01 := (hR'.2 0).1
  rw [map_zero] at h
  have h0 := congrFun h 0
  rw [toy_commit_e01] at h0
  exact absurd h0 (by decide)

/-- The straightline extractor on the honest proof string, computed: the un-fold
`e₀ − 1·e₀ = 0` in the running slot, the absorbed opening kept. -/
theorem toy_srExtract_eq :
    srExtract (foldCarriedRbr toy 1 one_pos (Fin 3) chalVal3 0 toy_chalVal3_mem) 0
        toyHonestOut (fun i => twoOracle (toyHonestOut.query i)) []
      = (0, fun _ => e01) := by
  show wAt _ toySt (List.ofFn fun _ : Fin 1 => (intCommit 97 A97 e01, (2 : Fin 3)))
    (e01, fun _ => e01) 0 = _
  simp only [List.ofFn_succ, List.ofFn_zero]
  rw [wAt_of_lt _ _ _ _ (by simp), wAt_of_le _ _ _ _ (by simp)]
  show foldExtract toy 1 one_pos (Fin 3) chalVal3 0 toySt
    ⟨[] ++ [(intCommit 97 A97 e01, (2 : Fin 3))], none⟩ (e01, fun _ => e01) = _
  rw [foldExtract_concat _ _ _ _ _ _ _ 0 [] rfl]
  show (e01 - chalVal3 2 • e01, fun _ => e01) = _
  rw [show chalVal3 2 = 1 from by decide, one_smul, sub_self]

/-- **The extractor is NOT the identity**: on the honest proof string it returns a witness
different from the carried one. The proof type is `SrOutput`, not `W × (Fin T → W)`, so
"the proof is the witness" is already refused by the type; this is the stronger fact that
extraction does work. -/
theorem toy_srExtract_ne_id :
    srExtract (foldCarriedRbr toy 1 one_pos (Fin 3) chalVal3 0 toy_chalVal3_mem) 0
        toyHonestOut (fun i => twoOracle (toyHonestOut.query i)) []
      ≠ toyHonestOut.w' := by
  rw [toy_srExtract_eq]
  intro h
  have h0 := congrFun (congrArg Prod.fst h) 0
  exact absurd h0 (by decide)

theorem toySystem_knowledgeSound : KnowledgeSound toySystem :=
  carriedFsSystem_knowledgeSound toy 1 one_pos (Fin 3) chalVal3 0 toy_chalVal3_mem 0
    twoOracle

/-- **`rung_sound`, consumed at the toy**: every accepted FS proof string yields a proof the
decider of the relaxed genesis opening accepts. -/
theorem toy_rung (x : toySystem.Stmt) (π : toySystem.Proof)
    (hacc : toySystem.Verify x π = true) :
    ∃ πA, (relDecider toySystem).Verify x πA = true :=
  rung_sound (relDeciderEmbedding toySystem) toySystem_knowledgeSound x π hacc

/-- The rung, fired on the honest proof string. -/
theorem toy_rung_fired : ∃ πA, (relDecider toySystem).Verify toySt πA = true :=
  toy_rung toySt toyHonestOut toy_honest_accepted

end ToyFold

/-! ## Axiom audit -/

/-- info: 'Minidregg.Selvage.knowledgeSound_of_fs_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms knowledgeSound_of_fs_zero
/-- info: 'Minidregg.Selvage.fsKnowledgeSoundRO_of_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fsKnowledgeSoundRO_of_fs
/-- info: 'Minidregg.Selvage.rung_sound_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rung_sound_ro
/-- info: 'Minidregg.Selvage.accBcs_knowledgeSoundRO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accBcs_knowledgeSoundRO
/-- info: 'Minidregg.Selvage.AccRbrBcsExample.honest_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsExample.honest_accepted
/-- info: 'Minidregg.Selvage.AccRbrBcsExample.badOut_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsExample.badOut_rejected
/-- info: 'Minidregg.Selvage.AccRbrBcsExample.accBcsSystem_F5_not_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsExample.accBcsSystem_F5_not_knowledgeSound
/-- info: 'Minidregg.Selvage.AccRbrBcsExample.accBcsSystem_F5_knowledgeSoundRO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsExample.accBcsSystem_F5_knowledgeSoundRO
/-- info: 'Minidregg.Selvage.AccRbrBcsExample.rung_hypothesis_load_bearing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsExample.rung_hypothesis_load_bearing
/-- info: 'Minidregg.Selvage.carried_srExtract_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms carried_srExtract_sound
/-- info: 'Minidregg.Selvage.carriedFsSystem_knowledgeSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms carriedFsSystem_knowledgeSound
/-- info: 'Minidregg.Selvage.carriedFsSystem_knowledgeSound_of_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms carriedFsSystem_knowledgeSound_of_fs
/-- info: 'Minidregg.Selvage.carried_rung' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms carried_rung
/-- info: 'Minidregg.Selvage.ToyFold.toy_honest_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_honest_accepted
/-- info: 'Minidregg.Selvage.ToyFold.toy_bad_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_bad_rejected
/-- info: 'Minidregg.Selvage.ToyFold.toy_srExtract_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_srExtract_ne_id
/-- info: 'Minidregg.Selvage.ToyFold.toy_rung_fired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ToyFold.toy_rung_fired

end Minidregg.Selvage
