/-
# Selvage.AccRbrInstance — [ZK-RBR-game-resid]: the WARP-Def-4.2-NATIVE instance
for the accumulator chain, ASSEMBLED — `fs_composed` fires on the
accumulator's OWN instance.

`Selvage/ZkRbrGame.lean` closed the ZK-argument game packaging and named its one
packaging residual precisely: the literal
`Reduction`/`KStateFn`/`extract`/`RbrKnowledgeSoundness` quadruple for the
accumulator chain (`k = ch.length`, `Chal = F`, `err = accRbrError`) — the
object that lets `fs_composed`/`accFsSound` fire ON THE ACCUMULATOR ITSELF
rather than on a caller-supplied Def-4.2 instance. `Selvage/ZkExtraction.lean`
removed what blocked it (the extract target is the MASKED words, provably
sufficient and provably the only straightline-reachable resolution; the
counterfactual family is a function of one execution). This file builds the
quadruple:

* `accReduction` — the accumulator chain as a WARP `Reduction`: one round per
  fold step (`k = ch.length`), challenge alphabet `F` (the fold challenge),
  prover message = the round's word (the oracle message of the IOR — WARP
  Defs 4.1/4.2 are stated at the interactive-oracle-reduction resolution,
  BEFORE BCS compilation; queries are an efficiency measure `Reduction.verify`
  deliberately does not count). Source relation: the genesis claim holds of
  the implicit instance and the witness family witnesses every link
  THROUGH THE GENESIS CHANNEL (`LinkAligned` — an audit-grade finding, not a
  convenience: the aggregate keeps the genesis functionals at every depth
  (`aggregate_weights`), so `accSound_rbr`'s falseness package tests
  candidate link words through the RUNNING claim's weights; the naive
  per-link `Satisfies` source relation does NOT refine into the fold event
  without alignment. Under `Aligned A₀ ch` — the deployed post-alignment
  state — the two coincide, `linkAligned_iff_satisfies`). Target relation:
  the folded word satisfies the challenge-determined aggregate — word-level,
  as the accumulator's guarantee genuinely is (`W` threads the SOURCE side's
  link words; the aggregate is its own witness object).
* `accKState` — the Def-4.1 knowledge state function, three clauses PROVED:
  the state at a partial transcript is "the fold-so-far is δ-relaxedly
  satisfiable AND the remaining links are witnessed", which collapses to
  `R_{≤δ}` at the empty transcript (`empty_iff`), is pending-blind at partial
  transcripts (`prover_monotone` — the prover's dangling message changes
  nothing), and collapses to accept-with-`R'_{≤δ}` at the full transcript
  (`full_iff`, through `chainClaim_ofFn`/`chainWord_ofFn`).
* `accRbrKnowledgeSound` — the Def-4.2 instance, `extract_sound` PROVED: the
  round extractor peels the round's transcript word as the link witness,
  decoding it to a satisfying codeword at the fixed radius `δ⋆` when needed
  (δ-obliviously — Def 4.2 gives the extractor no δ input; the canonical
  radius is the reduction's own `δstar`, exactly the resolution
  `Selvage/AccSoundRbr.lean`'s audit prescribed). The per-round `∃ w`-event
  refines into the fold event: a surviving knowledge-state witness at the
  extended transcript forces the fold-so-far event, and the extractor's
  failure at the shorter transcript forces the falseness package `hfar` —
  either the previous fold was already δ-unsatisfiable (first component) or
  no codeword within δ of the round word satisfies the link (second
  component, through the decoder). `accSound_rbr` (CITED, not re-derived)
  then prices the round at `accRbrError F errstar δ = err⋆(δ) + 1/|F|` — the
  err field IS that function, no slack inserted.
* `accFsSound_native` — `FsOfRbrSound` applied to the native pair: the
  Fiat–Shamir compilation of the accumulator chain itself is straightline
  knowledge-sound at `(t + k)·accRbrError` — `accFsSound` (riding
  `fsKeystone_proved`, PROVED unconditionally) with `hbound := le_refl`.
  What `[ZK-RBR-game-resid]` owed is DISCHARGED at this resolution: the
  keystone `native_fs_fired` runs `zkRbrGame_F5.fs_composed` on
  `accReduction_F5`/`accRbr_F5` — the game's carrier field firing on the
  accumulator's own instance, where `game_fs_fired` could only offer Depth's
  trivial one.
* `accRbr_backward_masked` — the extract target is ZkExtraction's, on the
  nose: the full Construction-B.5 backward composition (`wAt`, seeded with
  ANY prover candidate) applied to an honest masked-chain transcript returns
  EXACTLY the masked word family — `srExtract` is `wAt` at 0 by `rfl`, and
  the F₅ keystone chains this with `zkRbrGame_F5.masked_exact` to equate the
  native extractor's output with `extractChain`'s.

The mutual-CA floor rides as hypotheses, exactly as in `accSound_rbr`: the
instance consumes `hdC`/`hMCA` with the δ-window pinned by
`δstar ≤ min(dC/2, 1−B⋆)` — landed witnesses at `C = ⊤`
(`minDistLB_inhabited`, `hasMutualCorrelatedAgreement_top_affine`, the F₅
keystones below); at the RS code and macroscopic δ the same package is the
standing `hPG` floor, consumed never claimed.

**Honest scope — what closes and what remains.** The Def-4.1/4.2 transcript
plumbing and the per-round `∃ w`-event refinement — the two bullets
`[ZK-RBR-game-resid]` named as the remaining real work — are CLOSED here at
the IOR resolution, with no sorry and no `Prop := True`. What this file does
NOT build is the BCS-resolution instance, named `[ACC-rbr-bcs]` at the
bottom: the `Reduction` whose `PMsg` is the DEPLOYED message alphabet
(recommitted root + opened columns), whose knowledge state demands
committed-column consistency, and whose extractor is `extractChain` composed
with `seamCounterfactual` through `binding_columns` — the object that would
make FS-of-the-deployed-protocol (hashing roots, not words) native. Its
algebra is landed (`extractChain_committed_seam`); its packaging is the
residual. Inherited unchanged: `[FS-ROM]`/`[COMMIT-CR]`/`hPG` and
`[ZK-RBR-extract]` open lemma A.

**Keystones** (F₅, landed objects REUSED): `accReduction_F5`/`accRbr_F5` —
the native instance BUILT on `goodChain` at `C = ⊤`, `δ⋆ = 1/16`, every floor
hypothesis discharged by landed witnesses; `native_state_alive` (the
knowledge state fires true on the honest genesis statement with the masked
witness family); `native_err_computes` (`err ≡ 1/5` on the nose, citing
`accRbrError_zero_five`); `native_extract_masked` + `native_extract_chain`
(the backward extraction returns the masked words exactly and coincides with
`extractChain`'s output, citing `masked_exact`); `native_fs_fired` (the
game's `fs_composed` on the native pair); `native_err_attained` (the round
bound met with equality on the landed adversarial fold — teeth, not slack);
`native_teeth_pair_barred` (the extractor's masked-word target is forced:
two distinct `(witness, mask)` families share one masked-word family, citing
`game_teeth_pair_invisible`'s realizer). No `sorry`, no vacuous
`Prop := True`.
-/
import Selvage.Rbr
import Selvage.Depth
import Selvage.FiatShamir
import Selvage.AccSoundRbr
import Selvage.ZkExtraction
import Selvage.ZkRbrGame

namespace Minidregg.Selvage

/-! ## Fold plumbing: snoc and schedule-congruence forms of the chain algebra

`aggregate`/`foldWords` (`Selvage/LightClient.lean`) recurse head-first with a
shifting schedule; the RBR game grows transcripts TAIL-first (one round
appended per challenge). These four lemmas are the bridge — pure list
algebra, nothing semantic. -/

section FoldPlumbing

variable {Root : Type*} {F : Type*} [Field F] {ι : Type*} {r : ℕ}
variable (foldRoot : Root → F → Root → Root)

/-- Appending one link to an aggregate folds it at schedule position
`ls.length` — the snoc form of `aggregate_cons`. -/
theorem aggregate_snoc (γs : ℕ → F) (A₀ : AccClaim Root F ι r)
    (ls : Chain Root F ι r) (l : Link Root F ι r) :
    aggregate foldRoot γs A₀ (ls ++ [l])
      = foldClaims foldRoot (aggregate foldRoot γs A₀ ls) l.claim
          (γs ls.length) := by
  induction ls generalizing γs A₀ with
  | nil => rfl
  | cons l' ls ih =>
    rw [List.cons_append, aggregate_cons, aggregate_cons, ih]
    rfl

/-- Appending one word to a fold adds it at schedule position `ws.length` —
the snoc form of `foldWords_cons`. -/
theorem foldWords_snoc (γs : ℕ → F) (f₀ : ι → F) (ws : List (ι → F))
    (w : ι → F) :
    foldWords γs f₀ (ws ++ [w]) = foldWords γs f₀ ws + γs ws.length • w := by
  induction ws generalizing γs f₀ with
  | nil => rfl
  | cons w' ws ih =>
    rw [List.cons_append, foldWords_cons, foldWords_cons, ih]
    rfl

/-- The aggregate reads the schedule only below the chain length. -/
theorem aggregate_congr_sched {γs γs' : ℕ → F} {A₀ : AccClaim Root F ι r}
    {ch : Chain Root F ι r} (h : ∀ j, j < ch.length → γs j = γs' j) :
    aggregate foldRoot γs A₀ ch = aggregate foldRoot γs' A₀ ch := by
  induction ch generalizing γs γs' A₀ with
  | nil => rfl
  | cons l ls ih =>
    rw [aggregate_cons, aggregate_cons, h 0 (by simp)]
    exact ih fun j hj => h (j + 1) (by simp only [List.length_cons]; omega)

/-- The word fold reads the schedule only below the word-list length. -/
theorem foldWords_congr_sched {γs γs' : ℕ → F} {f₀ : ι → F}
    {ws : List (ι → F)} (h : ∀ j, j < ws.length → γs j = γs' j) :
    foldWords γs f₀ ws = foldWords γs' f₀ ws := by
  induction ws generalizing γs γs' f₀ with
  | nil => rfl
  | cons w ws ih =>
    rw [foldWords_cons, foldWords_cons, h 0 (by simp)]
    exact ih fun j hj => h (j + 1) (by simp only [List.length_cons]; omega)

end FoldPlumbing

/-! ## Reading a transcript: schedule, running claim, running word

A round of the chain game is one `(word, challenge)` pair; a transcript
prefix `rs` determines the challenge schedule (`chainSched`), the claim
folded so far (`chainClaim` — `aggregate` over the chain prefix), and the
word folded so far (`chainWord` — `foldWords` over the sent words). -/

section TranscriptReads

/- `F : Type` (not `Type*`): matches `padSched`'s universe
(`Selvage/LightClientSound.lean`, the sampled-schedule discipline). -/
variable {Root : Type*} {F : Type} [Field F] {ι : Type*} {r : ℕ}
variable (foldRoot : Root → F → Root → Root)

/-- The challenge schedule a transcript prefix carries: coordinate `j` is
round `j`'s challenge, `0` above the transcript (never read). -/
def chainSched {P : Type*} (rs : List (P × F)) : ℕ → F :=
  fun j => (rs[j]?.map Prod.snd).getD 0

theorem chainSched_append_lt {P : Type*} (rs : List (P × F)) (e : P × F)
    {j : ℕ} (hj : j < rs.length) :
    chainSched (rs ++ [e]) j = chainSched rs j := by
  unfold chainSched
  rw [List.getElem?_append_left hj]

theorem chainSched_append_self {P : Type*} (rs : List (P × F)) (π : P)
    (ρ : F) : chainSched (rs ++ [(π, ρ)]) rs.length = ρ := by
  unfold chainSched
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

/-- On a function-shaped transcript the read-off schedule IS the padded
sampled schedule (`Selvage/LightClientSound.lean`'s `padSched`). -/
theorem chainSched_ofFn {P : Type*} {k : ℕ} (f : Fin k → P)
    (ρs : Fin k → F) :
    chainSched (List.ofFn fun i => (f i, ρs i)) = padSched ρs := by
  funext j
  unfold chainSched padSched
  by_cases hj : j < k
  · rw [List.getElem?_eq_getElem (by simpa using hj)]
    simp [hj]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj)]
    simp [hj]

/-- The claim folded so far: `aggregate` over the chain prefix matching the
transcript length, at the transcript's own schedule. -/
def chainClaim (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    (rs : List ((ι → F) × F)) : AccClaim Root F ι r :=
  aggregate foldRoot (chainSched rs) A₀ (ch.take rs.length)

/-- The word folded so far: `foldWords` over the sent words at the
transcript's own schedule. -/
def chainWord (f₀ : ι → F) (rs : List ((ι → F) × F)) : ι → F :=
  foldWords (chainSched rs) f₀ (rs.map Prod.fst)

@[simp] theorem chainClaim_nil (A₀ : AccClaim Root F ι r)
    (ch : Chain Root F ι r) : chainClaim foldRoot A₀ ch [] = A₀ := rfl

@[simp] theorem chainWord_nil (f₀ : ι → F) :
    chainWord f₀ ([] : List ((ι → F) × F)) = f₀ := rfl

/-- **The claim-side round transition**: one appended round folds the running
claim with the NEXT link's claim at the fresh challenge — `foldClaims` on the
nose, which is what lets `accSound_rbr` price the round. -/
theorem chainClaim_append (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    {rs : List ((ι → F) × F)} (π : ι → F) (ρ : F)
    (hlt : rs.length < ch.length) :
    chainClaim foldRoot A₀ ch (rs ++ [(π, ρ)])
      = foldClaims foldRoot (chainClaim foldRoot A₀ ch rs)
          (ch.get ⟨rs.length, hlt⟩).claim ρ := by
  unfold chainClaim
  have hlen : (rs ++ [(π, ρ)]).length = rs.length + 1 := by simp
  rw [hlen]
  have htake : ch.take (rs.length + 1)
      = ch.take rs.length ++ [ch.get ⟨rs.length, hlt⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt]
    rfl
  rw [htake, aggregate_snoc]
  rw [show (ch.take rs.length).length = rs.length from by
    rw [List.length_take]; omega]
  rw [chainSched_append_self]
  have hagg : aggregate foldRoot (chainSched (rs ++ [(π, ρ)])) A₀
        (ch.take rs.length)
      = aggregate foldRoot (chainSched rs) A₀ (ch.take rs.length) :=
    aggregate_congr_sched foldRoot fun j hj =>
      chainSched_append_lt rs (π, ρ) (by rw [List.length_take] at hj; omega)
  rw [hagg]

/-- **The word-side round transition**: one appended round moves the running
word by the challenge-weighted fresh word — the `f + γ • g` shape of the
fold. -/
theorem chainWord_append (f₀ : ι → F) (rs : List ((ι → F) × F))
    (π : ι → F) (ρ : F) :
    chainWord f₀ (rs ++ [(π, ρ)]) = chainWord f₀ rs + ρ • π := by
  unfold chainWord
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [foldWords_snoc]
  rw [show (rs.map Prod.fst).length = rs.length from by simp]
  rw [chainSched_append_self]
  have hw : foldWords (chainSched (rs ++ [(π, ρ)])) f₀ (rs.map Prod.fst)
      = foldWords (chainSched rs) f₀ (rs.map Prod.fst) :=
    foldWords_congr_sched fun j hj =>
      chainSched_append_lt rs (π, ρ) (by rw [List.length_map] at hj; exact hj)
  rw [hw]

/-- On the full function-shaped transcript the running claim is the verifier's
aggregate. -/
theorem chainClaim_ofFn (A₀ : AccClaim Root F ι r) (ch : Chain Root F ι r)
    (πs : Fin ch.length → ι → F) (ρs : Fin ch.length → F) :
    chainClaim foldRoot A₀ ch (List.ofFn fun i => (πs i, ρs i))
      = aggregate foldRoot (padSched ρs) A₀ ch := by
  unfold chainClaim
  rw [chainSched_ofFn]
  congr 1
  rw [List.length_ofFn, List.take_length]

/-- On the full function-shaped transcript the running word is the verifier's
fold. -/
theorem chainWord_ofFn (f₀ : ι → F) {k : ℕ} (πs : Fin k → ι → F)
    (ρs : Fin k → F) :
    chainWord f₀ (List.ofFn fun i => (πs i, ρs i))
      = foldWords (padSched ρs) f₀ (List.ofFn πs) := by
  unfold chainWord
  rw [chainSched_ofFn, List.map_ofFn]
  rfl

end TranscriptReads

/-! ## The distance bridge: Rbr's `fracHamming` IS `relDist` on `Fin m` -/

/-- `Selvage/Rbr.lean`'s `fracHamming` and `Selvage/CorrelatedAgreement.lean`'s
`relDist` are the same function on `Fin n → F` — the two files' δ-balls are
one δ-ball, so `RelaxedMem` and the mutual-CA package speak about the same
proximity. -/
theorem fracHamming_eq_relDist {F : Type} [DecidableEq F] {n : ℕ}
    (u v : Fin n → F) : fracHamming u v = relDist u v := by
  unfold fracHamming relDist
  rw [show Nat.card {i : Fin n // u i ≠ v i} = hammingDist u v from by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl]
  rw [Fintype.card_fin]

/-! ## `accReduction` — the accumulator chain in WARP's `Reduction` shape -/

section AccInstance

variable {Root : Type} {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {m r : ℕ}

/-- **Link satisfaction through the genesis channel** — the fold-faithful
link relation: the word is in the code and meets the link's TARGETS read
through the GENESIS claim's functionals. This is the only link relation the
fold channel can attest: the aggregate keeps the genesis accumulator's
functionals at every depth (`aggregate_weights`, `Selvage/LightClient.lean`),
so `accSound_rbr`'s falseness package tests candidate words through `A`'s
weights against `B`'s targets — exactly this relation. Under alignment
(`Aligned A₀ ch`, the deployed post-alignment state) it coincides with the
link's own satisfaction (`linkAligned_iff_satisfies`). -/
def LinkAligned (C : Submodule F (Fin m → F)) (A₀ : AccClaim Root F (Fin m) r)
    (ch : Chain Root F (Fin m) r) (k : Fin ch.length) (v : Fin m → F) :
    Prop :=
  v ∈ C ∧ ∀ j, A₀.weights j v = (ch.get k).claim.targets j

omit [Fintype F] [DecidableEq F] in
/-- Under alignment the aligned-channel link relation IS the link's own
satisfaction — the deployed regime, where the two readings coincide. -/
theorem linkAligned_iff_satisfies {C : Submodule F (Fin m → F)}
    {A₀ : AccClaim Root F (Fin m) r} {ch : Chain Root F (Fin m) r}
    (halign : Aligned A₀ ch) (k : Fin ch.length) (v : Fin m → F) :
    LinkAligned C A₀ ch k v ↔ AccClaim.Satisfies C (ch.get k).claim v := by
  have hw : ∀ j, (ch.get k).claim.weights j = A₀.weights j :=
    halign (ch.get k) (ch.get_mem k)
  unfold LinkAligned AccClaim.Satisfies
  constructor
  · rintro ⟨hv, ht⟩
    exact ⟨hv, fun j => by rw [hw j]; exact ht j⟩
  · rintro ⟨hv, ht⟩
    exact ⟨hv, fun j => by rw [← hw j]; exact ht j⟩

omit [Fintype F] [DecidableEq F] in
/-- The running claim's functionals are the genesis claim's, at every
transcript prefix — `aggregate_weights` (CITED) through `chainClaim`; the
fact that pins the extract-side falseness choreography to the aligned
channel. -/
theorem chainClaim_weights (foldRoot : Root → F → Root → Root)
    (A₀ : AccClaim Root F (Fin m) r) (ch : Chain Root F (Fin m) r)
    (rs : List ((Fin m → F) × F)) :
    (chainClaim foldRoot A₀ ch rs).weights = A₀.weights :=
  aggregate_weights foldRoot _ _ _

/-- **The accumulator chain as a WARP reduction** (Def-4.2's carrier shape,
`Selvage/Rbr.lean`): `k = ch.length` rounds — one per fold step — with challenge
alphabet `F` (the fold challenge) and prover message the round's word (the
IOR-resolution oracle message; the BCS root-and-columns alphabet is
`[ACC-rbr-bcs]`, module header). Statement: genesis claim `𝕩 = A₀`
(explicit), genesis word `𝕪 = f₀` (implicit, length `m` over `F`). Source
relation `R`: the genesis claim holds of the implicit instance and the
witness family `w` witnesses every link of `ch`. Target relation `R'`: the
folded word satisfies the challenge-determined aggregate — word-level (the
aggregate is its own witness object; `W` threads the source side). The
verifier folds and never rejects: soundness lives in the target relation and
the extraction game, exactly as in the deployed accumulator where the final
claim is handed onward to the one decider pass. -/
@[reducible] def accReduction (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) : Reduction where
  Idx := Unit
  X := AccClaim Root F (Fin m) r
  A := F
  X' := AccClaim Root F (Fin m) r
  A' := F
  W := Fin ch.length → Fin m → F
  n := m
  n' := m
  n_pos := hm
  n'_pos := hm
  R := fun _ A₀ f₀ w => AccClaim.Satisfies C A₀ f₀ ∧
    ∀ k : Fin ch.length, LinkAligned C A₀ ch k (w k)
  R' := fun _ Agg h _ => AccClaim.Satisfies C Agg h
  k := ch.length
  k_pos := hch
  PMsg := Fin m → F
  Chal := F
  pmsgNonempty := ⟨fun _ => 0⟩
  chalFintype := inferInstance
  chalNonempty := ⟨0⟩
  δstar := δs
  δstar_pos := hδpos
  δstar_le_one := hδone
  verify := fun _ A₀ f₀ πs ρs =>
    some (aggregate foldRoot (padSched ρs) A₀ ch,
      foldWords (padSched ρs) f₀ (List.ofFn πs))

/-! ## The knowledge state: fold-so-far δ-satisfiable + remaining links
witnessed -/

/-- The fold-so-far obligation of the knowledge state: the running word is
within δ of some word satisfying the running claim — the SAME event shape
`accSound_rbr` bounds per round, at the transcript's own prefix. -/
def FoldTracks (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (δ : ℝ) (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (rs : List ((Fin m → F) × F)) : Prop :=
  ∃ w', relDist (chainWord f₀ rs) w' ≤ δ ∧
    AccClaim.Satisfies C (chainClaim foldRoot A₀ ch rs) w'

/-- The remaining-links obligation: the knowledge-state witness still
witnesses (through the genesis channel) every link the transcript has not
folded yet. -/
def RemWitnessed (C : Submodule F (Fin m → F))
    (A₀ : AccClaim Root F (Fin m) r) (ch : Chain Root F (Fin m) r) (n : ℕ)
    (w : Fin ch.length → Fin m → F) : Prop :=
  ∀ k : Fin ch.length, n ≤ (k : ℕ) → LinkAligned C A₀ ch k (w k)

omit [Fintype F] [DecidableEq F] in
/-- Above the chain length the remaining-links obligation is vacuous — the
full transcript owes nothing to the witness, matching Def 4.1's third clause
(the target relation is word-level). -/
theorem remWitnessed_of_length_le {C : Submodule F (Fin m → F)}
    {A₀ : AccClaim Root F (Fin m) r} {ch : Chain Root F (Fin m) r} {n : ℕ}
    (h : ch.length ≤ n) (w : Fin ch.length → Fin m → F) :
    RemWitnessed C A₀ ch n w :=
  fun k hk => absurd (lt_of_lt_of_le k.isLt (le_trans h hk)) (lt_irrefl _)

/-- The knowledge-state proposition, all transcript shapes at once: the
fold-so-far tracks, and EITHER the transcript is full (word-level target, no
witness obligation) OR the witness carries the remaining links. Junk shapes
(overlong transcripts, dangling messages on full ones) fall through the
second disjunct harmlessly — Def 4.1 constrains them only through
`prover_monotone`, which the pending-blind design satisfies by reflexivity. -/
def AccStateProp (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (δ : ℝ) (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (rs : List ((Fin m → F) × F)) (pend : Option (Fin m → F))
    (w : Fin ch.length → Fin m → F) : Prop :=
  FoldTracks C foldRoot ch δ A₀ f₀ rs ∧
    ((rs.length = ch.length ∧ pend = none) ∨
      RemWitnessed C A₀ ch rs.length w)

/-! ## The round extractor: peel the word, decode at the canonical radius -/

open Classical in
/-- The link decoder at fixed radius `ρ₀`: return the round's word itself
when it already witnesses the link through the genesis channel (the honest
masked case — `mask_sat_of_ker` makes masked words witnesses, and this branch
is what makes the backward extraction EXACT on honest masked transcripts);
otherwise classically choose an aligned-channel witness within `ρ₀` if one
exists. δ-oblivious: the radius is the reduction's `δstar`, fixed once —
exactly the canonical-radius resolution `Selvage/AccSoundRbr.lean`'s audit
prescribed for Def 4.2's δ-free extractor. -/
noncomputable def decodeLink (C : Submodule F (Fin m → F))
    (A₀ : AccClaim Root F (Fin m) r) (ch : Chain Root F (Fin m) r) (ρ₀ : ℝ)
    (k : Fin ch.length) (π : Fin m → F) : Fin m → F :=
  if LinkAligned C A₀ ch k π then π
  else if h : ∃ v, LinkAligned C A₀ ch k v ∧ relDist π v ≤ ρ₀
    then h.choose
  else π

theorem decodeLink_sat (C : Submodule F (Fin m → F))
    (A₀ : AccClaim Root F (Fin m) r) (ch : Chain Root F (Fin m) r) (ρ₀ : ℝ)
    (k : Fin ch.length) (π : Fin m → F)
    (h : ∃ v, LinkAligned C A₀ ch k v ∧ relDist π v ≤ ρ₀) :
    LinkAligned C A₀ ch k (decodeLink C A₀ ch ρ₀ k π) := by
  unfold decodeLink
  by_cases h1 : LinkAligned C A₀ ch k π
  · rwa [if_pos h1]
  · rw [if_neg h1, dif_pos h]
    exact h.choose_spec.1

/-- On a word that already witnesses the link the decoder is the identity —
the branch that keeps honest masked extraction exact. -/
theorem decodeLink_of_sat {C : Submodule F (Fin m → F)}
    {A₀ : AccClaim Root F (Fin m) r} {ch : Chain Root F (Fin m) r} (ρ₀ : ℝ)
    {k : Fin ch.length} {π : Fin m → F} (h : LinkAligned C A₀ ch k π) :
    decodeLink C A₀ ch ρ₀ k π = π := by
  unfold decodeLink
  rw [if_pos h]

/-- **The Def-4.2 round extractor**: read the extended transcript's LAST
prover message — the round's word — and install its decoding as the round's
link witness; everything else passes through. Straightline and δ-oblivious:
a pure function of the statement, the transcript, and the incoming
witness. -/
noncomputable def accExtract (C : Submodule F (Fin m → F))
    (A₀ : AccClaim Root F (Fin m) r) (ch : Chain Root F (Fin m) r) (ρ₀ : ℝ)
    (tr : Transcript (Fin m → F) F) (w : Fin ch.length → Fin m → F) :
    Fin ch.length → Fin m → F :=
  tr.rounds.getLast?.elim w fun e =>
    if h : tr.rounds.length - 1 < ch.length then
      Function.update w ⟨tr.rounds.length - 1, h⟩
        (decodeLink C A₀ ch ρ₀ ⟨tr.rounds.length - 1, h⟩ e.1)
    else w

/-- The extractor on a one-round extension, in closed form. -/
theorem accExtract_append (C : Submodule F (Fin m → F))
    (A₀ : AccClaim Root F (Fin m) r) (ch : Chain Root F (Fin m) r) (ρ₀ : ℝ)
    {rs : List ((Fin m → F) × F)} {j : ℕ} (hj : rs.length = j)
    (hlt : j < ch.length) (π : Fin m → F) (ρ : F)
    (w : Fin ch.length → Fin m → F) :
    accExtract C A₀ ch ρ₀ ⟨rs ++ [(π, ρ)], none⟩ w
      = Function.update w ⟨j, hlt⟩ (decodeLink C A₀ ch ρ₀ ⟨j, hlt⟩ π) := by
  subst hj
  unfold accExtract
  rw [List.getLast?_concat]
  have h1 : (rs ++ [(π, ρ)]).length - 1 = rs.length := by simp
  simp only [Option.elim_some, h1]
  rw [dif_pos hlt]

/-! ## `accKState` — Def 4.1's three clauses, PROVED -/

open Classical in
/-- **The knowledge state function for the accumulator chain** (WARP Def 4.1,
`Selvage/Rbr.lean`'s `KStateFn`): the classical bit of `AccStateProp`. The three
clauses are proved outright: `empty_iff` (the state at the empty transcript
IS `R_{≤δ}` — fold-so-far collapses to the genesis pair, remaining links to
all links, through the `fracHamming = relDist` bridge), `prover_monotone`
(the state never reads the dangling message: partial-shape state is
pending-blind, so doom is preserved by reflexivity), `full_iff` (the state at
the full transcript IS accept-with-`R'_{≤δ}` — the verifier is total and the
running claim/word equal its aggregate/fold by `chainClaim_ofFn`/
`chainWord_ofFn`). -/
noncomputable def accKState (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) :
    KStateFn (accReduction C foldRoot ch hm hch δs hδpos hδone) where
  state := fun δ st tr w =>
    decide (AccStateProp C foldRoot ch δ st.x st.y tr.rounds tr.pending w)
  empty_iff := by
    intro δ hδ st w
    simp only [Transcript.empty, decide_eq_true_eq]
    unfold AccStateProp RelaxedMem
    constructor
    · rintro ⟨⟨w', hd, hs⟩, hrest⟩
      have hrem : ∀ k : Fin ch.length, LinkAligned C st.x ch k (w k) := by
        rcases hrest with ⟨h0, -⟩ | hrem
        · exact absurd h0 (Nat.ne_of_lt hch)
        · exact fun k => hrem k (Nat.zero_le _)
      refine ⟨w', ⟨hs, hrem⟩, ?_⟩
      rw [fracHamming_eq_relDist]
      exact hd
    · rintro ⟨ystar, ⟨hsat, hlinks⟩, hdist⟩
      rw [fracHamming_eq_relDist] at hdist
      exact ⟨⟨ystar, hdist, hsat⟩, Or.inr fun k _ => hlinks k⟩
  prover_monotone := by
    intro δ hδ st rs w hlen h π
    rw [decide_eq_false_iff_not] at h ⊢
    intro hP
    apply h
    obtain ⟨hfold, hrest⟩ := hP
    refine ⟨hfold, ?_⟩
    rcases hrest with ⟨-, hpend⟩ | hrem
    · exact absurd hpend (by simp)
    · exact Or.inr hrem
  full_iff := by
    intro δ hδ st πs ρs w
    simp only [Transcript.ofFull, decide_eq_true_eq]
    unfold AccStateProp
    have hlen : (List.ofFn fun i => (πs i, ρs i)).length = ch.length := by
      simp
    constructor
    · rintro ⟨hfold, -⟩
      refine ⟨aggregate foldRoot (padSched ρs) st.x ch,
        foldWords (padSched ρs) st.y (List.ofFn πs), rfl, ?_⟩
      obtain ⟨w', hd, hs⟩ := hfold
      refine ⟨w', ?_, ?_⟩
      · rwa [chainClaim_ofFn] at hs
      · rw [fracHamming_eq_relDist]
        rwa [chainWord_ofFn] at hd
    · rintro ⟨x', y', heq, hrel⟩
      have heq' : (aggregate foldRoot (padSched ρs) st.x ch,
          foldWords (padSched ρs) st.y (List.ofFn πs)) = (x', y') :=
        Option.some.inj heq
      obtain ⟨hx, hy⟩ := Prod.mk.injEq .. ▸ heq'
      subst hx
      subst hy
      obtain ⟨ystar, hsat, hdist⟩ := hrel
      refine ⟨⟨ystar, ?_, ?_⟩, Or.inl ⟨hlen, rfl⟩⟩
      · rw [chainWord_ofFn, ← fracHamming_eq_relDist]
        exact hdist
      · rw [chainClaim_ofFn]
        exact hsat

open Classical in
/-- The state, unfolded — the shape every proof below manipulates. -/
theorem accKState_state_eq (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (δ : ℝ)
    (st : Stmt (accReduction C foldRoot ch hm hch δs hδpos hδone))
    (tr : Transcript (Fin m → F) F) (w : Fin ch.length → Fin m → F) :
    (accKState C foldRoot ch hm hch δs hδpos hδone).state δ st tr w
      = decide (AccStateProp C foldRoot ch δ st.x st.y tr.rounds tr.pending
          w) := rfl

/-! ## `accRbrKnowledgeSound` — the Def-4.2 instance, `extract_sound` PROVED -/

/-- **The native Def-4.2 instance for the accumulator chain** (WARP Def 4.2,
`Selvage/Rbr.lean`'s `RbrKnowledgeSoundness`) — `[ZK-RBR-game-resid]`'s owed
quadruple, assembled: `kstate = accKState`, `extract = accExtract` (peel the
round's word, decode at the canonical radius `δ⋆`), `err = accRbrError`
(`Selvage/AccSoundRbr.lean`'s proved round price, the SAME function — no slack
inserted), and `extract_sound` PROVED by refining the per-round `∃ w`-event
into the fold event `accSound_rbr` bounds:

* a knowledge-state witness alive at the EXTENDED transcript carries the
  fold-so-far event at the fresh challenge (`chainWord_append`/
  `chainClaim_append` rewrite it into `accSound_rbr`'s exact event shape);
* the extractor's output dead at the SHORTER transcript forces the falseness
  package `hfar` — either the previous fold was already δ-unsatisfiable
  (`hfar`'s accumulator component) or the decoder found no satisfying word
  within `δ⋆ ≥ δ` of the round word (`hfar`'s link component);
* when neither doom holds the event is EMPTY: the alive witness's remaining
  links plus the decoder's success rebuild the shorter state.

The mutual-CA floor (`hdC`, `hMCA`) and the δ-window pins
(`δ⋆ ≤ 1 − B⋆`, `δ⋆ ≤ dC/2`) ride as hypotheses exactly as in
`accSound_rbr` — landed witnesses at `C = ⊤`; the standing `hPG` at RS with
macroscopic δ. Nothing is re-derived: the probability bound is
`accSound_rbr` verbatim. -/
noncomputable def accRbrKnowledgeSound (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) {dC Bstar : ℝ} (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ) :
    RbrKnowledgeSoundness (accReduction C foldRoot ch hm hch δs hδpos hδone)
    where
  kstate := accKState C foldRoot ch hm hch δs hδpos hδone
  extract := fun st tr w => accExtract C st.x ch δs tr w
  err := fun _i _st δ => accRbrError F errstar δ
  extractTime := fun _ => 0
  extract_sound := by
    classical
    intro δ hδ st i rs hlen π
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hi : rs.length < ch.length := by
      rw [hlen]
      exact i.isLt
    have hδB : δ < 1 - Bstar := lt_of_lt_of_le hδ.2 hBstar
    have hδC : δ < dC / 2 := lt_of_lt_of_le hδ.2 hdC2
    -- the alive fold conjunct IS the accSound_rbr event, via the round
    -- transitions
    have hstep : ∀ ρ : F,
        FoldTracks C foldRoot ch δ st.x st.y (rs ++ [(π, ρ)]) ↔
          ∃ w', relDist (chainWord st.y rs + ρ • π) w' ≤ δ ∧
            AccClaim.Satisfies C
              (foldClaims foldRoot (chainClaim foldRoot st.x ch rs)
                (ch.get ⟨rs.length, hi⟩).claim ρ) w' := by
      intro ρ
      unfold FoldTracks
      rw [chainWord_append, chainClaim_append foldRoot st.x ch π ρ hi]
    by_cases hdoom : FoldTracks C foldRoot ch δ st.x st.y rs ∧
        LinkAligned C st.x ch ⟨rs.length, hi⟩
          (decodeLink C st.x ch δs ⟨rs.length, hi⟩ π)
    · -- no doom: the round event is EMPTY — the alive witness rebuilds the
      -- shorter state through the decoder
      refine le_trans (le_of_eq (uniformProb_false fun ρ hev => ?_))
        (accRbrError_nonneg (hstar δ hδ))
      obtain ⟨w, hdead, halive⟩ := hev
      rw [accKState_state_eq, decide_eq_true_eq] at halive
      rw [accKState_state_eq, decide_eq_false_iff_not] at hdead
      have halive' : AccStateProp C foldRoot ch δ st.x st.y (rs ++ [(π, ρ)])
          none w := halive
      apply hdead
      show AccStateProp C foldRoot ch δ st.x st.y rs (some π)
        (accExtract C st.x ch δs ⟨rs ++ [(π, ρ)], none⟩ w)
      refine ⟨hdoom.1, Or.inr ?_⟩
      rw [accExtract_append C st.x ch δs rfl hi π ρ w]
      intro k hk
      rcases eq_or_ne k (⟨rs.length, hi⟩ : Fin ch.length) with rfl | hne
      · rw [Function.update_self]
        exact hdoom.2
      · rw [Function.update_of_ne hne]
        have hkch : (k : ℕ) < ch.length := k.isLt
        have hkv : (k : ℕ) ≠ rs.length := fun hc => hne (Fin.ext hc)
        have hlen1 : (rs ++ [(π, ρ)]).length = rs.length + 1 := by simp
        rcases halive'.2 with ⟨hfull, -⟩ | hrem
        · rw [hlen1] at hfull
          omega
        · refine hrem k ?_
          rw [hlen1]
          omega
    · -- doom: the event refines into the fold event, priced by accSound_rbr
      have hfar : ∀ u ∈ C, ∀ v ∈ C,
          relDist (chainWord st.y rs) u ≤ δ → relDist π v ≤ δ →
          ∃ j, ¬((chainClaim foldRoot st.x ch rs).weights j u
              = (chainClaim foldRoot st.x ch rs).targets j ∧
            (chainClaim foldRoot st.x ch rs).weights j v
              = (ch.get ⟨rs.length, hi⟩).claim.targets j) := by
        intro u hu v hv hfu hgv
        by_contra hcon
        push Not at hcon
        rcases not_and_or.mp hdoom with hnF | hnD
        · exact hnF ⟨u, hfu, hu, fun j => (hcon j).1⟩
        · refine hnD (decodeLink_sat C st.x ch δs ⟨rs.length, hi⟩ π
            ⟨v, ⟨hv, fun j => ?_⟩, le_trans hgv hδ.2.le⟩)
          have hj := (hcon j).2
          rwa [congrFun (chainClaim_weights foldRoot st.x ch rs) j] at hj
      have hsound := accSound_rbr (C := C) foldRoot hdC hMCA hδ.1 hδB hδC hfar
      refine le_trans (uniformProb_mono ?_) hsound
      rintro ρ ⟨w, -, halive⟩
      rw [accKState_state_eq, decide_eq_true_eq] at halive
      exact (hstep ρ).mp halive.1

/-! ## The extract target is ZkExtraction's: masked words, exactly -/

/-- **The full backward extraction returns the masked words, exactly** —
Construction B.5 (`Selvage/Depth.lean`'s `wAt`, `w_k := w'` seed, one
`accExtract` peel per round, output `w_0`) applied to any transcript whose
round words all witness their links (the honest MASKED transcripts:
`mask_sat_of_ker` makes homogeneous-masked words witnesses) returns the sent
word family on the nose, for EVERY seed `w'` — the extract field realizes
`[ZK-RBR-game-resid]`'s fixed target (the masked words, not the provably
unreachable `(witness, mask)` pairs), at arbitrary depth. The decoder's
identity branch is what makes this exact rather than merely satisfying. -/
theorem accRbr_backward_masked (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) {dC Bstar : ℝ} (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    (st : Stmt (accReduction C foldRoot ch hm hch δs hδpos hδone))
    (ms : Fin ch.length → Fin m → F) (γv : Fin ch.length → F)
    (hms : ∀ k, LinkAligned C st.x ch k (ms k))
    (w' : Fin ch.length → Fin m → F) :
    wAt (accRbrKnowledgeSound C foldRoot ch hm hch δs hδpos hδone errstar
        hdC hMCA hBstar hdC2 hstar) st
      (List.ofFn fun k => (ms k, γv k)) w' 0 = fun k => ms k := by
  set rbrI := accRbrKnowledgeSound C foldRoot ch hm hch δs hδpos hδone
    errstar hdC hMCA hBstar hdC2 hstar with hrbrI
  set L : List ((Fin m → F) × F) :=
    List.ofFn fun k : Fin ch.length => (ms k, γv k) with hL
  have hLlen : L.length = ch.length := by simp [hL]
  have key : ∀ dd ii, ii + dd = ch.length →
      wAt rbrI st L w' ii
        = fun k : Fin ch.length => if ii ≤ (k : ℕ) then ms k else w' k := by
    intro dd
    induction dd with
    | zero =>
      intro ii hii
      rw [wAt_of_le rbrI st L w' (by omega : L.length ≤ ii)]
      funext k
      rw [if_neg (by have := k.isLt; omega)]
    | succ dd ih =>
      intro ii hii
      have hiilt : ii < ch.length := by omega
      rw [wAt_of_lt rbrI st L w' (by rw [hLlen]; exact hiilt)]
      rw [ih (ii + 1) (by omega)]
      have htake : L.take (ii + 1)
          = L.take ii ++ [(ms ⟨ii, hiilt⟩, γv ⟨ii, hiilt⟩)] := by
        rw [List.take_add_one,
          List.getElem?_eq_getElem (by rw [hLlen]; exact hiilt)]
        simp [hL]
      rw [htake]
      have htlen : (L.take ii).length = ii := by
        rw [List.length_take]
        omega
      have hex : rbrI.extract st
            ⟨L.take ii ++ [(ms ⟨ii, hiilt⟩, γv ⟨ii, hiilt⟩)], none⟩
            (fun k : Fin ch.length => if ii + 1 ≤ (k : ℕ) then ms k else w' k)
          = Function.update
              (fun k : Fin ch.length => if ii + 1 ≤ (k : ℕ) then ms k
                else w' k)
              ⟨ii, hiilt⟩
              (decodeLink C st.x ch δs ⟨ii, hiilt⟩ (ms ⟨ii, hiilt⟩)) :=
        accExtract_append C st.x ch δs htlen hiilt _ _ _
      rw [hex, decodeLink_of_sat δs (hms _)]
      funext k
      rcases eq_or_ne k (⟨ii, hiilt⟩ : Fin ch.length) with rfl | hne
      · rw [Function.update_self, if_pos (le_refl _)]
      · rw [Function.update_of_ne hne]
        have hkv : (k : ℕ) ≠ ii := fun hc => hne (Fin.ext hc)
        by_cases hk : ii + 1 ≤ (k : ℕ)
        · rw [if_pos hk, if_pos (by omega)]
        · rw [if_neg hk, if_neg (by omega)]
  rw [key ch.length 0 (by omega)]
  funext k
  rw [if_pos (Nat.zero_le _)]

/-! ## `accFsSound_native` — FS-composed soundness ON the accumulator -/

/-- **[ZK-RBR-game-resid] discharged at the IOR resolution**: the Fiat–Shamir
compilation of the accumulator chain's OWN reduction is straightline
knowledge-sound at the `(t + k)·accRbrError` grinding factor — `accFsSound`
(`Selvage/AccSoundRbr.lean`, riding `fsKeystone_proved`'s unconditional
`FsOfRbrSound`) applied to the NATIVE pair, with `hbound := le_refl` because
the instance's `err` IS `accRbrError`. Where `accFsSound`'s `red`/`rbr`/
`hbound` premises were caller-supplied, they are now BUILT — this is the
sentence `selvage_zk_argument`'s `fs_composed` field owed. Scope: the IOR-level
message alphabet (full round words; the BCS root-and-columns alphabet is
`[ACC-rbr-bcs]`), the mutual-CA floor as hypotheses, and the pessimistic
proved numbers `(t + ch.length)·(err⋆(δ) + 1/|F|)` — nothing sharper is
claimed. -/
theorem accFsSound_native (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) {dC Bstar : ℝ} (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    (Z : Set (Stmt (accReduction C foldRoot ch hm hch δs hδpos hδone))) :
    FsStraightlineKnowledgeSoundness
      (accReduction C foldRoot ch hm hch δs hδpos hδone) Z
      (fun _s t δ => ((t : ℝ) + (ch.length : ℝ))
        * accRbrError F errstar δ) :=
  accFsSound (accReduction C foldRoot ch hm hch δs hδpos hδone)
    (accRbrKnowledgeSound C foldRoot ch hm hch δs hδpos hδone errstar hdC
      hMCA hBstar hdC2 hstar)
    Z F errstar hstar (fun _i _st _hst _δ _hδ => le_refl _)

end AccInstance

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

The native instance BUILT and FIRED on the landed F₅ chain: `goodChain` at
`C = ⊤` (where the mutual-CA package is landed exactly:
`hasMutualCorrelatedAgreement_top_affine` with `err⋆ ≡ 0`,
`minDistLB_inhabited` with `dC = 1/4`), `δ⋆ = 1/16` — the SAME δ-window the
landed `accSound_rbr_fired` keystone runs in. At the RS code and macroscopic
δ the identical package is the standing `hPG` floor, consumed never
claimed. -/

namespace AccRbrInstanceExample

open RSExample AccExample LCExample ZkHidingExample ZkArgumentExample
  AccExtractChainExample RbrZkExample ZkExtractionExample AccSoundRbrExample
  ZkRbrGameExample

/-- **The native reduction, BUILT** on the landed F₅ chain: `k = 2` rounds,
`Chal = ZMod 5`, statement = (genesis claim, genesis word). -/
noncomputable def accReduction_F5 : Reduction :=
  accReduction (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)

/-- **The native Def-4.2 instance, BUILT — satisfiable**: every hypothesis
discharged by a landed witness (`minDistLB_inhabited` for the minimum
distance, `hasMutualCorrelatedAgreement_top_affine` for the mutual-CA
package, arithmetic for the δ-window pins). The reduction, the knowledge
state, the extractor, and the `accRbrError` price all fire on this one
object below. -/
noncomputable def accRbr_F5 : RbrKnowledgeSoundness accReduction_F5 :=
  accRbrKnowledgeSound (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
    goodChain (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    (fun _ => 0) (minDistLB_inhabited _)
    hasMutualCorrelatedAgreement_top_affine
    (by
      rw [Fintype.card_fin, max_eq_left (by norm_num)]
      norm_num)
    (by
      rw [Fintype.card_fin]
      norm_num)
    (fun _ _ => le_refl 0)

/-- The genesis statement of the native game: index trivial, explicit
instance the landed genesis claim, implicit instance the landed genesis
word. -/
noncomputable def st_F5 : Stmt accReduction_F5 := ⟨(), genesis, xWord⟩

/-- The masked witness family witnesses the chain at `C = ⊤`: membership is
trivial and the channel computation is the landed `mask_sat_of_ker` (masks
are channel-killed, CITED). -/
theorem msEx_sat_top (k : Fin 2) :
    AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      ((goodChain.get k).claim) (msEx k) :=
  ⟨Submodule.mem_top,
    (mask_sat_of_ker (γbase (k : ℕ)) (wsEx_sat k) (gsEx_mem k)
      (gsEx_ker k)).2⟩

/-- The masked witnesses through the GENESIS channel — the aligned-channel
form the native source relation carries; the bridge fires because the landed
chain is aligned (`goodChain_aligned`, CITED). -/
theorem msEx_linkAligned (k : Fin 2) :
    LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) genesis goodChain
      k (msEx k) :=
  (linkAligned_iff_satisfies goodChain_aligned k (msEx k)).mpr
    (msEx_sat_top k)

/-- **The knowledge state fires TRUE** on the honest genesis statement with
the masked witness family at the empty transcript — the state is inhabited,
not vacuously false: `empty_iff`'s `R_{≤δ}` clause discharged by the landed
`genesis_satisfied` (weakened to `⊤`) and the masked links. -/
theorem native_state_alive :
    accRbr_F5.kstate.state (1 / 32) st_F5 Transcript.empty
      (fun k => msEx k) = true := by
  refine (accRbr_F5.kstate.empty_iff (1 / 32)
    (by
      rw [Set.mem_Ioo]
      exact ⟨by norm_num, by show (1 : ℝ) / 32 < 1 / 16; norm_num⟩) st_F5
    (fun k => msEx k)).mpr ?_
  refine ⟨xWord, ⟨⟨Submodule.mem_top, genesis_satisfied.2⟩,
    fun k => msEx_linkAligned k⟩, ?_⟩
  show fracHamming xWord xWord ≤ 1 / 32
  rw [fracHamming_self]
  norm_num

/-- **The err field computes**: the native instance's per-round price is
`1/5` at every round, statement, and δ — `accRbrError_zero_five` (CITED)
through the instance. -/
theorem native_err_computes (i : Fin accReduction_F5.k)
    (st : Stmt accReduction_F5) (δ : ℝ) :
    accRbr_F5.err i st δ = 1 / 5 :=
  accRbrError_zero_five δ

/-- **The err bound is ATTAINED — teeth**: the landed adversarial fold
(`accSound_rbr_exact_attained`, CITED) meets the native instance's round
price with EQUALITY — `accRbrError` is not slack for the instance that
carries it. -/
theorem native_err_attained (i : Fin accReduction_F5.k) :
    uniformProb (ZMod 5) (fun γ =>
        AccClaim.Satisfies (reedSolomonCode dom₅ 2)
          (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • 0))
      = accRbr_F5.err i st_F5 0 :=
  accSound_rbr_exact_attained

/-- **The backward extraction, fired**: `wAt` (Construction B.5) on the
honest masked transcript of `goodChain` returns EXACTLY the masked word
family, for every seed — the native extract field hitting ZkExtraction's
fixed target on the landed instance. -/
theorem native_extract_masked (w' : Fin 2 → Fin 4 → ZMod 5) :
    wAt accRbr_F5 st_F5 (List.ofFn fun k => (msEx k, γbase (k : ℕ))) w' 0
      = fun k => msEx k :=
  accRbr_backward_masked _ _ _ _ _ _ _ _ _ _ _ _ _ _ st_F5 msEx
    (fun k => γbase (k : ℕ)) msEx_linkAligned w'

/-- The FS-level straightline extractor IS the backward composition — WARP
Construction B.5 verbatim, by definition. -/
example (s : ℕ) (o : SrOutput accReduction_F5 s)
    (ρs : Fin accReduction_F5.k → accReduction_F5.Chal)
    (log : List (SrMove accReduction_F5 s × accReduction_F5.Chal)) :
    srExtract accRbr_F5 s o ρs log
      = wAt accRbr_F5 o.stmt (List.ofFn fun i => (o.πs i, ρs i)) o.w' 0 :=
  rfl

/-- **The native extractor coincides with `extractChain`** on the honest
masked family — the game's `masked_exact` field (`zkRbrGame_F5`, CITED) and
the native backward extraction produce the SAME list: the extract field is a
genuine wrapper of the landed chain extraction, not a lookalike. -/
theorem native_extract_chain (w' : Fin 2 → Fin 4 → ZMod 5) :
    List.ofFn (wAt accRbr_F5 st_F5
        (List.ofFn fun k => (msEx k, γbase (k : ℕ))) w' 0)
      = extractChain γbase γalt₂ (flatFold γbase xWord msEx)
          (fun k : Fin 2 => flatFold (updSched γbase γalt₂ k) xWord msEx) := by
  rw [native_extract_masked]
  exact (zkRbrGame_F5.masked_exact xWord wsEx gsEx).symm

/-- **THE RESIDUAL'S SENTENCE — `fs_composed` fires on the accumulator's OWN
instance**: the assembled game's Fiat–Shamir carrier field
(`zkRbrGame_F5.fs_composed`) applied to `accReduction_F5`/`accRbr_F5` — the
native pair, not Depth's trivial stand-in — yields straightline FS knowledge
soundness for the accumulator chain itself at the `(t + k)·accRbrError`
factor (`= (t + 2)·(1/5)` here, `native_err_computes`). Compare the landed
`game_fs_fired`, which could only fire the carrier on `trivialReduction` and
said so; this is the discharge `[ZK-RBR-game-resid]` named. -/
theorem native_fs_fired :
    FsStraightlineKnowledgeSoundness accReduction_F5 Set.univ
      (fun _s b δ => ((b : ℝ) + (accReduction_F5.k : ℝ))
        * accRbrError (ZMod 5) (fun _ => 0) δ) :=
  zkRbrGame_F5.fs_composed accReduction_F5 accRbr_F5 Set.univ (fun _ => 0)
    (fun _ _ => le_refl 0) (fun _i _st _ _δ _ => le_refl _)

/-- **Teeth — the masked-word target is forced, on the game's own witness
data**: two DISTINCT `(witness, mask)` families with the SAME masked words
(realizer from `game_teeth_pair_invisible`, CITED) — no straightline
extractor reading the honest execution, this file's included, can output the
pair; the native extract field's masked-word resolution is the theorem-backed
choice, not a concession. -/
theorem native_teeth_pair_barred :
    ∃ p₁ p₂ : (Fin 2 → Fin 4 → ZMod 5) × (Fin 2 → Fin 4 → ZMod 5),
      p₁ ≠ p₂ ∧ maskedWord γbase p₁.1 p₁.2 = maskedWord γbase p₂.1 p₂.2 := by
  obtain ⟨ws', gs', hne, -, -, heq, -⟩ := game_teeth_pair_invisible
  exact ⟨(ws', gs'), (wsEx, gsEx), hne, heq⟩

end AccRbrInstanceExample

/-! ## Residual obligation — prose, not a stub

**What CLOSED here.** `[ZK-RBR-game-resid]` named two pieces of remaining
real work: (1) the Def-4.1 transcript plumbing — encode the chain game in
`Reduction`'s shape and exhibit a `KStateFn` honoring the three clauses; and
(2) the per-round `extract_sound` refinement — the `∃ w`-event over
knowledge states refining into the fold event `accSound_rbr` bounds. BOTH
are closed at the IOR resolution: `accReduction`/`accKState`/
`accRbrKnowledgeSound` are built with every clause and the round bound
PROVED (`accSound_rbr` cited for the number, never re-derived), and
`accFsSound_native`/`native_fs_fired` run the FS carrier on the native pair.
The extract target is ZkExtraction's fixed one — the masked words
(`accRbr_backward_masked` + `native_extract_chain`), with the pair
resolution barred by the landed ambiguity teeth.

**`[ACC-rbr-bcs]`** — what remains, stated precisely. This file's `PMsg` is
the round's FULL word: the interactive-oracle-reduction resolution, which is
exactly where WARP states Defs 4.1/4.2 and where `FsOfRbrSound` consumes its
instances (the SR game salts and hashes prover messages). The DEPLOYED
protocol hashes commitments: its message alphabet is (recommitted root +
opened columns + opening proofs). The remaining packaging is the
BCS-resolution instance — a `Reduction` with that `PMsg`, a `KStateFn` whose
state demands CONSISTENCY WITH THE COMMITTED COLUMNS (so binding pins the
masked words — `binding_columns`), and an extract field that synthesizes the
round word from one execution's columns (`seamCounterfactual` composed with
`extractChain`, exactly `extractChain_committed_seam`'s landed algebra) —
so that FS-of-the-deployed-transcript, not FS-of-the-IOR, is native. The
algebra for every piece is landed in `Selvage/ZkExtraction.lean` and
`Selvage/Commitment.lean`; the packaging (this file's construction re-run at
that alphabet, with the state's column-consistency clause feeding the same
`hfar` choreography) is the residual. It rides `[COMMIT-CR]` and, for
constrained masks below unique decoding, `[ZK-RBR-extract]` open lemma A —
both inherited, unchanged.

**What rides as hypotheses, honestly**: `accRbrKnowledgeSound` consumes the
mutual-CA package (`hdC`/`hMCA`) with the δ-window pinned by
`δ⋆ ≤ min(dC/2, 1 − B⋆)` — the same floor `accSound_rbr` consumes; landed
exactly at `C = ⊤` (the F₅ keystones), the standing `hPG` at RS with
macroscopic δ. The FS carrier itself (`FsOfRbrSound`) is PROVED with no
seam. The covered scope of `accFsSound_native`, in one sentence: the
accumulator chain's IOR compiles by Fiat–Shamir to a straightline
knowledge-sound argument at `(t + k)·(err⋆(δ) + 1/|F|)`, given the
mutual-CA floor, at the full-word message alphabet — proven parameters only.

## Ledger

* `aggregate_snoc` / `foldWords_snoc` / `aggregate_congr_sched` /
  `foldWords_congr_sched` — PROVED: the tail-first forms of the chain fold.
* `chainSched` / `chainClaim` / `chainWord` (+ `_append`, `_ofFn`, `_nil`)
  — DEFINED/PROVED: transcript reads; the round transitions are `foldClaims`
  / `f + γ • g` on the nose.
* `fracHamming_eq_relDist` — PROVED: Rbr's δ-ball is CorrelatedAgreement's.
* `LinkAligned` / `linkAligned_iff_satisfies` / `chainClaim_weights` —
  DEFINED/PROVED: the aligned-channel link relation (the fold-attestable
  one, forced by `aggregate_weights`; equals per-link satisfaction under
  `Aligned` — the audit finding recorded in the module header).
* `accReduction` — DEFINED: the accumulator chain as a WARP `Reduction`
  (`k = ch.length`, `Chal = F`, source = genesis + aligned-channel links,
  target = word-level aggregate).
* `decodeLink` (+ `_sat`, `_of_sat`) / `accExtract` (+ `_append`) —
  DEFINED/PROVED: the δ-oblivious round extractor at the canonical radius.
* `accKState` — DEFINED, all three Def-4.1 clauses PROVED.
* `accRbrKnowledgeSound` — BUILT, `extract_sound` PROVED via `accSound_rbr`
  (cited): the Def-4.2-native instance, `err = accRbrError`.
* `accRbr_backward_masked` — PROVED: Construction B.5 on honest masked
  transcripts returns the masked words exactly, any depth, any seed.
* `accFsSound_native` — PROVED: FS of the accumulator's OWN instance,
  straightline, `(t + k)·accRbrError`.
* Keystones — `accReduction_F5` / `accRbr_F5` (built, landed witnesses);
  `msEx_sat_top` / `msEx_linkAligned` (the masked words witness the chain,
  both readings, via `goodChain_aligned`); `native_state_alive`;
  `native_err_computes` (`1/5`); `native_err_attained` (teeth — equality);
  `native_extract_masked` / `native_extract_chain` (+ the `srExtract = wAt`
  `rfl`); `native_fs_fired` (the game's carrier on the native pair);
  `native_teeth_pair_barred`.
* Residual — `[ACC-rbr-bcs]` (prose above): the BCS-resolution instance;
  `[FS-ROM]`/`[COMMIT-CR]`/`hPG` and `[ZK-RBR-extract]` lemma A inherited.

`#print axioms` on `accRbrKnowledgeSound`, `accFsSound_native`,
`accRbr_backward_masked`, `AccRbrInstanceExample.accRbr_F5`,
`AccRbrInstanceExample.native_fs_fired`,
`AccRbrInstanceExample.native_extract_chain`: `propext`, `Classical.choice`,
`Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
