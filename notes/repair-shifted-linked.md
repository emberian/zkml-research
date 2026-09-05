# Repair lane — `[ACC-rbr-bcs-shifted-linked]` at `accRbrError`: CHECKPOINT

**Lane note, 2026-09-05 (checkpoint on coordinator's usage-wall call).** Tree:
`~/dev/minidregg` (branch `main`, on top of `60f0499`). **No Lean file was edited by
this lane** — the reading and design below were complete, proof work had not started
when the checkpoint was called. `git status --short Selvage/` is empty. This note is the
only new file.

## 1. The transport did NOT close — and the reason is a theorem, not a gap

The task: inhabit `accRbrKnowledgeSoundBcsShiftedLinked C foldRoot ch hm hch δs hδpos
hδone S dom d q wv (accRbrError F errstar)` (`Selvage/AccRbrBcsShiftedTransport.lean:523`)
by transporting `linkedAdaptiveIncrementSound_proved`
(`Selvage/OracleLogLinkedAssembly.lean:461`).

**Finding: the obligation as stated is FALSE below error one, at the linked reduction
too** — by a *different* adversary than the untethered one the retiring lane priced.
The linking is not the hole; the fixed spot-check is.

The structural fact (proved in the tree already, in pieces): at the linked verifier,
`LinkOpened S q (S.commit (wv i)) π_i π_{i+1} ρ_i` plus `binding_columns` force
`π_{i+1}.cols = π_i.cols + ρ_i · (wv i ∘ q)` at EVERY challenge (the `ρ ≠ 0` in
`linkOpened_increment_pinned_free` is only for the division). With `wv i ∈ RS`, `d ≤ t`,
`dom ∘ q` injective, `recoverFromColumns_line` + `recoverFromColumns_sound` give
`bcsWord π_{i+1} = bcsWord π_i + ρ_i • wv i`. So on acceptance the output word is

    Y(ρ) = f̂₀ + Σ_{i<k} ρ_i • wv i,   f̂₀ := recoverFromColumns dom d q (f₀ ∘ q),

a function of the STATEMENT and the CHALLENGES alone. The prover's only freedom is
whether the verifier accepts. Consequently the verifier never reads `f₀` off the `t`
fixed positions `q` (a *parameter* of the reduction, not a challenge), and:

* **the unopened-positions adversary**: take `g ∈ RS` with `g ∘ q = f₀ ∘ q`,
  `Satisfies C A₀ g`, and `wv` aligned for `A₀`. The prover sends
  `π_c := shiftedMsg S q γ g wv c` (level `c` reads `γ` only below `c`:
  `shiftedMsg_committable`). The linked verifier accepts at EVERY schedule
  (`linked_verify_of_shifted` + the anchor `g ∘ q = f₀ ∘ q` + `linkOpened_honest`) with
  output `(aggregate γ A₀ ch, flatFold γ g wv)`, which satisfies the aggregate exactly
  (linearity: `aggregate_weights`/`aggregate_targets`). The full Def-4.1 state is alive at
  every schedule (`full_iff`, `fracHamming_self`). The backward chain of
  `shiftedRbr_floor` (identical, with `shiftedMsg … g wv` in `untetheredMsg`'s place)
  forces the state alive at the empty transcript, where `empty_iff` demands an
  `R_{≤δ}` witness for `(A₀, f₀)` — which `f₀ := g + e`, `e` supported off `q` and
  weight `> δ·m` with `A₀.weights e ≠ 0`, does not have.

**The floor, statement (to be landed as `linkedRbr_floor`):**

```lean
theorem linkedRbr_floor
    (rbr : RbrKnowledgeSoundness
      (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos hδone S dom d q wv))
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) δs)
    (st : Stmt (accReductionBcsShiftedLinked …))
    (hno : ∀ w, ¬ RelaxedMem (accReductionBcsShiftedLinked …).R δ st.idx st.x st.y w)
    (g : Fin m → F) (hg : g ∈ reedSolomonCode dom d)
    (hanchor : ∀ j, g (q j) = st.y (q j))
    (hsat : AccClaim.Satisfies C st.x g)
    (halign : ∀ i, LinkAligned C st.x ch i (wv i)) :
    ∃ i : Fin (ch.length + 1), 1 ≤ rbr.err i st δ
```

and `accRbrKnowledgeSoundBcsShiftedLinked_forces_one` (same premises, `1 ≤ εfold δ`).

**F₅ refutation instance (designed, not yet elaborated).** `qPair = ![0, 2]` and the
landed channel `q2 = LinearMap.proj 2` reads an OPENED position, so the genesis-shaped
claims cannot fire the floor; a claim reading position 1 does:

* `A₀ := ⟨0, fun _ => (LinearMap.proj 1, 1)⟩`, `g := xWord` (`xWord 1 = 1`, `xWord_mem`);
* `f₀ := xWord + e₁` with `e₁ := fun i => if i = 1 then 1 else 0` — `f₀ ∘ qPair = xWord ∘ qPair`,
  `f₀ 1 = 2 ≠ 1`; for `δ < 1/4` the `δ`-ball is `{f₀}` (`one_div_card_le_relDist`), so no
  witness (the `farSt_no_witness` pattern);
* `wv := fun k => if k = 0 then 0 else oneWord` — `proj 1 0 = 0 = claim₀.targets`,
  `proj 1 oneWord = 1 = claim₁.targets`, both in `RS(dom₅, 2)` (`Submodule.zero_mem`,
  `oneWord_mem`), so `LinkAligned ⊤ A₀ goodChain k (wv k)` for both links.

Then `linked_accRbrError_false_F5 : ¬ accRbrKnowledgeSoundBcsShiftedLinked ⊤ linRoot
goodChain … S₅ dom₅ 2 qPair wv (accRbrError (ZMod 5) (fun _ => 0))` at `δ = 1/32`
(`accRbrError_zero_five`, `1/5 < 1`). The named obligation is thereby closed
NEGATIVELY in its all-statements form, exactly as the unlinked one was.

## 2. The extraction source (the coordinator's question), answered

At `accReductionBcsShiftedLinked` the log route uses **(a) + (c)**, and nothing else:

* **(a)** an *extractable commitment as modeled*: `BindingCommitment.binding_columns` is a
  STRUCTURE FIELD (perfect binding at the column level — an opened column against
  `S.commit w` IS `w` at that position). No Ajtai-type "short opening" relation, no
  exceptional-set/rewinding argument, no scaled openings anywhere in the cone. Every
  extraction step is single-transcript and exact.
* **(c)** a *canonical, publicly specified witness*: the designated family `wv` is a
  PARAMETER of the linked reduction. The source relation is
  `R () A₀ f₀ w := Satisfies C A₀ f₀ ∧ ∀ i, LinkAligned C A₀ ch i (w i)`; over the
  deployed statement set `linkedStatementSet = {st | Satisfies C st.x st.y ∧ ∀ i,
  LinkAligned C st.x ch i (wv i)}` the witness IS `wv` (`linked_relaxedMem_of_statementSet`,
  `OracleLogLinkedTarget.lean:90`). The tree already knows the constant extractor has
  error 0 there (`knownWitnessOracleLogReduction`, `:151`). The log route's `(t+k)·1/|F|`
  is entirely the ROM-game cost of *reading `wv` back off the transcript* — the hit horn
  pays for a zero recorded challenge (`linkedHitSlot_le`), the fresh horn for an
  unqueried prefix (`linkedFreshLink_le`, `freshAggregateChallenge_injective` at a FIXED
  output word). Knowledge follows from soundness at zero extra openings; the runtime is
  a replay of the pinned fold.

So: the shifted shape's source relation at the deployed workload IS of the "deterministic
public trace" kind on the link side — `wv` is public and the increments are pinned to it
by binding — and NOT of the "short opening of an arbitrary Ajtai commitment" kind. **In
Def 4.2's oracle-free, worst-case-over-prefix model, the `1/|F|` of the log route has no
counterpart**: a zero challenge `ρ_{i-1} = 0` cannot be charged at round `i` (the event is
deterministic in the fresh `ρ_i`), and the state after round `i-1` cannot exclude it
(`full_iff` pins the full state at every schedule). The Def-4.2 extractor must fall back
to the public `wv` — which is exactly the canonical-witness extractor, error 0 over `Z`.

## 3. What the positive object at `accRbrError` actually is (designed, statement written)

Over ALL statements: floor 1 (§1). Over `linkedStatementSet`: trivially 0 (§2). The
non-trivial object sits in between, on the statement set the deployed genesis actually
lives in — **oracles that are codewords**, `Z_RS := {st | st.y ∈ reedSolomonCode dom d}`
(`xWord_mem`; `farStLinked.y = xWord`, so `linked_zero_false_F5`'s teeth live INSIDE
`Z_RS`). There `f̂₀ = f₀` and the spot-check gap closes.

**The corrected statement** (the Def-4.2 error bound restricted to `Z`, exactly the form
`OB2_depth_composition` consumes — "`εrbr` a uniform bound over `Z`"):

```lean
def accRbrKnowledgeSoundBcsShiftedLinkedOn (wv : Fin ch.length → Fin m → F)
    (Z : Set (Stmt (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos hδone S dom d q wv)))
    (εfold : ℝ → ℝ) : Prop :=
  ∃ rbr : RbrKnowledgeSoundness (accReductionBcsShiftedLinked … wv),
    (∀ δ st tr w, rbr.kstate.state δ st tr w = true → ColsConsistent S q tr.rounds) ∧
    ∀ (i : Fin (ch.length + 1)) st, st ∈ Z → ∀ δ ∈ Set.Ioo (0 : ℝ) δs, rbr.err i st δ ≤ εfold δ
```

(`_On Set.univ` is the landed obligation.) ATLAS fields for the keystone
`accRbrKnowledgeSoundBcsShiftedLinkedOn … Z_RS (accRbrError F errstar)`:
* satisfiable: the instance below (`linkedRbr`), premises discharged at F₅ by the SAME
  package as `accRbrBcs_F5` (`minDistLB_inhabited`, `hasMutualCorrelatedAgreement_top_affine`,
  `qPair_inj`, `msEx_mem`);
* teeth: `linked_zero_false_F5` re-run inside `Z_RS` (`farStLinked.y = xWord ∈ RS`):
  `εfold ≡ 0` is FALSE — the price is genuinely positive; and `linkedRbr_floor` (§1):
  dropping the `Z_RS` restriction is FALSE below 1;
* premise: `accReductionBcsShiftedLinked_F5` + `linked_completeness_F5` (CITED).

**The state design (the old residual (b), resolved by the pin).** At the linked verifier the
"fold so far" after `i` rounds is the PINNED partial fold, which reads NO message:

    Y_i := partialFold (chainSched rs) f₀ wv i        (i = rs.length ≤ k)
    Y_{k+1} := bcsWord (last message)                 (the full transcript, so `full_iff` holds)
    A_i := aggregate (chainSched rs) A₀ (ch.take i)   (= chainClaim on any length-i list)

```lean
def LinkedStateProp (δ : ℝ) (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (rs : List (BcsMsg Root' F Op t × F)) (pend : Option (BcsMsg Root' F Op t))
    (w : Fin ch.length → Fin m → F) : Prop :=
  ColsConsistent S q rs ∧
  (∀ e ∈ rs.head?, ∀ j, e.1.cols j = f₀ (q j)) ∧                                  -- anchor
  (∀ (c : ℕ) (hc : c < ch.length) e e', rs[c]? = some e → rs[c+1]? = some e' →
      LinkOpened S q (S.commit (wv ⟨c, hc⟩)) e.1 e'.1 e.2) ∧                       -- links so far
  (∃ z, relDist (stateWord f₀ rs) z ≤ δ ∧ AccClaim.Satisfies C (A rs) z) ∧          -- FoldTracks
  ((rs.length = ch.length + 1 ∧ pend = none) ∨ RemWitnessed C A₀ ch rs.length w)
```

Extractor: `fun st tr w => accExtract`-shaped — at round `i < k` install
`decodeLink C st.x ch δs i (wv i)` at slot `i` (δ-oblivious; `wv` public); at the inert
round `k`, identity. Error:

    err i st δ := if (i : ℕ) < ch.length ∨ st.y ∈ reedSolomonCode dom d
                  then accRbrError F errstar δ else 1

**The three bridging lemmas the round bound needs (each a statement, none elaborated):**

* `linkOpened_bcsWord_succ : LinkOpened S q (S.commit w) π π' ρ → w ∈ RS → d ≤ t →
  Injective (dom ∘ q) → bcsWord dom d q π' = bcsWord dom d q π + ρ • w` — the inner
  `hword` of `linkOpened_increment_pinned_free`, WITHOUT `ρ ≠ 0` (it is there already,
  un-named).
* `linked_verify_recommit` — `linked_verify_honest` with the committed genesis `g` decoupled
  from the statement's `f₀` under `g ∘ q = f₀ ∘ q` (needed by §1's adversary, and by the
  round-`k` bookkeeping).
* `linked_full_word_pinned` — on a full transcript with `Cols ∧ anchor ∧ all links` and
  `f₀ ∈ RS`: `bcsWord (last) = partialFold (chainSched rs) f₀ wv ch.length`
  (induction on `c ≤ k` with `partialFold_succ` and the two lemmas above).

**Why the round bound then closes at `accRbrError` on every LINK round at EVERY statement**
(no `Z_RS` needed there): at round `i < k` the extended word is `Y_i + ρ_i • wv i` with
`Y_i` and `wv i` FIXED before `ρ_i` — precisely `accSound_rbr`'s event
`Pr_ρ[∃ z, relDist (f + ρ • g) z ≤ δ ∧ Satisfies (foldClaims A B ρ) z]` with
`f := Y_i`, `g := wv i`, `A := A_i`, `B := (ch.get i).claim`. Pending-state doom gives
`hfar` verbatim as in `accRbrKnowledgeSoundBcs` (`AccRbrBcs.lean:526`, the doom/no-doom
split): either no `u ∈ C` within `δ` of `Y_i` satisfies `A_i`, or no aligned `v` within
`δ⋆ ≥ δ` of `wv i` (`decodeLink_sat`). This is the shifted schedule's problem DISSOLVED:
the increment scored by the fresh `ρ_i` is not the message committed after it (which is
what made the fresh challenge inert at the unlinked verifier) but the public `wv i`,
which `LinkOpened` forces the next message to fold. Only the inert round `k` at a
non-codeword oracle is unpriced — and §1 proves SOME round must be `≥ 1` there, so the
instance localizes the fixed-`q` gap to exactly that round.

Hypotheses of the instance: `hdC`, `hMCA`, `hBstar`, `hdC2`, `hstar` (as
`accRbrKnowledgeSoundBcs` — the fold price genuinely uses the mutual-CA `errstar`, unlike
the log route whose fresh horn had a fixed word) plus `hdt`, `hq`, `hwv` (the pin).

## 4. What is genuinely open, named

`[ACC-rbr-bcs-shifted-spot]` — the reduction in which the spot positions `q` are a
CHALLENGE drawn after the recommitted roots, not a parameter. §1 shows no Def-4.2 object
over all statements exists at fixed `q`; the deployment's actual proximity soundness for
the genesis recommitment lives in sampled `q`, which this tree's `accReductionBcsShifted`
does not model. Out of this lane's touch list (it is a new `Reduction`).

## 5. Exact file list and elaboration status

* NEW `~/dev/zkml-research/notes/repair-shifted-linked.md` (this note) — prose.
* **No file under `~/dev/minidregg` was created or modified.** `Selvage/AccRbrBcsShiftedTransport.lean`
  and `Selvage/AccRbrBcsShifted.lean` are at `60f0499`, untouched; the planned NEW
  `Selvage/AccRbrBcsShiftedLinked.lean` was not started. Nothing to revert, nothing
  half-edited. No commit, no stash, no `add -A`.

Build state observed: `lake build` processes were live on the box (`pgrep` non-empty) the
whole session; `Selvage/AccRbrBcsShiftedTransport.olean` is NOT in `.lake/build` (the
umbrella has not imported it — the retiring lane's owner action stands).
