# Fold extractor upgrade — census §7 item 3, resolved the other way

Lane record, 2026-09-05. Unit: a CONSTRUCTED extractor for `FoldRoundBound`
(`minidregg/Selvage/AccRbrFold.lean:566`) and the round bound at the
per-absorbed-commitment `ε_MSIS` (`[ACC-rbr-fold-resid](a)`, 06-OPEN item 4).

**Verdict in one paragraph.** The requested theorem
`FoldRoundBound … foldExtract (fun _ => ε_MSIS)` is FALSE for every
`extractFn` at any instance where binding holds one step above the genesis
budget — proved (`foldRoundBound_floor`): the round event fires at EVERY
challenge, so the only inhabitants of `FoldRoundBound` there are at `ε ≥ 1`,
and `foldRoundBound_one` is tight. The obstruction is the witness type, not
the extractor: a single plane vector cannot be un-folded without an opening
of the absorbed commitment, and Def 4.2 is single-transcript. The un-fold
extractor EXISTS, linear and constructed, once the witness carries the
absorbed openings (`foldReductionCarried`, witness `W × (Fin T → W)`), and
there the round bound is `0` unconditionally — no MSIS hypothesis consumed.
The price moves to the source relation: the extracted genesis opening is
`budget b₀ (2T)`-short (slack `2T·ρB`, twice the honest fold budget), and the
carried decider checks `T + 1` openings — no succinctness. At the production
point the binding capacity for the extracted opening HALVES: safe through
`T ≤ 2^46 − 1`, lost at `T ≥ 2^46` (`carried_capacity_safe` / `carried_break`).

## Statements (copied from `Selvage/AccRbrFoldExtract.lean`)

### The floor — every extractor

```lean
theorem foldRoundBound_floor (Z : W) (hlo : b₀ < S.nrm Z)
    (hhi : S.nrm Z ≤ S.budget b₀ 1) (hbind : S.BindingAt (S.nrm Z))
    (extractFn : Stmt (foldReduction S T hT Kh chalVal b₀) →
      Transcript C Kh → W → W) (εfold : ℝ → ℝ)
    (h : FoldRoundBound S T hT Kh chalVal b₀ extractFn εfold) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 1 ≤ εfold δ
```

The zero-absorb attack. Statement `C₀ := commit Z`, round `0`, pending message
`π := 0`. At every `ρ` the extended fold is `C₀ + ρ•0 = C₀`, so `Z` is in the
extended knowledge state (`budget b₀ 1`-short opening). A witness in the
prefix state is a `b₀`-short opening of `commit Z`, hence `= Z` by
`BindingAt (nrm Z)`, hence not `b₀`-short: the prefix state is EMPTY. The
round event is the whole challenge space, `Pr = 1`.

Instances, hypotheses discharged:

```lean
theorem ToyFold.toy_roundBound_floor (extractFn …) (εfold : ℝ → ℝ)
    (h : FoldRoundBound toy 1 one_pos (Fin 3) chalVal3 1 extractFn εfold) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 1 ≤ εfold δ
-- Z := unitSpike 0 2 (‖Z‖ = 2, b₀ = 1, budget 1 1 = 2), binding from
-- toy_binding_T1 (rides the PROVED msisHardEx_toy).

theorem DualModeParams.production_roundBound_floor {κ N} (hN : 0 < N) (A) (T) (hT)
    (Kh) [Fintype Kh] [Nonempty Kh] (chalVal : Kh → ℤ)
    (hmsis : (intFoldScheme q A 1 B).MsisHardEx (2 * (intFoldScheme q A 1 B).budget B 1))
    (extractFn …) (εfold) (h : FoldRoundBound (intFoldScheme q A 1 B) T hT Kh chalVal B extractFn εfold) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 1 ≤ εfold δ
-- Z := unitSpike 0 (B+1): one over the honest b₀ = B, inside budget B 1 = 2B;
-- binding from production_fold_binding at T = 1 — the SAME [FOLD-msis]
-- hypothesis the positive half already consumes.
```

Consequence for the four callers (`foldRbrOfRoundBound`,
`fold_depth_composition`, `fold_fs_sound`, `fold_fs_price_msis`): at any
binding instance their hypothesis `h : FoldRoundBound … εfold` forces
`εfold ≥ 1`, so every conclusion they reach there is at error
`(t + T)·εfold ≥ T`. They are not wrong; they are vacuous below `T`.

### The carried fold — the extractor, constructed

```lean
@[reducible] def foldReductionCarried (S) (T) (hT) (Kh) [Fintype Kh] [Nonempty Kh]
    (chalVal : Kh → R) (b₀ : ℝ) : Reduction where
  X  := C                       -- genesis commitment
  X' := C × (Fin T → C)         -- the fold AND the absorbed commitments
  W  := W × (Fin T → W)         -- running opening + one opening per absorbed
  R  := fun _ C₀ _ w => S.ShortOpens (S.budget b₀ (2 * T)) C₀ w.1     -- RELAXED
  R' := fun _ out _ w => S.ShortOpens (S.budget b₀ T) out.1 w.1 ∧
    ∀ j : Fin T, S.ShortOpens S.B (out.2 j) (w.2 j)
  k := T; PMsg := C; Chal := Kh
  verify := fun _ C₀ _ πs ρs =>
    some ((chalFoldList chalVal C₀ (List.ofFn fun i => (πs i, ρs i)), πs), fun _ => ())

def FoldCarriedStateProp (C₀ : C) (rs : List (C × Kh)) (w : W × (Fin T → W)) : Prop :=
  S.commit w.1 = chalFoldList chalVal C₀ rs ∧
    S.nrm w.1 ≤ S.budget b₀ (2 * T - rs.length) ∧      -- DESCENDING budget
    OpensAbsorbed S T Kh rs w.2

def foldExtract (_st) (tr : Transcript C Kh) (w : W × (Fin T → W)) : W × (Fin T → W) :=
  match tr.rounds.getLast? with
  | none => w
  | some (_, ρ) =>
    if h : tr.rounds.length - 1 < T then
      (w.1 - chalVal ρ • w.2 ⟨tr.rounds.length - 1, h⟩, w.2)
    else w

theorem foldExtract_state (hchal : ∀ c, chalVal c ∈ S.chalSet) … 
    (hw : FoldCarriedStateProp … st.x (rs ++ [(π, ρ)]) w) :
    FoldCarriedStateProp … st.x rs (foldExtract … st ⟨rs ++ [(π, ρ)], none⟩ w)

def FoldCarriedRoundBound (extractFn) (εfold : ℝ → ℝ) : Prop := -- Def-4.2 round event, carried

theorem foldCarriedRoundBound_zero (hchal : ∀ c, chalVal c ∈ S.chalSet) :
    FoldCarriedRoundBound S T hT Kh chalVal b₀ (foldExtract S T hT Kh chalVal b₀) (fun _ => 0)

noncomputable def foldCarriedRbr (hchal) : RbrKnowledgeSoundness (foldReductionCarried …)
-- kstate := foldCarriedKState, extract := foldExtract, err ≡ 0

theorem foldCarried_depth_composition (hchal) (Z) :
    StraightlineSrKnowledgeSoundness (foldReductionCarried …) Z (fun _ _ _ => 0)
theorem foldCarried_fs_sound (hchal) (Z) :
    FsStraightlineKnowledgeSoundness (foldReductionCarried …) Z (fun _ _ _ => 0)
```

**Norm growth of the recovered witness.** One un-fold:
`nrm (Y − ρ_i • Ys i) ≤ nrm Y + ρ·B` (`nrm_sub` + `nrm_smul` at `Ys i`
`B`-short, `chalVal ρ ∈ chalSet`). From the target `budget b₀ T` back to the
genesis: `budget b₀ T + T·ρB = budget b₀ (2T) = b₀ + 2T·ρB`. The knowledge
state carries this as the descending budget `budget b₀ (2T − c)` at prefix
length `c`; `empty_iff` forces the source relation to be the relaxed
`ShortOpens (budget b₀ (2T))`. The factor is exactly 2× the honest fold
budget's growth term.

### Halved capacity at the production point

```lean
theorem DualModeParams.carried_capacity_safe : ∀ T : ℕ, T ≤ 2 ^ 46 - 1 → 2 * (B * (1 + 2 * T)) < q
theorem DualModeParams.production_carried_binding (A) (T)
    (h : MsisHardEx (2 * budget B (2 * T))) : BindingAt (budget B (2 * T))
theorem DualModeParams.carried_break (hN : 0 < N) (A) {T} (hT : 2 ^ 46 ≤ T) :
    ¬ BindingAt (budget B (2 * T))
```

Against `capacity_safe` (`2^47 − 2`) / `production_break` (`2^47 − 1`): the
extracted genesis opening lives at `B(1 + 2T)`, so the wall for ITS binding is
at `2^46`. Pessimistic number, stated with scope: this is the capacity at
which the carried extractor's output is a bound opening; the honest fold
witness's own binding wall is unchanged at `2^47 − 1`.

## ATLAS fields

`FoldRoundBound` (existing Prop, now fully priced):
* satisfiable — `foldRoundBound_one` (`ε ≡ 1`), now TIGHT by the floor;
* teeth — `ToyFold.toy_roundBound_floor` (every extractor, `ε ≥ 1`),
  strictly stronger than `toy_roundBound_zero_id_false`;
* premise-inhabitation — unchanged (`foldKState`, `ToyFold`).

`FoldCarriedRoundBound` (new Prop, statement-first):
* satisfiable — `foldCarriedRoundBound_zero`: the CONSTRUCTED `foldExtract`
  at `ε ≡ 0`, every instance with `hchal`;
* teeth — `ToyFold.toy_carriedRoundBound_zero_id_false`: the identity
  extractor at the toy is REFUTED at `ε ≡ 0` (challenge `+1`, witness
  `(e₀, e₀)`) — un-folding is real work;
* premise-inhabitation — `foldCarriedKState` (three Def-4.1 clauses proved),
  `ToyFold.toy_chalVal3_mem` discharges `hchal` on concrete data.

## What closed vs what is conditional

CLOSED, no hypothesis beyond `hchal` (challenge decode in-set — the same
premise `nrm_chalFoldList_le` carries; inhabited at the toy):
`foldExtract_state`, `foldCarriedRoundBound_zero`, `foldCarriedRbr`,
`foldCarried_depth_composition`, `foldCarried_fs_sound`,
`toy_carriedRoundBound_zero_id_false`, `toy_roundBound_floor`,
`carried_capacity_safe`, `carried_break`, `foldRoundBound_floor` (abstract,
its binding premise discharged at the toy).

CONDITIONAL on the existing named hypothesis `[FOLD-msis]`
(`MsisHardEx`, exact-nonexistence form, expected false at production by
pigeonhole — the file's own label): `production_roundBound_floor` (at
`2·budget B 1`), `production_carried_binding` (at `2·budget B (2T)`). No NEW
computational `Prop` was named: no theorem here consumes one. The `ε_MSIS`
term does not appear in the carried round bound at all; it enters only where
the extracted (relaxed) opening is asserted BOUND, via the file's existing
`fold_binding` at the doubled budget.

Axiom pins: nine `#guard_msgs`-pinned `#print axioms`, all
`[propext, Classical.choice, Quot.sound]`.

## What this says about 06-OPEN item 4

`[ACC-rbr-fold-resid](a)` — "the per-absorbed-commitment `ε_MSIS` home" — has
no home in a single-transcript round bound: at the compressing witness type
the round error is 1, and at the carried witness type it is 0. The
`Q·ε_MSIS` accounting of the Nebula read belongs to the DECIDER composition
(binding of each opened commitment), i.e. to `fold_binding` per absorbed
commitment, not to Def 4.2. `fold_fs_price_msis`'s `(t+T)·εr + (t+T)·εM`
split is a true theorem about a hypothesis that, by the floor, only holds at
`εr + εM ≥ 1`. Recommend retiring `foldRbrOfRoundBound`/`fold_*` in favour of
the carried analogs in a follow-up that may edit `AccRbrFold.lean`'s body
(out of this lane's brief), and re-labelling the `FoldRoundBound` docstring
at `:549` ("the ONLY missing piece", "where the ε_MSIS term lives") — left
untouched here per the brief's "nothing else in those docstrings".

## Docstring fixes

`AccRbrFold.lean:52` and `:561` cited `foldRoundBound_zero_id_false` /
`ToyFold.foldRoundBound_zero_id_false`; the resolving name is
`ToyFold.toy_roundBound_zero_id_false` (`:1277`). Name only; nothing else in
those docstrings changed. `grep -rn foldRoundBound_zero_id_false` is now
empty tree-wide.

## Files

* `/Users/ember/dev/minidregg/Selvage/AccRbrFoldExtract.lean` — NEW (imports
  `Selvage.AccRbrFold`, `Selvage.AuditSampling` — the latter for
  `uniformProb_true` only; not twinned).
* `/Users/ember/dev/minidregg/Selvage/AccRbrFold.lean` — two docstring
  citations (`:52`, `:561`), name only.
* `/Users/ember/dev/zkml-research/notes/fold-extractor-upgrade.md` — this note.

Not committed.
