/-
# Selvage.Commitment — the vector-commitment (Merkle/BCS) binding layer.

Everything upstream of this file is word-level algebra. `Selvage/Accumulator.lean`
keeps `Root` opaque by design ("that `rt` binds the word is the commitment
layer's obligation"); `Selvage/AccExtract.lean` recovers witnesses from the folded
WORDS, with the words' binding to the prover's roots the named seam
`[ACC-extract-bind]`; `Selvage/Decider.lean` consumes the witness word `f` as
given, with "`rt` opens to this `f`" the named seam `[DEC-open]`. This file IS
that commitment layer: the binding relation between a root and the word it
commits, so "the prover committed to word f" and "the extracted/checked word is
THE committed one" become real statements, and both seams close at the
resolution stated below.

The construction (Merkle/BCS vector commitment, WARP 2025/753 / WHIR 2024/1586
deployment shape, abstracted to its load-bearing content):

* `OpeningScheme` — `commit : (ι → F) → Root`, `openAt` (the Merkle path),
  `verifyOpen : Root → ι → F → Op → Prop` (check one symbol against the root),
  with completeness `verifyOpen_commit` (an honest opening of a committed word
  verifies).
* `PositionBinding` — THE load-bearing property: one root cannot open to two
  different values at one position. Everything extraction and the decider need
  from the commitment is this.
* `BindingCommitment` — an opening scheme CARRYING its binding as a Prop field.

**The honest floor (read before auditing).** Position-binding is not provable
from nothing: for the deployed Merkle/sponge it rests on collision-resistance
of the hash. Following the discipline of `Selvage/FiatShamir.lean`'s ROM (an
INHABITED handler, `Oracle.empty` — never an unproved axiom), the idealization
here is a STRUCTURE with binding as a field, and it is INHABITED:
`idealCommitment`, the identity scheme (`Root := ι → F`, `commit = id`,
`verifyOpen rt i v _ := rt i = v`), has its binding PROVED — a binding scheme
EXISTS, the abstraction is non-vacuous, and no axiom enters the tree. The
deployed sponge realizing `BindingCommitment` is the one named residual
`[COMMIT-CR]` below, priced at deployment exactly like `[FS-ROM]`.

**Transcription notes:**

* **Position-binding is the primitive; word binding is derived.** Merkle
  binding is per-leaf; `word_binding` extends it to whole words by `funext`
  over fully-opened positions, and `opened_eq_committed` specializes to the
  honest root: any word fully opened from `commit w` IS `w`.

* **Resolution: all positions opened.** The seam theorems consume openings at
  EVERY position (`∀ i, verifyOpen …`). In deployment the prover opens `t`
  spot-checked columns and the FULL word is reconstructed by erasure
  correction inside the mutual-agreement set (WARP App. B; mutual correlated
  agreement PROVED at unique decoding in `Selvage/CorrelatedAgreement.lean`).
  That partial-opening lift is obligation (b) of `[ACC-extract-bind]`'s prose
  ledger in `Selvage/AccExtract.lean` and stays THERE; this file closes
  obligations (a) binding and (c) attribution at the stated resolution, and
  says so rather than smuggling the lift into a hypothesis.

* **`verifyOpen` is a Prop, not a program.** The deployed Merkle-path check
  (hash the leaf up the tree, compare to the root) is the `[COMMIT-CR]`
  realizer's job; the seam theorems consume only the relation and its two
  laws. Nothing here is hand-written circuit/AIR material — this is the
  spec-level commitment relation the emit path will eventually refine to.

* **Why the fold algebra never inspected `Root`.** `committed_fold_bind`
  renders the seam at the accumulation step: the prover's recommitment
  (`foldRoot A.rt γ B.rt`) committing the folded word is a HYPOTHESIS relating
  root to word — exactly the datum the opaque-root discipline deferred to this
  layer. The extraction side (`Selvage/AccExtract.lean`'s `extractPair`, which
  consumes folded words `h, h'`) composes with `committed_extract_bind`
  downstream: binding hands extraction the committed words, extraction hands
  back witnesses ATTACHED to the prover's commitments. (The composition is
  stated in the chain lane, which owns the AccExtract import; this file stays
  import-light under it — `Selvage/Depth.lean` is a sibling-lane surface.)

**Keystones** (ATLAS: satisfiable + teeth + premise inhabitation, all BUILT,
computing over F₅): completeness fires on `xWord`; binding FIRES (two values
at one position cannot both verify — generic and computed); the seam theorems
fire on a WARP-shape claim rooted at `commit xWord`; and binding is
LOAD-BEARING — the equivocator (constant commit, accept-everything verify) is
a genuine `OpeningScheme` whose completeness holds, yet it admits NO
`BindingCommitment` extension (`equivocal_no_binding_extension`) and it BREAKS
the seam conclusion (`equivocal_breaks_extract_bind`: one root fully opens to
two different words, so "extracted = committed" fails). Without the `binding`
field the whole attribution story is false, not merely unproved.
-/
import Selvage.Accumulator
import Selvage.Decider

namespace Minidregg.Selvage

variable {Root F ι Op : Type*}

/-! ## The opening scheme and position-binding -/

/-- **A vector-commitment opening scheme**: commit a word to a root, open any
position (`openAt` — the Merkle path in deployment), verify one claimed symbol
against the root. `verifyOpen` is the relation the deployed Merkle-path check
realizes (`[COMMIT-CR]`); completeness (`verifyOpen_commit`) is the honest
prover's side. Binding is NOT a field here — `PositionBinding` below is the
separate property whose necessity the equivocator keystone exhibits. -/
structure OpeningScheme (Root : Type*) (F : Type*) (ι : Type*) (Op : Type*) where
  /-- Commit a word to a root (the Merkle root in deployment). -/
  commit : (ι → F) → Root
  /-- The honest opening of a committed word at a position (the Merkle path). -/
  openAt : (ι → F) → ι → Op
  /-- Verify a claimed symbol at a position against a root. -/
  verifyOpen : Root → ι → F → Op → Prop
  /-- Completeness: an honest opening of a committed word verifies. -/
  verifyOpen_commit : ∀ (f : ι → F) (i : ι), verifyOpen (commit f) i (f i) (openAt f i)

/-- **Position-binding** — the load-bearing property of the whole layer: one
root cannot be opened to two DIFFERENT values at the same position, whatever
the two openings. This is what the deployed Merkle tree buys with
collision-resistance, and it is everything `[ACC-extract-bind]`(a)/(c) and
`[DEC-open]` consume. -/
def OpeningScheme.PositionBinding (S : OpeningScheme Root F ι Op) : Prop :=
  ∀ (rt : Root) (i : ι) (v v' : F) (o o' : Op),
    S.verifyOpen rt i v o → S.verifyOpen rt i v' o' → v = v'

/-- **A binding vector commitment**: an opening scheme carrying its
position-binding as a Prop field. The honest-floor shape: binding rests on
collision-resistance in deployment, so it enters as CARRIED STRUCTURE —
inhabited below by `idealCommitment` (binding PROVED), never an axiom; the
sponge realizer is the named residual `[COMMIT-CR]`. -/
structure BindingCommitment (Root : Type*) (F : Type*) (ι : Type*) (Op : Type*)
    extends OpeningScheme Root F ι Op where
  /-- Position-binding — the field the seam theorems apply. -/
  binding : toOpeningScheme.PositionBinding

/-! **Forgetting binding, silently.** A `BindingCommitment` may be handed to
anything that needs only `commit`/`openAt`/`verifyOpen`, and the coercion is
definitionally the parent projection — `S.verifyOpen` on either side is the
same term. This exists so that predicates which do NOT consume binding can be
STATED at `OpeningScheme` without a second copy at `BindingCommitment`: the
weaker type is the real home, and every existing binding-typed call site keeps
its syntax. Where binding IS consumed (`bcs_root_pins_word`, `binding_columns`,
`word_binding`) the argument stays a `BindingCommitment` and the coercion never
applies. -/
attribute [coe] BindingCommitment.toOpeningScheme

instance : CoeOut (BindingCommitment Root F ι Op) (OpeningScheme Root F ι Op) :=
  ⟨BindingCommitment.toOpeningScheme⟩

/-! ## Derived binding, word level -/

/-- **Word binding**: two words fully opened from the SAME root are equal —
position-binding extended over all positions by `funext`. The deep content of
both seams is this one application of `binding`. -/
theorem BindingCommitment.word_binding (S : BindingCommitment Root F ι Op)
    {rt : Root} {f g : ι → F} {of og : ι → Op}
    (hf : ∀ i, S.verifyOpen rt i (f i) (of i))
    (hg : ∀ i, S.verifyOpen rt i (g i) (og i)) : f = g :=
  funext fun i => S.binding rt i (f i) (g i) (of i) (og i) (hf i) (hg i)

/-- Any word fully opened from an honest commitment `commit w` IS `w` — word
binding against the honest opening `verifyOpen_commit` supplies. -/
theorem BindingCommitment.opened_eq_committed (S : BindingCommitment Root F ι Op)
    {w e : ι → F} {oe : ι → Op}
    (he : ∀ i, S.verifyOpen (S.commit w) i (e i) (oe i)) : e = w :=
  S.word_binding he fun i => S.verifyOpen_commit w i

/-- A binding commitment DETERMINES the word: `commit` is injective —
completeness of both words against one root, closed by word binding. -/
theorem BindingCommitment.commit_injective (S : BindingCommitment Root F ι Op) :
    Function.Injective S.commit := fun f g h =>
  S.opened_eq_committed (w := g) (oe := fun i => S.openAt f i)
    fun i => h ▸ S.verifyOpen_commit f i

/-- The honest prover's side at a known root: if `rt` commits `w`, every
position of `w` opens from `rt` — completeness transported along the root
equation (consumed by `decider_open_complete`). -/
theorem OpeningScheme.verifyOpen_of_commit_eq (S : OpeningScheme Root F ι Op)
    {rt : Root} {w : ι → F} (hrt : rt = S.commit w) :
    ∀ i, S.verifyOpen rt i (w i) (S.openAt w i) :=
  fun i => hrt.symm ▸ S.verifyOpen_commit w i

/-- A retained position-level equivocation attempt: the submitted value and
the honest value of `word` both verify at the same root and position, but the
two values differ.  This is the binding-free event a concrete Merkle
collision reduction consumes; unlike a `BindingCommitment` premise, it keeps
the adversary's value and opening path visible. -/
def OpeningScheme.PositionEquivocation (S : OpeningScheme Root F ι Op)
    (rt : Root) (i : ι) (value : F) (opening : Op) (word : ι → F) : Prop :=
  S.verifyOpen rt i value opening ∧
    S.verifyOpen rt i (word i) (S.openAt word i) ∧ value ≠ word i

/-- Perfect position binding refutes the retained equivocation event.  A
deployed short-root scheme pays for this implication through its collision-
resistance reduction rather than constructing `BindingCommitment` for free. -/
theorem BindingCommitment.not_positionEquivocation
    (S : BindingCommitment Root F ι Op) (rt : Root) (i : ι)
    (value : F) (opening : Op) (word : ι → F) :
    ¬ S.toOpeningScheme.PositionEquivocation rt i value opening word := by
  rintro ⟨hvalue, hword, hne⟩
  exact hne (S.binding rt i value (word i) opening (S.openAt word i)
    hvalue hword)

/-! ## The inhabitation — the honest floor is a BUILT object

A binding scheme EXISTS: the identity/injective commitment, `Root := ι → F`,
`commit = id`, `verifyOpen rt i v _ := rt i = v`. Binding is a two-line
theorem (`rt i = v` and `rt i = v'` force `v = v'`). This is the exact
`Oracle.empty` move: the idealized layer is inhabited, so every theorem taking
a `BindingCommitment` has a non-vacuous instance, and no axiom is ever
declared. What the identity scheme idealizes away — succinctness of the root
and the hash realizing it — is `[COMMIT-CR]`'s ledger, not a soundness gap. -/

/-- **The ideal (identity) commitment** — the inhabitation witness of the
honest floor: the root IS the word, verification is symbol equality, binding
is proved. Trivially succinctness-free; the deployed Merkle/sponge scheme
realizing `BindingCommitment` with a short root is `[COMMIT-CR]`. -/
def idealCommitment (F ι : Type*) : BindingCommitment (ι → F) F ι Unit where
  commit := id
  openAt := fun _ _ => ()
  verifyOpen := fun rt i v _ => rt i = v
  verifyOpen_commit := fun _ _ => rfl
  binding := fun _ _ _ _ _ _ h h' => h.symm.trans h'

@[simp] theorem idealCommitment_commit (f : ι → F) :
    (idealCommitment F ι).commit f = f := rfl

@[simp] theorem idealCommitment_openAt (f : ι → F) (i : ι) :
    (idealCommitment F ι).openAt f i = () := rfl

@[simp] theorem idealCommitment_verifyOpen (rt : ι → F) (i : ι) (v : F) (o : Unit) :
    (idealCommitment F ι).verifyOpen rt i v o ↔ rt i = v := Iff.rfl

/-- The floor is inhabited — a built instance, the `Oracle.empty` pattern. -/
instance : Inhabited (BindingCommitment (ι → F) F ι Unit) :=
  ⟨idealCommitment F ι⟩

/-! ## Closing the seams: `[ACC-extract-bind]`(a)(c) and `[DEC-open]`

Both seams are the same question asked by two consumers: the algebra holds of
a WORD; the prover supplied a ROOT; is the word the root's? With a
`BindingCommitment` and full openings, yes — and the claim-level conclusion
transfers from the transcript word to THE committed word. -/

section Seams

variable [Field F] {r : ℕ}

/-- **`[ACC-extract-bind]`, the binding + attribution seam closed** (at the
all-positions resolution — module header): if the accumulated claim's root
commits `w` and the word `e` the extraction algebra worked on fully opens from
that root, then `e` IS `w`, and satisfaction of the claim transfers to the
committed word. Word-level extraction (`Selvage/AccExtract.lean`: witnesses
recovered from and bound to the folded words) + this theorem = witnesses
attached to the prover's COMMITMENTS, not merely to algebraically consistent
words. The deep step is one application of `binding` (via
`opened_eq_committed`); the `t`-column erasure lift remains
`[ACC-extract-bind]`(b) upstream. -/
theorem committed_extract_bind (S : BindingCommitment Root F ι Op)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w e : ι → F}
    {oe : ι → Op} (hrt : A.rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen A.rt i (e i) (oe i))
    (hsat : AccClaim.Satisfies C A e) :
    e = w ∧ AccClaim.Satisfies C A w := by
  have he : e = w := S.opened_eq_committed fun i => hrt ▸ hopen i
  exact ⟨he, he ▸ hsat⟩

/-- The seam at the ACCUMULATION STEP, where extraction operates: the prover's
recommitment `foldRoot A.rt γ B.rt` (WARP recommits the folded word every
step) committing `w`, plus full openings of the transcript's folded word `h`,
force `h = w` — the folded word `extractPair` consumes at this challenge IS
the recommitted one. This is why `foldClaims` could keep `Root` opaque: the
root–word relation enters here, once, as commitment data. -/
theorem committed_fold_bind (S : BindingCommitment Root F ι Op)
    (foldRoot : Root → F → Root → Root) {C : Submodule F (ι → F)}
    {A B : AccClaim Root F ι r} {γ : F} {w h : ι → F} {oh : ι → Op}
    (hrt : foldRoot A.rt γ B.rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen (foldClaims foldRoot A B γ).rt i (h i) (oh i))
    (hsat : AccClaim.Satisfies C (foldClaims foldRoot A B γ) h) :
    h = w ∧ AccClaim.Satisfies C (foldClaims foldRoot A B γ) w :=
  committed_extract_bind S (by rw [foldClaims_rt]; exact hrt) hopen hsat

/-- **`[DEC-open]`, closed** (same resolution): the decider's checked word,
fully opened from the final accumulator's root, IS the committed word — so
`D_ACC`'s verdict on the opened word is a verdict on THE word `rt` binds,
which is the contract `Selvage/Decider.lean` stated itself conditional on. -/
theorem decider_open_sound (S : BindingCommitment Root F ι Op)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w f : ι → F}
    {of : ι → Op} (hrt : A.rt = S.commit w)
    (hopen : ∀ i, S.verifyOpen A.rt i (f i) (of i))
    (hdec : decider C A f) :
    f = w ∧ decider C A w := by
  have hf : f = w := S.opened_eq_committed fun i => hrt ▸ hopen i
  exact ⟨hf, hf ▸ hdec⟩

/-- The honest side of `[DEC-open]`: a satisfying committed word both opens at
every position and passes the decider — the two checks the light client's
final step runs are jointly satisfiable whenever the claim is. -/
theorem decider_open_complete (S : BindingCommitment Root F ι Op)
    {C : Submodule F (ι → F)} {A : AccClaim Root F ι r} {w : ι → F}
    (hrt : A.rt = S.commit w) (hsat : AccClaim.Satisfies C A w) :
    (∀ i, S.verifyOpen A.rt i (w i) (S.openAt w i)) ∧ decider C A w :=
  ⟨S.toOpeningScheme.verifyOpen_of_commit_eq hrt, decider_complete hsat⟩

end Seams

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

All BUILT, computing over F₅, reusing `RSExample` (`xWord`, `dom₅`) and
`AccExample` (`oneWord`, `q2`, `consv`):

* **satisfiable** — `ideal_commit_opens` / `ideal_open_computes`: commit a
  concrete word, open a position, verification succeeds (by completeness, and
  again by kernel computation).
* **teeth, binding fires** — `ideal_binding_fires` (generic: two distinct
  values never both verify) and `ideal_binding_computes` (the concrete
  refutation computed); `seam_teeth`: the DIFFERENT word `oneWord` cannot be
  fully opened from `commit xWord` — equivocation against an honest root is
  impossible for the ideal scheme.
* **premise inhabitation** — `committed_extract_bind_fires` /
  `decider_open_fires`: both seam theorems fire on a WARP-shape claim rooted
  at a real commitment, every hypothesis discharged by built objects
  (`ideal_decider_accepts` runs the decider on it by `decide`).
* **binding is load-bearing** — the equivocator `equivocal` (constant commit,
  accept-everything verify) IS an `OpeningScheme` with completeness proved,
  but: `equivocal_not_binding` refutes its position-binding;
  `equivocal_no_binding_extension` shows NO `BindingCommitment` has it as its
  opening scheme (the missing field cannot be filled); and
  `equivocal_breaks_extract_bind` exhibits the seam conclusion FAILING for it
  — one root fully opens to two different words, so "extracted = committed"
  is false, not merely unproved. The `binding` field is exactly what stands
  between the stack and that counterexample. -/

namespace CommitExample

open RSExample AccExample

/-- The keystone scheme: the ideal commitment over the F₅ word space. -/
def S₅ : BindingCommitment (Fin 4 → ZMod 5) (ZMod 5) (Fin 4) Unit :=
  idealCommitment (ZMod 5) (Fin 4)

/-- **Satisfiable**: commit `xWord`, open position 2, verification succeeds —
completeness applied to a built word. -/
theorem ideal_commit_opens :
    S₅.verifyOpen (S₅.commit xWord) 2 (xWord 2) (S₅.openAt xWord 2) :=
  S₅.verifyOpen_commit xWord 2

/-- The same check by kernel computation: the committed root opens to the
symbol value `2` at position 2 (`xWord 2 = 2`). -/
theorem ideal_open_computes : S₅.verifyOpen (S₅.commit xWord) 2 2 () := by
  show xWord 2 = 2
  decide

/-- **Teeth, generic**: binding FIRES — no root of the ideal scheme opens to
two distinct values at one position, whatever the openings. -/
theorem ideal_binding_fires {rt : Fin 4 → ZMod 5} {v v' : ZMod 5}
    (hne : v ≠ v') (o o' : Unit) :
    ¬ (S₅.verifyOpen rt 2 v o ∧ S₅.verifyOpen rt 2 v' o') :=
  fun ⟨h, h'⟩ => hne (S₅.binding rt 2 v v' o o' h h')

/-- **Teeth, computed**: the concrete equivocation attempt — opening
`commit xWord` at position 2 to both `2` and `3` — is refuted by kernel
computation. -/
theorem ideal_binding_computes :
    ¬ (S₅.verifyOpen (S₅.commit xWord) 2 2 () ∧
        S₅.verifyOpen (S₅.commit xWord) 2 3 ()) := by
  show ¬ (xWord 2 = 2 ∧ xWord 2 = 3)
  decide

/-- A WARP-shape claim whose root is a REAL commitment (of `xWord`, under the
ideal scheme) rather than an opaque `Unit` — the object on which the seam
theorems fire. Channel as in `AccExample.goodClaim`. -/
def idealClaim : AccClaim (Fin 4 → ZMod 5) (ZMod 5) (Fin 4) 2 :=
  AccClaim.warp (S₅.commit xWord) (q2, 2) (consv, 1)

theorem idealClaim_satisfies :
    AccClaim.Satisfies (reedSolomonCode dom₅ 2) idealClaim xWord :=
  AccClaim.warp_satisfies_iff.mpr ⟨xWord_mem, q2_xWord, consv_xWord⟩

/-- The decider RUNS on the committed-root claim, by `decide` — the
commitment layer changes the root type, not the executability of the final
check. -/
theorem ideal_decider_accepts :
    decider (reedSolomonCode dom₅ 2) idealClaim xWord := by decide

/-- **Premise inhabitation, `[ACC-extract-bind]` side**: the seam theorem
fires with every hypothesis discharged by built objects — the ideal scheme,
the committed-root claim, the honest full opening, the satisfying word. -/
theorem committed_extract_bind_fires :
    xWord = xWord ∧
      AccClaim.Satisfies (reedSolomonCode dom₅ 2) idealClaim xWord :=
  committed_extract_bind S₅ (oe := fun _ => ()) rfl (fun _ => rfl)
    idealClaim_satisfies

/-- **Premise inhabitation, `[DEC-open]` side**: opened word in, verdict on
the committed word out — the full pipeline fires on built objects. -/
theorem decider_open_fires :
    xWord = xWord ∧ decider (reedSolomonCode dom₅ 2) idealClaim xWord :=
  decider_open_sound S₅ (of := fun _ => ()) rfl (fun _ => rfl)
    (decider_complete idealClaim_satisfies)

/-- **Seam teeth**: the DIFFERENT codeword `oneWord` can NOT be fully opened
from `idealClaim`'s root — an adversary holding the honest commitment cannot
attribute another word to it. (Refuted through `opened_eq_committed`: a full
opening would force `oneWord = xWord`, which computation denies.) -/
theorem seam_teeth :
    ¬ ∀ i, S₅.verifyOpen idealClaim.rt i (AccExample.oneWord i) () := fun h =>
  absurd (S₅.opened_eq_committed (w := xWord) (oe := fun _ => ()) h)
    (by decide)

/-! ### The equivocator: binding is load-bearing, exhibited -/

/-- **The equivocator** — constant root, accept-everything verification: a
genuine `OpeningScheme` (completeness holds trivially) modeling a commitment
with NO binding. Everything a `BindingCommitment` carries EXCEPT the binding
field. -/
def equivocal : OpeningScheme Unit (ZMod 5) (Fin 4) Unit where
  commit := fun _ => ()
  openAt := fun _ _ => ()
  verifyOpen := fun _ _ _ _ => True
  verifyOpen_commit := fun _ _ => trivial

/-- The equivocator is NOT position-binding: its one root opens to `0` and to
`1` at the same position. -/
theorem equivocal_not_binding : ¬ equivocal.PositionBinding :=
  fun h => absurd (h () 2 0 1 () () trivial trivial) (by decide)

/-- No `BindingCommitment` extends the equivocator: the binding FIELD cannot
be inhabited over it — the structure's Prop field genuinely constrains, and a
constant-commit scheme is refuted, not merely unproved. -/
theorem equivocal_no_binding_extension :
    ¬ ∃ S : BindingCommitment Unit (ZMod 5) (Fin 4) Unit,
        S.toOpeningScheme = equivocal :=
  fun ⟨S, hS⟩ => equivocal_not_binding (hS ▸ S.binding)

/-- **Without binding, attribution is FALSE**: under the equivocator, the
premise shape of `committed_extract_bind` — a root committing `w`, a word `e`
fully opened from it — is satisfied by TWO DIFFERENT words (`xWord` committed,
`oneWord` opened), so the conclusion `e = w` fails. The extraction chain would
attach witnesses to a word the prover never committed; `binding` is exactly
what forbids this. -/
theorem equivocal_breaks_extract_bind :
    ∃ (w e : Fin 4 → ZMod 5) (oe : Fin 4 → Unit),
      () = equivocal.commit w ∧
      (∀ i, equivocal.verifyOpen () i (e i) (oe i)) ∧
      e ≠ w :=
  ⟨xWord, AccExample.oneWord, fun _ => (), rfl, fun _ => trivial, by decide⟩

end CommitExample

/-! ## Residual obligation — prose, not a stub

Named residual with its realizer; it becomes a real theorem, never a
`def : Prop := True` (the audit discipline).

**[COMMIT-CR]** — the deployed scheme realizing `BindingCommitment`. In
deployment `Root` is a short digest: `commit` Merkle-hashes the word with the
stack's sponge (the same hash family `[FS-ROM]` idealizes for the transcript
layer), `openAt` produces the authentication path, and `verifyOpen` re-hashes
the leaf up the path and compares roots. Its `binding` field is a theorem ONLY
relative to collision-resistance of the compression function: an adversary
opening one root to two values at a position exhibits a hash collision along
the paths — the standard Merkle binding reduction. What this residual owes:
(i) the Merkle `commit`/`openAt`/`verifyOpen` as derived objects over the
chosen sponge; (ii) the reduction "equivocation ⇒ collision" as a real
theorem, making `binding` conditional on a NAMED CR hypothesis carried as
structure (exactly as this file carries `binding`), never an axiom; (iii) the
succinctness accounting (root and path sizes — the reason the identity scheme,
sound as it is, is not the deployed one). Until it lands, the honest label:
the commitment LAYER is proved and inhabited (identity scheme, binding a
theorem); the seams are closed GIVEN any `BindingCommitment`; the deployed
Merkle/sponge instance is priced, not assumed. The `t`-column erasure lift
(partial openings to full words inside the mutual-agreement set) is
`[ACC-extract-bind]`(b), owed in `Selvage/AccExtract.lean`'s ledger, riding
`Selvage/CorrelatedAgreement.lean` — not re-owed here.

## Ledger

* `OpeningScheme` / `PositionBinding` / `BindingCommitment` — the layer's
  vocabulary; binding a Prop FIELD (honest floor), never an axiom.
* `idealCommitment` — the inhabitation witness, binding PROVED; `Inhabited`
  instance registered (the `Oracle.empty` pattern).
* `word_binding`, `opened_eq_committed`, `commit_injective` — derived binding
  at the word level; the deep step of every seam.
* `committed_extract_bind` / `committed_fold_bind` — `[ACC-extract-bind]`
  (a) + (c) closed at the all-positions resolution; (b) stays upstream.
* `decider_open_sound` / `decider_open_complete` — `[DEC-open]` closed at the
  same resolution, both directions.
* Keystones — satisfiable (`ideal_commit_opens`, `ideal_open_computes`),
  teeth (`ideal_binding_fires`, `ideal_binding_computes`, `seam_teeth`),
  premise inhabitation (`committed_extract_bind_fires`, `decider_open_fires`,
  `ideal_decider_accepts`), load-bearing (`equivocal_not_binding`,
  `equivocal_no_binding_extension`, `equivocal_breaks_extract_bind`).
* Residual — `[COMMIT-CR]` (prose above).
* `#print axioms`: `idealCommitment` — NO axioms; `word_binding` —
  `Quot.sound`; the seam theorems (`committed_extract_bind`,
  `committed_fold_bind`, `decider_open_sound`) — `propext`, `Quot.sound`;
  keystones add `Classical.choice` (via `decide`'s `Decidable` instances). -/

end Minidregg.Selvage
