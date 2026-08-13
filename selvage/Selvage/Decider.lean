/-
# Selvage.Decider — D_ACC: the light client's ONE-TIME final check.

LOOM §6: the accumulator defers "the proximity test — all queries, all Merkle
paths — entirely to the decider, which runs ONE WHIR descent ending in a
transparent constant-size f̂_M"; the decider opens the final accumulator and
checks the claim directly, once — the one-time price the light client pays
after the whole chain has folded (concretely 621 KiB / 4.8 ms / 10k hashes at
UD parameters, LOOM §6). This file is that check's CONTRACT, executable:

* `decider C A f` — the conjunction the decider evaluates on the claimed
  witness word `f`: (a) code membership `f ∈ C`, (b) every constraint channel
  of the final accumulated claim, `⟨f, wᵢ⟩ = σᵢ`. It is DECIDABLE whenever
  code membership and field equality are (`Decidable (f ∈ C)` +
  `DecidableEq F`), so over F₅ it genuinely COMPUTES — the keystones below
  accept and reject by `decide`, kernel-checked runs of the actual check.
* `decider_sound` / `decider_complete` / `decider_rejects` — the interface
  contract: the decider accepts EXACTLY `AccClaim.Satisfies` (definitionally —
  the decider checks the claim, nothing more, nothing less). This is the
  relation every fold-soundness bound of `Selvage/AccSound.lean` bounds, so the
  decider is precisely the point where those bounds cash out.
* `decider_constrainedRS` — on a transported constraint list the decider
  verifies exactly membership in the sibling's constrained code
  `CRS[F, dom, d, cs]` (`Selvage/ConstrainedCode.lean`): the code membership the
  decider verifies IS the CRS claim.
* **Depth independence** (LOOM §6's compression): `foldChain` iterates the
  accumulation step over an arbitrary chain; `foldChain_weights` proves the
  functional channel after ANY number of folds is the initial accumulator's
  own — depth never adds a functional — and `decider_depth_independent`
  restates the decider's verdict on a depth-`n` fold as `1 + r` atomic checks:
  one membership check plus the SAME `r` functionals evaluated once against
  `r` scalars carried by the final claim. The chain enters only through those
  scalars (and the opaque root); the check never walks the links.

**Executable membership, how**: the keystone code `RS[F₅, {0,1,2,3}, 2]` is
2-dimensional; `code_eq_span` identifies it with `span {oneWord, xWord}`, so
membership becomes a 25-case search (`Submodule.mem_span_pair` + `Fintype`) —
a genuine `DecidablePred`, and `decide` closes membership both ways
(`xWord ∈`, `outWord ∉`) where previously membership needed a hand-supplied
polynomial witness. This is EXACT membership: the strict (honest-decider) side
of LOOM §1's promise split, matching `AccClaim.Satisfies`. What the deployed
decider does at rate < 1 instead — accept δ-CLOSE words via the one-shot WHIR
descent — is `[DEC-proximity]` below; that `rt` opens to this `f` is
`[DEC-open]`. Neither is a hypothesis smuggled into a theorem here: the
statements are exact and honest about being exact.

**Keystones (ATLAS: satisfiable + teeth, BUILT, computing):** the decider
ACCEPTS the honest word on the good claim (`decider_accepts`, `decide`) and on
folded chains of depth 1 and 2 (`decider_accepts_chain` — the one-time check
AFTER folding, computing; `decider_accepts_fold` at every γ via the closure
theorem). It REJECTS through EACH conjunct separately: a codeword violating a
channel (`decider_rejects_offchannel` — membership holds, channel fails), a
word meeting every channel but outside the code (`decider_rejects_offcode` —
channels hold by `outWord_channels_ok`, membership fails by `outWord_not_mem`),
and a tampered claim on the honest word (`decider_rejects_badclaim`). Both
conjuncts are individually load-bearing; accept and reject both fire.
-/
import Selvage.ConstrainedCode
import Selvage.Accumulator

namespace Minidregg.Selvage

variable {Root : Type*} {F : Type*} [Field F] {ι : Type*} {r : ℕ}

/-! ## The decider -/

/-- **D_ACC** — the light client's one-time final check: given the final
accumulated claim `A` and a claimed witness word `f`, check (a) `f` is in the
fixed code `C`, (b) every constraint channel holds on `f` exactly. This is BY
CONSTRUCTION the conjunction `AccClaim.Satisfies` checks (`decider_sound` is
definitional): the decider's job is to decide the claim, and the claim is what
every fold-soundness bound bounds. -/
def decider (C : Submodule F (ι → F)) (A : AccClaim Root F ι r) (f : ι → F) :
    Prop :=
  f ∈ C ∧ ∀ i, A.weights i f = A.targets i

/-- The decider is a genuine DECISION procedure whenever code membership and
field equality are decidable: `1` membership check plus `r` field equalities.
Over F₅ this computes — the keystones run it by `decide`. -/
instance (C : Submodule F (ι → F)) (A : AccClaim Root F ι r) (f : ι → F)
    [Decidable (f ∈ C)] [DecidableEq F] : Decidable (decider C A f) :=
  decidable_of_iff (f ∈ C ∧ ∀ i, A.weights i f = A.targets i) Iff.rfl

/-- **The interface contract**: the decider accepts iff the accumulated claim
is genuinely satisfied by `f` — acceptance IS `AccClaim.Satisfies`
(definitionally; stated as the seam other files consume). Soundness and
completeness of the final check in one line. -/
theorem decider_sound (C : Submodule F (ι → F)) (A : AccClaim Root F ι r)
    (f : ι → F) : decider C A f ↔ AccClaim.Satisfies C A f :=
  Iff.rfl

/-- Completeness, directional form: an honest satisfying word passes the
decider. -/
theorem decider_complete {C : Submodule F (ι → F)} {A : AccClaim Root F ι r}
    {f : ι → F} (h : AccClaim.Satisfies C A f) : decider C A f :=
  (decider_sound C A f).mpr h

/-- Soundness, directional form: a word that does not satisfy the claim is
rejected. -/
theorem decider_rejects {C : Submodule F (ι → F)} {A : AccClaim Root F ι r}
    {f : ι → F} (h : ¬ AccClaim.Satisfies C A f) : ¬ decider C A f :=
  fun hd => h ((decider_sound C A f).mp hd)

/-- On a transported constraint list the decider verifies EXACTLY membership in
the constrained Reed–Solomon code `CRS[F, dom, d, cs]` of
`Selvage/ConstrainedCode.lean` — the code membership the decider checks is the
CRS claim itself (via the bridge `AccClaim.ofConstraints_satisfies_iff`). -/
theorem decider_constrainedRS [Fintype ι] [DecidableEq ι] [DecidableEq F]
    {dom : ι ↪ F} {d : ℕ} {rt : Root} {cs : List (LinearConstraint ι F)}
    {f : ι → F} :
    decider (reedSolomonCode dom d) (AccClaim.ofConstraints rt cs) f
      ↔ f ∈ constrainedRS dom d cs :=
  (decider_sound _ _ _).trans AccClaim.ofConstraints_satisfies_iff

/-! ## Depth independence — the one-time compression (LOOM §6)

The decider runs ONCE on the FINAL accumulator, whatever the chain depth: its
input type `AccClaim Root F ι r` is one root plus `r` (functional, target)
pairs for every chain length — `foldChain` below lands in that same type for
any list of links — and its verdict is `1 + r` atomic checks. The theorems
make the structural content of "cost independent of depth" machine-checked:
the functional half of the channel is INVARIANT under folding
(`foldChain_weights` — depth never adds or changes a functional), so the
decider's work on a depth-`n` fold is the SAME `r` functionals evaluated once,
compared against `r` scalars the final claim carries
(`decider_depth_independent`). What is NOT in the tree is an operation-counting
cost model — see `[DEC-succinct]` below. -/

/-- Iterated accumulation: fold a chain of (link claim, challenge) pairs into
a running accumulator, one `foldClaims` step per link. -/
def foldChain (foldRoot : Root → F → Root → Root) (A : AccClaim Root F ι r) :
    List (AccClaim Root F ι r × F) → AccClaim Root F ι r
  | [] => A
  | (B, γ) :: links => foldChain foldRoot (foldClaims foldRoot A B γ) links

@[simp] theorem foldChain_nil (foldRoot : Root → F → Root → Root)
    (A : AccClaim Root F ι r) : foldChain foldRoot A [] = A := rfl

@[simp] theorem foldChain_cons (foldRoot : Root → F → Root → Root)
    (A B : AccClaim Root F ι r) (γ : F)
    (links : List (AccClaim Root F ι r × F)) :
    foldChain foldRoot A ((B, γ) :: links)
      = foldChain foldRoot (foldClaims foldRoot A B γ) links := rfl

/-- **The functional channel is depth-invariant**: after folding an ARBITRARY
chain, the accumulated claim's functionals are the initial accumulator's own.
Folding combines targets and recommits roots; it never adds a functional —
this is the structural half of the decider's depth-independence. -/
theorem foldChain_weights (foldRoot : Root → F → Root → Root)
    (A : AccClaim Root F ι r) (links : List (AccClaim Root F ι r × F)) :
    (foldChain foldRoot A links).weights = A.weights := by
  induction links generalizing A with
  | nil => rfl
  | cons Bγ links ih =>
      obtain ⟨B, γ⟩ := Bγ
      exact ih (foldClaims foldRoot A B γ)

/-- **Depth independence of the decider's check** (LOOM §6's compression): on
the fold of ANY chain, the decider's verdict is one membership check plus the
INITIAL accumulator's `r` functionals — fixed, independent of `links.length` —
each evaluated once on `f` and compared against a single scalar carried by the
final claim. The chain enters the check only through those `r` target scalars;
the decider reads the final `AccClaim`, never the links. -/
theorem decider_depth_independent (foldRoot : Root → F → Root → Root)
    (C : Submodule F (ι → F)) (A : AccClaim Root F ι r)
    (links : List (AccClaim Root F ι r × F)) (f : ι → F) :
    decider C (foldChain foldRoot A links) f
      ↔ f ∈ C ∧ ∀ i, A.weights i f = (foldChain foldRoot A links).targets i := by
  simp only [decider, foldChain_weights]

/-! ## Keystones over F₅ (ATLAS: satisfiable + teeth, BUILT, computing)

The tiny code `RS[F₅, {0,1,2,3}, 2]` and the claims of
`Selvage/Accumulator.lean`'s `AccExample`. The new ingredient making the decider
RUN: an executable membership test for the keystone code. -/

namespace DeciderExample

open RSExample AccExample

/-- The keystone code is 2-dimensional: `RS[F₅, {0,1,2,3}, 2]` is spanned by
the constant word and the identity word (evaluations of `1` and `X`). This is
what makes v0 decider membership EXECUTABLE: span membership over F₅ is a
finite search. -/
theorem code_eq_span :
    reedSolomonCode dom₅ 2
      = Submodule.span (ZMod 5) {AccExample.oneWord, xWord} := by
  apply le_antisymm
  · rintro f hf
    rw [mem_reedSolomonCode_iff] at hf
    obtain ⟨p, hdeg, heval⟩ := hf
    rcases eq_or_ne p 0 with rfl | hp0
    · have hf0 : f = 0 := funext fun i => by simpa using heval i
      rw [hf0]
      exact Submodule.zero_mem _
    · have hle : p.degree ≤ 1 := by
        have hnd : p.natDegree ≤ 1 := by
          have h2 := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hdeg
          omega
        exact_mod_cast Polynomial.natDegree_le_iff_degree_le.mp hnd
      have hp := Polynomial.eq_X_add_C_of_degree_le_one hle
      rw [Submodule.mem_span_pair]
      refine ⟨p.coeff 0, p.coeff 1, ?_⟩
      funext i
      have hfi := heval i
      rw [hp] at hfi
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X] at hfi
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, AccExample.oneWord,
        xWord, hfi, dom₅, Function.Embedding.coeFn_mk]
      ring
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨oneWord_mem, xWord_mem⟩

/-- Membership in the keystone code DECIDES: `f ∈ RS[F₅, {0,1,2,3}, 2]` is the
25-case span search `∃ a b, a • oneWord + b • xWord = f`. -/
instance : DecidablePred (· ∈ reedSolomonCode dom₅ 2) := fun f =>
  decidable_of_iff (∃ a b : ZMod 5, a • AccExample.oneWord + b • xWord = f)
    (by rw [code_eq_span]; exact Submodule.mem_span_pair.symm)

/-- Membership now computes — where `xWord_mem` needed a hand-supplied
polynomial witness, the decider's membership conjunct closes by `decide`. -/
example : xWord ∈ reedSolomonCode dom₅ 2 := by decide

/-! ### Satisfiable: the decider ACCEPTS -/

/-- **Satisfiable, computing**: the decider ACCEPTS the honest word on the good
claim — the full check (code membership AND both channels of the WARP-shape
claim) runs by `decide`. -/
theorem decider_accepts :
    decider (reedSolomonCode dom₅ 2) goodClaim xWord := by decide

/-- The decider run ONCE after a depth-2 chain fold: the folded word of the
chain `evalA ←(γ=3)— evalB1 ←(γ=2)— evalB0`. -/
def chainWord : Fin 4 → ZMod 5 :=
  xWord + (3 : ZMod 5) • AccExample.oneWord
    + (2 : ZMod 5) • (0 : Fin 4 → ZMod 5)

/-- **The one-time check after folding, computing**: the decider accepts the
honestly-folded word of a DEPTH-2 chain — `foldChain` compresses the links
into one claim, and the single decider pass closes by `decide`. -/
theorem decider_accepts_chain :
    decider (reedSolomonCode dom₅ 2)
      (foldChain trivialRoot evalA [(evalB1, 3), (evalB0, 2)]) chainWord := by
  decide

/-- Premise inhabitation at every challenge: the decider accepts the folded
word of an honest depth-1 fold for EVERY γ, by the closure theorem — the
decider is exactly where `foldClaims_satisfies` cashes out. -/
theorem decider_accepts_fold (γ : ZMod 5) :
    decider (reedSolomonCode dom₅ 2)
      (foldClaims trivialRoot evalA evalB1 γ) (xWord + γ • AccExample.oneWord) :=
  decider_complete (fold_honest_nonzero γ)

/-! ### Teeth: the decider REJECTS — through each conjunct separately -/

/-- **Channel teeth, computing**: `oneWord` IS in the code (`oneWord_mem`) but
violates the good claim's channels (`q2 oneWord = 1 ≠ 2`) — the decider
rejects on the channel conjunct alone. -/
theorem decider_rejects_offchannel :
    ¬ decider (reedSolomonCode dom₅ 2) goodClaim AccExample.oneWord := by
  decide

/-- A word rigged to meet BOTH channels of the good claim (`f 2 = 2`,
`∑ f i = 1`) while lying OUTSIDE the code. -/
def outWord : Fin 4 → ZMod 5 := ![0, 0, 2, 4]

/-- `outWord` passes every channel check of the good claim… -/
theorem outWord_channels_ok :
    ∀ i, goodClaim.weights i outWord = goodClaim.targets i := by decide

/-- …but is not a codeword… -/
theorem outWord_not_mem : outWord ∉ reedSolomonCode dom₅ 2 := by decide

/-- **Membership teeth, computing**: the decider rejects `outWord` — with the
channels all passing (`outWord_channels_ok`), the rejection is carried by the
code-membership conjunct ALONE. Both conjuncts are load-bearing. -/
theorem decider_rejects_offcode :
    ¬ decider (reedSolomonCode dom₅ 2) goodClaim outWord := by decide

/-- **Tampered-claim teeth, computing**: on the HONEST word, a claim with
doctored targets (`badPair`) is rejected — the decider protects the claim
against the word and the word against the claim. -/
theorem decider_rejects_badclaim :
    ¬ decider (reedSolomonCode dom₅ 2) badPair xWord := by decide

end DeciderExample

/-! ## Residual obligations — prose, not stubs

Named residuals with their realizers; each becomes a real theorem, never a
`def : Prop := True` (the audit discipline).

**[DEC-proximity]** — the deployed decider at rate < 1 does not check EXACT
membership of the huge word: it runs the one-shot WHIR descent (the proximity
test deferred from every link — all queries, all Merkle paths, ending in the
transparent constant-size `f̂_M`; LOOM §6), which accepts words δ-CLOSE to the
code and carries the descent's own RBR error. This file's decider is the
strict (honest-decider) side of LOOM §1's promise split — exact membership,
matching `AccClaim.Satisfies` on the nose — which is the RIGHT contract for
the claim level: the δ-slack lives in extraction (`[ACC-extract]`) and in the
fold-soundness bounds (`Selvage/AccSound.lean`), never in the claim relation.
What remains under this residual: the WHIR descent itself as a derived object
(per-round folding checks, query/Merkle-path verification, the final
`f̂_M` read-off) and its checked cost constants (621 KiB / 4.8 ms / 10k hashes
at UD; 299 KiB / 2.5 ms at Johnson — LOOM §6). Until it lands, "the decider
verifies code membership" is priced at the exact-membership resolution only.

**[DEC-open]** — the decider consumes the witness word `f` as given: that the
final accumulator's commitment `rt` BINDS and OPENS to this `f` (Merkle/BCS
binding, the opened columns) is the commitment layer's obligation — the same
seam `[ACC-extract]` consumes, which is why neither the fold algebra nor the
decider ever inspects `Root`. No theorem in this file claims anything about
`rt`; `decider_sound` is exactly the claim-level contract conditional on the
opening being the committed word.

**[DEC-succinct]** — the compression property, status: the STRUCTURAL content
is proved (`foldChain_weights`: the functional channel after any chain is the
initial accumulator's own; `decider_depth_independent`: the verdict on a
depth-`n` fold is `1 + r` atomic checks against the final claim's scalars;
type-level: `foldChain` lands in `AccClaim Root F ι r` — one root, `r` pairs —
for every chain length, the accumulator's constant size). What is NOT in the
tree: an operation-counting cost model (a machine semantics for the checker)
under which "decider time is O(1) in chain depth" is a theorem rather than a
reading of the above; that model, if ever wanted, prices the membership check
too (`[DEC-proximity]`'s descent is where the real verifier cost lives). -/

end Minidregg.Selvage
