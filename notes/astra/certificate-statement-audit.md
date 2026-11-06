# Astra certificate statement audit — 2026-11-06 task

[READ] Corpus: `docs/CERTIFICATES.md` at zkml-research `439da79ca95432ee5f428bb6b77c6d3b8347453d`, the complete `notes/selvage-foundations-critique-2026-11-05.md` and `notes/proof-system-codex-synthesis.md`, and the specific Lean sources listed below. The label is the requested task date; this run began on 2026-11-05 America/Los_Angeles. Companion source snapshots: minidregg `c4ecabe0fad1c8b9eb32a6b3cc2340f689078f55`, breadstuffs `22fad151e9f118e3aa001a823e075918ffa139e8`. No companion-tree files were modified.

[DERIVED] **28 distinct obligations audited: 7 definite contract/prose defects, 6 interface or scope qualifications, and 15 fine statements/tests.** Thirteen obligations receive repairs or explicit qualifications; this is not a claim of thirteen false Lean theorems. These are 19 structures, relations, laws and implementation statements, plus the nine proposed falsifiers. Aliases are deduplicated: P1 is the structure, P2 the three named relations, P3=L6, P4=L3, P5=L1, P7=L2 plus its digest-width implementation requirement, P8=L4. Each falsifier is separately identified because it is a distinct proposed assertion; the count does not count the same law twice. Syntax-only normalizations do not count as semantic defects.

[EXECUTED] `certificates/CertificateAudit.lean` contains **15 proved model facts**, with `#guard_msgs`-pinned axiom reports, no `sorry`, `axiom`, or `native_decide`. `certificates/StatementSchemas.lean` contains checked definitions of the repaired statement targets as `Prop` values. **Typechecking a `Prop` definition is not proving that proposition.** Both compile with installed Lean 4.35.0 and core `Lean`, without a Lake build or dependency download. Exact commands, exit statuses and output are in `certificates/validation.json`, `lean-check.log`, and `schema-check.log`. Disk availability was 133 GiB before compilation, above the clarified 30 GiB threshold.

## Inventory and verdicts

[READ] Line numbers below refer to `docs/CERTIFICATES.md` in the snapshot above. [DERIVED] “Fine” means the specified mathematical relation or conditional target is sensible; it does not assert a deployed cryptographic instance.

| ID | Source | Statement / alias | Verdict | Repair or witness |
|---|---|---|---|---|
| CS01 | 60–68; P1 233–237 | `ContentScheme`, claimed computational binding | **Too weak / unconnected bound** | Put executions, admissibility, setup/oracle world, actual winning event and reduction cost in the contract; add length completeness/binding. §1 |
| CS02 | 75; P2 239–241 | `SubstringAt` | Fine | Explicit range and exact slice; six-symbol positive/negative example. §2 |
| CS03 | 76; P2 | `OccursIn` | Fine | Existential position; do not claim position privacy without ZK. §2 |
| CS04 | 77 | `MatchesAt` | **Too weak** | Require `i ≤ j ≤ length`; clamped invalid spans otherwise match nullable regexes. §2 |
| CS05 | 78 | `FormOK` | Fine | Grammar language is an explicit semantic predicate. §2 |
| CS06 | 79 | `Framed` | Fine | Exact render plus separately defined guarded-safety predicate; no global safety claim. §2 |
| CS07 | 80; P2 | `Absent` | Fine after disambiguating literal vs language | Nullable patterns occur at empty spans; absence then false. §2 |
| CS08 | 81 | `AllRecords` | Fine as existential committed-list relation | Bind `L` explicitly and preserve length/order in its root; not coverage of real-world arrivals. §2 |
| CS09 | 82 | `Produced` | **Qualification: input/context interpretation unspecified** | Bind an actual input witness and complete inference context, not an unexplained `prompt c_in`. §2 |
| CS10 | 84–90 | Certificate / `Sound` | **Qualification: experiment/extractor interface unspecified** | Quantify adversary, experiment and efficient log extractor; preserve relation and encoding on instantiation. §3 |
| CS11 | L0 99–101 | Content well-formedness | Fine, deliberately structural | `R x w → commit w = root x`; does not prove that verifier checks R. §3 |
| CS12 | L1 103–107; P5 261–269 | `cert_and` | **Missing hypotheses / bound unjustified** | Shared execution, whole-word including length binding, admissible joint extraction reduction and its budget. §4 |
| CS13 | L2 109–114; P7 282–285 | Aggregation and replacement by `ε_engine` | **Qualification: numeric/semantic scope unspecified** | Distinguish existential aggregate from canonical-content claim; no automatic disappearance of leaf errors under recursion. §5 |
| CS14 | L3 116–121; P4 252–255 | Padded complement | Fine mathematically | Use actual `.cat` syntax and bounded spans or prefix/middle/suffix decomposition. §6 |
| CS15 | L4 123–128; P8 287–290 | Model/certificate bridge | **Missing binding legs** | Three proof errors plus two same-content binding reductions, unless bridge error explicitly includes them. §7 |
| CS16 | L5 130–133 | Scheme morphism transport | **Qualification: morphism undefined; mere computability insufficient** | Prove same-word commitment square commutes; existential transport itself adds no binding loss. §8 |
| CS17 | L6 135–137; P3 243–250 | Openings imply substring certificate | **Too weak in P3; too strong as §1 knowledge certificate** | Verify length and range; provide reference content or separate extraction. No phantom-word inference. §9 |
| CS18 | P6 271–280 | Content-bound DFA soundness | **Qualification: new kernel/crypto hypotheses elided** | Word-linked extracted trace, content-aware verifier, probabilistic error; handle empty-word acceptance. §10 |
| CS19 | P9 292–295 | All-lane weld denotation | Fine target, not sufficient alone | Check every recomputed opening lane; still need routing and computational binding. §11 |
| CF01 | P1 234–237 | Toy equivocation falsifier | Fine for named toy | Explicit colliding pair and executable attack; not “all compression implies easy collision at every budget.” §12 |
| CF02 | P2 239–241 | Position-sensitive six-byte test | Fine | `position_matters`. §12 |
| CF03 | P3 250 | Omitted-opening falsifier | Fine | `[0,1]` vs claimed `[0,2]`, opening only index zero. §12 |
| CF04 | P4 256–259 | Whole-word complement is not absence | Fine | Word `[0,1,0]`, literal language `{[1]}`. §6/§12 |
| CF05 | P5 267–269 | Two sound legs, false conjunction | Fine | Same root for `[]` and `[()]`, predicates length zero and one. §4/§12 |
| CF06 | P6 278–280 | Old DFA accepts splice, new relation refuses | Fine | Accepting nonempty all-zero run; target word contains one. §10/§12 |
| CF07 | P7 282–285 | One-felt collision refutes `AllRecords` soundness | **Qualification: bound and reference semantics unspecified** | Exhibit two concrete histories/properties, accepted evidence, failure event and bound violated. Width alone is not soundness. §5/§12 |
| CF08 | P8 287–290 | Different word necessarily refused unless K collides | **Too strong** | Invalid proofs can accept on proof-soundness failure too; total bad event includes all proof and binding legs. §7/§12 |
| CF09 | P9 292–295 | No two different lane vectors may satisfy descriptor | **Too strong as stated in prose** | Fix opening transcript/leaf/path and public context; one altered lane must refuse. Distinct honest roots remain legal. §11/§12 |

## 1. Computational binding is a contract, not a number (CS01)

[READ] The source defines `bindAdv : ℕ → ℝ≥0` but no field connecting it to a probability or adversary. `verifyLen` has neither completeness nor a binding game. The comment mentions only *position* equivocation. That game cannot detect different lengths with identical prefixes. The field itself is fully inhabited even with `bindAdv := fun _ => 0` and a verifier that accepts both Boolean values at every index: `unbacked_advantage` proves the defect.

The original Lean-shaped assertion being relied upon is:

```lean
-- Invalid inference from the structure in CERTIFICATES alone:
def OriginalBindingClaim (S : ProposedScheme Sym D Op)
    (Pr : (Attack → Prop) → Rat) (win : Attack → Prop) (q : Nat) : Prop :=
  Pr win ≤ (S.bindAdv q : Rat)
```

[DERIVED] The repaired interface separates syntax/completeness from a security assertion. The compiled `StatementSchemas.lean` gives the exact declaration, summarized here:

```lean
structure ContentScheme (Sym Digest Op LenOp : Type) where
  commit : List Sym → Digest
  openAt : List Sym → Nat → Op
  openLen : List Sym → LenOp
  verifyOpen : Digest → Nat → Sym → Op → Bool
  verifyLen : Digest → Nat → LenOp → Bool
  complete : ∀ w i (h : i < w.length),
    verifyOpen (commit w) i w[i] (openAt w i) = true
  lengthComplete : ∀ w, verifyLen (commit w) w.length (openLen w) = true

inductive BindingWitness where
  | word (u v : List Sym)
  | position (c : Digest) (i : Nat) (v v' : Sym) (o o' : Op)
  | length (c : Digest) (n m : Nat) (o o' : LenOp)

-- BindingWin checks actual equal-root distinct-word pairs, or two accepted
-- incompatible position/length openings. It never means “some collision exists”.
def ComputationalBinding {A Ω : Type} (G : Game A Ω)
    (Sω : Ω → ContentScheme Sym Digest Op LenOp)
    (output : A → Ω → BindingWitness)
    (ε : Nat → Rat) : Prop :=
  ∀ q a, G.admissible q a →
    (G.experiment a).prob
      (fun ω => BindingWin (Sω ω) (output a ω)) ≤ ε q
```

[DERIVED] `Ω` includes sampled keys or the random-oracle world when those are part of the claim. A fixed deterministic compressing hash plus arbitrary nonuniform hardcoded attackers does **not** support an all-adversary tiny error merely by counting runtime hash queries: an attacker can contain a colliding pair in its code. Restricting and implementing the adversary model, setup distribution and resource accounting is load-bearing. `Game.admissible` is a named *interface obligation*, not a claim that any proposed implementation satisfies it. `ReductionWithin` in the schemas requires that each composed attacker fits the actual target budget. A deployed keyed/ROM instance is [OPEN].

[EXECUTED] `prefix_perfect_position_binding` and `prefix_word_collision` show a second independent defect: over the one-symbol alphabet `Unit`, **every** position-equivocation game is unwinnable, yet `[]` and `[()]` can have the same root. Thus adding only the position game from lines 66–67 would still not repair L1. Comparing lengths first and then a differing index gives an efficient full-word collision reduction once length completeness/binding are supplied.

[DERIVED] A probability also needs a query parameter. Lines 151–154 conflate collision work factor with advantage. For an ideal uniform hash into `p` values and `q` *distinct* queried inputs, collision probability is at most `q(q−1)/(2p)` (and is approximately that when small); fixed-target search is at most `q/p`. At BabyBear `p = 2013265921`, two queried inputs collide with probability `1/p ≈ 4.97×10⁻¹⁰`, not `2⁻¹⁵⋅⁵`. Around `sqrt(p)` queries one gets constant collision probability; “15.5-bit birthday work” is not an ε. Likewise “124-bit collision security” of an eight-lane ideal digest is not `ε = 2⁻¹²⁴` independent of query count. These are ideal-function formulas, not a cryptanalysis theorem for Poseidon2. This is part of CS01's quantification defect, not an extra counted statement.

## 2. The eight content relations (CS02–CS09)

[DERIVED] These are Lean syntax, not prose shorthand; the complete declarations compile in `StatementSchemas.lean`. For `S : ContentScheme Sym Digest Op LenOp`:

```lean
def SpanAt (w : List Sym) (i : Nat) (p : List Sym) : Prop :=
  i + p.length ≤ w.length ∧ (w.drop i).take p.length = p

def SubstringAt (c : Digest) (i : Nat) (p w : List Sym) : Prop :=
  S.commit w = c ∧ SpanAt w i p

def OccursIn (c : Digest) (p w : List Sym) : Prop :=
  ∃ i, SubstringAt S c i p w

-- Original MatchesAt lacked the two inequalities:
def OriginalMatchesAt (accepts : List Sym → Regex → Prop)
    (c : Digest) (i j : Nat) (r : Regex) (w : List Sym) : Prop :=
  S.commit w = c ∧ accepts ((w.drop i).take (j - i)) r

def MatchesAt (accepts : List Sym → Regex → Prop)
    (c : Digest) (i j : Nat) (r : Regex) (w : List Sym) : Prop :=
  S.commit w = c ∧ i ≤ j ∧ j ≤ w.length ∧
    accepts ((w.drop i).take (j - i)) r

def FormOK (language : List Sym → Prop) (c : Digest) (w : List Sym) : Prop :=
  S.commit w = c ∧ language w

def Framed (render : Data → List Sym) (safe : Data → Prop)
    (c : Digest) (w : List Sym) : Prop :=
  S.commit w = c ∧ ∃ d, w = render d ∧ safe d

def AbsentLiteral (c : Digest) (p w : List Sym) : Prop :=
  S.commit w = c ∧ ∀ i, ¬ SpanAt w i p

def AbsentLanguage (language : List Sym → Prop) (w : List Sym) : Prop :=
  ¬ ∃ pre mid post, w = pre ++ mid ++ post ∧ language mid

def AllRecords (mroot : List Digest → Root) (r : Root)
    (n : Nat) (φ : List Sym → Prop) : Prop :=
  ∃ roots : List Digest, mroot roots = r ∧ roots.length = n ∧
    ∀ c ∈ roots, ∃ w, S.commit w = c ∧ φ w
```

[EXECUTED] `position_matters` inhabits SubstringAt at position 2 and refutes it at 1. `clamped_span` exhibits the CS04 defect: `(drop 99 [1]).take 1 = []`, so a nullable regex accepts the claimed span `[99,100)` of a one-symbol word. Explicit bounds refuse it. Empty pattern handling is deliberate: an empty pattern occurs at positions `0..length`, so literal absence of the empty pattern is false for every word.

[DERIVED] Witnesses for the other fine relations: any word with its honest commitment and itself as `p` gives OccursIn; grammar language `fun w => w = [()]` gives an inhabited, discriminating FormOK; `render := id`, `safe := fun w => w = [()]` does likewise for Framed. `AllRecords` is inhabited by the exact root of `[commit [()]]`, `n=1`, and predicate length one. `n=0` is legitimately vacuous only for a claim about an empty *committed corpus*. It says nothing about whether every external record was admitted into that corpus. Recording a count is not external non-omission.

[READ] The original Produced relation at line 82 uses `prompt c_in` without specifying an opening or encoding. Reconstructing its intended syntax exposes the gap:

```lean
def OriginalProduced (weights : Model → Weights) (prompt : Digest → List Sym)
    (eval : Weights → List Sym → List Sym → Prop)
    (m : Model) (cin cout : Digest) : Prop :=
  ∃ out, eval (weights m) (prompt cin) out ∧ S.commit out = cout
```

[DERIVED] An arbitrary `prompt` can map every digest to `[]`, proving outputs for an unrelated prompt. The repair puts both opened words in the relation and makes the semantic context explicit:

```lean
structure InferenceStatement (Model Context Digest : Type) where
  model : Model
  context : Context
  input : Digest
  output : Digest

def Produced (eval : Model → Context → List Sym → List Sym → Prop)
    (s : InferenceStatement Model Context Digest) (input output : List Sym) : Prop :=
  S.commit input = s.input ∧ S.commit output = s.output ∧
    eval s.model s.context input output
```

`Context` must bind the tokenizer/detokenizer, arithmetic version, generation rule/randomness and any KV/prefix/RAG state that affects the claimed inference. A model identifier must bind weights and architecture under its own stated relation. These do not all need separate fields if one canonical context commitment covers them. An identity model with explicit input/output commitments is an inhabited toy; the actual FlashProve relation transport is [OPEN], not a definitional substitution justified by similar theorem shape.

## 3. Knowledge soundness and L0 (CS10–CS11)

[READ] Lines 84–90 describe one soundness formula without defining the probability space, allowed adversaries, extractor budget, or composition under a shared oracle. Original syntax at the level specified is only:

```lean
def OriginalSound (Pr : (Ω → Prop) → Rat) (accept badExtraction : Ω → Prop)
    (ε : Rat) : Prop := Pr (fun ω => accept ω ∧ badExtraction ω) ≤ ε
```

[DERIVED] That is a meaningful fixed-experiment inequality but not a cryptographic universal theorem. The checked replacement is:

```lean
def KnowledgeSound {A Ω X Proof Log W : Type} (G : Game A Ω)
    (stmt : A → Ω → X) (proof : A → Ω → Proof) (log : A → Ω → Log)
    (verify : Ω → X → Proof → Bool) (relation : Ω → X → W → Prop)
    (extract : Log → W) (ε : Nat → Rat) : Prop :=
  ∀ q a, G.admissible q a → (G.experiment a).prob (fun ω =>
    verify ω (stmt a ω) (proof a ω) = true ∧
    ¬ relation ω (stmt a ω) (extract (log a ω))) ≤ ε q
```

An actual package additionally carries an extractor construction and its efficiency bound (or an explicitly weaker non-efficient knowledge notion). For independent certificates the component attacker is the projection of the **joint** attacker in the same run, including its adaptive auxiliary information and oracle use. An always-reject verifier inhabits soundness trivially; a completeness instance accepting an honest committed word and a false-input refusal test are therefore separate requirements. `φ := True` alone is not a useful demonstration.

L0 is correctly a structural rule:

```lean
def BindsContent (root : X → Digest) (relation : X → List Sym → Prop) : Prop :=
  ∀ x w, relation x w → S.commit w = root x
```

It does not establish `KnowledgeSound`; adding a digest field which the verifier ignores is still insecure.

## 4. Conjunction (CS12 and CF05)

[READ] The proposed theorem is:

```lean
-- Original header, with implicit types supplied by its undefined Sound interface:
theorem cert_and (S : ContentScheme Sym D Op)
    (h₁ : Sound S V₁ φ₁ ε₁) (h₂ : Sound S V₂ φ₂ ε₂) :
  Sound S (fun x π => V₁ x π.1 && V₂ x π.2)
    (fun w => φ₁ w ∧ φ₂ w) (fun q => ε₁ q + ε₂ q + S.bindAdv q)
```

[EXECUTED] The exact deterministic repair is already proved in `CertificateAudit.lean`:

```lean
theorem conjunction_or_collision (commit : W → D) (c : D)
    (φ ψ : W → Prop) (u v : W)
    (hu : commit u = c ∧ φ u) (hv : commit v = c ∧ ψ v) :
    (commit u = c ∧ φ u ∧ ψ u) ∨
      (u ≠ v ∧ commit u = commit v)
```

[DERIVED] This disjunct names the **actual extracted words**, not an existential collision anywhere in the scheme. The probability target in `ConjunctionBound` is the union-bound lift on a shared experiment and world-indexed commitment:

```lean
-- w₁,w₂,c,accept₁,accept₂ are functions of the same ω.
-- bad₁ := accept₁ ∧ ¬(commitω w₁ = c ∧ φ w₁), similarly bad₂.
-- badBind := commitω w₁ = c ∧ commitω w₂ = c ∧ w₁ ≠ w₂.
theorem cert_and_fixed_run
    (h₁ : μ.prob bad₁ ≤ ε₁) (h₂ : μ.prob bad₂ ≤ ε₂)
    (hb : μ.prob badBind ≤ β) :
    μ.prob (fun ω => accept₁ ω ∧ accept₂ ω ∧
      ¬ (commitω ω (w₁ ω) = c ω ∧ φ (w₁ ω) ∧ ψ (w₁ ω))) ≤ ε₁ + ε₂ + β
```

The complete typed target is in `ConjunctionBound`; the displayed theorem header abbreviates its event definitions. To replace `β` by a library advantage requires constructing the attacker that emits `(.word w₁ w₂)`, simulating both extractors, and proving admissibility at `q' = reductionBudget q`, not silently reusing `q`. The bounds for the two proof projections may need their own budget transforms. Neither independence of the two proofs nor an independent collision event is required.

[EXECUTED] `two_true_legs_false_join` is the requested falsifier and also catches the missing length game: use a constant-root one-symbol scheme, `φ w := w.length = 0`, `ψ w := w.length = 1`, with extracted words `[]` and `[()]`. Each component is perfectly sound for its existential relation; no word can satisfy both. The position game never breaks on the one-symbol alphabet. The length/whole-word game is therefore essential.

## 5. Aggregation, recursion and digest width (CS13 and CF07)

[DERIVED] The phrase “union bound” in L2 hides **two distinct claims**. If the conclusion is exactly the existential `AllRecords` relation written in §1, and one explicit list `roots` has been extracted/authenticated, then each extracted `w_k` is already a witness for its root. **No content-binding term is needed merely to assemble those existential witnesses.** The source’s extra nonnegative binding term is thus not itself a false upper bound under this interpretation; it is unnecessary accounting. The pure target is:

```lean
def AggregateExtracted (mroot : List Digest → Root) (r : Root)
    (n : Nat) (φ : List Sym → Prop) (roots : List Digest) : Prop :=
  mroot roots = r → roots.length = n →
  (∀ c ∈ roots, ∃ w, S.commit w = c ∧ φ w) → AllRecords S mroot r n φ
```

For a fixed list of `N` component proof failures, `ε_MMR + ∑ k, ε_k` bounds existential aggregate failure. If the intended claim is instead “the *actual canonical* N documents have φ,” every extracted `w_k` must agree with its corresponding reference document. Then either add `∑ k, β_k` or supply a **single joint multi-instance binding reduction** that finds and outputs a first unequal pair, with the budget for all N extractions. It is unjustified to silently treat a per-root `bindAdv_S(q)` as a multi-root bound at the same cost. Root-list authentication likewise requires an explicit MMR length/order scheme and a named extraction or equivocation reduction.

[READ] The original line 112 says recursion turns `N·ε` into `ε_engine`. [DERIVED] A recursive proof that only establishes “all N *verifiers accepted*” retains the leaf soundness errors. The replacement is legal only if `ε_engine` is already a bound for the **final aggregate semantic relation**, including leaves, binding and recursion, or if that relation is directly reproved inside the engine. A new outer soundness theorem about verifier computation does not erase the semantic failures of its leaves.

[READ] Crucially, actual `RecursiveAggregation.lean:121–154` already bundles `recursive_sound`, `leaf_sound`, and `binding_sound` in `EngineSound`; `:221–225` consumes that whole package. Its conditional theorem does **not** assert that outer verification alone erases leaf errors. The qualification here concerns the unprovided numerical ε-engine instantiation and what the prose means by replacing `N·ε`. It is not a refutation of that Lean theorem.

The exact event target, checked in `AggregateFailureBound`, is:

```lean
def AggregateFailureBound (μ : Experiment Ω) (n : Nat)
    (bad : Fin n → Ω → Prop) (aggregateBad : Ω → Prop)
    (ε : Fin n → Rat) : Prop :=
  (∀ ω, aggregateBad ω → ∃ k, bad k ω) →
  (∀ k, μ.prob (bad k) ≤ ε k) →
    μ.prob aggregateBad ≤ (List.ofFn ε).foldr (· + ·) 0
```

[DERIVED] Changing `Digest` from one felt to eight does not prove this reduction or the probability bounds. Eight constant lanes are eight lanes and still admit certain equivocation. A one-felt collision alone does not refute the existential relation “there exists a root-list whose words have φ”: the good colliding list may witness it. CF07 must name the **reference list** and property, produce an accepted false claim about it, and violate a specified error bound. The corrected test is:

```lean
-- Pr is the explicitly specified attack experiment, Good is relative to reference.
def CorpusFalsifier (Pr : (Ω → Prop) → Rat) (accepted Good : Ω → Prop)
    (claimedError : Rat) : Prop :=
  claimedError < Pr (fun ω => accepted ω ∧ ¬ Good ω)
```

For example, the constant-root toy with reference word `[()]`, property “empty,” and certificate/extractor for `[]` has false canonical-content acceptance probability one. Its existential AllRecords claim is true, which is exactly why naming the semantics matters. A real digest8 instance and its joint game are [OPEN].

## 6. Padded complement and its falsifier (CS14, CF04)

[READ] Actual constructors in `Dregg2/Crypto/Deriv/Core.lean:41–64` are `.cat`, `.star`, `.neg`; `any` is an abbreviation for `.sym .tt`, not an inductive constructor. `derives` returns `Bool`; `derives_cat` is at `Correctness.lean:118–120`, `derives_neg` at 103–107, and correctness at 267–268. The source sketch's `.star .any ++ r` is not the actual regex concatenation syntax.

The repaired statement uses a decomposition, so there are no out-of-range spans or ambiguous `List.slice` conventions:

```lean
-- In namespace Dregg2.Crypto.Deriv.PredRE:
theorem absent_iff_padded_complement (w : List Value) (r : PredRE) :
    (¬ ∃ pre mid post, w = pre ++ mid ++ post ∧ derives mid r = true) ↔
    derives w (.neg (.cat (.star any) (.cat r (.star any)))) = true

theorem whole_word_complement_is_not_absence :
    ∃ w r, derives w (.neg r) = true ∧
      ∃ pre mid post, w = pre ++ mid ++ post ∧ derives mid r = true
```

[DERIVED] These are mathematical targets supported by the stated semantic lemmas; the actual Dregg2 theorems were not compiled in this run. The abstract target `PaddedComplement` compiles. [EXECUTED] The explicit one-symbol-language model `complement_not_absence` proves a nonempty witness: `[0,1,0]` is not `[1]` but contains it. This is stronger than choosing the empty regex/empty word, and pins the intended trap. For a regex accepting ε, every word has an accepted empty span and padded-complement absence is correctly false.

## 7. Cross-scheme bridge (CS15, CF08)

[READ] L4 gives error `ε_inf + ε_c + ε_bridge`, then explains that a bridge proves one word opens under both schemes. Let the inference extractor return `a`, the bridge extractor `b`, and the property extractor `d`. Successful extraction yields:

```lean
S.commit a = c ∧ Produced a
S.commit b = c ∧ T.commit b = c'
T.commit d = c' ∧ Property d
```

[DERIVED] These facts do not identify `a=b=d`. A bridge can be perfectly sound and still extract a different word than either endpoint when either commitment collides. The repaired pointwise target `BridgeJoin` is:

```lean
def BridgeJoin (a b d : List Sym) (c : Digest) (c' : Digest') : Prop :=
  S.commit a = c ∧ produced a →
  S.commit b = c ∧ T.commit b = c' →
  T.commit d = c' ∧ property d →
  (produced a ∧ property a) ∨
    BindingWin S (.word a b) ∨ BindingWin T (.word b d)
```

The generic probability bound is therefore `ε_inf + ε_bridgeProof + ε_property + β_S + β_T` at their actual reduction budgets, on one common world. L4's shorter formula can be retained **only by defining** `ε_bridge := ε_bridgeProof + β_S + β_T` and documenting that convention. For a fused relation extracting one shared word, the extra comparisons and their binding legs disappear; the fused proof's own soundness still remains.

[DERIVED] CF08's blanket “different word is refused unless K collides” misses ordinary proof-soundness failure. Even an injective content map can have a verifier with a nonzero erroneous acceptance probability. The repaired assertion is the event inclusion:

```lean
-- Actual events from the three proof extractors and two emitted collision pairs.
def AlienWordFailureCovered : Prop :=
  ∀ ω, AcceptedFalseWeld ω →
    BadInference ω ∨ BadBridgeProof ω ∨ BadPropertyProof ω ∨
      BindS ω ∨ BindT ω
```

An instantiated small adversary should exercise both (i) a collision attack and (ii) a false-proof acceptance event, rather than test only collision rejection. The FlashProve source theorem and its public-input encoding still need a concrete adapter; these notes do not assert that theorem has been instantiated over TK.

## 8. Scheme transport (CS16)

[READ] L5 gives only “a map of content schemes ... computable in the certificate prover.” It does not specify a commuting diagram or the relation mapped.

```lean
-- Original claimed implication, too weak a premise:
def OriginalTransport (f : Digest → Digest') (computable : (Digest → Digest') → Prop) : Prop :=
  computable f → ∀ c w,
    S.commit w = c ∧ φ w → T.commit w = f c ∧ φ w
```

[DERIVED] Choose `f` constant while `T.commit` distinguishes the source word: the claim fails despite trivial computability. The repaired target is:

```lean
def SchemeMorphism (f : Digest → Digest') : Prop :=
  ∀ w, f (S.commit w) = T.commit w

theorem transport_same_witness (s : W → D) (t : W → D') (f : D → D')
    (commutes : ∀ w, f (s w) = t w) (φ : W → Prop)
    (w : W) (c : D) (h : s w = c ∧ φ w) : t w = f c ∧ φ w
```

[EXECUTED] The theorem is proved in `CertificateAudit.lean`, with no axioms. [DERIVED] For this *same-extracted-word existential relation*, the soundness error remains `ε_V`; no binding loss is required. The extra terms belong to a subsequent reference-word or separately extracted-witness join. For two unrelated hashes there need not be an efficient digest-to-digest `f`; proving both hashes on one witness is the bridge construction of §7, with its own proof cost/error. “Same alphabet” alone supplies no morphism. Identity schemes/morphisms are inhabited positive examples.

## 9. Tier one, vacuity and phantom roots (CS17)

[READ] P3 quantifies:

```lean
∀ w, S.commit w = c → i + P.length ≤ w.length →
  SubstringAt S c i P w ∨ BindBreak S c
```

[DERIVED] This can be true when `c` has no preimage, and true for an out-of-range `i`; neither authenticates the claimed range. With `P=[]`, its only acceptance premise is vacuous. `unchecked_empty_pattern` proves that an out-of-range empty pattern passes all zero opening checks. Furthermore, if `BindBreak S c` means “there exists any collision,” it can be globally true even when no efficient attacker has found it. A computational statement must concern the attack's **named output pair**, not globally quantified collision existence.

[EXECUTED] `phantomCommit w := some w` is injective. The extra digest `none` is accepted as a one-symbol root; each symbol is `Unit`, so position uniqueness is perfect, and `phantom_length_unique` proves length uniqueness. `phantom_no_word` nevertheless proves `¬ ∃ w, phantomCommit w = none`. This is a concrete falsifier of “openings plus binding imply existence/knowledge of a whole word.” It models the missing-preimage problem of an opaque/fabricated sibling digest without claiming a cryptanalytic attack on a deployed tree.

[DERIVED] A tier-one verifier must check `(i+|P| ≤ n)`, a length opening to `n`, and every required symbol opening. Its suitable guarantee is relative to an independently supplied committed reference `w` (or an earlier extraction/certification of that reference):

```lean
-- The complete family-indexed target is TierOneRelative in StatementSchemas.
def TierOneRelative (μ : Experiment Ω)
    (Sω : Ω → ContentScheme Sym Digest Op LenOp)
    (reference pattern : Ω → List Sym) (root : Ω → Digest)
    (position : Ω → Nat) (accepted : Ω → Prop) (β : Rat) : Prop :=
  μ.prob (fun ω => accepted ω ∧ (Sω ω).commit (reference ω) = root ω ∧
    ¬ SpanAt (reference ω) (position ω) (pattern ω)) ≤ β
```

On a bad accepted run, compare the verified length with `reference.length`; if unequal emit those two length openings, otherwise find a mismatching pattern symbol and emit its accepted opening and the honest opening from `reference`. That is an explicit position-or-length reduction. A full-word `KnowledgeSound` certificate needs a separate whole-word extractor or origin certificate; it cannot be inferred from partial Merkle paths. This is a capability distinction, not a reason to discard the inexpensive authenticated-substring receipt. Hiding the untouched content additionally requires an actual hiding/ZK scheme; salts of inadequate entropy do not provide it by terminology.

## 10. Content-bound DFA (CS18, CF06)

[READ] Actual `Dfa.Statement` is at `Dregg2/Crypto/Dfa.lean:169–177`, the kernel at 183–195 and theorem at 200–205. The theorem is conditional on `K.extractable`, then composes extraction with structural DFA soundness. `trace` is a `List (Step State Sym)`; its word is `trace.map Step.sym` (`Step` fields at 48–54), **not** a `trace.word` field. The original `DfaAccepts` requires a nonempty run (`:70–74`).

[READ] P6 adds `c` to the statement and writes a deterministic accepted-proof theorem but leaves `K` and `...` unspecified. Merely extending the statement does not change the old kernel's `verify` type or its extraction relation. And a computationally sound verifier with nonzero ε does not satisfy unconditional acceptance ⇒ truth.

The repaired content relation is:

```lean
-- acceptTrace is the real DfaAccepts predicate and traceWord := List.map Step.sym.
def BoundDfaRelation (traceWord : Trace → List Sym)
    (acceptTrace : Trace → Prop) (emptyAccept : Prop)
    (c : Digest) (w : List Sym) : Prop :=
  S.commit w = c ∧
    ((w = [] ∧ emptyAccept) ∨ ∃ t, acceptTrace t ∧ traceWord t = w)
```

[DERIVED] The new verifier's public inputs must bind `c`, the automaton identity, encoding and length; its satisfying trace must enforce content hashing and exactly the same symbol sequence used in the DFA transition checks. A per-trace theorem then transports circuit satisfaction to `BoundDfaRelation`, and a **probabilistic extraction theorem for that new circuit** supplies `KnowledgeSound ... BoundDfaRelation ... ε_DFA`. If empty inputs are intentionally unsupported, replace the empty branch by an explicit nonempty domain restriction and do not advertise arbitrary regex-language completeness.

The proof target is Lean syntax under that complete interface:

```lean
theorem dfa_bound_sound
    (hExtract : KnowledgeSound G stmt proof log verify SatisfyingBoundTrace extractTrace ε)
    (hSem : ∀ ω s t, SatisfyingBoundTrace ω s t →
      BoundDfaRelation (Sω ω) traceWord (acceptTrace s) (emptyAccept s)
        s.content (traceWord t)) :
    KnowledgeSound G stmt proof log verify BoundDfaClaim
      (fun log => traceWord (extractTrace log)) ε
```

Here `BoundDfaClaim` is exactly the relation on `s.content` shown, not another free property. This is a theorem *schema*; it is not asserted compiled against the current Dregg2 API. `StatementSchemas` checks the relation itself. An honest one-state zero-symbol automaton with a nonempty `[0]` run inhabits the old and repaired relation at `commit [0]`; a statement with `commit [1]` admits the old splice but not the repaired relation when commitment is identity. CF06 should exhibit this **specific** kernel instance. For ε>0, refusal is a bound over the bad acceptance event, not a pointwise consequence.

## 11. All-lane denotation and the right regression (CS19, CF09)

[READ] `AttestedAutomatonWeld8.lean:16–21` says `MapOp.holdsAt` and `rowAt` read lane zero only. Its actual `weld_completion_lanes_free` (`:758–768`) universally allows arbitrary completion assignments with the same scalar-root calculation. `root8_binds_automaton_or_collides` is at `:238` and is already a theorem over eight-lane tree roots. Correcting the opening denotation is a sound target; routing is a separate deployment obligation (`:39–48`).

[DERIVED] The exact target checks every lane of the root **recomputed from the supplied authenticated opening**:

```lean
def AllLaneOpening (holds : Input → Trace → Prop)
    (root : Input → Fin 8 → F) (recomputed : Trace → Fin 8 → F) : Prop :=
  ∀ s t, holds s t → ∀ lane, root s lane = recomputed t lane

def TamperedLaneRefused (holds : Input → Trace → Prop)
    (root : Input → Fin 8 → F) (recomputed : Trace → Fin 8 → F) : Prop :=
  AllLaneOpening holds root recomputed →
    ∀ s t, (∃ lane, root s lane ≠ recomputed t lane) → ¬ holds s t
```

The original all-completions-free universal theorem should cease to hold for the repaired relation. Its prose gloss “two different lane vectors cannot satisfy the descriptor” is too strong: different genuine commitments with corresponding genuine openings must remain accepted. Even a fixed opened value can have different valid roots if unqueried siblings change. Fix the path/leaf/index/opening computation in the tampering regression; then change a public root lane without changing that computation. Also supply an accepted honest instance so always-refuse does not pass. `distinct_honest_roots_allowed` is the minimal model separating legitimate root diversity from free completion lanes.

## 12. Falsifier statements, all nine (CF01–CF09)

[DERIVED] Original target and repaired test coincide for CF01–CF06 after the scope clarifications above. The concrete forms below show the statements; their matching proved model lemmas are in `CertificateAudit.lean` unless marked a target.

```lean
-- CF01: the proposal permits a zero bound alongside a certain explicit break.
theorem unbacked_advantage :
  zeroClaim.bindAdv 0 = 0 ∧ zeroClaim.verifyOpen () 0 false () = true ∧
    zeroClaim.verifyOpen () 0 true () = true ∧ false ≠ true

-- CF02: same six-symbol word and pattern, changed public position.
theorem position_matters :
  At [0,1,2,3,4,5] 2 [2,3] ∧ ¬ At [0,1,2,3,4,5] 1 [2,3]

-- CF03: one verified position does not cover the omitted second position.
theorem omitted_index :
  ([0,1] : List Nat)[0]? = some 0 ∧ ¬ At [0,1] 0 [0,2]

-- CF04: explicit instance of P4's existential falsifier.
theorem complement_not_absence :
  ([0,1,0] : List Nat) ≠ [1] ∧ At [0,1,0] 1 [1]

-- CF05: two individually true root-bound predicates cannot be conjoined.
theorem two_true_legs_false_join :
  prefixScheme.commit [] = () ∧ prefixScheme.commit [()] = () ∧
  ([] : List Unit).length = 0 ∧ ([()] : List Unit).length = 1 ∧
  ¬ ∃ w : List Unit, w.length = 0 ∧ w.length = 1

-- CF06: implementation target, with one explicit alphabet/kernel and identity root.
def SpliceSeparation (oldAccept : Bool) (newRelation : Prop) : Prop :=
  oldAccept = true ∧ ¬ newRelation
```

For CF06 the argument values must be the actual disclosed zero-only automaton, `[0]` proof and target `[1]`; unconstrained booleans/propositions are only the type of the target, not a completed falsifier.

For the three tests requiring repair/qualification (CF07 is underspecified; CF08–CF09 have overstrong prose formulations):

```lean
-- CF07 original vague “a collision refutes soundness” needs this quantified test.
def CorpusFalsifier (Pr : (Ω → Prop) → Rat) (accepted Good : Ω → Prop)
    (claimedError : Rat) : Prop :=
  claimedError < Pr (fun ω => accepted ω ∧ ¬ Good ω)

-- CF08 original (false when a proof leg errs even without a collision):
def OriginalAlienWordRefusal : Prop :=
  ∀ ω, AcceptedFalseWeld ω → BindS ω ∨ BindT ω
-- Repaired: all actual failure events, as in §7.
def AlienWordFailureCovered : Prop :=
  ∀ ω, AcceptedFalseWeld ω →
    BadInference ω ∨ BadBridgeProof ω ∨ BadPropertyProof ω ∨ BindS ω ∨ BindT ω

-- CF09 original overstrong gloss, banning even two honest roots:
def OriginalNoDifferentRoots (holds : Input → Trace → Prop)
    (root : Input → Fin 8 → F) : Prop :=
  ∀ s t s' t', holds s t → holds s' t' → root s = root s'
-- Repaired: TamperedLaneRefused in §11, with fixed opening computation,
-- plus ∃ s t, holds s t to rule out an always-refuse repair.
```

[OPEN] Production obligations are now explicit: a keyed/ROM computational-binding instance, joint extraction resource/coupling proofs, length-aware tier-one verification, actual bound-DFA circuit and extractor, full-lane opening/routing transport, and a FlashProve relation adapter. The audited conditional algebra should be proved and used while these remain named obligations; none should be silently represented as `bindAdv := tinyNumber`.
