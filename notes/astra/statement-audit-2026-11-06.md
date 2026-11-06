# Statement audit — 2026-11-06

[READ] This is the integrated audit of the proposed contracts in CERTIFICATES.md, DARK-LEARNING-PROGRAM.md, GOVERNANCE-CLAIM-LATTICE.md and SILICON-TO-SEMANTICS-ALIGNMENT-2026-11-05.md. The domain sections pin the source revisions and line locations, expand the statements in Lean 4 syntax, identify witnesses and falsifiers, and supply a replacement for every defective row. Earlier withdrawn sketches are not counted again as new defects. Follow-on commits are audited separately in watch-log.md.

[INFERRED] **109 distinct statement obligations: 21 definite defects or stale false headlines, 26 qualification/interface obligations, 1 realization gap, and 61 fine conditional targets.** A missing implementation is not by itself a false theorem. A true conditional theorem is not evidence that its deployment assumptions hold. Counts are per inventory row, not per missing premise or repeated appearance.

| Domain | Obligations | Defects with proposed repairs | Qualification/interface | Realization gap | Fine conditional |
|---|---:|---:|---:|---:|---:|---:|
| Certificates | 28 | 7 | 6 | 0 | 15 |
| Dark learning | 37 | 9 | 9 | 1 | 18 |
| Governance and silicon | 44 | 5 | 11 | 0 | 28 |
| **Total** | **109** | **21** | **26** | **1** | **61** |

[INFERRED] The highest-impact repairs are: a resource-bounded binding game instead of an unexplained error field; whole-object extraction and length binding before certificate conjunction; conditional-history versus global binding accounting for displacement; an admission/rejection-aware decryption privacy game; a leakage-based claim for instance encodings instead of a prohibition on physical computation; semantic receipt interpretation; and failure-event-aware evidence deduplication. The fine statements retain their meaningful assumptions rather than being weakened to tautologies.

[EXECUTED] Counterexamples and small semantic lemmas were checked in the domain evidence files. Certificate statement schemas also elaborate as definitions. The proposed application signatures in this report are explicitly schemas: abstract game, device and compiler interfaces remain to be implemented. They are not silently postulated as axioms and are not represented as completed proofs.

[EXECUTED] The additive [displacement-bound.patch](displacement-bound.patch) contains a proved finite-horizon 2B/q theorem with a nonzero witness and an envelope-removal falsifier. Its exact current-source-fragment Lean 4.35 check, patch applicability and import-boundary check passed. Full-module integration is still open because local cached Selvage modules use Lean 4.30 while the project pin and Mathlib cache use 4.35. The separate Task 3 [binding-term.patch](binding-term.patch) supplies computational composition and global/conditional audit adapters; its scope and checks are recorded in [binding-term-design.md](binding-term-design.md).

[READ] Reproducible evidence: [certificates/validation.json](certificates/validation.json), [certificates/CertificateAudit.lean](certificates/CertificateAudit.lean), [certificates/StatementSchemas.lean](certificates/StatementSchemas.lean), [dark-learning/check_displacement_adapter.py](dark-learning/check_displacement_adapter.py), and [governance/GovernanceAudit.lean](governance/GovernanceAudit.lean). Domain reports below are included in full so the complete inventory and replacements are reviewable in this requested output file.

## Astra certificate statement audit — 2026-11-06 task

[READ] Corpus: `docs/CERTIFICATES.md` at zkml-research `439da79ca95432ee5f428bb6b77c6d3b8347453d`, the complete `notes/selvage-foundations-critique-2026-11-05.md` and `notes/proof-system-codex-synthesis.md`, and the specific Lean sources listed below. The label is the requested task date; this run began on 2026-11-05 America/Los_Angeles. Companion source snapshots: minidregg `c4ecabe0fad1c8b9eb32a6b3cc2340f689078f55`, breadstuffs `22fad151e9f118e3aa001a823e075918ffa139e8`. No companion-tree files were modified.

[DERIVED] **28 distinct obligations audited: 7 definite contract/prose defects, 6 interface or scope qualifications, and 15 fine statements/tests.** Thirteen obligations receive repairs or explicit qualifications; this is not a claim of thirteen false Lean theorems. These are 19 structures, relations, laws and implementation statements, plus the nine proposed falsifiers. Aliases are deduplicated: P1 is the structure, P2 the three named relations, P3=L6, P4=L3, P5=L1, P7=L2 plus its digest-width implementation requirement, P8=L4. Each falsifier is separately identified because it is a distinct proposed assertion; the count does not count the same law twice. Syntax-only normalizations do not count as semantic defects.

[EXECUTED] `certificates/CertificateAudit.lean` contains **15 proved model facts**, with `#guard_msgs`-pinned axiom reports, no `sorry`, `axiom`, or `native_decide`. `certificates/StatementSchemas.lean` contains checked definitions of the repaired statement targets as `Prop` values. **Typechecking a `Prop` definition is not proving that proposition.** Both compile with installed Lean 4.35.0 and core `Lean`, without a Lake build or dependency download. Exact commands, exit statuses and output are in `certificates/validation.json`, `lean-check.log`, and `schema-check.log`. Disk availability was 133 GiB before compilation, above the clarified 30 GiB threshold.

### Inventory and verdicts

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

### 1. Computational binding is a contract, not a number (CS01)

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

### 2. The eight content relations (CS02–CS09)

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

### 3. Knowledge soundness and L0 (CS10–CS11)

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

### 4. Conjunction (CS12 and CF05)

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

### 5. Aggregation, recursion and digest width (CS13 and CF07)

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

### 6. Padded complement and its falsifier (CS14, CF04)

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

### 7. Cross-scheme bridge (CS15, CF08)

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

### 8. Scheme transport (CS16)

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

### 9. Tier one, vacuity and phantom roots (CS17)

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

### 10. Content-bound DFA (CS18, CF06)

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

### 11. All-lane denotation and the right regression (CS19, CF09)

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

### 12. Falsifier statements, all nine (CF01–CF09)

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

## Dark-learning statement audit — 2026-11-06 task

[READ] Scope: every theorem-shaped construction C1–C23 (including subcases), every distinct §5 target, and F12's envelope premise in `docs/DARK-LEARNING-PROGRAM.md` (DP below), `notes/dark-learning-foundations-critique.md` (F below), and `notes/dark-learning-codex-synthesis.md`, read in full. Duplicate appearances are cross-references, not extra audited statements. The five top-level properties P1–P5 map to DL10/DL35, DL01/DL02, DL27, DL18, and DL14. Numerical cost estimates, literature novelty and performance comparisons are outside this statement inventory.

[READ] Source snapshot: zkml-research `439da79ca95432ee5f428bb6b77c6d3b8347453d`; minidregg `c4ecabe0fad1c8b9eb32a6b3cc2340f689078f55`; breadstuffs `22fad151e9f118e3aa001a823e075918ffa139e8`. All companion trees were read-only. Paths below are relative to their named repository. No search queries or PDF downloads were used.

[INFERRED] **37 distinct statement obligations audited: 9 concrete defects or stale contradictory headlines, 9 underspecified targets needing explicit contracts, 1 deployment-realization gap, and 18 fine conditional targets.** Only the first category is counted as defects. “Fine” is neither a completed proof nor a deployed cryptographic instantiation. A defect is counted once per inventory row, even if several premises are missing. Material defects or scope gaps surviving yesterday's corrections include: step-proof bisection; public-coefficient expiry; sampled “exact” unlearning; zero-error proof gates; rejection-channel privacy; the gap from encoding simulation to physical execution prohibition; epoch-key security versus semantic historical-state secrecy; and the signed-decoder mismatch despite an already existing unsigned no-wrap theorem. Later-state leakage under C22 is a scope boundary, not a counterexample to cryptographic retirement. Missing formal signatures alone are not counted as defects.

### Inventory and verdicts

[INFERRED] Table verdicts refer to the current revised prose, not the withdrawn first drafts. Every defective row has its replacement below.

| ID | source / target | verdict | deciding reason |
|---|---|---|---|
| DL01 | DP:127–151 C1 encrypted step | fine conditional target | The prose already requires factors produced by forward/backward; preserve that clause and per-step no-wrap invariants. |
| DL02 | DP:155–187 C2 `displacement_bound`; §5 duplicate | underspecified target | Fill positive q, stopping convention and conditional-vs-global computational failure accounting; core 2B/q claim is sound. |
| DL03 | DP:166–168; F7:213–215 `bisect_localizes` | defect: false | Local validity is not monotone; cancelling bad steps can restore an honest endpoint. |
| DL04 | DP:191–212 C3 / F9 merge decider | underspecified target | Make merge arithmetic, complete state, all carried witnesses and fresh restart explicit. |
| DL05 | DP:217–240 C4 / F4 append-only noise | defect: too strong F4 formula | Missing base term, two-product composition, message magnitudes and relin noise. |
| DL06 | DP:244–258 C5 expert minimum | underspecified target | Minimum is over a nonempty exhaustive corruption cover and actual conditional probabilities. |
| DL07 | DP:262–274 C6 all-reduce | fine for field/ciphertext arithmetic | No range check is needed for modular addition; an integer-decryption claim would need a separate no-wrap bridge. |
| DL08 | DP:278–309 C7 conversion / segment sampling | fine conditional target | Revised text includes conversion semantics, all state, coverage and independence qualification. |
| DL09 | DP:313–316 C8 zero decryption failure | defect: stale zero-error headline | The first C8 target says probability 0; the later corrected target rightly includes proof/binding errors. |
| DL10 | DP:336–357 C8 restricted IND-CPA-D | underspecified target | Equal outputs alone do not specify admission/rejection and partial-share leakage; define the game. |
| DL11 | DP:363–384 C9 single-prime target | fine narrowed target | Removing limb indexing removes that quantifier swap, not content binding or rounding. |
| DL12 | DP:397–403 C10a exact unlearning | defect: sampled exactness | C2 as the allowed retraining certificate permits a wrong transition with positive probability. |
| DL13 | DP:404–410 C10b generic exact expiry | defect: false | Public coefficients permit propagation of old state; simple subtraction need not equal retraining. |
| DL14 | DP:417–430 C11 welded absence | realization gap; target fine | Proposed content-bound absence is valid; existing word-free DFA/lane-0 weld does not instantiate it. |
| DL15 | DP:434–441 C12a RL provenance | fine conditional target | Source pins sampler/reward dependencies; retain the full prescribed update and distinguish C2 receipts. |
| DL16 | DP:442–446 C12b eval DAG | underspecified target | Specify complete covered ancestry versus a checkpoint-relative path, and receipt type on edges. |
| DL17 | DP:459–462 C13 no unauthorized service | fine conditional security target | Revised scope excludes local FHE evaluation; formal game must charge cryptographic errors. |
| DL18 | DP:463–466 C13 single accepted timeline | fine conditional safety target | Honest intersection plus durable anti-equivocation proves compatible accepted prefixes, not liveness. |
| DL19 | DP:478–499 C14 seeded ZO | underspecified target | Make finite-difference denominator, integer rounding and two randomness stages explicit. |
| DL20 | DP:504–515 C15 MPC custody | defect: structural P3 overclaim | MPC privacy alone does not forbid computation deducible from authorized outputs. |
| DL21 | DP:519–539 C16 folding | underspecified target | Digit opening, ciphertext reconstruction, accumulation validity and model semantics need a common relation. |
| DL22 | DP:543–545 C17a TEE leg | fine conditional conjunction | Adding an attestation leg does not improve epsilon without a joint failure model. |
| DL23 | DP:546–550 C17b DP step | underspecified target | Define actual rounded noise distribution, release view, adjacency and adaptive composition budget. |
| DL24 | DP:556–568 C18 statistics deletion | fine conditional target | Active multiset and deterministic solver/invertibility are explicitly named. |
| DL25 | DP:572–581 C19 projected gradient | fine conditional target | Fixed U,V plus prescribed rounding defines a reduced learner; utility is separate. |
| DL26 | DP:585–595 C20 activation | fine as proof-object gate safety | No activation without a verified proof object can be exact; no false active model is a different probabilistic theorem. |
| DL27 | DP:599–608 C21 instance-bound encoding | defect: P3 scope overclaim | Simulation supports authorized-output leakage; it does not establish the advertised physical execution prohibition. |
| DL28 | DP:612–621 C22 epoch custody | fine conditional epoch-key target | Later-state leakage limits semantic historical secrecy but does not refute retired-key security. |
| DL29 | DP:625–635 C23 one-step contraction | fine conditional target | Use the same prescribed map, full state, and explicit nonnegative contraction constant. |
| DL30 | DP:625–635 C23 horizon-independent consequence | defect: unqualified horizon bound | Continuing rounding needs a uniform ceiling and C2 only bounds stopped/pre-alarm injection. |
| DL31 | DP:641 / F1:49–57 no-wrap iteration | defect: decoder mismatch / stale omission claim | Noise.lean:490 already has mi<t; symmetric range does not make unsigned decode return negatives. |
| DL32 | DP:643 / F4:141–150 `stepRR_noise_le` | fine open target | Ring multiplication bound includes N, scales, rounding and relin; implementation refinement remains open. |
| DL33 | DP:651 `BFVScaleLiftRefinement` | fine integer target | Quotient/remainder is over integers with exact lifted convolution, not mod Q. |
| DL34 | DP:652 / F2:89–95 paired derivative lookup | fine target | Address is the same input with fixed derivative and exceptional-input convention. |
| DL35 | DP:653 / F14:298–311 `F_dark` simulation | underspecified target | Define leakage, corruption, abort, erasure and public outputs before proving simulation. |
| DL36 | DP:654 / F15:313–325 reference learner refinement | fine target | Full-state simulation with trace/randomness alignment is the right theorem. |
| DL37 | F12:270–279 product-norm envelope | fine conservative target | Cap actual product/update, not a factor or lower spectral estimate. |

### Syntax and quantification convention

[INFERRED] Code blocks are **Lean 4 theorem signatures**, with proof bodies intentionally omitted: they are statements to implement, not `axiom` declarations, compiled proofs, or placeholder `sorry`s. Schematic abstract types/relations are explicit parameters or named interface obligations described beside the signature; they must be given executable definitions before an implementation claim. `Pr` always means probability in the named, fixed finite game (never an arbitrary unconstrained real-valued function); `adv` is its distinguishability advantage with a fixed normalization. Error terms bound the whole named experiment unless explicitly marked conditional. No existential “some epsilon” may replace the stated budget. A theorem receiving its whole conclusion as a premise would be tautological; the lower-level obligations below instead name arithmetic identities, transition rules, extraction/refinement or simulator interfaces whose realization is separately open.

#### DL01 — complete encrypted transition

[READ] Current prose correctly includes “factors the step's forward/backward produced”. This is a fine conditional specification, not a source defect. Omitting that clause during formalization would recreate the error already exposed by minidregg `Selvage/Rank1GradientCheck.lean:368` (`rank1_blind_to_the_error`).

```lean
-- Faithful expansion: IntLearner and Witness hold ALL optimizer/scale/coin state.
theorem encrypted_step_refines (L : IntLearner) (s : PublicStep) (w : StepWitness)
    (henc : CiphertextTraceValid s w) (hlift : ExactIntegerLifts s w)
    (hnoise : AllDecryptMargins s w) (hforward : ForwardBackward L s w)
    (hupdate : IntegerUpdate L s w) (hbind : OpensAllNamedBoundaries s w) :
    DecodedTransition s w = L.step (DecodedPrestate s w) (DecodedBatch s w)
      (StepCoins s w)
```

[INFERRED] Witness: one-dimensional integer learner with identity activation, fixed batch, zero bounded noise and correctly committed trace. Falsifier: retain valid outer-product factors but choose δ unrelated to the declared loss. `rankK_sound` only rejects a wrong product of the supplied factors. A cryptographic acceptance theorem additionally bounds the chance that extraction of such `w` fails; it cannot simply conclude this equality from a Boolean verifier. The range invariant must be re-established for every evolving state, not inherited forever from the initial weight width: see the independent counts-audit lane's valid 4-bit-factor update that increases a weight beyond its originally priced 4-bit bound. Per-step `ExactIntegerLifts` and `AllDecryptMargins` must use the actual updated operand ranges; fresh encryption resets noise, not plaintext magnitude.

#### DL02 — displacement, conditional detection, and the bad world

[READ] `Selvage/AuditSampling.lean:196–265` places corruption before the current coin; `:585–619` requires `0<q`; `:495–505` counts the corrupt step that **raises** the alarm. `:1036–1041` explicitly leaves semantic-corruption to δ-farness transport open. The repaired target below measures *injected* displacement up to and including that step, at each finite horizon.

```lean
noncomputable def injected (R : Round Ω) (delta honest : List Ω → V) : List Ω → ℝ
  | [] => 0
  | _ :: h => if R.stopped h then injected R delta honest h
    else injected R delta honest h + ‖delta h - honest h‖

theorem displacement_bound [Fintype Ω] [Nonempty Ω] [NormedAddCommGroup V]
    (R : Round Ω) (delta honest : List Ω → V) (B q : ℝ)
    (hactual : ∀ h, ‖delta h‖ ≤ B) (hhonest : ∀ h, ‖honest h‖ ≤ B)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest h)
    (hq : 0 < q)
    (hdetect : ∀ h, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun w => R.alarms h w)) (n : ℕ) :
    expOver Ω n (injected R delta honest) [] ≤ 2 * B / q
```

[INFERRED] The exact `hdetect` is implied by DetectionLegs with **per-history** `BindLeg`, not by ordinary global computational binding. If a hidden setup bit selects an insecure commitment with probability ε, observing that setup can leave a reachable history with binding failure probability 1. An unconditional bound ε says nothing like `∀h, Pr[bad|h]≤ε`.

[INFERRED] Use either a resource-bounded continuation binding assumption strong enough for every relevant history, or a whole-game coupling to an ideal bounded process. For the latter a finite horizon and an unconditional damage ceiling are necessary:

```lean
theorem displacement_bad_world (realLoss idealLoss : Ω → ℝ)
    (bad : Ω → Prop) (M eps B q : ℝ)
    (hM : 0 ≤ M) (hq : 0 < q)
    (hgap : ∀ w, realLoss w ≤ idealLoss w + if bad w then M else 0)
    (hbad : Pr bad ≤ eps) (hideal : E idealLoss ≤ 2 * B / q) :
    E realLoss ≤ 2 * B / q + M * eps
```

[INFERRED] Here `E` and `Pr` are expectation/probability under the **same explicit coupling**. `eps` may include the full-run envelope and binding reduction failures; it is not inserted back into a conditional q. Do not condition on the future “no proof ever fails” event and reuse unchanged beacon probabilities. If only a per-step damage ceiling D is universal, take M=nD. Without a ceiling, loss `M/ε` on a rare bad event defeats any fixed additive error bound.

[INFERRED] Nonvacuity: `AuditWitness.round` has q=1/2; use δ=1, honest=−1, B=1, producing the bound 4. Honest update is from the actual pre-state. Small semantic deviations require `hcoverage` to be false only where the checker detects them, or an extra bounded residual per step; δ-far soundness alone does not do this.

#### DL03 — bisection needs prefix validity, not isolated steps

```lean
-- Old claim shape: false without a monotone dispute predicate.
theorem bisect_localizes_old (T : ℕ) (committed : ∀ t ≤ T, HasBoundary t)
    (alarm : ∃ t < T, ¬ StepValid t) :
    FindsFirstBadWithStepQueries (Nat.clog 2 T)
-- Repair target:
theorem bisect_localizes (T : ℕ) (hT : 0 < T)
    (prefix : ℕ → Bool)
    (hspec : ∀ k ≤ T, prefix k = true ↔ ∀ i < k, StepValid i)
    (hbad : prefix T = false) (hanswers : AuthenticatedPrefixAnswers prefix) :
    ∃ i < T, (∀ j < i, StepValid j) ∧ ¬ StepValid i ∧
      PrefixQueryCost i ≤ Nat.clog 2 T
```

[INFERRED] Each queried prefix requires a proof/check of **all transitions** in that prefix, including fixed initial state; a bare endpoint equality is insufficient. Those are not `⌈log₂T⌉` local step proofs. Falsifier: honest identity map, committed states `0,1,0`; both updates are corrupt, final state is honest. More generally a local validity bit vector can contain a unique bad bit at any position, so worst-case first-bad search with local queries needs linear queries. Witness: prefix true through k and false afterward, authenticated prefix proofs. Charge prefix-proof generation separately.

#### DL04 — merge and restart semantics

```lean
theorem merge_discharges_carried_witness (epoch : Epoch) (a : Accumulator)
    (ws : CarriedWitnesses epoch) (m : MergeStatement)
    (hdec : DeciderAccepts a ws) (hchain : CarriesExactEpoch a epoch ws)
    (hmerge : MergeRelation epoch ws m)
    (hroot : FreshCommitOpens m.newRoot m.mergedState)
    (hrestart : RestartUses m.newRoot m.nextAccumulator) :
    EpochValid epoch ∧ ModelAt m.newRoot = EndModel epoch ∧
      InitialState m.nextAccumulator = EndModel epoch
```

[INFERRED] `MergeRelation` must tie the full optimizer state, base, factors and exact integer rounding; a decider for opening claims alone cannot discharge training validity. Witness: empty factor epoch followed by identity merge and correctly restarted accumulator. Falsifier: valid openings plus replacement of the recommitted model by zero. Computational roots add extraction/binding errors over *all* merges; a merge does not reset accumulated failure probability.

#### DL05 — append-only noise is a sum of complete term bounds

```lean
-- F4's old numeric shortcut (not justified for the described depth-two pass):
theorem append_noise_old : OutputNoise ≤ T * N * (2 * Bfresh * t)
-- Repair target; termBound includes both products, input message magnitudes,
-- both rounding operations, key-switch noise, and ring expansion at each product.
theorem appendOnly_noise_history_free
    (hdecomp : outputError = baseError + ∑ s : Fin T, termError s)
    (hbase : ‖baseError‖ ≤ Ebase)
    (hterm : ∀ s, ‖termError s‖ ≤ termBound s) :
    ‖outputError‖ ≤ Ebase + ∑ s : Fin T, termBound s
```

[READ] `Bfv/Mul.lean:165–190` contains `M₁B₂+M₂B₁`, a quadratic/residue term, rounding `+1`, and `Bks`; freshness alone fixes none of the message magnitudes. `Bfv/Ring.lean:269–326` establishes expansion N and its tightness. [INFERRED] Witness: zero errors and zero noise, any finite history. Falsifier to old numeric form: T=0 with nonzero base noise; even for T>0, unconstrained relin noise is unbounded. Per-term bounds may be uniform, yielding `Ebase+T·Eterm`, but Eterm must be derived for the **two-product** evaluation schedule. No cryptographic crossing-reset theorem is supplied by this triangle inequality.

#### DL06 — expert sampling

```lean
theorem stratified_detection [Nonempty Expert]
    (covers : History → Expert → Prop) (qE : Expert → ℝ)
    (hcover : ∀ h, Corrupt h → ∃ e, covers h e)
    (hlocal : ∀ h e, covers h e → qE e ≤ PrAlarm h)
    (hq : ∀ e, qmin ≤ qE e) :
    ∀ h, Corrupt h → qmin ≤ PrAlarm h
```

[INFERRED] Witness: one expert, all corrupt actions covered, honest random sampler. Falsifier: an unmodeled router/optimizer mutation is corrupt but in no expert stratum. `p_e` must be the actual probability of auditing the implicated object conditional on its corruption, not its nominal frequency among all expert draws. Stratification is sufficient, not logically necessary; auditing every expert in a selected step also has the advertised floor.

#### DL07 — valid modular collective; separate integer lift

```lean
theorem allReduce_field_sound (hfixed : FixedBeforeChallenge shardRoots outputRoot)
    (hsz : CheckPolynomialNonzero inputShards output) :
    Pr (fun r => CommonPointAccepts inputShards output r) ≤ degree / fieldCard

theorem allReduce_integer_exact (xs : Fin nodes → Fin width → ℤ)
    (out : Fin width → ℤ) (p : ℤ) (hp : 0 < p)
    (hmod : ∀ j, out j % p = (∑ i, xs i j) % p)
    (hlift : ∀ j, |out j - ∑ i, xs i j| < p) :
    out = fun j => ∑ i, xs i j
```

[INFERRED] The source modular/ciphertext collective is fine: range checks are not required to prove modular addition. The added integer corollary is a distinct consumer obligation, inhabited by honest summed shards with ordinary range bounds. Falsifier to that stronger claim without a lift: out=sum+p passes every field equality and is a wrong integer. Computational commitment errors and random-evaluation error remain even when no sumcheck rounds are required. Sender/receiver openings must share message IDs and occurrence indices, not only reusable tensor content hashes.

#### DL08 — conversion and coverage (fine after revision)

```lean
theorem conversion_sound (cIn cOut : Ct) (sIn sOut : Shares)
    (h : ProvedConversion cIn sIn sOut cOut transition) :
    Decode cIn = Reconstruct sIn ∧
    Reconstruct sOut = transition (Reconstruct sIn) ∧
    Decode cOut = Reconstruct sOut

theorem covered_segments_detection
    (hcover : ∀ h, Corrupt h → ∃ j, BadSegment h j)
    (hlocal : ∀ h j, BadSegment h j → qj j ≤ PrAlarm h)
    (hfloor : ∀ j, qmin ≤ qj j) :
    ∀ h, Corrupt h → qmin ≤ PrAlarm h
```

[INFERRED] `ProvedConversion` denotes arithmetic validity, not Boolean acceptance. Wire decoding, signed representations, key epochs and state metadata are part of the fixed conversion definition. Witness: plaintext identity conversion with correct fresh encryption. An actual proof-system acceptance theorem pays its errors. The independent product-of-misses bound is available only with the stated conditional independence; the min bound needs none.

#### DL09–DL10 — proof gates and the restricted game

```lean
-- Old target mistakes proof acceptance for truth:
theorem gate_failure_zero_old : Pr (fun w => GateAccepts w ∧ DecFails w) = 0
-- Arithmetic repair, exact within the ideal certified relation:
theorem certified_decrypts (q : Query)
    (hprov : ExactCertifiedEvaluation q) (hnoise : FullNoiseMargin q)
    (hmsg : PrescribedIntegerNoWrap q) :
    CombineAndDecode q = IdealOutput q
-- Computational corollary:
theorem gate_failure_bound
    (hreduction : GateBadToProofOrBindingOrKeygenBad game)
    (hbudgets : GateGameBudgets game epsProof epsBind epsKeygen) :
    Pr (fun w => GateAccepts w ∧ DecFails w) ≤ epsProof + epsBind + epsKeygen
```

[INFERRED] FullNoiseMargin includes *combined* smudging/share coefficients, not only pre-release evaluation noise. Noise witnesses must describe the prescribed plaintext and exact derivation. Witness: honest zero-noise evaluation under a gate checked on every release. Falsifier to zero failure: a soundness-error event in which a forged proof admits an over-margin ciphertext.

```lean
structure PairedQuery where
  left right : IdealQuery
  samePublic : PublicMetadata left = PublicMetadata right
  sameAdmit : Allowed left = Allowed right
  sameRelease : Allowed left = true → IdealOutput left = IdealOutput right
  sameLeakage : IdealLeakage left = IdealLeakage right

theorem restricted_ind_cpa_d
    (hkeys : CPAWithIssuedEvaluationKeys scheme epsCPA)
    (hgate : WholeRunGateSound protocol epsProof epsBind epsKeygen)
    (hmpc : AdaptiveThresholdSimulation protocol ideal epsMPC)
    (hshares : ConditionalTranscriptHybrids protocol ideal epsTranscript)
    (hqueries : AdmissibleStatefulAdversary A PairedQuery)
    (hbudget : RealQueryCount A ≤ K) :
    DistinguishingAdvantage (RestrictedRealGame protocol A)
      (RestrictedIdealGame ideal A) ≤
      epsCPA + epsProof + epsBind + epsKeygen + epsMPC +
        ∑ i : Fin K, epsTranscript i
```

[INFERRED] All releases, rejections, scheduling/timing included in the adversary's modeled view must be covered by `sameLeakage` and the simulator. Novel falsifier: both worlds promise equal released output 0, but policy admits only when a hidden weight bit is 0. Reject/accept distinguishes perfectly while equal-output decryption holds vacuously for the rejected world. Require equal admissibility, or explicitly allow and account for that policy leakage. Proof witnesses must not be used as an unexplained decryption oracle by the CPA reduction; adaptive simulation/extraction is part of `hgate`/`hmpc`, with its actual reduction resources.

[READ] `Bfv/Smudging.lean:442–469` packages real-valued distances and assumed per-step hybrid bounds; no protocol inhabitation follows from `TranscriptHybridLedger.sound`. [INFERRED] A trivial constant-output protocol supplies a nonempty toy premise witness. A useful reactive BFV threshold instance remains [OPEN]. This is a target under a restricted oracle, not unrestricted IND-CPA-D or model secrecy against allowed identity release. Global error terms are aggregated over the whole run; per-query errors must first be summed or reduced.

#### DL11 — single-prime provenance (fine in the narrowed scope)

```lean
theorem singleton_limb_source
    (Rel : Source → Fin 1 → Prop)
    (h : ∀ i : Fin 1, ∃ src, Rel src i) :
    ∃ src, ∀ i : Fin 1, Rel src i
```

[INFERRED] Witness any genuine single source. This only removes the cross-limb quantifier swap. Two different ciphertext handles at the sole limb, incorrect lifted multiplication, wrong public inputs or weak commitment roots remain possible. C9 now explicitly retains Hole B; DL33 is still required.

#### DL12–DL13 — exact deletion

```lean
theorem shard_retraining_exact (D : Dataset) (id : RecordId)
    (hpartition : FixedIndependentShardPartition D)
    (htrain : EveryRetainedShardExactlyTrained D)
    (hretrain : AffectedShardExactlyRetrained (EraseRecordId D id))
    (hshared : InitialAndSharedStateIndependentOf D id)
    (hcompose : FixedAdditiveComposition) :
    ReassembledAfterDeletion D id = ReferenceLearner (EraseRecordId D id)
```

[INFERRED] A C2 receipt alone cannot inhabit `hretrain`; it proves a loss/detection guarantee, not that the retrained model is exactly the reference. Either require a full epoch proof (C20), or replace equality by the correctly stopped expectation bound and residual assumptions. Fix seeds/rounding for equality; randomized retraining instead needs a specified distributional comparator. Deletion is by record ID/multiplicity, not ambiguous value subtraction. Witness: independent deterministic one-record shards. Falsifier: one forged retraining step that escapes sampling.

```lean
-- Old public-coefficient generalization is false:
theorem expiry_old : PublicCoefficientLearner L →
    RemoveOriginalContribution (L.run D) id = L.run (EraseRecordId D id)
-- Useful additive-statistics repair:
theorem statistics_expiry [DecidableEq Record] [AddCommGroup Stat]
    (contrib : Record → Stat) (D : Multiset Record)
    (d : Record) (hd : d ∈ D) :
    (D.map contrib).sum - contrib d = ((D.erase d).map contrib).sum
```

[INFERRED] Falsifier over ℤ, all coefficients public: `s←2s+d`, s₀=0, teachings (1,0). Final state=2; subtract original contribution 1 gives 1; retraining on (0) gives 0. A general linear dynamical learner can remove the **transported** contribution `A_last⋯A_after d`, but that is a different theorem and may require stored transition history. Nonlinear prox/rounding breaks even that simple transport. The core-only witness is kept in `dark-learning/CoreCounterexamples.lean`.

#### DL14 — valid content-bound absence target; realization gap

```lean
theorem batch_policy_valid (stmt : TrainingPolicyStatement) (w : PolicyWitness)
    (hdata : OpensBatch stmt.batchRoot w.batch)
    (hused : StepConsumesExactly stmt.step w.batch)
    (hcorpus : EveryRecordMember stmt.corpusRoot w.batch)
    (hlanguage : DfaRunOnExactBytes stmt.patternSemantics w.batch w.trace)
    (habsence : RejectsContainsPattern w.trace)
    (hencoding : CanonicalTokenizerAndByteEncoding stmt w) :
    ∀ record ∈ w.batch, MemberOfCorpus stmt.corpusRoot record ∧
      ¬ ContainsExcludedPattern stmt.patternSemantics record
```

[INFERRED] The source intends the correct shared-content relation. Its unfilled realization must make substring/whole-word language explicit, cover complete bytes with lengths, and use all digest lanes in the commitment relation. A cryptographic version concludes a bad-accept probability. [READ] Prior critique identifies the cited `AttestedAutomatonWeld8` as lane-0 only and the DFA statement as word-free; claiming its existing theorem fills `hlanguage` or `hused` is invalid. Witness empty exclusion set and an honestly opened finite batch. Falsifier: proof for safe bytes B and training on B′; content hash equality cannot be assumed perfect for a compressing hash. This proves batch-level absence; complete history requires DL16's ancestry coverage.

#### DL15–DL16 — RL and evaluation lineage

```lean
theorem rl_step_refines (spec : RLSpec) (tr : RLTrace)
    (hpin : PinsAllDependencies spec tr)
    (hsampler : SamplerRefinesWithCommittedPolicy spec tr)
    (hrandom : NoSeedSelectionAfterSeeingRollouts spec tr)
    (hreward : RewardExecutionRefines spec tr)
    (hupdate : FullUpdateRelation spec tr) :
    tr.after = spec.step tr.before tr.batch tr.coins

theorem eval_lineage_valid (g : ProvenanceDAG) (r : EvalReceipt)
    (hclosure : CompleteAncestryIncludingInitialization g r.model)
    (hedges : AllEdgesFullyValid g)
    (habsence : AllTrainingInputsExclude g r.evalSet)
    (heval : EvalExecutionRefines r)
    (hidentity : FullInferenceIdentityPinned r) :
    r.result = ReferenceEval r.model r.evalSet r.harness ∧
      NoDeclaredEvalItemInCompleteTrainingLineage g r.model
```

[INFERRED] C12a is fine as the prescribed-step claim: the source already pins sampler and reward dependencies and supplies an unpinned-state falsifier. Its formal expansion includes tokenizer, optimizer, policy version, reward program/state, seed/counter and rounding. For an audit edge, carry its error/loss judgment instead of `AllEdgesFullyValid`. A public checkpoint of unknown ancestry cannot witness `hclosure`; the truthful claim starts at that checkpoint and names the residual. Witness: genesis empty training set, one fully verified update, deterministic reward/eval harness. Falsifier: omit a pretraining checkpoint containing the eval set, or select among many beacon seeds while each chosen rollout is individually reproducible. For finite corpora exact-item absence is not absence of paraphrases or all contamination.

#### DL17–DL18 — service gates and one accepted timeline

```lean
theorem noUnauthorizedService
    (hthreshold : ThresholdSecurity epsThreshold)
    (hgate : EveryServiceEnforcesGate epsProof epsBind)
    (hconsensus : CanonicalAuthorizationLog epsConsensus) :
    Pr (fun w => ∃ e ∈ ServicesObtained w,
      ¬ AuthorizedAtLinearizationPoint (LogOf w) e) ≤
      epsThreshold + epsProof + epsBind + epsConsensus

theorem SingleTimeline (hinit : ValidGenesis)
    (hintersection : HonestQuorumIntersectionAcrossEpochs)
    (hsign : DurableHonestAntiEquivocation)
    (hauth : AuthenticatedCertificates)
    (hparent : CertificatesBindParentAndEpoch) :
    ∀ c1 c2, AcceptedChain c1 → AcceptedChain c2 →
      c1.IsPrefix c2 ∨ c2.IsPrefix c1
```

[INFERRED] These are fine within their stated assumptions. A cryptographic authentication implementation adds its failure probability; deterministic signature truth is the idealized premise. Witness: one honest durable signer, one chain. Falsifier if `hintersection` is removed: disjoint quorums certify children of the same parent. Neither conclusion is liveness, deletion of local copies, absence of withholding, or proof that a local FHE computation did not occur. Gate authorization must be checked at a serializable state transition, not a stale precheck.

#### DL19 — integer seeded ZO

```lean
theorem seeded_zo_step (spec : ZOSpec) (tr : ZOTrace)
    (heps : 0 < spec.epsilonNumerator)
    (hpin : DirectionInputsCommittedBeforeSeed spec tr)
    (hdir : tr.direction = spec.generator tr.directionSeed)
    (hloss : ExactPairedLossEvaluation spec tr)
    (hround : tr.coefficient = spec.roundedDifferenceQuotient tr.lossPlus tr.lossMinus)
    (hupdate : IntegerScaledUpdate spec tr)
    (haudit : CoefficientCommittedBeforeIndependentAudit tr) :
    tr.after = spec.step tr.before tr.batch tr.directionSeed
```

[INFERRED] Witness one-dimensional integer quadratic loss with exact rational denominator and declared rounding. Falsifier: ε=0, or replace division by modular inverse while claiming real finite differences. Random direction does not prevent malicious coefficient selection after seeing it; cap the actual update for DL02. A seed is not a rank factor.

#### DL20–DL23 — MPC, folding, attestation and DP

```lean
theorem mpc_custody_simulation
    (hcorrupt : AllowedAdaptiveCorruptions adversary threshold)
    (hprotocol : MaliciousSecureMPC protocol ideal epsMPC)
    (hstate : AuthorizationAndStateBinding protocol)
    (hpre : SecurePreprocessingWithErasure protocol) :
    ∃ sim, DistinguishingAdvantage (RealView protocol adversary)
      (IdealView ideal sim) ≤ epsMPC
```

[INFERRED] DL20 repairs the claim that no single host “runs anything.” An MPC output may reveal W or sufficient queries to reconstruct it. This theorem allows whatever is computable from ideal outputs; P3 needs DL27's narrower confinement game and cannot prohibit physical replay. Witness: ideal private addition of secret-shared constants with a fixed authorized output; useful deployment remains conditional on malicious security and preprocessing.

```lean
theorem folded_ciphertext_epoch_sound
    (hshort : BoundedDigits digits) (hreconstruct : ReconstructDigits digits = ciphertexts)
    (hfold : CarriedFoldRelation accumulator digits)
    (hdecider : DeciderRelation accumulator digits)
    (hsteps : CiphertextTransitionRelation ciphertexts)
    (hsemantic : CiphertextTransitionsRefineLearner ciphertexts) :
    DecodedFinalState ciphertexts = ReferenceEpoch InitialState Batches Coins
```

[INFERRED] DL21: witness honest finite digit decomposition and identity epoch; zero-absorb or unrelated accumulator/model pair falsifies the old “accumulator IS model” shortcut. Ring shortness and extraction are real obligations; ciphertext coefficients cannot be assumed short, and finite field Schwartz–Zippel cannot be transplanted to a split ring.

```lean
theorem tee_proof_join
    (hshared : BothEvidenceLegsBindSameTypedStatement)
    (hproof : ProofBadEventBound epsProof)
    (hquote : AttestationBadEventBound epsQuote)
    (hbind : JointBindingBadEventBound epsBind) :
    Pr JointFalseAcceptance ≤ epsProof + epsQuote + epsBind
```

[INFERRED] DL22 is fine as a union-bound conjunction with explicit occurrence/validity claims and assumptions. Multiplying errors or claiming improved ε requires a joint attack/independence model not supplied by a TEE. Witness ideal attester reporting an honest fixed execution; residual vendor trust remains.

```lean
theorem dark_step_dp
    (hclip : ExactPerExampleClipping spec)
    (hnoise : NoiseSamplerDistributionRefines spec)
    (hprivacy : ReferenceMechanismDP spec eps delta)
    (hrefine : ReleasedViewRefinesReferenceWithFailure epsRefine)
    (hpolicy : AdaptiveReleaseAccountant budget) :
    DifferentiallyPrivate ReleasedView eps (delta + epsRefine)
```

[INFERRED] DL23: `(eps,delta)` must be instantiated for the actual rounded finite sampler and adjacency relation; a secret seed is neither sufficient nor necessary for distributional DP. Host-observed randomness belongs in ReleasedView. Noise-source rejection/selective abort and extra outputs/partial decryptions can defeat the target. Witness a constant-output mechanism (ε=δ=0), or an actually proved discrete-noise mechanism; naming Box–Muller alone is not a proof.

#### DL24–DL26 — statistics, subspace and epoch activation

```lean
theorem statistics_erase [DecidableEq Record] [AddCommGroup Stat]
    (phi : Record → Stat) (D : Multiset Record) (d : Record) (hd : d ∈ D) :
    (D.erase d |>.map phi).sum = (D.map phi).sum - phi d

theorem projected_core_transition (spec : CoreSpec) (tr : CoreTrace)
    (hfixed : tr.U = spec.U ∧ tr.V = spec.V)
    (hgrad : tr.coreGradient = spec.projectedGradient tr.before tr.batch)
    (hround : tr.after = spec.roundedUpdate tr.before tr.coreGradient) :
    tr.after = spec.step tr.before tr.batch
```

[INFERRED] DL24 and DL25 are fine conditional algebra. DL24's released model additionally uses the same deterministic solver; exact field solve needs invertibility as the source already says. Witness nonempty multiset with duplicate records, deleting one occurrence; for DL25 use U=V=[1]. Counterexamples to removed premises: deleting two duplicate occurrences, changing φ, changing U/V, singular system claimed uniquely solved. In a field, formulas prove field results until integer-lift/no-wrap obligations connect them to an integer learner.

```lean
-- Exact gate invariant, matching the source's "no unproved model active":
theorem activation_requires_verified_proof (htransition : ImplementsActivationGate system) :
    ∀ event ∈ system.events, Activates event →
      ∃ proof, VerifyEpoch event.statement proof = true

-- Different semantic-security consumer theorem:
theorem epoch_activation_sound
    (hgate : EveryObservableServiceRequiresActiveRoot)
    (hparent : ActivationBindsCertifiedCurrentParent)
    (hcheck : WholeEpochVerifierSound epsEpoch)
    (hbind : EpochAndServiceBinding epsBind)
    (hconsensus : AtomicActivationConsensus epsConsensus) :
    Pr (fun w => ∃ e ∈ ObservableServices w,
      ¬ CertifiedReferenceDescendant (ServedModel e)) ≤
      epsEpoch + epsBind + epsConsensus
```

[INFERRED] DL26 is fine as the exact gate invariant. It is not refuted by probabilistic proof soundness: “proof supplied and verified” is a syntactic property. The additional semantic conclusion that the activated model is actually valid is probabilistic. All release/action paths, including partial decryption, must satisfy `hgate`; sampled training does not. Witness honest full epoch proof followed by atomic activation. Falsifier: a stale-parent proof races with another activation, or an inference route bypasses active-root checking. Correctness of *speculative* private state is not obtained by withholding its outputs.

#### DL27 — what C21 can and cannot promise

```lean
-- Privacy alone (necessary, insufficient for the prose P3):
theorem one_instance_view_simulation (hsecure : SecureEncodingProtocol protocol ideal epsSim) :
    ∀ A, AdmissibleHost A → ∃ S,
      ViewAdv (RealView protocol A) (IdealView ideal S) ≤ epsSim

-- Separate authenticity/confinement game:
theorem instance_bound_transition_authenticity
    (henc : AuthenticatedInstanceEncoding protocol epsEnc)
    (hinput : CommittedInputBinding protocol epsInput)
    (hstate : ParentNonceEpochBinding protocol epsState)
    (hgate : CanonicalCustodianRelease protocol epsGate) :
    Pr (fun w => ∃ o ∈ AcceptedDecodings w,
      ¬ MatchesIssuedAuthorizedInstance (IssuedInstances w) o) ≤
      epsEnc + epsInput + epsState + epsGate
```

[INFERRED] `MatchesIssuedAuthorizedInstance` must match **parent state, input, circuit/version, nonce, epoch and output decoding**. Cross-instance label/authentication attacks are excluded by an authenticated composition theorem, not merely by randomized-encoding privacy. The ideal view explicitly includes public metadata and all authorized outputs; computational consequences of those outputs are unavoidable leakage. Witness: one fixed-input one-time encoding with an ideal private custodian; no reusable model handle exported. Useful reactive implementation [OPEN].

[REFUTED: physical P3 from simulation] Copy a valid classical encoding and evaluate it twice; both copies have the same simulatable view and accepted result. Stronger: if an authorized output is W, the simulator can generate the host's later chosen-input computations from W, so view simulation holds while reusable evaluation is available. Even without identity release, a public sufficiently learnable function can be reconstructed from allowed outputs. Thus withdraw “C21 actually delivers P3” unless P3 is renamed **no accepted new transition beyond authorized instances and ideal-output leakage**. Neither cryptography nor this model decides whether duplicate evaluation constitutes experience. This is not a refutation of the usefulness of MPC custody.

#### DL28 — valid epoch-key target; historical-state scope boundary

```lean
theorem retired_epoch_key_recovery_bound
    (hbound : PerEpochCorruptionBelowThresholdIncludingRefreshWindows)
    (herase : HonestErasureAndNoRollback)
    (hkeys : IndependentEpochKeyGeneration)
    (hmigrate : ForwardSecurePrivateMigration epsMigrate) :
    RetiredKeyRecoveryAdvantage ≤ epsEpochCrypto + epsMigrate

-- Optional stronger historical-state game, NOT the source's key-retirement claim:
theorem historical_state_secrecy
    (hbound : PerEpochCorruptionBelowThresholdIncludingRefreshWindows)
    (herase : HonestErasureAndNoRollback)
    (hkeys : IndependentEpochKeyGeneration)
    (hmigrate : ForwardSecurePrivateMigration epsMigrate)
    (hrelease : EqualAuthorizedLeakageAcrossChallengeHistories)
    (hlater : EqualPostChallengeStatesAndCorruptionLeakage) :
    HistoricalCiphertextDistinguishingAdvantage ≤ epsEpochCrypto + epsMigrate
```

[INFERRED] The source C22 retires key/decryption authority and a read-all credential; that conditional target is fine. Distinguish it from the stronger semantic historical-state claim in the optional second signature. Later compromise of a current state identical to the historical state reveals it without recovering any retired key. Equal later state/leakage is therefore needed for an historical-state indistinguishability game, or the claim must concern retired key recovery only. Erasure must cover old shares, backups and refresh/migration material; a bound only at each instant misses sequential corruption of enough parties within one refresh interval. Witness independent one-time epochs with erased old keys, constant public outputs and no model-preserving later leakage. This does not protect classical ciphertexts against a future break of the underlying cryptosystem; its security assumptions must be quantum-appropriate if that is the threat model.

#### DL29–DL30 — contraction and its actual horizon bound

```lean
theorem contractive_step
    (hcontract : ∀ x y, dist (f t x) (f t y) ≤ rho * dist x y)
    (hactual : dist (actual (t + 1)) (f t (actual t)) ≤ inj t + rnd t)
    (hhonest : honest (t + 1) = f t (honest t)) :
    dist (actual (t + 1)) (honest (t + 1)) ≤
      rho * dist (actual t) (honest t) + inj t + rnd t

theorem contractive_unroll (hrho : 0 ≤ rho)
    (hstep : ∀ t < T, d (t + 1) ≤ rho * d t + err t) :
    d T ≤ rho ^ T * d 0 +
      ∑ t ∈ Finset.range T, rho ^ (T - 1 - t) * err t

theorem contractive_expected_bound (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcouple : SamePrescribedMapsDataAndCoins)
    (hstop : InjectionStopsAtFirstAlarm)
    (hround : ∀ t, 0 ≤ rnd t ∧ rnd t ≤ RoundingCap)
    (hinject : E TotalInjected ≤ 2 * B / q)
    (hunroll : PathwiseContractiveRecurrence) :
    E (fun w => dist (actual T w) (honest T w)) ≤
      rho ^ T * InitialDistance + 2 * B / q + RoundingCap / (1 - rho)
```

[INFERRED] DL29 is fine for the same function `f t` on both states; if adaptive data selection changes with the altered state, either include that selector in the contractive transition or explicitly couple the comparator to the realized data/coins. “Same dataset distribution” is not pointwise same map. DL30 needs a uniform rounding ceiling (otherwise rounding may grow without bound) and stopped injection: C2 says nothing about arbitrary corruptions continued after the first alarm. Include the DL02 `M·ε` term when applying a computational envelope. Witness f(x)=x/2 on a bounded scalar domain with exact arithmetic; finite quantization may need a nonzero rounding term. This is an upper bound on full state, not a utility theorem.

#### DL31 — no-wrap already exists; signed decoding needs a bridge

[READ] breadstuffs `metatheory/Bfv/Noise.lean:490–517`, `iter_decrypts_exact`, already assumes both a noise ceiling and `hmi : (mi:ℤ)=iterMsg S T m i`, `hlt : mi<P.t`. The critique's “nothing here carries a message ledger” is too broad. What is absent is a derived range invariant for the desired signed training iteration, and the signed-decoder refinement.

```lean
-- Unsigned decoder + a symmetric range assumption is not this theorem:
theorem signed_no_wrap_old (hsmall : |intended| < (t : ℝ) / 2) :
    unsignedDecrypt ct = intended
-- Repair target:
theorem iter_decrypts_exact_no_wrap
    (hnoise : IteratedNoiseSafe params S T ct msg)
    (hunsigned : UnsignedDecoderRefinesResidue params ct msg)
    (hcenter : CanonicalCenteredDecoder params centeredDecrypt)
    (hrange : ∀ i, CenteredMessageRange params (iterMsg S T msg i)) :
    ∀ i, centeredDecrypt (iterCt S T ct i) = iterMsg S T msg i
```

[INFERRED] Witness zero messages and safe zero noise, any bounded finite linear trajectory. Falsifier: intended −1, modulus t>2; `|−1|<t/2` but the unsigned residue is t−1. Do not “repair” the existing correct unsigned theorem by claiming it already returns centered integers. Also, the advertised deployed 42-step example has `tauDen=1`, not fractional-learning-rate denominator 16 (`Noise.lean:519–525`); calling that specific example wrapped because “tauDen>1” misidentifies its parameters.

#### DL32–DL34 — primitive numerical targets

```lean
theorem stepRR_noise_le
    (hoperand1 : NormInfLE message1 M1 ∧ NormInfLE noise1 B1)
    (hoperand2 : NormInfLE message2 M2 ∧ NormInfLE noise2 B2)
    (hks : NormInfLE keySwitchError Bks)
    (hrefine : RingMultiplyScaleRelinRefinesIntegers ct1 ct2 ctOut) :
    NormInfLE (NoiseRelativeTo ctOut (negaMul message1 message2))
      (RingMultiplyBound N params M1 M2 B1 B2 Bks)

theorem BFVScaleLiftRefinement (Q t z y s : ℤ)
    (hQ : 0 < Q) (hs0 : 0 ≤ s) (hsQ : s < Q)
    (hcert : t * z + Q / 2 = Q * y + s) :
    y = (t * z + Q / 2) / Q

theorem paired_lookup_sound (table : Code → Code × Code) (x y dy : Code)
    (hrow : (y, dy) = table x)
    (hforward : ∀ z, (table z).1 = QuantizedActivation z)
    (hbackward : ∀ z, (table z).2 = SpecifiedDerivative z) :
    y = QuantizedActivation x ∧ dy = SpecifiedDerivative x
```

[INFERRED] All three are fine targets. DL32's `RingMultiplyBound` must be derived from the specified centered integer scale/relinearization operation and explicit N expansion; it is not a free scalar-bound copy. Witness N=1 bounded messages/noises, corresponding to scalar semantics. DL33's `z` must itself be linked to the integer lifted convolution; quotient/remainder alone proves only division of the supplied z. For nearest ties-up with integer numerator and integer positive Q, `(t*z + Q/2)/Q` is the specified rounding; do not use this to assert correctness of an unspecified library's different ties convention. Falsifier mod-Q-only certificate: Q=31,t=4,z=1 vs z=32. DL34 fixes the nondifferentiable point and NaN/infinity conventions or restricts the input domain. Sharing an address but opening different addresses in the two proof legs fails `hrow`.

#### DL35–DL37 — ideal functionality, whole-machine refinement and envelope

```lean
theorem dark_ideal_simulation
    (hprotocol : RealizesReactiveIdealFunctionality protocol Fdark eps)
    (hcorrupt : ExplicitAdaptiveCorruptionAndErasureModel adversary)
    (hresources : AdversaryWithinReductionResources adversary) :
    ∃ simulator, ViewAdv (RealExecution protocol adversary)
      (IdealExecution Fdark simulator) ≤ eps

theorem integer_learner_refinement
    (R : ConcreteState → ReferenceState → Prop)
    (hinit : ∀ c r, InitPair c r → R c r)
    (hstep : ∀ c r input coins c', R c r → ConcreteStep c input coins c' →
      ∃ r', ReferenceStep r input coins r' ∧ R c' r' ∧
        PublicEvents c input coins c' = ReferenceEvents r input coins r') :
    EveryConcreteTraceHasMatchingReferenceTrace R

theorem product_envelope
    (hsub : frobenius (A * B) ≤ frobenius A * frobenius B)
    (hcap : frobenius A * frobenius B ≤ cap) :
    frobenius (A * B) ≤ cap
```

[INFERRED] DL35's signature makes the proof obligation visible but is not itself the reduction: a useful implementation must define Fdark's admission/release/abort/rollback/refresh events, allowed public metadata, corrupt-party views, and erasure boundaries, then **construct** `hprotocol`. A trivial simulator premise would be P→P; do not advertise this header as a construction. Witness: ideal protocol implementing Fdark internally gives perfect simulation but no distributed implementation claim. Identity releases are allowed leakage if authorized, never a proof of opacity.

[INFERRED] DL36 is a standard induction target; all components of optimizer state, rounding, clipping, derivative lookup, counters and key epochs must be in R. Silent concrete steps require a stuttering trace relation rather than falsely demanding one concrete instruction per reference training step. Witness identical reference/concrete machine; a real ciphertext implementation needs DL01/DL32/DL33 and custody refinements.

[INFERRED] DL37 is fine: submultiplicativity is independent lower-level mathematics; product-cap suffices and is conservative under gauge. For mutable factors apply it to the **actual delta** `ΔA·B+A·ΔB+ΔA·ΔB`, or sum three certified product bounds. Witness zero update or rank-one unit vectors with cap 1. Falsifier to factor-only cap: A very small and B arbitrarily large. Power iteration only supplies a lower norm bound, already withdrawn in the source.

### Validation and limitations

[EXECUTED] **Concrete repair:** `notes/astra/displacement-bound.patch` adds `Selvage/AuditDisplacement.lean` in namespace `Minidregg.Selvage.AuditDisplacement`. It proves the exact finite-horizon `2B/q` target, its pathwise domination lemma, an inhabited nonzero-damage q=1/2 witness, and a falsifier when the actual envelope is removed. The source carries a consumer-signature check and `#guard_msgs` axiom pins; no `sorry` or new axioms. `git -C /Users/ember/dev/minidregg apply --check /Users/ember/dev/zkml-research/notes/astra/displacement-bound.patch` exited 0; the patch was **not applied**.

[EXECUTED] The pinned v4.35.0 compiler cannot directly import the warm `AuditSampling.olean`: incompatible header (v4.30.0). Instead, `python3 notes/astra/dark-learning/check_displacement_adapter.py` assembled **exact current source fragments** of `Rbr.uniformProb`, the `Depth` counting lemmas, `AuditSampling` through its detection/expectation/sequential/leakage proofs, and `AuditWitness`, followed by the exact proposed module body. This source-fragment elaboration exited **0 on Lean v4.35.0** with all axiom pins matching. No stubs, assumed replacements or new axioms were used. `adapter-source-slices.json` identifies the source fragments and their hashes; `displacement-adapter-check.log` preserves the command/output. Deprecation warnings come from unchanged copied AuditSampling proofs; the helper also has a harmless unused-section-instance warning.

[EXECUTED] Separately, `DisplacementCore.lean` checks the isolated pathwise lemma and nonzero witness against current warm Mathlib; `CoreCounterexamples.lean` checks four exact counterexamples without imports. Both current-pin checks exit 0 with axiom guards. The four core counterexamples have no axioms; the norm and expectation theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

[EXECUTED] Import boundary: the actual minidregg `scripts/check-import-boundary.sh` exited 0, run read-only with `PYTHONDONTWRITEBYTECODE=1`. Parsing the proposed module with that script's own `lean_imports.header_imports` yields only `Selvage.AuditSampling` and `Mathlib.Analysis.Normed.Group.Real`: permitted Selvage roots and no new library edge. Output is `import-boundary-check.log`.

[OPEN] This is **source-fragment proof validation, not a complete current-toolchain minidregg module/integration build**. The cached closure is incompatible; no full Lean build or dependency download was attempted, and no companion file was modified. The integrator should apply the additive patch in its own lane and run the normal per-module check on the designated warm build host. `Displacement.lean` is the earlier audit-namespace candidate; the exact patch source is `dark-learning/source/Selvage/AuditDisplacement.lean`.

[OPEN] Most signatures above are intentionally statement/interface targets, not implementations. The physical/custody games need concrete protocols and proofs. No claimed attack on BFV, MPC or garbling follows from an interface counterexample. The repairs limit the prose to what the stated theorem would establish and preserve the useful construction work.

## Governance and silicon statement audit — 2026-11-06 task

[READ] This audits the working-tree text of:

- **G** = `/Users/ember/dev/degg-research/research/GOVERNANCE-CLAIM-LATTICE.md`, at clean HEAD `15db9784e2043bb170431203f3c63d88625933e2`.
- **S** = `/Users/ember/dev/redregg/designs/SILICON-TO-SEMANTICS-ALIGNMENT-2026-11-05.md`, at clean HEAD `d1540c5c1435ead2c01c92fe6a1cef3cc303c097`.
- The governance foundations critique and governance Codex synthesis at the same degg-research HEAD, read in full. They describe yesterday's defects, not evidence that their replacements work.

[MEASURED] [EXECUTED] `git rev-parse HEAD` and scoped `git status --short -- <files>` supplied these snapshots; both scoped status outputs were empty. The audit's source line numbers refer to those snapshots. No companion-tree files were changed.

[INFERRED] **44 statement contracts audited; 5 definite current defects with repairs, plus 11 qualification/interface obligations.** This count includes every named theorem in S, its replacements where one old theorem split into several obligations, S's unnamed construction-grade obligations (g)–(n), and G's mathematical/receipt claims. It does **not** count each topical governance claim row as a proposed theorem or count the eleven previously identified bad sketches again. The old sketches are explicitly marked false/incomplete in the source; the current prose repairs are the audit target. The table preserves their status so a maintainer cannot mistake an old code block for the recommended statement.

[INFERRED] The most important new correction is that **deduplication by evidence identity is not sound**. Identical bytes can support different predicates whose false-accept events are disjoint. An important interface qualification is that the advertised binding leg does no logical work in the displayed rule until local subjects and their semantic transport to the joint subject are formalized. A wording hazard is that `Pr[accept ∧ false] ≤ ε` must not be read as posterior reliability of an accepted receipt; §0 already defines the intended false-accept meaning correctly.

[OPEN] The Lean signatures below are **proposed interfaces**, not compiled implementation theorems. Domain names (`DeviceRun`, `ReceiptCheck`, `Experiment`, etc.) denote the semantics spelled out in each entry; they do not claim those types exist upstream. Proof bodies are intentionally not supplied, rather than hidden with `sorry`. Shared conventions: `G.prob E` is the probability of event `E : G.World → Prop` under one normalized experiment; `G.admissible a` is its resource/assumption restriction; `Gₐ` is the induced experiment for adversary `a`; `Budget` is a nonnegative rational plus its upper-bound interpretation. Cryptographic contracts quantify over admissible adversaries and their resource bounds. Deterministic reduction obligations are separate from computational advantage assumptions.

[MEASURED] [EXECUTED] The small, executable falsifiers and semantic event-transport lemma in `notes/astra/governance/GovernanceAudit.lean` were checked with `lean +leanprover/lean4:v4.35.0 notes/astra/governance/GovernanceAudit.lean`; output is in `notes/astra/governance/lean-check.txt`. This compiles only the small `Std`-based audit file, not a project. It contains no `sorry`, new axiom, `native_decide`, or implementation escape; the transport signature and printed axiom footprints are `#guard_msgs`-pinned. `projected_bad_subset` uses standard classical axioms; the finite dedup, record and projection counterexamples have no axioms. These checks prove counterexamples and an event inclusion, not the proposed device/crypto implementations.

### Inventory

[READ] Source locations; [INFERRED] classifications. **D** marks one of the 5 definite current defects. **Q** marks a useful formalization or conditional qualification, not a newly refuted theorem. “Fine” always means the stated contract has meaningful content under its explicit model, not that an implementation satisfies it.

| ID | Source | Statement | Current verdict |
|---|---|---|---|
| G01 | G:32–37 | semantic Boolean lattice | Fine, classical extensional semantics |
| G02 | G:41–47, 59–61 | evidence judgment | Fine with a fixed experiment and adversary class |
| G03 | G:50–65; S:471–475 | meet/composition | **Q:** true union bound; explicit transport is the remaining binding interface |
| G04 | G:77–89; S:457–482 | serialized `Judgment` | **Q:** schema needs an executable budget format and external checked interpretation |
| G05 | G:98–103 | discharge coverage assumption | **Q:** exact theorem discharge is valid; probabilistic receipt discharge pays its failure |
| G06 | G:116–120 | hypergeometric miss | Fine on the uniform, frozen, feasible-size domain |
| G07 | G:152–160 | tolerance implies at best T3 | **D: too strong**, conflates relation tolerance with proof error |
| G08 | G:375–380 | receipt “holds with error ε” | **Q:** intended false-accept meaning is fine; posterior reading is false |
| G09 | G:409–413; S:477–479 | evidence deduplication | **D: too strong**, identity does not identify failure events |
| G10 | G:350–360 | zero undeclared admissions | Fine after the explicit narrowing; not zero computations |
| G11 | G:361–374 | served/evaluated/trained/absent join | **Q:** formalize the one-root shorthand as typed components and relations |
| G12 | G:112, 139–141 | T2* drops verifier-implementation assumption | **Q:** verified binary route is fine; source export alone keeps compilation/FFI premises |
| S01 | S:88–111 | `ozaki_exact_under_acc` | Fine only with the prose's accumulator/refinement premises; old sketch too strong |
| S02 | S:95–107 | `field_dot_via_mma` | Fine with reconstruction/range/reduction; old sketch incomplete |
| S03 | S:159–162, 178–183 | `commit_before_forward` | Fine as occurrence-injective durable coverage; old sketch false |
| S04 | S:163, 184–186 | `leaf_binds` | Fine as a collision reduction; old equation trivial |
| S05 | S:164, 187–189 | `overflow_refuses` safety | Fine with fresh admission IDs; old sketch ill-scoped |
| S06 | S:189–190 | non-full forwarding companion | **D: too strong**, lacks progress/fairness and frame admissibility |
| S07 | S:165, 191–193 | `reboot_continuity` | Fine as accepted recovery under an authoritative durable anchor; old sketch false |
| S08 | S:243–246 | residue intersection/projection | Fine, definitional; projection only inclusion |
| S09 | S:248–254 | proof-leg interpretation independent of TEE | Fine as false-accept bound over an adversary class permitting a broken TEE |
| S10 | S:250–257 | TEE occurrence and confidentiality | **Q:** model confidentiality relationally; occurrence remains unary |
| S11 | S:306, 308 | `air_denotes` | Fine on supported syntax with field/word interpretation |
| S12 | S:307–308 | `air_sound` | Fine; follows from the forward half of S11 |
| S13 | S:309–310 | combinational `rtl_refines` | Fine under successful compilation, supported inputs and representation |
| S14 | S:311–312 | sequential RTL refinement | Fine as separate safety, with progress separate |
| S15 | S:313 | `receipt_means` | **D: too weak**, AST equality neither checks evidence nor proves denotation |
| S16 | S:355–356 | record agreement | **D: too strong**, omitted equality of authenticated terminal roots |
| S17 | S:357–358 | endpoint execution and acknowledged delivery | Fine under an explicit authenticated-ACK transition model |
| S18 | S:359–360 | terminal truncation obligation | Fine as deadline alarm; not a proof of malicious withholding |
| S19 | S:389–392 | tap feasibility | Fine as average work conservation, not a burst/service theorem |
| S20 | S:393–399 | tap assurance/detection | **Q:** make the intended adaptive per-history floor explicit |
| S21 | S:406–428 | attested choke-point coverage | Fine conditional composition; no inferred physical no-bypass fact |
| S22 | S:433–455 | vendor equivalence ⇒ device step | **Q:** source already names gaps; formal implication must include them |
| S23 | S:488–491 | checked accelerator cutpoints | Fine with output commitment preceding challenge and explicit nonlinear TEE leg |
| S24 | S:492–494 | consumable lease ⇒ once-only | **Q:** specify once-only authorization/receipt/billing separately from computation/delivery |
| S25 | S:495–496 | translation certificate | Fine with checker soundness for precisely the artifact semantics |
| S26 | S:497; G:235 | lineage capsules | Fine as transition/rooted-lineage proof target, not merely a hash chain |
| S27 | S:498–500 | proof-gated decryption + persistent DP budget | **Q:** specify adaptive DP and full release transcript game for this proposed direction |
| S28 | S:501–504 | leakage-preserving sharing | Fine as a relational trace/distribution obligation |
| S29 | S:511–520 | retirement accounting | Fine for completed architectural operations, not useful-work attribution |
| S30 | S:521–529 | authenticated operand reads | Fine for declared-dataset consumption; full lineage remains separate |
| S31 | S:530–538 | key retirement confidentiality | Fine only as the explicitly conditional cryptographic-erasure game |
| S32 | S:539–545 | PHY distance bound | Fine under the named timing/error/fraud model; no jurisdiction-continuity upgrade |

### G01–G12: lattice and judgment contracts

#### G01 — semantic lattice

[READ] G:32–37 correctly separates the semantic lattice from evidence. [INFERRED] Lean's `Set Ω` is already extensional predicates; no extra AST quotient is needed for this mathematical layer. Classical complement makes it Boolean. A restricted executable AST is a separate representation and need not decide semantic equivalence.

```lean
theorem semantic_meet {Ω : Type} (P Q R : Set Ω) :
    R ⊆ P ∩ Q ↔ R ⊆ P ∧ R ⊆ Q

theorem semantic_complement {Ω : Type} (P : Set Ω) :
    P ∪ Pᶜ = Set.univ ∧ P ∩ Pᶜ = ∅
```

[INFERRED] Witness: `Ω := Bool`, `P := {true}`, `Q := {false}`. Nontrivial bottom/top and proper predicates exist. Do not demand decidable logical equivalence for arbitrary predicate ASTs merely because the semantic lattice exists.

#### G02 — evidence judgment

[INFERRED] This is a sound definition when the probability experiment, verifier interpretation and resource-bounded adversary class are fixed:

```lean
def EvidenceSound (G : Experiment) (V P : G.World → Prop) (ε : ℝ≥0) : Prop :=
  ∀ a, G.admissible a → (G.withAdversary a).prob (fun w => V w ∧ ¬ P w) ≤ ε
```

[INFERRED] Witness: a verifier that recomputes a nonconstant Boolean function has error zero; admissible adversaries include a constant forgery, and a valid input is accepted. Falsifier for vacuous auditing: an empty adversary class or an always-reject verifier meets soundness but supplies no useful receipt. Require a separate accepted honest instance; this is not a reason to put completeness in the soundness definition.

#### G03 — repair the unused binding leg

[READ] G:51 already gives bounds on `¬P₁` and `¬P₂` in one common world. Those two bounds alone imply the displayed conclusion by a union bound; `Bind` and `ε_b` add no logical content. [INFERRED] This is true mathematics but too weak a specification of the intended semantic join. The local statements must be about their own subjects, and alignment must transport them to the common target.

```lean
theorem projected_composition
    (G : Experiment) (acc₁ acc₂ bind local₁ local₂ aligned target : G.World → Prop)
    (ε₁ ε₂ εb : ℝ≥0)
    (h₁ : G.prob (fun w => acc₁ w ∧ ¬ local₁ w) ≤ ε₁)
    (h₂ : G.prob (fun w => acc₂ w ∧ ¬ local₂ w) ≤ ε₂)
    (hb : G.prob (fun w => bind w ∧ ¬ aligned w) ≤ εb)
    (transport : ∀ w, aligned w → local₁ w → local₂ w → target w) :
    G.prob (fun w => acc₁ w ∧ acc₂ w ∧ bind w ∧ ¬ target w) ≤
      min 1 (ε₁ + ε₂ + εb)
```

[INFERRED] `aligned` means the decoded local subjects agree under specified projections, not that an untrusted Boolean says they do. Witness: two checked openings of one typed request tuple with the same model/input/output and different evidence mechanisms. Falsifier: both local predicates are true of different requests while the target is false. [EXECUTED] `projected_bad_subset` proves the exact event inclusion needed for the repaired union bound; `no_transport_falsifier` supplies the propositional countermodel without transport. No independence assumption is needed.

#### G04 — repair the receipt schema

[READ] G:81–88 is a record of claims; it has no verifier, experiment ID, semantic derivation or binding certificate. Its `ℝ≥0` cannot be a general finite serialized numeric type. `Finset Assumption` gives decidable membership only, not decidable satisfiability. [INFERRED] An attacker can fill this record with `eps = 0`, an arbitrary predicate, and unrelated references.

```lean
structure ReceiptClaim where
  subject : TypedSubject
  predicate : PredAst subject
  window : Window
  experiment : ExperimentId
  resources : ResourceBound
  budget : NonnegativeRational
  assumes : AssumptionFormula
  evidence : List EvidenceRef
  derivation : DerivationCertificate

theorem check_receipt_sound (r : ReceiptClaim)
    (hc : checkReceipt r = true) :
    InterpretedEvidenceSound r.experiment r.resources r.assumes
      (evidenceVerifier r) (denotePred r.subject r.window r.predicate) r.budget
```

[INFERRED] `checkReceipt` must validate a derivation in a restricted calculus whose primitive rules carry proofs/reduction bounds, authenticate all referenced bytes, check their subject/window/version, and round numerical bounds **upward**. Consistency is checked by a sound decision procedure for the chosen assumption language, or by a checkable satisfiability witness; “a Finset” does not suffice. Witness: a recomputation receipt with rational budget zero and an accepted derivation; falsifier: preserve evidence but lower its budget from `1/2` to zero. The repaired checker refuses. No type declaration itself establishes this theorem.

#### G05 — exact discharge is valid; probabilistic discharge has a cost

[READ] G:98–103 proposes removing coverage from downstream assumptions after proving it as a predicate. [INFERRED] Exact implication supports this directly, which is the source’s stated device-step-theorem route. This is not a defect in that route. If it is replaced by a probabilistic receipt, that variant requires an additional error term and joint acceptance.

```lean
theorem discharge_coverage
    (G : Experiment) (accCover accClaim covers target : G.World → Prop)
    (εc ε : ℝ≥0)
    (hc : G.prob (fun w => accCover w ∧ ¬ covers w) ≤ εc)
    (hp : G.prob (fun w => accClaim w ∧ covers w ∧ ¬ target w) ≤ ε) :
    G.prob (fun w => accCover w ∧ accClaim w ∧ ¬ target w) ≤ min 1 (εc + ε)
```

[INFERRED] A conditional-on-coverage proof must be transported to the common experiment carefully; the second premise above is an **unconditional** bound on its restricted bad event. Witness: exact device coverage (`εc=0`). Falsifier: coverage fails with probability `δ`, and every failure hides an undeclared action; the other leg has error zero when coverage holds, yet the joint error is `δ`, not zero.

#### G06 — fixed-population sampling

```lean
theorem fixed_population_miss (N b k : Nat) (hb : b ≤ N) (hk : k ≤ N)
    (bad : Finset (Fin N)) (hcard : bad.card = b) :
    missProbabilityUniformKSubset N k bad =
      (Nat.choose (N - b) k : ℚ) / Nat.choose N k
```

[INFERRED] Freeze `bad` before sampling; uniform sampling ranges over all size-`k` subsets and does not censor unavailable records. Witness: `N=4,b=1,k=2`, miss probability `1/2`. If `k>N`, the “uniform size-k sample” is uninhabited. If an adversary chooses `bad` after seeing the sample, the theorem's independence/freeze domain has been left. Those domains belong in the formal statement.

#### G07 — tolerance is not soundness error

[READ] G:160 says tolerance claims are never stronger than T3 with error including the channel. [REFUTED: that general implication] An exact proof of `|y-f(x)| ≤ 1` can have proof error zero. Its statement is weaker than equality; it is not a randomly wrong equality proof. No probability law on allowed perturbations is implied by the tolerance.

```lean
def Within (f : X → ℝ) (δ : ℝ) (x : X) (y : ℝ) : Prop := |y - f x| ≤ δ

theorem tolerance_relation_sound
    (G : Experiment) (verify : G.World → Prop) (x : G.World → X)
    (y : G.World → ℝ) (δ : ℝ) (ε : ℝ≥0) :
    ProofSystemSoundFor G verify (fun w => Within f δ (x w) (y w)) ε →
    G.prob (fun w => verify w ∧ ¬ Within f δ (x w) (y w)) ≤ ε
```

[INFERRED] Repair the schema by carrying the actual tolerance relation, units and quantifiers. Do not convert tolerance into an error budget without an independently specified distribution/game. Witness: `f(x)=0,y=1,δ=1` is exactly within tolerance and not equal. A deterministic checker can accept it with zero false-accept error for `Within`. The allowed-output relation can indeed permit steering; that does not turn tolerance into a probability of relation falsity.

#### G08 — false acceptance is not posterior truth

[INFERRED] G:41–43 already fixes the intended false-accept meaning; the following refutes only a stronger posterior interpretation of G:375, not its defined judgment. In a 100-point uniform experiment, accept only world 0 and let the asserted predicate be false everywhere. False-accept probability is `1/100`, but conditioned on acceptance the predicate is false with probability 1. [EXECUTED] `conditional_reliability_falsifier` checks the accepted/no-true-accept structure; `rare_accept_count` also checks exactly one accepted world among `List.finRange 100`; the probability numbers are the derived uniform count divided by 100.

```lean
theorem posterior_bound (G : Experiment) (acc P : G.World → Prop) (ε α : ℝ)
    (hα : 0 < α) (hacc : α ≤ G.prob acc)
    (herr : G.prob (fun w => acc w ∧ ¬ P w) ≤ ε) :
    G.conditionalProb acc (fun w => ¬ P w) ≤ ε / α
```

[INFERRED] The repair is primarily to say **“false-accept probability bounded by ε in experiment E”** on receipts. Use the posterior theorem only when its lower bound on acceptance and a meaningful prior distribution actually exist. This is independent of the adaptive composability issue.

#### G09 — deduplicate events, not just evidence IDs

[REFUTED: S:477–479 and G:409–413 as a general sound dedup rule] Let the evidence be the same constant bytes in both legs and let both verifiers always accept. In a uniform Boolean world, `P₁(w)=w` and `P₂(w)=¬w` each have error `1/2`. Their conjunction is always false. Deduplicating by evidence identity to one `1/2` term undercounts the true joint error 1. [EXECUTED] `dedup_premises` and `dedup_by_identity_false` check this exact counterexample.

```lean
theorem dedup_same_failure (G : Experiment) (bad₁ bad₂ : G.World → Prop)
    (h : ∀ w, bad₁ w ↔ bad₂ w) :
    G.prob (fun w => bad₁ w ∨ bad₂ w) = G.prob bad₁
```

[INFERRED] Repair: deduplicate exact repeated **judgments** (same experiment, adversary/resources, accepted-false event, predicate/subject/window and assumption interpretation), or share one primitive failure event after a checked implication from every use to that event. A derivation DAG can record this proof. Identical evidence references alone are insufficient. Exact self-composition is harmless and should be idempotent; it is not a reason to undercount different uses.

#### G10 — the narrowed admission claim is meaningful

```lean
theorem no_undeclared_admissions (r : DeviceRun)
    (hinit : InitialInventoryValid r)
    (hcoverage : EveryAdmissionRecorded r)
    (hlog : EveryRecordedAdmissionDeclared r) :
    ∀ e, AdmissionInWindow r e → DeclaredAtAdmission r e
```

[INFERRED] Witness: a nonempty execution admitting and forwarding a declared job, including a valid initial inventory. Falsifier to the broader claim: an already-approved persistent job performs a training update without a new admission. The displayed theorem says nothing false about that run. Initial inventory matters for a separate claim about active contexts, not for the bare universal statement over new admissions. A probability statement about evidence for these premises must compose their errors; the semantic implication above itself is fine.

#### G11 — replace “one commitment” with one typed relation over multiple roots

[READ] G:361–374 now includes training lineage, correctly. [INFERRED] The remaining root shorthand is dangerous: model weights, corpus bytes and evaluation items are different objects; equal opaque digests cannot say they are related. A single tuple commitment is possible, but its fields and semantic edges must be explicit.

```lean
structure EvaluationServingSubject where
  modelRoot : ModelRoot
  dataRoot : DatasetRoot
  evalRoot : EvaluationRoot
  initRoot : TrainingStateRoot
  lineageRoot : LineageRoot
  inferenceSpec : InferenceSpecId
  trainingSpec : TrainingSpecId
  request : RequestId
  epoch : EpochId

def JoinedClaim (s : EvaluationServingSubject) (w : World) : Prop :=
  ServedWith w s.request s.epoch s.inferenceSpec s.modelRoot ∧
  EvaluatedModel w s.evalRoot s.inferenceSpec s.modelRoot ∧
  TrainedBy w s.trainingSpec s.initRoot s.dataRoot s.lineageRoot s.modelRoot ∧
  EvalItemsAbsentFrom w s.evalRoot s.dataRoot
```

[INFERRED] The repaired soundness statement is G03 instantiated with these projections and all relevant legs (not a single two-leg shortcut). The lineage includes pretraining/imported checkpoints or explicitly limits the claim to the declared training suffix. Witness: a one-step training run with distinct dataset/model roots, served and evaluated under one full inference spec. Falsifier: the same weights with a different tokenizer/system prompt passes a weights-only join but does not mean “the evaluated inference system answered.” A clean suffix starting from an undeclared pretrained checkpoint also does not prove lifetime absence.

#### G12 — T2* must name the deployed machine semantics

[READ] G:112 removes “verifier implementation correct” at T2*. G:139–141 gives a Lean-decided export as the pattern. [INFERRED] Exporting a checked Lean predicate closes a source-level mirror; it does not prove the Lean compiler, runtime, FFI decoding, integer conversions or caller routing correct. Those remain named assumptions unless checked.

```lean
theorem deployed_verifier_refines (r : ReceiptBytes) (m : MachineState)
    (hdecode : decodeReceipt r = some claim)
    (hffi : FfiPrecondition m r)
    (hbuild : LoadedBinaryRefines checkedVerifier m) :
    machineAccepts m r ↔ checkedVerifier claim = true
```

[INFERRED] To remove the implementation assumption completely, `hbuild` must be discharged through a trusted compiler theorem/translation validator and the actual loaded artifact. Otherwise put it in `assumes`. Witness: a byte-pinned binary with a verified decode/refinement path; falsifier: a caller ignoring the Lean return value and returning “accept”. The Lean predicate remains proved while the deployed verifier is wrong.

### S01–S10: arithmetic, receipt device and evidence interpretations

#### S01 — accumulator exactness

[READ] S:92–94's old code remains too strong; S:98–110 explicitly adds the missing premises. [INFERRED] Treat the replacement as a refinement theorem for an explicit accumulator transition, not as a bound on the final sum alone.

```lean
theorem ozaki_exact_under_acc (A : AccModel) (xs ys : List FP4)
    (hlen : xs.length = ys.length)
    (hrep : EveryOperandRepresented A xs ys)
    (hinit : A.initialAccumulator = A.encodeInt 0)
    (hschedule : ValidMmaSchedule A xs ys)
    (hexact : EveryIntermediateOperationExact A xs ys) :
    A.decodeInt (hwMma A xs ys) = integerDot (decodeOperands A xs) (decodeOperands A ys)
```

[INFERRED] `EveryIntermediateOperationExact` must be derived from **local** representability/range lemmas and concrete rounding/alignment semantics. Defining it as the final equality would be `P → P`. A useful lower lemma quantifies over representable inputs and proves the one-step transition commutes with integer addition/multiplication. Nonempty witness: one product `1×1`, zero initial accumulator, supported scale and enough exponent/significand range. Falsifiers to the old bound: nonzero initial accumulator, unequal input lengths, or a model whose alignment discards a small addend before cancellation. The GPU observation is evidence for the model, not a kernel proof that physical silicon follows it.

#### S02 — field dot reconstruction

```lean
theorem field_dot_via_mma (p : Nat) (hp : 1 < p) (A : AccModel)
    (u v : Fin n → Fin p)
    (hlimbs : LimbDecompositionReconstructs 13 u v)
    (hmma : EveryLimbDotExact A u v)
    (hwidth : RecombinationHasNoOverflow A u v)
    (hreduce : ReductionImplementsIntMod p) :
    reduceMod p (recombine13 (limbwiseMma A u v)) =
      (∑ i, (u i).val * (v i).val) % p
```

[INFERRED] This integer-residue identity needs no primality premise. A field presentation can subsequently require prime `p`. Witness: `n=1,u=v=1` and exact integer semantics. Falsifier: a wraparound recombiner can corrupt the result while every individual limb dot is correct. Reconstruction, bit widths and reduction must be actual lemmas, not `hmma` defined as this conclusion.

#### S03 — per-occurrence commit before forward

```lean
theorem commit_before_forward (r : DeviceRun)
    (hinit : ValidInitialState r.initial)
    (hrun : FollowsDeviceStep r)
    (hdurable : DurableStoreSemantics r) :
    ∃ commitOf : ForwardOccurrence r → DurableCommitOccurrence r,
      Function.Injective commitOf ∧
      ∀ f, (commitOf f).time < f.time ∧
        (commitOf f).record = admittedRecord r f.admissionId ∧
        PreservedInAuthenticatedHistory r (commitOf f)
```

[INFERRED] `admittedRecord` contains actual forwarded bytes (or a binding digest), occurrence ID, job/session, epoch and VJM root at admission; the transition relation connects these to what the output port emits. Durability is an acknowledgement from the persistent-store model, not a queued `persist` command. Witness: admit→durable-ack→forward one real frame. Falsifiers: emit forward before durable ack and crash; reuse one commit for two separate forwarding authorizations; mutate VJM before final root inspection. The current prose repairs all three. This proves forwarding coverage, not peer receipt, and it need not allow retransmissions to share one occurrence unless the specification explicitly says they are one event.

#### S04 — leaf binding reduction

```lean
theorem leaf_collision_extract (r₁ r₂ : Record)
    (hne : r₁ ≠ r₂) (heq : leaf r₁ = leaf r₂)
    (henc : Function.Injective encodeRecord) :
    HashCollision outerHash ∨ HashCollision payloadHash
```

[INFERRED] `Record` uses actual payload bytes plus the full typed metadata. The reduction returns colliding preimages, not merely an existential axiom called “collision resistance.” Witness: an injective outer encoding and a toy constant hash allow a concrete nontrivial collision, showing the antecedent is inhabited and the extraction meaningful. In a cryptographic theorem the colliding inputs must be efficiently produced and the reduction's resource overhead charged. An injective hash is unnecessary; the old `leaf = H(...)` equation is just its definition.

#### S05 — overflow safety

```lean
theorem overflow_refuses (r : DeviceRun) (j : AdmissionId) (f : Frame)
    (hrun : FollowsDeviceStep r) (hfresh : FreshAdmission r j)
    (hfull : InsufficientReservableDurableCapacity r.now f) :
    RefusedAt r.now j ∧ ¬ AuthorizedAt r.now j ∧
      ∀ t, r.now ≤ t → ForwardedAt r t j →
        ∃ k, FreshReadmissionBetween r j k r.now t
```

[INFERRED] The later forwarding occurrence belongs to a fresh readmission token; do not silently reuse `j`. Witness: a full one-slot device refuses a second distinct admission. Falsifier: refusal leaves a pending authorization which is forwarded later after a reset. This is a safety theorem; always-refuse is deliberately a model of it. S06 supplies useful progress separately.

#### S06 — repair the non-full liveness companion

[READ] S:189–190 says a non-full execution does forward. [REFUTED: unconditional liveness] A non-full device can receive a malformed/unauthorized frame, crash forever before its durable ack, or be starved by its scheduler. No correct safety device must forward in those runs.

```lean
theorem admitted_frame_eventually_forwarded (r : InfiniteDeviceRun) (j : AdmissionId)
    (hrun : FollowsDeviceStep r)
    (hadmit : ValidFrameAdmittedWithReservation r j)
    (hready : FairDownstreamReady r j)
    (hstore : DurableWritesEventuallyComplete r j)
    (hsched : FairDeviceScheduling r)
    (hstable : EventuallyNoFurtherCrashBeforeCompletion r j)
    (hcancel : NotCancelled r j) :
    ∃ t, ForwardedAt r t j
```

[INFERRED] A bounded-latency variant needs quantitative service bounds, not just fairness. If the chosen abstract device instead makes persistence and forwarding one total atomic operation, state that synchronous model explicitly; fairness is then unnecessary inside that operation, but its refinement to a real asynchronous persistent device remains an obligation. Witness: the three-event admit/ack/forward trace extended by idle steps. Falsifier: the same admitted frame with downstream-ready false forever. This repair does not smuggle availability into safety.

#### S07 — anchored recovery

```lean
theorem reboot_continuity (r : DeviceRun) (a : AuthoritativeAnchor) (s : Snapshot)
    (hanchor : AnchorTracksDurableCommitOrder r a)
    (hload : recover a s = some recovered)
    (hauth : SnapshotAuthenticationHolds s) :
    HistoryExtends recovered.history (authorizedPrefix r a) ∧
      recovered.nextId > maxPreviouslyAuthorizedId r ∧
      recovered.epoch = a.epoch

theorem stale_snapshot_refused (a : AuthoritativeAnchor) (s : Snapshot)
    (hstale : s.counter < a.counter) : recover a s = none
```

[INFERRED] These are accepted-recovery safety contracts; they do not promise recovery succeeds after every crash. The anchor update, log persistence and authorization protocol need a crash model that makes `AnchorTracksDurableCommitOrder` provable. Witness: matching authenticated snapshot and anchor after one durable commit. Falsifier: restore the empty snapshot after one authorized frame. A counter checked only after forwarding cannot repair the gap. The source's “preserves every previously authorized forward” must refer to persistent coverage, not actually resending every old frame.

#### S08 — residual-set identity and projection

```lean
def Res {Ω : Type} (A E : Set Ω) : Set Ω := A ∩ E

theorem residue_intersection {Ω : Type} (A E₁ E₂ : Set Ω) :
    Res A (E₁ ∩ E₂) = Res A E₁ ∩ Res A E₂

theorem projected_residue_inclusion {Ω Subject : Type}
    (π : Ω → Subject) (A E₁ E₂ : Set Ω) :
    π '' Res A (E₁ ∩ E₂) ⊆ (π '' Res A E₁) ∩ (π '' Res A E₂)
```

[INFERRED] These are fine algebra, not evidence interpretation. Witness making inclusion strict: two worlds map to the same subject; `E₁` holds only in the first and `E₂` only in the second. [EXECUTED] `projected_intersection_strict` checks the incompatible hidden-witness core. Distinct predicate interpretations, not the definitional identity, carry assurance.

#### S09 — proof leg independent of TEE integrity

```lean
theorem proof_leg_validity (G : ProofReceiptGame) (a : Adversary)
    (ha : G.proofAdmissible a) (hps : ProofSystemSound G a ε)
    (hbind : SubjectBindingReduction G a εb) :
    (G.run a).prob (fun w => ProofAccepted w ∧ ¬ OutputRelation w) ≤ min 1 (ε + εb)
```

[INFERRED] `proofAdmissible` must permit the adversary to break/control the TEE, and the proof statement must not use an unverified TEE-supplied assertion as an algebraic premise. Witness: a direct proof of `y=f(x)` over a public input/output relation while the TEE lies. Falsifier: the proof only establishes “the TEE signed y”; then its own relation is true and there is no theorem of output validity independent of TEE trust. The source correctly calls for per-leg interpretation.

#### S10 — separate occurrence safety from confidentiality games

[READ] S:250–257 places occurrence and confidentiality in the same per-world predicate story. [INFERRED] Occurrence can be a trace property. Confidentiality compares adversarial observations across possible secrets; it is a hyperproperty or indistinguishability game. Putting the word `Confidential` into a unary predicate does not specify that game. Nor is a TEE the only possible mechanism for these goals; this is only the role of the chosen TEE leg in this construction.

```lean
theorem tee_occurrence (G : AttestationGame) (a : Adversary)
    (ha : G.admissible a) (hcode : MeasuredCodeRefinesEndpoint G)
    (hfresh : EpochAndChallengeFreshness G) :
    (G.run a).prob (fun w => QuoteAccepted w ∧ ¬ OccurredOnNamedDevice w) ≤ G.occurrenceError

theorem tee_confidentiality (G : ConfidentialExecutionGame) (a : Adversary)
    (ha : G.admissible a) (hcode : MeasuredCodeRefinesEndpoint G)
    (hobs : ExplicitLeakagePolicy G) (hisolation : TeeIsolationAndLifecycle G) :
    G.distinguishingAdvantage a ≤ G.confidentialityError
```

[INFERRED] Specify allowed outputs/metadata, corruption timing, migration, rollback, termination and side channels in the second game. Witness: two secrets with the same authorized public output and a constant public trace in an ideal isolated endpoint. Falsifier: a perfectly correct, freshly attested program that prints the secret; the occurrence theorem holds and secrecy fails. “Both share Stmt” repairs identity, not confidentiality.

### S11–S22: refinements, transcripts, taps and vendor devices

#### S11 — AIR denotation

```lean
theorem air_denotes (e : SupportedAst) (x : Input e) (y : Output e) :
    (∃ aux : AuxTrace e, Sat (emitAir e) (encodeInput x) (encodeOutput y) aux) ↔
      y = denote e x
```

[INFERRED] Fine for a total supported fragment with proved range checks and field-to-word interpretation. The existential is necessary: wrong intermediate columns do not satisfy just because endpoints are right. Witness: a one-gate addition/multiplication with the genuine witness. Falsifier to a missing range bridge: a field value representing a different integer modulo the characteristic; a field equation alone cannot identify the intended integer.

#### S12 — per-trace AIR soundness

```lean
theorem air_sound (e : SupportedAst) (x : Input e) (y : Output e) (aux : AuxTrace e)
    (h : Sat (emitAir e) (encodeInput x) (encodeOutput y) aux) :
    y = denote e x
```

[INFERRED] Fine; follows from S11's forward direction with witness `aux`. Witness: the same nontrivial gate. Negative test: alter a wire used by that gate and show either refusal or unchanged semantics, rather than test only the honest trace. No cryptographic probability is asserted here; this is the deterministic relation before the proof-system soundness leg.

#### S13 — combinational RTL refinement

```lean
theorem rtl_refines (e : SupportedAst) (m : RtlModule)
    (hc : compileBookToRtlSat (bookOf e) = some m)
    (x : Input e) (hwf : WellFormedInput e x) :
    decodeOutputs e (evalModuleOutputs m (encodeEnv e x)) = some (denote e x)
```

[INFERRED] Prefer decoded outputs to equality with a singleton association list unless the port contract truly has exactly one output in that order. Witness: supported one-gate expression, successful compile, nonzero input. Falsifier to over-generalization: unsupported syntax causes `none`; no circuit follows. `WellFormedInput` must have a concrete inhabitant and only express representation constraints, not the desired output equality.

#### S14 — sequential refinement is a separate contract

```lean
theorem rtl_trace_refines (m : SequentialRtl) (f : ReferenceMachine) (r : ClockedRun m)
    (hreset : ResetProtocol r) (hmem : MemoryOrderProtocol r)
    (hhs : HandshakeProtocol r) (hrel : InitialStateRelation r f) :
    ∃ a : AbstractRun f,
      visibleInputs a = acceptedInputs r ∧ visibleOutputs a = emittedOutputs r
```

[INFERRED] For infinite runs use a stuttering simulation and a prefix/safety formulation, then separately prove progress under fairness. This contract requires no spurious or reordered outputs; merely showing every emitted output is individually valid is weaker. Witness: one request, one stalled clock, then one correct response. Falsifier: duplicate a correct response; per-output validity passes but trace equality fails.

#### S15 — repair `receipt_means`

[READ] S:313 states accepted receipt ⇒ its AST equals `Pred.graph f ...`. [INFERRED] If the receipt language permits other predicates, that is false; if the checker merely demands this AST, it is a syntactic tautology. Neither direction connects receipt evidence to the world's computation.

```lean
theorem graph_receipt_sound (G : ReceiptGame) (r : GraphReceipt f)
    (hc : checkGraphReceipt r = true)
    (hroute : DeployedCheckerRefines checkGraphReceipt G)
    (hderive : VerifiedDerivationSound r.derivation G) :
    G.prob (fun w => acceptsEvidence r w ∧ ¬ GraphHoldsForSubject f r.subject w) ≤ r.budget
```

[INFERRED] This is a G04 specialization with an indexed predicate type. Witness: a genuine graph proof whose model/input/output match the receipt and loaded checker. Falsifier: the right graph AST with garbage evidence; the old AST-equality statement can still hold, the repaired verifier refuses. A deterministic `GraphHolds` conclusion is possible only for an exact evidence checker with its full reduction premises, not a general positive-error proof receipt.

#### S16 — record agreement needs root equality

[READ] S:355–356 says authenticated roots binding the same session, length and schema imply record agreement except binding failure. [REFUTED: literal current sentence] Two honest parties can authenticate different roots for different one-record histories with identical session/length/schema. There is no hash collision. [EXECUTED] `equal_length_different_records` checks the minimal record counterexample.

```lean
theorem equal_root_record_agreement (a b : TranscriptOpening)
    (ha : ValidOpening a) (hb : ValidOpening b)
    (hs : a.session = b.session) (hn : a.length = b.length)
    (hv : a.schemaVersion = b.schemaVersion) (hr : a.root = b.root)
    (hneq : a.records ≠ b.records) :
    ∃ c, EfficientHashCollisionWitness a b c
```

[INFERRED] Different authenticated roots are instead an **equivocation/conflict evidence** object, when obligations require one history. They are not a record-agreement premise. Witness: identical nonempty transcripts. Falsifier to the unrepaired form: `[false]` versus `[true]`, signed by the same legitimate session endpoint. Canonical length/root conventions must be checked; a root over an untyped list is insufficient.

#### S17 — execution and acknowledged delivery

```lean
theorem endpoint_records_mean (r : EndpointRun)
    (hrun : FollowsVerifiedEndpoint r) (hauth : AuthenticatedPeerAcks r) :
    (∀ rec, ExecutionRecord r rec → ∃ e, ExecutionEvent r e ∧ BindsRecord rec e) ∧
    (∀ rec, DeliveryRecord r rec → ∃ a, PeerAcknowledged r a ∧ BindsRecord rec a)
```

[INFERRED] This is fine under the endpoint model. “Acknowledged” is the precise claim; it does not prove a human read or use of the result. The ACK itself binds the session/request/response digest, and the peer-key assumption is named. Witness: request→execution→response→authenticated ACK. Falsifier: log “delivered” immediately after a local socket send, then drop the packet; execution happened but no peer acknowledgement did.

#### S18 — deadline/truncation alarm

```lean
theorem terminal_obligation_alarm (r : MonitorRun) (o : TerminalObligation)
    (ho : AuthenticatedAndAgreed r o) (ht : TrustedClockPastDeadline r o)
    (hm : MissingRequiredTerminalEvidence r o) :
    alarm r = true
```

[INFERRED] Fine as fail-closed alarm; it establishes an unfulfilled obligation, not malicious intent. Witness: terminal length/root agreed in advance, deadline elapsed, no terminal receipt. Falsifier to a broader malicious-truncation conclusion: a network outage after an honest endpoint completed. Detectability also requires the monitor to run and have the authenticated obligation; it cannot be inferred from inspecting an arbitrary shorter prefix.

#### S19 — average work conservation

```lean
theorem sustainable_tap_feasible (s : TapSchedule) (p Btap Bengine : ℝ)
    (hnonneg : 0 ≤ p ∧ 0 ≤ Btap ∧ 0 ≤ Bengine)
    (hunits : UniformAuditCostUnits s Btap Bengine)
    (harrivals : LongRunSelectedWorkRate s = p * Btap)
    (hservice : LongRunServiceRate s ≤ Bengine)
    (hstable : SublinearBacklogGrowth s) :
    p * Btap ≤ Bengine
```

[INFERRED] Fine as necessity only. Averages do not prevent a finite burst overflowing the FIFO, and `Btap` bytes/sec cannot be compared with proof jobs/sec without a work conversion. Witness: constant input, constant per-item cost, service exceeding arrivals. Falsifier to sufficiency: arbitrarily large bursts under an acceptable long-run mean. Selection with value-dependent audit costs also changes the average-work expression.

#### S20 — repair adaptive tap assurance with conditional floors

[READ] S:393–395 demands every bad item detected at the stated probability, but does not formalize its conditioning. [INFERRED] A marginal floor is inadequate for AuditSampling's adaptive stopping-time consumer: an adversary can corrupt exactly histories with no service. Service availability and corruption decision must precede fresh selection appropriately.

```lean
theorem tap_detection_conditional (G : AdaptiveTapGame) (h : G.History)
    (hh : G.reachable h) (hbad : G.nextCommittedItemBad h)
    (hcommit : ItemAndWitnessFrozenBeforeSelection G h)
    (hservice : UniformConditionalServiceGuarantee G h)
    (hbeacon : ConditionalSelectionUnpredictability G h εbeacon)
    (hcheck : ConditionalCheckerSoundness G h εchk)
    (hbind : ConditionalBindingFailureBound G h εbind) :
    G.nextAlarmProbability h ≥ max 0 (G.sampleRate * (1 - εchk) - εbind - εbeacon)
```

[INFERRED] A stronger unconditional bad-event hybrid can derive these legs if its conditioning losses are accounted for; one global adversary advantage must not be reused as an unchanged conditional bound on arbitrarily rare histories. Witness: fair fresh independent coin after each frozen item, sufficient reserved audit capacity, fail-closed timeout. Falsifier: service succeeds on half the histories; attacker recognizes the unserved half and corrupts only there. The overall service rate is `1/2`, detection on corrupt rounds is zero.

#### S21 — coverage through an attested choke point

```lean
theorem choke_point_covers (r : FacilityRun)
    (hroute : EveryScopedExternalEffectCrossesDevice r)
    (hcode : DeviceExecutionRefinesReceiptStep r)
    (hdev : EveryDeviceForwardDurablyRecorded r) :
    EveryScopedExternalEffectDurablyRecorded r
```

[INFERRED] Fine conditional implication. Attestation establishes `hcode` only through code measurement, initialization and measured-code semantics. The external no-bypass premise is not proved by the number of NICs in a VM manifest. Witness: a model with one enforced output transition. Falsifier: GPU DMA or a management channel outside the modeled path. Both the source and the repaired statement keep this physical/runtime premise visible.

#### S22 — vendor netlist equivalence is not deployed device equivalence

[READ] S:443–444 writes `(vendor attestation ∧ ZK equivalence ∧ public refinement) ⇒ device step = f`; S:449–455 acknowledges substitution and combinational limitations. [INFERRED] The deterministic implication still overstates positive-error proof evidence and a combinational check. A stateful receipt device requires state/reset/handshake refinement plus the loaded-bitstream/netlist and silicon bridge.

```lean
theorem deployed_vendor_device_sound (G : VendorDeviceGame)
    (hpub : PublicRtlSequentiallyRefines f)
    (hcec : EquivalenceProofSound G εcec)
    (hload : LoadedArtifactBindingSound G εload)
    (hatt : AttestationInterpretationSound G εatt)
    (hsilicon : PhysicalDeviceRefinesLoadedArtifact G) :
    G.prob (fun w => AllDeviceEvidenceAccepted w ∧ ¬ DeviceTraceRefines f w) ≤
      min 1 (εcec + εload + εatt)
```

[INFERRED] If equivalence is only combinational, restrict `f` to that combinational sub-block and retain a separate theorem for the sequential wrapper; do not quantify over the whole device. Witness: a one-step stateless device with pinned loaded artifact. Falsifier: equivalent combinational datapaths but a wrapper that forwards before durable ACK, or a correct proven netlist with a swapped bitstream. The honest physical premise is an assumption until an actual implementation bridge exists.

### S23–S32: the additional construction obligations

#### S23 — proof-checked accelerator cutpoints

```lean
theorem checked_cutpoint_sound (G : CutpointGame) (a : Adversary)
    (ha : G.admissible a)
    (hfreeze : InputsAndClaimedOutputsCommittedBeforeChallenge G)
    (hfresh : FreshUniformFreivaldsChallenge G)
    (hlinear : LinearCheckerRefinesMatrixRelation G)
    (hnonlinear : TrustedNonlinearEndpointRefinesSpec G) :
    (G.run a).prob (fun w => CutpointAccepted w ∧ ¬ CutpointRelation w) ≤
      G.freivaldsError + G.bindingError
```

[INFERRED] This is a fine conditional target. The nonlinear trust leg must be named in the larger inference claim; the linear checker alone does not verify nonlinearities or all model identity. Witness: one fixed matrix/vector/output with a fresh challenge and correct nonlinear transition. Falsifier: reveal the challenge first, then choose a wrong output in its orthogonal kernel. “Post-commitment” must include the **claimed result**, not only the public matrix/input.

#### S24 — once-only what?

[READ] S:492–494 burns a lease before releasing a result and claims O-2. G:233 combines unique receipt, no double billing and counted retries. [INFERRED] These are different events. Consuming a monotonic token is not enough to show one computation, one delivery, or one invoice: the same authorized result can be sent twice, a retry can duplicate computation, and a crash after burning can produce zero releases.

```lean
theorem lease_authorizes_at_most_one_release (r : LeaseRun)
    (hrun : FollowsAuthoritativeLeaseMachine r)
    (hanchor : DurableLinearizableCounter r)
    (hbind : ReleaseBindsLeaseRequestAndOutput r) :
    ∀ lease, (releaseAuthorizations r lease).length ≤ 1

theorem invoice_idempotent (r : BillingRun)
    (hrun : FollowsInvoiceMachine r)
    (hid : BillingKeyIsRequestAndLease r) :
    ∀ request, (chargedInvoices r request).length ≤ 1
```

[INFERRED] Repair the receipt predicate to say which of authorization, computation, send, acknowledged delivery or charge is once-only. Deduplicate retransmissions at the receiver if the service needs effective once-only delivery. State retry policy explicitly. Witness: consume lease then authorize exactly one result; falsifier: crash after consumption (no liveness), or replay a signed result on two network sends (one authorization, two transmissions). Do not assert exactly-once computation from this mechanism.

#### S25 — translation validation

```lean
theorem translation_certificate_sound (src : SourceArtifact) (dst : TargetArtifact)
    (cert : TranslationCertificate)
    (hc : checkTranslation src dst cert = true) :
    Refines (targetSemantics dst) (sourceSemantics src)
```

[INFERRED] Fine; `Refines` must specify termination/exception/undefined-behavior and memory observations relevant to the consumer. The target's actual artifact digest is the one checked and loaded. Witness: a nontrivial one-block identity/addition translation. Falsifier: mutate an output instruction while retaining the certificate and confirm refusal. A checker defined as a constant `false` needs a separate accepted witness; a constant `true` requires proving a generally false refinement.

#### S26 — optimizer lineage capsules

```lean
theorem lineage_sound (c : LineageCertificate)
    (hc : checkLineage c = true)
    (htrans : TransitionCheckerSound c)
    (hbind : CapsuleOpeningBinding c) :
    ∃ states : Fin (c.steps + 1) → TrainingState,
      states 0 = c.initialState ∧
      StateCommitsTo (states (Fin.last c.steps)) c.finalRoot ∧
      ∀ i : Fin c.steps,
        TrainingTransition c.spec c.dataset c.schedule i
          (states i.castSucc) (states i.succ)
```

[INFERRED] This is the deterministic core under exact checker/binding premises; real cryptographic certificates require an event bound instead of treating hash binding as perfect. `TrainingState` includes weights, optimizer moments, RNG, data cursor and imported-parent identities. Root hash chaining alone would be vacuous provenance, but the source's transition-grade target is fine. Witness: two states linked by one specified update and explicit initialization. Falsifier: valid-looking capsules containing unrelated optimizer moments or a smuggled initial checkpoint. “Trained on D” is relative to the initialized/declared lineage, not a claim about an unproven ancestral history.

#### S27 — proof-gated release plus a DP counter is not a DP theorem

[READ] S:498–500 adopts a gate with a persistent DP budget. [INFERRED] A sound proof of computing a query says nothing about its differential privacy. A persistent counter can correctly account for queries whose privacy costs were falsely assigned, or ignore leakage from rejection, timing, threshold shares and repeated queries across rolled-back identities.

```lean
theorem adaptive_release_dp (G : ReleaseGame)
    (hneighbor : FixedDatasetAdjacency G)
    (hbudget : PersistentGlobalPrivacyFilterSound G ε δ)
    (hmechanisms : EachAdaptiveMechanismConditionallyDp G)
    (hrandom : MechanismCoinsSampledByAuthorizedProtocol G)
    (hgate : ProofGateBindsWholeReleasedDerivation G)
    (hsim : FullReleaseTranscriptSimulatableFromAllowedOutputs G εsim) :
    ApproximateDp G.adversaryView G.adjacency ε (δ + εsim)
```

[INFERRED] The approximation term depends on the simulator's distance definition; if `εsim` is computational indistinguishability, the conclusion is **computational DP**, not statistical DP. Keep that choice explicit. Counter scope includes every release under the same dataset/accounting identity across crashes, concurrency and migrations. Witness: one randomized-response mechanism with a trusted fresh coin and one-unit privacy charge. Falsifier: host chooses the random tape to reveal the raw bit while still proving correct execution for those supplied coins. A proof of knowing coins is not a proof they were sampled honestly. The proof-gated decryption game also needs release/share transcript simulation; the counter does not supply it.

#### S28 — leakage-preserving accelerator sharing

```lean
theorem sharing_preserves_leakage (G : SharedAcceleratorGame)
    (hpartition : EnforcedPartitionAndScheduler G)
    (hreset : CrossTenantStateSanitization G)
    (himpl : AcceleratorRefinesLeakageModel G) :
    ∀ s₀ s₁, G.allowedLeakage s₀ = G.allowedLeakage s₁ →
      Indistinguishable (G.otherTenantView s₀) (G.otherTenantView s₁)
```

[INFERRED] Fine as a relational contract, not a unary “confidential run” assertion. The observer includes timings, contention, cache state and proof/FHE scheduling visible to other tenants. Witness: time-partitioned ideal accelerator with fixed-length public schedules and cleared private state. Falsifier: secret-dependent instruction count delays another tenant even when values never cross address spaces. The formal leakage function prevents an empty “all observations are allowed leakage” definition from masquerading as secrecy.

#### S29 — completed architectural operation accounting

```lean
theorem retirement_counter_exact (r : AcceleratorRun)
    (hrun : FollowsCounterCoupledSemantics r)
    (hinit : r.counterInitial = 0)
    (hreset : ResetPreservesAuthoritativeAccounting r) :
    r.counterFinal = ∑ e ∈ completedArchitecturalOperations r, operationWeight e
```

[INFERRED] Fine for the source's explicitly named completed architectural operations. Define whether cancelled partial operations contribute; retries that really execute may contribute more than one event. Counter widths must avoid wrap or fail closed. Witness: two completed vector MACs with a stall and one pre-execution cancellation. Falsifier: a hidden completion path not incrementing the counter. This is not useful-work attribution or a count of all analog transistor activity; those require another relation to the declared job, precisely as S:520 notes.

#### S30 — authenticated reads at the operand boundary

```lean
theorem consumed_sample_provenance (r : TrainingExecution) (D : DatasetRoot)
    (hrun : FollowsAuthenticatedLoaderAndCache r)
    (himmut : VerifiedPagesRemainImmutableThroughConsumption r)
    (hbind : DatasetOpeningBinding r D) :
    ∀ c, ConsumedTrainingSample r c →
      ∃ index version bytes,
        OpensDataset D index version bytes ∧ ConsumedBytes c = bytes
```

[INFERRED] Fine for dataset provenance at this boundary. Bind tags and **bytes** together through DMA/cache replay and version transitions; labels and sample preprocessing must be included in the declared training relation when relevant. Witness: one verified immutable page consumed once. Falsifier: verify page D, mutate its bytes while preserving tag D, then consume. This theorem does not establish the initial weights' origin or that the optimizer used all and only these samples; S26 and the typed join G11 supply those distinct obligations.

#### S31 — cryptographic erase after epoch retirement

```lean
theorem retired_epoch_confidentiality (G : ErasureGame) (a : Adversary)
    (ha : G.admissibleAfterRetirement a)
    (hcopy : NoPriorSecretOrKeyCopyInAdversaryView G)
    (hclear : AllPlaintextBuffersAndKeyDerivationPathsDestroyed G)
    (hrollback : NoEpochRollback G)
    (henc : RetainedCiphertextEncryptionSecure G)
    (hleak : EqualAuthorizedPriorLeakage G) :
    G.postRetirementAdvantage a ≤ G.encryptionAdvantage + G.erasureFailure
```

[INFERRED] This gives the source's conditional confidentiality of retained ciphertext, not universal erasure. It must include persistent master-key derivation paths, in-flight DMA, caches and migration snapshots in the zeroization/lifecycle model. Witness: ideal one-use epoch key erased after draining buffers, same permitted pre-retirement leakage in both challenge worlds. Falsifier: erase a cached derived key but retain its derivable master secret. Without the encryption premise, destroying a key says nothing about ciphertext confidentiality.

#### S32 — PHY-timed proximity

```lean
theorem distance_bound_sound (G : DistanceBoundingGame) (a : Adversary)
    (ha : G.admissible a)
    (hkey : ResponseKeyBoundToNamedDeviceEpoch G)
    (hclock : BoundedOneSidedTimingError G)
    (hphysics : PropagationDelayLowerBound G)
    (hrapid : RapidPhaseProtocolSound G) :
    (G.run a).prob (fun w => ProximityAccepted w ∧
      G.actualDistance w > G.claimedRadius w) ≤ G.fraudAdvantage
```

[INFERRED] Fine only under its explicit timing, error, response and adversary model. The radius derives conservatively from a **lower** bound on travel time per distance and a maximum timing underestimate; arbitrary software RTT does not inherit the rapid-phase fraud bound. Witness: an honest enrolled device at known short distance with timing margin. Falsifier: early guessing, a colluding nearby key holder, or timestamp under-reporting beyond the stated error. A successful exchange establishes proximity at that epoch, not continuous jurisdiction residence or that an inference ran on the nearby device.

### Historical defects, regression teeth and integration

[READ] The twelve-item historical inventory in `governance-codex-synthesis.md:113–126` corresponds here to S01, S02, S03, S04, S05/S06, S07, S08/S09/S10, S11/S12, S13/S14, S16/S17/S18, S19/S20 and G03/G09. The source already retracts the bad sketches. This audit does not report the old final-root, repeated-frame, bad-aux-trace or reversed-bandwidth examples as new discoveries.

[INFERRED] The **5 definite current defects** are G07, G09, S06, S15 and S16. Each has a repaired statement and a witness/falsifier above. The **11 qualifications/interface obligations** are G03, G04, G05, G08, G11, G12, S10, S20, S22, S24 and S27. They have useful explicit contracts but are not counted as newly refuted theorems: some source prose already names their missing premises, some are proposed directions without a claimed theorem, and others warn against interpreting the source more strongly than it says.

[INFERRED] Priority for implementation:

1. Reuse one computational-binding **bad event and reduction witness** for G03/S04/S16; do not instantiate `PositionBinding` by assuming global hash injectivity. Thread its advantage into the shared experiment's budget. A global cryptographic advantage cannot automatically become a uniform conditional advantage in S20 without proving that transport.
2. Build receipts as checked derivation DAGs with typed subjects, exact rational budget upper bounds and primitive-failure references. Dedup only proven-identical failure events or exact repeated judgments. This repairs G04/G09 and makes the binding budget reviewable.
3. Implement the small durable device state machine and prove S03/S05/S07, then add the independently stated progress premises in S06. Model ack-before-forward, crash at every boundary and stale snapshots; count occurrences, not frame values.
4. Keep output validity, occurrence, authorized release, delivery and confidentiality separate. Their conjunction is G03 instantiated with explicit transports, not an intuition supplied by a shared hash.

[OPEN] No device, compiler, TEE, DP or cryptographic implementation was built by this lane. No theorem signature above is a claim of an upstream implementation. The compiled artifacts deliberately prove only the reusable logical transport and concrete counterexamples. No paid search queries or PDF downloads were used; this is a source-statement audit, not a literature survey.
