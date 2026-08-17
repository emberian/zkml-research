# The binary-field position: our layer is field-agnostic, and the short path is not Ligerito

2026-08-14. Full analysis: `notes/binaryspartan-position.md` (1,203 lines).

## ⚠ Same correction as the sibling lane: BinarySpartan EXISTS

This lane also could not find it and said so. **It is in the eprint review
queue** — ember holds the title page, abstract, and EF benchmark slide — so by
construction it is absent from every mirror, author listing and repo search.
**Two independent lanes made the same inference from a sound search.** The
class is now well enough attested to be a standing rule: *absence from a
published corpus is evidence about the corpus, never about reality, and a
paper described as unpublished is not evidence at all.*

## ⚑ But the benchmark scrutiny stands, and it matters

- **The EF harness (`privacy-ethereum/csp-benchmarks`) runs on an M1/8-core,
  not an M4 Max.** Measured there: Flock **33.93 ms**, Binius64 **67.29 ms** —
  and the slide's "Vega 44.2" corresponds to `spartan2` at **541.72 ms**.
- ⚠ **CORRECTED 2026-08-17 (paper read at source; our slide-era scrutiny
  partly refuted)**: **"Vega 44.2" is the real Vega_MC, measured 44.23 ms —
  NOT `spartan2` at 541 ms.** Our identification was wrong. Also dissolved:
  the M1-vs-M4 harness discrepancy (all rows same-machine M4 Max through
  Flock's pinned harness, best-of-five, disclosed) — *our scrutiny was
  scrutiny of the SLIDE, and the paper is cleaner than the slide.* What
  survives: **Flock-wins-in-aggregate, conceded and measured at 1.96× in the
  paper's own Table 1**; residuals are peak-of-sweep reporting and an
  "additive optimizations" claim eliding the JBR-vs-UDR regime difference.
- ⚑ **Flock's own verified abstract (eprint 2026/1329) reports 82k BLAKE3/s on
  a SINGLE M4 Max core**, against BinarySpartan's 410k on twelve — **2.2–2.4×
  faster per core, and >660k on ten cores, i.e. it wins outright in
  aggregate.**
- **The 6.2 ms latency and 219k h/s throughput claims differ by ~41×** — which
  is the *batched-vs-single* gap, the same shape as Thaler's `1/B + 1/n`
  overhead being 0.22% at B=512 and 100% at B=1. **Both figures can be true;
  quoting them together as one system's characterization is the error.**
- ⚑ **And "Poseidon was broken" is not what happened.** The Poseidon Initiative
  pivoted **Poseidon2 → Poseidon1 (MDS)** over a margin-eroding attack, still
  runs through Dec 2026, and there is **no institutional EF artifact — one
  researcher's thread.** **leanVM today is KoalaBear: a 31-bit PRIME field.**

## ✅ THE DELIVERABLE: 13 of 18 keystones transfer with NO new mathematics

**Decisive census: 0 `IsPrimitiveRoot`, 0 `rootsOfUnity`, 0 `primitiveRoot`
anywhere in the tree.** Every Reed–Solomon code is over an abstract
`dom : ι ↪ F`. ⚑ **The usual reason a proof system is prime-pinned — a smooth
multiplicative subgroup — never applied to us.** The prime pins that exist are
`ZMod 5/7` *teeth* and a BabyBear *deployment* layer; **never a theorem
binder.** Sponge indifferentiability is field-*free* (`[AddCommGroup Rate]` =
XOR), and the degree-3 rung was **already built char-2-deliberately.**

## ⚑⚑ ONE WALL, AND IT IS A VACUITY TRAP WAITING TO SPRING

`Selvage/Proximity.lean:178` — `FoldingData` carries **`two_ne : (2 : F) ≠ 0`
as a STRUCTURE FIELD.** That is **uninhabitable in characteristic 2**, so
**every theorem over it goes VACUOUSLY TRUE, on a green build, the moment
anyone "instantiates it at a binary field."** A whole binary-field port could
land, compile, pass its axiom pins, and prove nothing.

✅ **CLOSED 2026-08-14 — and the hypothesis is REAL, so the bug was the
silence, not the binder.** The multiplicative fold divides by `2` and `2x`; at
char 2, `f(x) + f(−x) = 2f(x) = 0` and squaring is the Frobenius, so the
`{x,−x}` fibres are **singletons**. ⚑ **Multiplicative FRI does not exist over
a binary field** — migrating `FoldingData` would not be a migration but a
*different protocol*, **and that protocol already exists and is proved**:
`AdditiveFriTower` + `AdditiveProximity` (`additiveProximityGap_UD`,
`additiveFold_distance_UD`, unconditional below `(1−ρ)/3`).

So the fix targets the silence: new `Selvage/CharTwoWall.lean` names the
emptiness, names **the consequence** (`foldingData_vacuous_of_charTwo` — at
char 2 *every* predicate holds of every `FoldingData`, including `False`), and
locates the wall exactly. ⚠ **Subtler than reported**: a theorem over
`FoldingTower F ι m` with `m` free is **not** fully vacuous at char 2 — it
survives at `m = 0`, so the refusal is satisfiable *and* refutable rather than
blanket. And `strippedCharTwoWitness` is a **machine-checked negative
control**: `FoldingData` *minus* `two_ne` is verified inhabited over `ZMod 2`,
so **`two_ne` is the whole wall and deleting it cannot be papered over.**

⚑⚑ **TWO NEW FAILURE CLASSES, BOTH CAUSED BY THE IMPORT GRAPH:**

1. **AN IMPOSSIBILITY PROOF DOWNSTREAM OF ITS SUBJECT CANNOT BE CITED BY IT.**
   The theorem refuting the two `Tower256AdditiveFri*` modules lived in a file
   that *imports* them. **That is exactly how a refuted module stays in the
   build looking healthy.** Fixed by splitting the cardinality argument into a
   new module directly above the controller — and the modules are now
   **retracted with the refutation machine-checked in-file.**
2. **AN IMPORT BOUNDARY WAS MISLEADING AN AUDITOR ABOUT WHAT IS PROVED.**
   Within `Theory/`, the additive proximity gap genuinely *is* a hypothesis —
   because the boundary forbids naming `Selvage` — so 4 files and 8 docstrings
   labelled it a floor or *"NAMED, not proved"* while
   `additiveProximityGap_UD` **proves it unconditionally one layer up.** Labels
   now read *"hypothesis HERE; PROVED one import layer up"* with the genuine
   remainder stated. **An auditor reading "residual" as "unproved anywhere"
   was being misled by an import edge.**

**The census is reassuring: exactly ONE trap in 345 structures.** `ringChar ≠
2`, `Invertible 2`, `CharZero`, odd-characteristic and 2-adic root-of-unity
hypotheses are **absent repo-wide**; `Fact (Nat.Prime p)` is never a wall; the
~150 `/2` hits are ℝ decoding radii. **One new find**:
`Compiler/FriQueryVerifierAir.lean` takes `(2:F)*half = 1` over an
unconstrained `[Field F]` — **vacuous at Tower256**, previously prose-only.

**And there is now a detector**: `scripts/check-char2-vacuity.sh` walks
**29,263 declarations** and gates on the *finding*, not a self-test — **proved
red-capable twice rather than assumed** (it reported 5 hits before the wall
module got its structural exemption, and *renaming that module fails the run
rather than reading clean*). Exemption is by home module, not a name list;
**allowlist empty by design.**

⚠ **Follow-up**: `SemanticHistoryTower256CheckpointGame` and
`...DeployedBcs` still build on the retracted admission module and are vacuous
for the same reason — deleting all four together is the next step.

## ✅ STEP 1 LANDED: BaseFold on the additive tower

`Selvage/AdditiveBaseFold.lean` — **838 lines, 0 `sorry`, 13 axiom pins all
clean, whole tree green (8,992 jobs)**, `b5da623`.

**The vacuity was avoided structurally, not by luck**: **not one declaration
takes a `FoldingData`, `FoldingTower`, `fold`, `proximityTest` or `chalExt` as
an argument** — the descent operator is `Theory.friFold`. Independently
confirmed by the sibling lane's detector: **0 vacuous across 29,263
declarations with this module in the tree.**

**Classification:**
- **Ports verbatim (cited, not reproved)**: the entire Boolean-Möbius /
  coefficient layer — *these are statements about coefficient VECTORS, so no
  characteristic enters.*
- **Genuinely different**: the fold operator — **not inconvenient,
  uninhabited.**
- **Char-2 analogue**: `friFold_eval_decomp`; `novelPack`, the LCH novelpoly
  packing — ⚑ **its recursion is literally `parityInterleave` with
  `expand F 2` replaced by `.comp (foldPoly (β 0))`**; and `lchLevelWord_succ`,
  where the new moving part is that **the ordered basis is STATE and folds
  alongside the word.**
- **Already proved additively (cited)**: the distance bound, unconditional
  below `(1−ρ)/3`.

**The terminal identity landed in its STRONG form** — `lchLevelWord_terminal`
for *every* `p` in the window, plus `exists_unique_table_novelPack`, with
**`novelPack` proved a bijection of the window** (surjective via
`foldPoly_decompose`, injective by a parity-of-degree argument).

## ⚑⚑ A SOUNDNESS GAP IN OUR OWN TRANSCRIPT, FOUND BY PORTING

`keystone_basis_ambiguity` at **GF(16)**: `X² + X` on the four-point domain
`span{1, x₁}` is the commitment of `X²` under basis `(1, x₁)` **and** of
`C(1+x₁)·X + X²` under `(x₁, 1)` — **same span, same evaluation points, same
Merkle leaves, both orderings proved independent, different tables, different
terminal constants.**

> **An additive-FRI transcript that binds the DOMAIN but not the ORDERED BASIS
> does not determine the committed multilinear.**

**There is no multiplicative counterpart** — there the packing basis *is* the
monomial basis and the domain gets no vote. **So this is a hazard that only
exists on the binary side, and it was invisible until someone ported.**

⚠ **And it was measured, not speculated**:
`Compiler/Tower256AdditiveFriController.lean` and its Raw sibling **bind a
sponge `domainId`, not a basis.** *Named, not repaired* — the fix is a
transcript change in a cone the lane did not read.

⚠ **A second convention hazard**: `AdditiveFriTower.lean` folds the **reversed
basis** while the multilinear layer peels **LSB-first**. **Two additive tower
conventions now coexist and will disagree**; unifying them needs the deployed
index layout, and the lane declined to decide it silently.

⚠ Correction to my brief: `Theory/AdditiveNTTTransform.lean` **had already
closed `[ANTT-transform]`** and already carried the fold machinery — *"part of
'port the machinery' was 'discover it exists.'"*

## The short path — and it is not Ligerito

**BaseFold on the additive tower → then ring-switching.**

⚑ **Ring-switching is a COMPILER with security-preserving reductions** (Thm 3.5
proved by *constructing an emulator*) — **precisely and only what Selvage is**
— and **Diamond–Posen's own stated compilation target is "a characteristic-2
adaptation of BaseFold."** ***Step 1 produces exactly what step 3 consumes.***

⚑ **THE LIGERITO VERDICT IS SUPERSEDED — exploratory formalization refuted
two of its six "absent" claims and inverted its sequencing** (ember: *"I'm more
in favour of exploratory formalization than dismissing out of pocket"*, and he
was right). `Selvage/LigeritoInterleaved.lean` (567 lines, **0 errors, 0
warnings, no `sorry`, no `axiom`**, 4 axiom pins, `0c08c93`):

- ❌ **"Column distance is a metric `relDist` cannot express" — REFUTED.**
  Diamond–Gruen define `Cᵐ` as *"a block code over the alphabet `𝔽ᵐ`"* whose
  words *"differ at a column if they differ at any component"* — **that is
  ordinary Hamming distance at a bigger alphabet.** The obstruction was a
  `[Field F]` binder on the **alphabet**, and `CorrelatedAgreement.lean`'s own
  `omit [Field F]` annotations are the evidence the mathematics never used it.
- ⚠ **"Interleaved code object" and "generic codes with distance" were
  overstated** — 12 lines, and the cone is already written over an arbitrary
  `Submodule`.
- ✅ **Genuinely absent**: the `ℓ = m` proximity gap, column openings, and any
  *proof* about tensor coefficients. *That is the part that matters.*
- ⚑ **The sequencing inverts the intuition**: Ligerito's **general-code** bound
  sits at the `d/3` radius — **exactly where `rs_proximityGap_UD` is proved
  unconditionally** — while its **headline RS** bound needs `d/2`, which
  `ProximityGapUDTight.lean` leaves open behind Polishchuk–Spielman. **The
  cheap case stands on proved ground; RS is the expensive one.**
- **Cost: 12 named missing lemmas** (8 to §3, 4 more to §6). **Exactly one —
  DG24 Thm 3.1 — is substantial mathematics**; two are wide-but-mechanical
  retypings of the binder class this lane showed is cosmetic.

⚑ **AND THE ERRATA ARE DISPLAY-ONLY — "Ligerito is broken" would have been the
flattering-number sin in reverse.** Every base in the theorem it quotes
(AER24 §3.2 eq 18) has the form `1 − (·)/m`, which settles both typos. The
cross-check that decides it: **the note's own `|S_i| = 148` is exactly
`⌈−100/log₂((1+ρ)/2)⌉`, and the printed base would have given 71** — so §6.4
and the benchmarks used the **corrected** base. **The claimed 100-bit level and
the proof sizes stand.**
⚠ Two things the note does not say, found by arithmetic: a general linear code
buys only **61 bits** from those 148 queries and needs **241** for 100 (1.63×
the Merkle openings §6.4 calls dominant); and §6.4's *"`|F| ≫ 2^λ` so drop the
`1/|F|` terms"* has only 2²⁸ of headroom against an `m₁k₁` of order 2²⁶–2³⁰,
so **those terms land at or above the query term.**
⚠ **A notation trap that probably caused the original mis-verdict**:
**Ligerito's "nonzero rows" and Diamond–Gruen's "differing columns" are the
same set** — the two papers put the interleaving factor on opposite axes, so
taking both at face value makes them look like different metrics.

## ✅ STEP 3 LANDED: the ring-switching connectors

`Theory/ExtensionBasis.lean` + `Selvage/RingSwitching.lean` (`eb1c6bf`,
`f5b604f`), whole tree green.

**Diamond–Posen read properly**: ring-switching **is** a compiler, and says so
— Construction 3.1 is **agnostic to the PCS it compiles**, naming Blaze, WHIR,
*"and even large-field schemes that haven't been created yet."* **Theorem 3.5
is STRAIGHT-LINE** (Def 2.9: the emulator outputs `t` immediately after the
commitment, *before seeing `r`*), its proof is three lines, and step 3 is
literally *"by reversing Definition 2.2."* Interface required: **exactly three
call sites**, plus completeness and Def-2.9 security. ⚑ **A fixpoint nobody
had flagged: `Setup′` chooses `L`, hence `κ`, hence `ℓ′` — the compiler does
not.**

**The connectors**, with Mathlib carrying more than expected (`Basis.reindex`,
`Basis.equivFun`, `Basis.tensorProduct`): what was genuinely missing is **the
cube reindexing `Fin (2^κ) ≃ B_κ` and the packing map on it.**
- `packEquiv` states Def 2.2 as a **`K`-linear equivalence**, so ⚑ **`.symm`
  *is* Theorem 3.5's extraction step** — the extractor is the inverse, not a
  construction.
- ⚑ **`towerExt_finrank`**: every sub-level extension of the binary tower has
  degree an exact power of two with **κ = d exactly** — *crossing `d` tower
  levels consumes `d` multilinear variables.* **That is why `B_κ`, not
  `Fin (2^κ)`, is the right index type.**
- ⚑ **`liftWord` was not pointing the wrong way — it is the packing map at
  κ = 0** (`liftWord_eq_packOf_zero`), its degenerate instance at the one arity
  that contracts nothing; `liftWord_not_packing` refuses it at every real
  extension, and `unpackWord` supplies the missing direction.
- ⚑ **`tensorMul_not_injective` turns the paper's Remark 3.3 into a theorem**:
  a verifier handed one `L`-element instead of the array `ŝ` is **unsound**,
  not merely lossier.

**Two things already in the tree that nobody knew were the paper's**:
`eqMle_zero_test` **is Theorem 3.5's Schwartz–Zippel leg verbatim**, and
**the straight-line extractor Def 2.9 demands is already code-agnostic**
(`subUdRecover` carries no characteristic hypothesis and an abstract domain,
with the additive distance bound inside its radius). ***Missing is wiring, not
mathematics.***

## ⚑⚑ THREE INDEPENDENT SOURCES CONVERGE ON ONE GAP

The handoff is `RingSwitchTarget = Complete + Extractable`, and **exactly one
item blocks**: `keystone_basis_ambiguity` makes **`Extractable` FALSE unless
the additive-FRI transcript binds the ORDERED basis, not just the domain.**

- The **BaseFold-additive lane** found it by constructing the GF(16)
  counterexample.
- The **ring-switching lane** found it independently as the blocker in its
  handoff list.
- ⚑ **And Diamond–Posen's own Corollary 4.5 is the same fact from the other
  side.**

✅ **CLOSED 2026-08-16** (`9679a16`, **minidregg** — ⚠ my brief had the path
wrong; no such controller exists under `breadstuffs/metatheory` at all).

⚑ **The diagnosis of WHY the hole existed is the finding.** Read at source:
`challengeInput` was `envelope statementBytes ++ roots`, and **`grep beta`
across both controllers returns nothing** — while **the `Clause` carries
`basis`/`basisExact`/`offset`/`offsetExact` first-order.** *The statement HAD
the ordered basis; no transcript function ever read it.* ⚠ And "`domainId`" is
two different objects, **neither of them the basis**: one is a per-level label
that is *a function of the level index alone — not even of `ell`*, the others
are cSHAKE namespace separators. ⚑⚑ **The entire obligation lived in a
DOCSTRING** on `statementBytes` (*"must include the complete manifest/clause
statement encoding"*), **with no field and no theorem behind it — and the
tree's only inhabitant sets it to nine constant bytes spelling
`"minidregg"`.**

**The binding**: `basisPrefix` encodes `ell`, `m`, `offset`, then the `ell`
elements as **indexed frames in index order**, spliced into `challengeInput`
*and* `queryPrefix` of *both* controllers — **positional by construction,
since anything set-shaped would reintroduce the hole one level down.**

**Closed both directions**: `table_unique_of_novelPack_eq`, and ⚑
**`no_span_indexed_decoder` — NO function of `(additiveDomain, codeword)` is
correct on honest commitments.** `transcript_determines_table` now holds in
both controllers and **was FALSE before this commit**; **`Extractable` is
discharged**, with `spanBoundPcs_not_extractable` proving it FALSE without the
binding (satisfiable *and* refutable). The reordering tooth proves the bases
differ **and** their `additiveDomain`s are **equal** — so the mutation is real
and the old binding is provably blind to it.

**Flag day: EMPTY** — zero Rust consumers, no `@[export]`, no golden bytes.
⚠ Incidental: `transcriptControllerDigest` values are **hand-assigned registry
naturals with no relation to the controller's actual bytes.**

⚠ **Residuals, stated not absorbed**: `statementBytes` is closed only for the
basis; **`Extractable` remains the zero-error idealization** — the handle is a
polynomial, not a Merkle root, so **what is proved is that the decode map is
WELL DEFINED, not that FRI proximity realizes it**; and the Raw deployment's
accept-tooth is **vacuous at `m=0`**.

~~That is overdetermined. Binding the ordered basis in the transcript is the
next concrete piece of work on this path**, and it is a change to
`Compiler/Tower256AdditiveFriController.lean`, which today binds a sponge
`domainId`.

## Vacuity discipline, self-caught

The ring-switching lane caught one **in its own work**: its first
`RingSwitchSecure` was `∃ err : ℝ, err ≤ bound` — **trivially provable, i.e.
exactly the sin.** Replaced with an assembly step constrained by a supplied
accepting set (**refutable by a wrong constant**) plus a theorem that the
antecedent is satisfiable.

## Corrections to my brief

- **The binary cone is NOT unwired** — it is consumed by 4 `Compiler/` and 3
  `Assurance/` modules, with a real proved multi-round bound
  `m·2^(ℓ−1)/|F| + (1−τ)^q` in **`AdditiveFriQuery.lean` (836 lines)** — not
  the file I named.
- **`HalfThresholdFriTower` is not binary at all** (`CharP` count 0).
- **The `Phalanx` in `~/paperbin` is the wrong paper** (FHE ciphertext
  packing); the right one is eprint 2021/1263.

## ✅ THE TOP OF THE STACK: Spartan is three things to COMPOSE, and the third isn't a reduction

`Assurance/SpartanR1CS.lean` — **883 lines, 56 decls, 20 axiom pins, no
`sorry`**, tree green.

| Spartan piece | verdict |
|---|---|
| Zerocheck randomization | **HAVE, proved** |
| Outer sumcheck (deg 3) | engine HAVE; R1CS instance **now built** |
| Inner sumcheck (deg 2) | engine HAVE; **now built** |
| Witness PCS opening | claim object HAVE, **protocol absent** (the Ligerito lane's) |
| Sparse matrix eval (SPARK) | **absent entirely** |

⚑ **The reframing: the inner sumcheck is not the hard part.** Its three claims
are literally three `Selvage.LinearConstraint` values on the witness word, so
**the landed γ-batching lemma retires them at `2/|F|` with nothing new
proved.** What is actually absent is **a commitment scheme for sparse
multilinears — and that is a COST obligation, not a soundness one.**

⚑ **And the cheapest path does NOT go through SPARK.** SuperSpartan's `ñext`
is **soundness-neutral in the IOP** *and removes the indexer-honesty
assumption* — **so the route is uniformity**, whose only prerequisite is a
trace/row/transition notion `Compiler/Air.lean` lacks. *That reroutes the one
piece listed as absent-entirely.*

**Two theorems worth naming:**
- **`spartanTerminal_eq_honest` is the hand-off AS A THEOREM** — phase 2's
  obligation is *exactly three values*, and the `eq` factor is not one of them.
  **That is the object the Ligerito and ring-switching lanes can aim at.**
- **`spartan_sound` composes against the DEPLOYED verifier**:
  `SpartanOuterRealAccepts` contains no honest side. ⚑ *"Without
  `outerReal_iff_sumcheckAccepts` every bound would have been about an
  idealized verifier — a vacuity that survives a green build and passes axiom
  pins."*

**Optimization classification** (criterion: does the verifier's *check*, the
*relation*, or the *bound* change?):
- **Free**: Gruen §4, the Speedup line §3–§6, **and Binius64's byte tables —
  which are NOT a lookup argument** (the section is titled *"Prover
  Algorithm"*; `grep -ci logup` = 0).
- **Protocol changes needing re-proof**: Gruen §3, the univariate skip,
  Dao–Thaler constraint packing (**needs a tower-basis linear-independence
  lemma**), BDT Alg. 4.
- **Relation change**: **Phalanx SIMD R1CS — and its own folding soundness has
  no explicit bound.**
⚠ **This supersedes an earlier triage that treated the whole
Gruen/Dao–Thaler/BDT line as "all prover-cost, soundness unchanged." Three of
them are protocol changes with new bounds.**

⚑ **The vacuity tooth it wrote against itself**: `composed_bound_is_vacuous_at_f7`
proves **`8/7 > 1`** — **characteristic-freedom buys the PROOFS, not the
PARAMETERS.** *That is the concrete reason ring-switching is load-bearing
rather than merely elegant.*

⚠ **Honest scope**, seven items, the sharpest being **M5: all these theorems
quantify over a GIVEN witness, and Spartan is an argument of KNOWLEDGE.**

⚑ **And a twin caught by the LINKER, not the file**: the lane's first draft
defined `matVec`, which `ZkmlLowRankUpdate.lean` already had. **`lake build
Assurance.SpartanR1CS` was GREEN — the two never met. Only the umbrella build
saw it.** ***A per-file green cannot see a twin, by construction.***

## Who else is doing this

**Exactly one group: ArkLib + CompPoly** (EF-funded, Quang Dao, active this
week). Clean is structurally prime-only (`[Fact p.Prime]`); soundcalc-lean's
`FieldParams` carries a **primality proof**. **Binius64 (632 Rust files) and
Flock carry zero formal content — not even a differential test.**

**They are ahead on ring-switching and composition. But their FRI-Binius has
no soundness statement at all (`-- TODO: state RBR KS`), and there are 33
`sorry`s in the Binius leaves — against our 0.**

## Repo defects surfaced en route

⚑ **Two `Assurance/Tower256AdditiveFri*` modules are VACUOUS at positive
height** — `merklePcs_empty_of_positive` *proves their carrier type empty.*
Plus `docs/SELVAGE-COMPLETE.md:155-159` is refuted by
`jointGameFamily_impossible` while `:106-107` calls landed work open, and
stale docstrings in `AdditiveNTTTransform.lean` would mislead an auditor into
thinking the additive cone **assumes** a proximity gap when it **proves** one.
