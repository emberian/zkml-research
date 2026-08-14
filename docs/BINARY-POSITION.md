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
- ⚑ **"Vega" is P-256 + Hyrax — discrete-log, NOT post-quantum.** A
  post-quantum comparison table with a discrete-log entry in it.
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

**The real gap is ring-switching's connectors**: no `Basis` of an extension
over a subfield exists in 400 files, and `liftWord` points the wrong way.

## Corrections to my brief

- **The binary cone is NOT unwired** — it is consumed by 4 `Compiler/` and 3
  `Assurance/` modules, with a real proved multi-round bound
  `m·2^(ℓ−1)/|F| + (1−τ)^q` in **`AdditiveFriQuery.lean` (836 lines)** — not
  the file I named.
- **`HalfThresholdFriTower` is not binary at all** (`CharP` count 0).
- **The `Phalanx` in `~/paperbin` is the wrong paper** (FHE ciphertext
  packing); the right one is eprint 2021/1263.

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
