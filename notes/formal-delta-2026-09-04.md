# Formal-methods delta, 2026-08-15 → 2026-09-04: does "nobody else has both legs" still hold?

2026-09-04. Landscape lane. The claim under test (SLVG_THOUGHT.md §I, verbatim): *"ArkLib's
composition theorems are `sorry`; the fast systems carry zero formal content; the one EF-funded
formal effort has 33 sorries in its Binius leaves and no soundness statement for its own FRI."*
Plus minidregg/README.md's four "to our knowledge" items: `fsKeystone` (RBR→FS at (t+k)·ε_rbr),
BCS at the deployed alphabet, `SpongeIndiff*` ("only mechanized indifferentiability outside
EasyCrypt CCS'19"), `Depth.lean`; and the frontier note's position #5, *"an instantiated two-sided
soundness bound < 1 at deployment parameters … Nobody else has a number at all."*

Baseline (notes/formalization-frontier.md, 2026-08-13): ArkLib `scripts/axiom_baseline.json` =
**416 sorry-tainted declarations, 133 security results**, at `9349870` (clone /Users/ember/src/ArkLib).

## 0. Verdict

**The compilation-layer half of the claim survives, and ArkLib's own status docs say so in their
own words** (§1.3). **Three sentences we hold are now wrong or overclaimed and should be edited:**

1. *"no soundness statement for its own FRI"* — was already inexact and is now clearly so: ArkLib
   has had a FRI soundness **statement** (`fri_soundness`, BCIKS20 Claim 8.3) with `by sorry`; and
   its Binius directory carries **13 `*_rbrKnowledgeSoundness` theorem statements** including the
   full-protocol one, all sorry-tainted. Correct wording: *"admitted soundness statements"*, not
   *"no statement"*. The "33 sorries" is now **32** (code-only tokens; tainted declarations 72 → 54).
2. *"Nobody else has a number at all"* (frontier #5; README's "two-sided budget" bullet as a
   uniqueness claim) — **false since 2026-08-20.** better.codes (EF FV team + Yukon + zkSecurity)
   runs a Lean-kernel-checked, axiom-closure-gated leaderboard whose live state is a **two-sided
   interval [68.02, 116.13] bits** on the ABF26 reduction threshold for a concrete KoalaBear
   interleaved-RS profile (§6). Different object from ours (one IOP reduction's spot-check
   quantity, *"not a full-protocol security claim"* — their words), but it is a two-sided,
   kernel-checked, parameter-concrete number, and 22 solvers' agents raise it daily.
3. *"RBR→Fiat–Shamir compiler theorem — absent everywhere"* — must be scoped to IOPs/RBR: VCVio has
   a **kernel-clean EUF-CMA theorem for the Fiat–Shamir Σ-protocol transform** (forking lemma,
   `FiatShamir.euf_cma_bound`, landed April 2026, not previously in our notes). Nobody has the
   state-restoration/RBR→FS compiler for IOPs; that sentence stands with the qualifier.

Not verdict-changing but load-bearing for the README's "seams" sentence: **VCVio landed sorry-free
Merkle multi-extractability under one global query bound (2026-09-01)** — the extractor half of
BCS now exists in the tree ArkLib's Phase-6 roadmap says will consume it. StarkWare: no delta.
Sponge indifferentiability: absence holds (§4, instruments listed). Depth/accumulation: absence
holds; one pre-window Lean twin of SuperNeo folding found (axiom-bearing, §4).

## 1. ArkLib re-measured at `22dbd4e` (2026-09-04 00:58 +0100)

Clone: `git clone --shallow-since=2026-07-15 https://github.com/Verified-zkEVM/ArkLib.git
/Users/ember/src/ArkLib-2026-09` (110 commits in window; **55 since 2026-08-14**).

### 1.1 Counts [DERIVED]

Method A — **their own kernel sweep** (`scripts/AxiomSweep.lean` → `scripts/axiom_baseline.json`,
the `sorryAx`-tainted allowlist CI gates against; this is what the 416 was):
```
python3 -c "import json;print(len(json.load(open('scripts/axiom_baseline.json'))['sorry']))"
```
| | `9349870` (08-13) | `22dbd4e` (09-04) | Δ |
|---|---|---|---|
| sorry-tainted declarations (their sweep) | **416** | **314** | −102 (131 removed, 29 added) |
| "security results" — name regex `sound\|complete\|knowledge\|secure\|binding\|hiding\|zk\|indiff\|extract` (reproduces 133 exactly on the old file) | **133** | **123** | −10 |
| same regex without `complete`/`extract` | 91 | 74 | |
| `nonstandard`-axiom-tainted | 0 | 0 | |

Method B — source tokens, comment-stripped (small Python lexer; block/line comments and strings
removed; `\bsorry\b`):
| | 08-13 | 09-04 |
|---|---|---|
| `.lean` files under `ArkLib/` | 347 | 430 |
| lines | 107,984 | 162,825 |
| code-only `sorry` tokens | **203** (59 files) | **183** (55 files) |
| crude `grep -rw sorry` (includes docstrings) | 228 | 239 |
| `axiom` declarations | 0 | 0 |
| `opaque` declarations | 1 | 1 |

The crude grep goes UP (228→239) while the code-only count goes DOWN (203→183): the new files
carry docstrings that *talk about* `sorry` ("Verified vs. admitted" sections). Count code, not text.

### 1.2 The load-bearing theorems, one by one [READ at HEAD]

| item | file:line | state 09-04 |
|---|---|---|
| composition `append_soundness` / `_knowledgeSoundness` / `_rbrSoundness` / `_rbrKnowledgeSoundness` (Verifier and OracleVerifier) | `OracleReduction/Composition/Sequential/Append.lean:846–1007` | all `:= by sorry`; 11 code-only sorries in file (was 16); tainted list shrank 57 → 27 append/seqCompose names — the removed ones are CWSS-package and `def`-level entries, **every `*Soundness` composition theorem is still tainted** |
| `seqCompose_*Soundness` | `…/General.lean:396–596` | tainted |
| textbook implications `rbrSoundness_implies_soundness` etc. | `OracleReduction/Security/Implications.lean:76` | `:= by sorry` (PR #783 "discharge three rbr-soundness admits" touched this file — 3 admits closed, this one not) |
| FRI soundness | `ProofSystem/BatchedFri/Security.lean:741` `lemma fri_soundness` (BCIKS20 Claim 8.3) | `:= by sorry`; `Fri.Spec.*Relation` definitions themselves tainted (`Fri/Spec/SingleRound.lean:280,289,496,505`) |
| STIR | `Stir/MainThm.lean:170 stir_rbr_soundness`, `:224` | tainted, `sorry` |
| sumcheck | `Sumcheck/` 19 tokens; `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` tainted | unchanged |
| **BCS transform** | `OracleReduction/BCS/Basic.lean` — 81 lines, `renameMessage` is the only definition; `BCSTransform` is a **commented-out stub** (lines 56–79), 0 code sorries because there is no code | **stub, unchanged** |
| **Fiat–Shamir (basic)** | `OracleReduction/FiatShamir/Basic.lean:160–170` `fiatShamir_completeness … := sorry`; docstring "We will show … state-restoration (knowledge) soundness implies (knowledge) soundness" | **no FS soundness statement exists**; completeness admitted |
| Fiat–Shamir (duplex sponge) | `FiatShamir/DuplexSponge/Security/Soundness.lean` — 16 lines, docstring only; `KeyLemma.lean` 1 sorry, `BadEvents.lean` 4, `Lookahead.lean` 2, `Backtrack.lean` 2, `ProverTransform.lean` 2, `State.lean` 5 | all files pre-date 08-13 (present in old clone); no change |
| Binius | `ProofSystem/Binius/` 11 files, 6,831 lines, **32** code-only sorries (was 33: `BinaryBasefold/Steps.lean` 13→12); 13 `*_rbrKnowledgeSoundness` statements incl. `BinaryBasefold/General.lean:145 fullOracleVerifier_rbrKnowledgeSoundness`; `FRIBinius/General.lean` still completeness-only | tainted decls 72 → 54 |
| RingSwitching | 15 files, 18 sorries; tainted 23 → 14 | |
| Hachi (lattice PCS) | "chain CWSS end to end" #770, "perfect correctness of the nonrecursive Hachi" #782, "make extractors computable" #697 — the `Ajtai.InnerOuter` cone lost 42 tainted names and gained 11 (`*_perfectCompleteness`) | the one composition track that is moving |

**Answer to the brief's three questions: no sorry-free FS/RBR compiler theorem; no BCS transform
theorem (not even a definition); no sorry-free FRI soundness statement.** Nothing in the window
touched `BCS/`, `FiatShamir/Basic.lean`, or the composition soundness theorems except lint/perf
passes (`git log --since=2026-08-14 -- <path>`).

### 1.3 ArkLib's own words, 2026-08-29/30 [READ]

`docs/design/00-current-status.md` (status date 2026-08-29, landed #811 2026-08-30): *"unrestricted
stateful composition theorems remain admitted"*; deferred from the first train: *"state
restoration, rewinding, and general conditioned-ROM arguments; the oracle-elimination compiler and
backend assignment; broad FRI, Spartan, Nova, and BCS migration."* `docs/design/05-roadmap.md`,
Phase 6 (sized XL): *"6. interactive BCS and Fiat–Shamir security transfer; 7. exact BCS knowledge
soundness through the extractor pipeline. The first Merkle adapter consumes VCVio's supported
shared-ROM extraction theorem."* Phase 7: *"indifferentiability and alternative oracle models."*
`ProofSystem/ToyProblem/Spec/General.lean:135–140`: *"the generic `StateT` security-composition
theorems of `OracleReduction/Composition/Sequential/Append.lean` (admitted, with no toy-problem
consumer …)"*. They also adopted our vocabulary independently: `Leaderboard.lean:100` — *"The
carrier is directional, and inhabitation alone asserts nothing."*

### 1.4 What DID land (08-14 → 09-04), by area [READ from `git log`]

- **Coding theory is where ArkLib is moving** (Hicks, Hristova, Prince, AryaETHn, `aleph-prover[bot]`):
  #763 *"admit-free MCA witness in the unique-decoding range"* (`McaLowerWitness.ofUniqueDecodingRange`,
  0 sorry, 2026-08-18); #762 BCIKS20 UD-CA on the `epsCa` carrier; #756/#767 correlated-agreement
  admits discharged "via Aleph"; #692/#755 module-alphabet MCA; #841 interleaved-RS list
  decodability (WHIR Lemma 4.4); #845 folding preserves list decoding (WHIR Thm 4.20); #843 RS
  Johnson counting bound; new dirs `ProximityGap/CapacityBounds/{Entropy,Frs,JohnsonLower,Powers,
  Subfield,UniqueDecoding}`, `ProximityGap/GrandChallenges/`, `ListDecodability/`. The Johnson-range
  MCA input `rs_mcaError_le_in_johnson_range` is a tagged **external admit** (in the baseline).
- **They are repairing their own statements**: #733 *"repair five defective statements in §5 and §7"*
  (BCIKS20), #718 *"add missing hypotheses to modified_guruswami_has_a_solution (Claim 5.4)"*, #772
  *"repair D_YZ index order and two Prop 5.5 defects"*, #715 *"encode witnesses over the Boolean
  cube, not the diagonal"* (Binius). Wrong-statement green is being found and fixed there too.
- **ABF26 toy problem** #754 (2026-08-20, same day as better.codes launch): `ProofSystem/ToyProblem/`,
  12 files, 6,766 lines, 0 code sorries, headline declarations on the three standard axioms
  (their docstring), error kept *symbolic* with the numeric route quarantined outside the import cone.
- **Instrument work**: #765 axiomsweep fixture matrix + native-trust gate (from VCV-io#513); #814
  "enforce trust and exact import ownership"; #839 lean-native source policy; #797 keep axiom
  fixtures out of workspace imports. CompPoly got the same kernel sweep + baseline (#300, 09-01).
- Toolchain: Lean v4.33.1 (#791, 08-27). Eleven lint/perf PRs 08-31→09-01 (Dao).

### 1.5 The δ* fork and issue #444 [READ]
`lalalune/ArkLib`: 1 commit since 08-15 (a CI retry fix); issue #444 last updated 2026-08-03
(1,321 comments). deltastar.computer write-up dated June 2026, unchanged. The agent-swarm campaign
the frontier note flagged has gone quiet; its successor is better.codes (§6).

## 2. The "EF-funded effort's Binius leaves"

The sentence refers to ArkLib itself (`ProofSystem/Binius/`, per notes/binaryspartan-position.md
:1043–1060). Measured above: 33 → 32 code sorries; 72 → 54 tainted declarations; the only window
change in the directory is #791/#830-#835 lint+toolchain. FRI/BaseFold soundness: statements
exist (`fullOracleVerifier_rbrKnowledgeSoundness`, `queryOracleVerifier_rbrKnowledgeSoundness`,
…), every one tainted; `FRIBinius/General.lean` has completeness only. No separate Nethermind /
academic Binius formalization surfaced (kagi "Binius Lean 4 formalization formal verification"
→ 47 generic Lean results, none Binius; `gh search repos binius --language Lean` → ∅).
Binius64 itself (`binius-zk/binius64`): Rust only, as before.

## 3. StarkWare / Avigad S-two — no delta [READ]

`starkware-libs/formal-proofs`: `pushed_at=2026-06-04`, zero commits since 08-15 (`gh api
repos/…/commits?since=2026-08-15` → empty); local clone at `d0dd827` (06-04) is current. arXiv
2606.04311 has a single version (updated 2026-06-03). `gh api search/repositories?q=org:starkware-
libs+language:Lean` → only that repo. notes/avigad-stwo-verdict.md stands unchanged.

## 4. Mechanized indifferentiability / Fiat–Shamir elsewhere

**Indifferentiability — absence holds.** Nothing mechanized since EasyCrypt CCS'19 found in:
- scry `academic.catalog`, `hasAllTokens(lower(title||abstract),['indifferentiability'])`,
  `published_at ≥ 2025-01-01` → 7 rows (FrogBard-512, "Condense to Conduct", CSH-256, "The Sponge is
  Quantum Indifferentiable" ×2, double-block sponge attacks, one titled "Indifferentiability") —
  none mechanized; the same query ANDed with `mechanized|easycrypt|lean|isabelle|coq|rocq|crypthol|
  machine|formally|formalized|formalization` → **0 rows** (coverage extent built 2026-08-13…08-27).
- scry `openalex.works`, `hasAllTokens(search_text_lc,['indifferentiability'])`, year ≥ 2025 → 7
  rows (sponge hash family attacks 2026-03, offline-online, STH/EDM, Misty, PKE) — none mechanized.
- kagi "mechanized indifferentiability sponge proof Lean OR EasyCrypt OR Coq 2025 2026" → CCS'19
  (Almeida et al.), 2504.16887 (quantum, paper), ShannonProver (2607.02847, EasyCrypt automation —
  no indifferentiability result claimed in its abstract); kagi "Isabelle CryptHOL OR Rocq
  indifferentiability Merkle-Damgard sponge formal proof 2026" → AFP index pages only.
- `gh search code indifferentiab --language Lean` → 7 hits: PNT/Mellin-calculus files (unrelated
  "indifferentiable" wording), `katzenpost/CryptWalker` (a mention), and
  `trailofbits/constructive-cryptography` `AbstractCryptography/MR11.lean` — a Lean 4 Maurer–Renner
  constructive-cryptography library (pushed 2026-09-04) whose docstring lists "the ∗-relaxation and
  indifferentiability (`Algebra.Star`, CR18 Def 5.9 and MauRen16 Lemma 5)" as a *definition
  layer*; no sponge or hash-construction theorem. Worth one line in the README's related-work
  paragraph as a Lean indifferentiability *definition*; not a proof of any construction.
- eprint 2026 titles 1761–1861 (one fetch of the year listing, which serves only the last 100) +
  mirror first pages for 1719–1734: only 1732 "Indifferentiability of Public-Key Encryption:
  Theory Meets Practice" (paper proof). ⚠ Titles 1735–1760 not scanned (not yet in the mirror).

**Fiat–Shamir — two things to cite, neither an RBR→FS compiler:**
- **VCVio `CryptoFoundations/FiatShamir/`** (17 files, 10,021 lines; the `Sigma/` subtree 12 files,
  8,505 lines, **0 sorry**; the only FS sorry in VCVio is the flagged placeholder `FiatShamirWithAbort.euf_cma_bound`, `WithAbort/
  Security.lean:123`, self-described "placeholder statement, not the final theorem"). Headline:
  `FiatShamir.euf_cma_to_nma` (CMA→NMA via HVZK, loss `qS·ζ_zk + qS(qS+qH)·β`), `euf_nma_bound`
  (forking lemma + special soundness), `euf_cma_bound`. Landed #280/#290/#293 2026-04-16…18;
  window commits are perf/refactor only (#615, #614, #612, #548). Not in our notes before today.
  Scope: Σ-protocols/signatures in a managed ROM, **not** IOPs, not state restoration, not RBR.
  VCVio also has `CryptoFoundations/RoundByRound.lean` (authored "Aristotle (Harmonic), Elias
  Judin"): BGTZ Def 3.12 generalized-RBR-knowledge *event families* — "extensional … not the
  paper's full computational round-by-round knowledge claim" (its own docstring).
- **eprint 2026/1086** "A Machine-Checked EUF-CMA Proof for the Hybrid Fiat-Shamir Signature
  Scheme" — EasyCrypt, ROM, FS-FS hybrid signatures (Bindel–Hale); signature-level, corollary
  "confirms the result is non-vacuous". Mirror PDF read, p.1.
- scry `academic.catalog` `fiat`+`shamir` since 2025-06 with any of lean|easycrypt|mechanized|
  formally|isabelle|rocq|coq → **0 rows**; `openalex.works` same shape since 2025 → **0 rows**.
- Not mechanized but relevant to the README's honest-scope note: **eprint 2026/1838** (Fenzi,
  received 08-31, approved 09-01) "How to prove more false statements: Fiat–Shamir limitations on
  (generated) R1CS" — extends KRS'25 to protocols "whose instances are generated by running a
  program … an adversary controlling the program code can break soundness"; Spartan and Aurora
  variants fall in the class; mitigation: derive the first FS challenge from the generated
  statement, not the program. ⚑ Our EVM-decompilation rail emits *per-program* circuits — this is
  exactly "instances generated by running a program"; the EVM lane should check which challenge
  our FS transcript binds first. [INFERRED from abstract only; PDF not in mirror yet.]
- eprint 2026/1167 (Ganesh–Weiss, June): FS of multi-round IOPs in the standard model via CIH +
  "doom checkability" — paper, not mechanized; pre-window.

**Accumulation / depth — absence holds, one twin found.** kagi "machine-checked accumulation
scheme OR folding scheme soundness Lean 2026" → `LFDT-Nightstream/Nightstream/formal/superneo-lean`
(Lean 4 "cross-check" of SuperNeo/Neo: embeddings, Π_CCS/Π_RLC/Π_DEC, "Theorem 8 invertibility
(axioms + constructive Goldilocks)", "parent-authority Fiat-Shamir reroute lemma"); 38 commits
2026-02-25 → 2026-06-29, none in window; README calls it "the theorem-facing Lean implementation"
with a `#guard`-driven test suite — a twin by our classification, axiom-bearing by its own README (⚠ 09-05 re-measured in `nightstream-read.md`: 0 `axiom` on main except one leaf `goldilocks_prime`, **185 `native_decide`**, Goldilocks primality under the `Field` instance; the 09-04 tip deletes the paper twin and ships 9,105 R1CS-layout theorems).
Not previously in notes/neo-superneo-read.md. No depth-composition theorem anywhere else.
`gh search code "stateRestoration OR state-restoration" --language Lean` → ∅.

## 5. Verified-zkEVM / Lean Ethereum milestones

- **better.codes launched 2026-08-20** (blog.ethereum.org/2026/08/20/better-codes-challenge, EF
  Formal Verification team + Yukon + zkSecurity): "an open autoresearch challenge … formalized in
  Lean … The Lean kernel checks every submission and each promoted proof raises the bound toward the
  fixed 128-bit target." Details in §6. This is the EF's FV program's visible milestone in the window.
- Org activity (gh, pushed_at): ArkLib 09-04; CompPoly 09-04 (fast fields Goldilocks/M31/binary
  towers/Pasta, Rabin certificates re-checkable by kernel replay, own axiom sweep #300); VCVio 09-04
  (Merkle multi-extractability #586–#591 09-01, SLH-DSA full FIPS interfaces #611/#617/#626–628
  09-02, "make Measure the primary probability semantics" #548 08-28); PolyFun 09-03 (62 commits);
  `clean` 09-04 (24 commits; BLAKE3/SHA-256 proofs restored after v4.33.1 bump; zkSecurity's
  "Clean: From Verified Circuits to Verified zkVMs" post is 2026-06-05 — pre-window); `riscv-zkvm`
  (created 08-25, Sail RISC-V → Lean extraction, v0.3.1 08-28); **`leanerVM`** "Lean 4
  implementation and formalization of leanVM" — created 2026-09-03, 4 commits, `init` only.
- **Lean Ethereum**: `leanEthereum/leanVM` is Rust ("now uses binary fields by default" per the
  `leanVM-b` README, 09-03); the formal track is the day-old `Verified-zkEVM/leanerVM`. The
  hash-based-signature side has a formal artifact in VCVio's SLH-DSA/XMSS-shaped `TweakableHash`
  + `MerkleTree` work (dates above), not in the leanEthereum org. No Poseidon2/leanSig Lean proof
  found (kagi "leanVM Lean 4 formalization leanerVM …" → ArkLib showcase and 2605.30106 only).
- verified-zkevm.org: still the grants/bounties template ("likely running until the end of 2026").
- Hirai `zksecurity/simple-rbr-fri`: pushed 2026-04-01, no change. IoTeX `rs-proximity-gaps`:
  pushed 2026-05-20, no change. `Verified-zkEVM/ArkLibFri`: 404 (deleted or private).

## 6. Mechanized proximity gaps / correlated agreement — the real delta

**better.codes / `proximity-prize/proximity-prize`** (GitHub, Lean, created 2026-08-13, pins ArkLib
`e651978` = the 08-20 toy-problem commit, CompPoly `zksecurity/CompPoly@rabin-explicit-q`, VCVio
v4.32.2). [READ from README + `Benchmark/{TargetLower,TargetUpper,IRSProfile}.lean`]

- Profile **koalaIRS12**: `Field := KoalaBear.Ext6`, index `Fin (2^18)` on the size-2^18 KoalaBear
  NTT domain embedded coefficient-wise, `totalDimension 2^20`, `interleaving 8`, `baseDimension
  2^17`, `repetitions t = 128`; proved `alphabetRate = 1/2`, `minDist = 131073` (relative
  131073/262144). Interleaved RS of ABF26 Constructions 6.2/6.9.
- Lower track (`ProtocolClaim B P Q`): certify one radius δ = P/Q with `certifiedGammaError(δ) ≤
  2^-128` (ABF26 Lemma 6.10 MCA-plus-list term for the executable straight-line extractor) and
  score `(1-δ)^128 ≤ 2^-B/100`. Upper track (`ProtocolClaimUpper B i`): for every admissible δ ≥
  δ* = i/2^18, `winningSetDensity(δ) > 2^-128`, scored by `(1-δ*)^128`. Both kernel-checked;
  candidate axiom closure restricted to `propext`, `Classical.choice`, `Quot.sound`; independent
  verifier in a trusted Linux sandbox. README, verbatim: *"The score is the spot-check quantity
  induced by a certified threshold radius. It is not `-log2(WSS)` and is not a full-protocol
  security claim."* and TargetUpper: *"This threshold certificate does not construct an end-to-end
  attacking prover."*
- Leaderboard state 2026-09-04 (better.codes, fetched): **soundness lower bound 68.02 bits**
  (DaniiRix, Claude Opus, Sep 3), **attack upper bound 116.13 bits**; literature baselines 64.00 /
  116.49; launch baselines 53.00 / 128.00; "70 promoted submissions, 22 solvers"; models credited:
  Claude Opus, GPT-5.6 Sol, Claude Fable 5.1; recmo's +10.45-bit jump on Aug 21 took it from 53.13
  to 63.58. [DERIVED] at t=128: 53 bits ↔ δ=0.2495 (≈ UDR 1/4 at rate 1/2), 64 bits ↔ δ=0.2929
  (= Johnson 1−√½), **68.02 bits ↔ δ=0.3081 — 1.5 points beyond Johnson**, 116.13 bits ↔
  δ=0.4668 (vs. relative distance 0.5000). ⚠ I have not replayed any submission; the numbers are
  the leaderboard's, and the pinned statement is the extractor-certificate, not δ* itself.

**What this bears on.** README bullet "A two-sided, parameter-concrete security budget … A bound that
is merely 'explicit' can be vacuously loose; a two-sided bound cannot" — still true of ours, but
the frontier note's *"Nobody else has a number at all"* and any uniqueness reading of the README
bullet are gone: there is now a public, kernel-checked, two-sided interval at a production-shaped
RS profile, on the proximity leg only, advancing at ~0.01–0.3 bits per promoted proof. Our object
(composed FS+FRI+grinding error at deployed parameters, `≤2^-55` and `>2^-56`) remains unique in
kind; state it that way. Second bearing: README's *"seams to consume external CA results as they are
mechanized"* — ArkLib #763 `McaLowerWitness.ofUniqueDecodingRange` (admit-free, UDR) and
`GrandChallenges/UniqueDecoding.lean` are exactly the shape our `CorrelatedAgreement` seam was
written for; the composition move in notes/formalization-frontier.md ("take their proved
unique-decoding CA as realizer + discharge Hirai's h_mca") now has a cleaner source object.

## 7. What I could not verify

- Any better.codes submission (proof bodies are in the private/promoted challenge repo; I read only
  the pinned targets and the public leaderboard). The "beyond-Johnson at 68 bits" derivation is mine.
- ArkLib's total declaration count / sweep summary (needs a `lake build`; not run). Counts are the
  committed baseline file + source lexing.
- eprint 2026 titles 1735–1760 (not in the mirror yet; year listing serves only 1761–1861).
- Whether `Verified-zkEVM/ArkLibFri` was deleted or made private (404 either way).
- StarkWare internal work beyond the public repo.
- Nightstream `superneo-lean` axiom count (not cloned; its README says "axioms").

## 8. Absence claims: corpus + instrument

| claim | corpus | instrument | result |
|---|---|---|---|
| no new mechanized indifferentiability | arXiv (scry academic.catalog, built 08-13…08-27) | `hasAllTokens(['indifferentiability'])` ≥2025 → 7; ∧ proof-assistant tokens → 0 | ∅ |
| same | OpenAlex (scry openalex.works) | `hasAllTokens(search_text_lc,['indifferentiability'])` year≥2025 → 7, none mechanized | ∅ |
| same | Kagi web | 2 queries (§4) | CCS'19 + paper-only |
| same | GitHub public code | `gh search code indifferentiab --language Lean` → 7, all definitional/unrelated | ∅ |
| same | eprint 2026 | titles 1761–1861 + mirror p.1 of 1719–1734 | ∅ (1735–1760 unscanned) |
| no mechanized RBR/SR→FS compiler for IOPs | ArkLib HEAD `22dbd4e` | grep `theorem fiatShamir_*`/`BCS*`; baseline names | only `fiatShamir_completeness := sorry` |
| same | VCVio HEAD `ffd0ca1` | `grep -rli 'fiat.?shamir'`; read `FiatShamir/Sigma/Security.lean` | Σ-protocol EUF-CMA only |
| same | arXiv/OpenAlex/Kagi | `fiat`+`shamir` ∧ proof-assistant tokens (2 scry queries, 2 kagi) | 0 rows; EasyCrypt 2026/1086 (signatures) |
| same | GitHub | `gh search code "stateRestoration OR state-restoration" --language Lean` | ∅ |
| no mechanized BCS transform | ArkLib HEAD; VCVio HEAD | `BCS/Basic.lean` read; `grep -rli '\bBCS\b\|\bIOP\b' VCVio` | stub / ∅ (Merkle extractor only) |
| no mechanized accumulation-depth theorem | Kagi (1 query), GitHub (`gh api` Nightstream) | §4 | one axiom-bearing Lean twin (Nightstream), pre-window |
| StarkWare: no delta | GitHub, arXiv API | `commits?since=2026-08-15`; `export.arxiv.org/api/query?id_list=2606.04311` | ∅ / v1 only |
| Binius formalization outside ArkLib | Kagi (2 queries), GitHub (`gh api search/repositories?q=binius+language:Lean`) | §2 | ∅ |

Instruments used: 16 of 25 Kagi queries; 6 scry SQL calls (all returned; one 28 s); `gh api` on
~15 repos; 5 non-eprint fetches (blog.ethereum.org, deltastar.computer, better.codes, zkSecurity
×2); 2 eprint fetches (year listing once; 2026/1838 abstract once). Clones: `/Users/ember/src/
ArkLib-2026-09` (`22dbd4e`), `/Users/ember/src/VCV-io-2026-09` (`ffd0ca1`, depth 1).

## 9. Suggested edits (not made — this lane does not edit VERDICTS or the implementation trees)

- SLVG_THOUGHT.md §I and §IV-b table, forcodex/00-ORIENTATION.md:43, docs/SELVAGE.md:30: replace
  *"33 sorries in its Binius leaves and no soundness statement for its own FRI"* with *"32 sorries
  in its Binius leaves and admitted soundness statements for its FRI and Binius (`fri_soundness`,
  `fullOracleVerifier_rbrKnowledgeSoundness`, both `sorry`); composition and FS transfer are
  Phase-6 roadmap items in its own 2026-08-29 status doc."* ArkLib count 416 → 314 (2026-09-04).
- notes/formalization-frontier.md #5 and the README "two-sided budget" bullet: drop *"nobody else
  has a number"*; add better.codes as the external two-sided proximity-leg number, with its own
  scope disclaimer quoted.
- README "RBR→Fiat–Shamir compiler theorem … absent everywhere": scope to IOPs; cite VCVio's
  Σ-protocol FS EUF-CMA (`FiatShamir.euf_cma_bound`) and EasyCrypt 2026/1086 as the signature-level
  precedents.
- README "seams to consume external CA results": name ArkLib #763 / `GrandChallenges/
  UniqueDecoding.lean` as the current admit-free UDR source object.
- README related-work paragraph: add VCVio Merkle multi-extractability (09-01, sorry-free) as the
  extractor half ArkLib's BCS will consume; add trailofbits/constructive-cryptography as a Lean
  indifferentiability *definition* layer.
- EVM lane: read eprint 2026/1838 once the mirror has it (generated-instance FS attack class).
