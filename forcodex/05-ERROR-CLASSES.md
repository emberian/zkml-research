# The recurring failure shapes, with their instances

Written 2026-08-16 for codex. ⚑ **For a newcomer this is the most transferable
content in the directory.** These are not anecdotes — each recurred, most within
a single week, and **inheriting them is far cheaper than rediscovering them.**

Every instance cites its file and its finding. Where a class now has a **cheap
detection**, it is called out — and the mechanical ones are the only ones that
have stayed fixed.

Inferences of mine that the notes do not state are marked *[my inference]*.
Nothing here re-litigates a verdict.

---

## 1. ABSENCE CLAIMS THAT WERE WRONG

`notes/the-absence-problem.md` — *"Five refutations in one day: our absence
claims are the weak part of the method"* — and by the end of that day:
**"the count reached TEN."** `notes/window-review-2026-08-13.md` puts the day's
total at *"roughly **fifteen** of our own claims"*.

| claim | fate |
|---|---|
| "MoE router binding: zero papers in 7,090" | **REFUTED** — two papers in `~/paperbin`, pulled the same day |
| "carrier census / vacuity instruments are novel" | **REINVENTION** — mathlib linter 2020; model checking 2001–2003 |
| "the prime + family law is ours" | **FOLKLORE** — Riesel 1994, Table 5, row h=127 |
| "multilinear/GKR substrate absent everywhere" | **REFUTED** — six shipped systems, one on Ethereum mainnet |
| "proof-aware QAT in nobody's paper" | **REFUTED** — two more papers in `~/paperbin`, plus a shipped product |
| "first MX-format-for-proving measurement in any literature" | **REFUTED** — arXiv 2608.03867 Fig. 3 is the same statistic |
| "a public weight-and-architecture registry is an open position" | **REFUTED at four layers** — incl. one paper *already in our paperbin* |
| "nobody sequentially audits an LLM service" | **REFUTED** — MPI-SWS 2510.05181, e-value auditor, <70 outputs |
| "machine-checked sampling soundness would be a genuine first" | **NOT NOVEL** — folklore under six names, incl. inspection games (60 years) |
| "nobody has turned interior-vs-boundary into a discipline" | **REFUTED** — it is `virtual polynomial`, Thaler 2025/2041 |
| "Ligerito's column distance is inexpressible for us" | **REFUTED by exploratory formalization** — `relDistV_eq_relDist` by `rfl` |

`notes/what-remains.md` states the aggregate plainly: *"**Essentially every entry
in that ledger was refuted** … Not one of those survived as 'first.'"*

### The four mechanisms — canonical statement, `notes/the-absence-problem.md`

1. **Corpus blindness.** *"The eprint mirror is cryptology-only and incomplete.
   ML systems, math, formal methods, architecture, and ALL grey literature are
   invisible to it. (Named in PREFLIGHT; **it cost us three of the five.**)"*
   `swarm/PREFLIGHT.md` enumerates the blind spots and gives a second proof:
   **Powdr's logup*-for-Twist/Shout note — a genuine contradiction to a law we
   had recorded — was never posted to eprint at all.**
2. **Instrument blindness.** *"A first-2-page keyword cache cannot see a §4.3 or
   an appendix. **Both MoE refutations and both QAT refutations bury the content
   past page 2.**"* And the cutoff: the scratchpad full-text cache **stops at
   2026/777**, missing ~276 recent 2026 papers, while the mirror runs to **1053+**.
3. ⚑ **WE DO NOT GREP OUR OWN HOLDINGS.** *"Four of the refuting papers were in
   `~/paperbin`, correctly named, when the absence was declared. **This is the
   cheapest possible check and we skipped it every time.**"*
4. ⚑ **arXiv's API `all:` field searches METADATA ONLY, not full text.** *"A
   zero-hit arXiv query is therefore much weaker evidence than it reads as.
   Several of our absences rest on exactly that."* Discovered by the PL sweep
   lane naming it in its own instrument declaration
   (`notes/inspiration-sweep-pl.md`), not by being caught by it.

### ⚠ Three "in our own library" facts that are NOT the same fact

They get fused; keep them apart.

- **FOUR refuting papers were in `~/paperbin`, correctly named, on the day the
  absence was declared** — the two MoE refutations plus the two QAT refutations.
  (`notes/the-absence-problem.md`, mechanism 3)
- **ONE paper is in our library TWICE under two filenames** — and it is a
  *different* absence claim. `notes/boundary-statements.md` §1.1:
  > *"Worst case: **`sumcheck-is-all-you-need-thaler-survey-2025-2041.pdf` and
  > `thaler-sumcheck-survey-2025-2041.pdf` are the same paper, in our library,
  > twice** — the paper whose one-line thesis is our sentence … **We have the
  > library. We did not read it.**"*
- **And one of the MoE refutations is present under THREE filenames** — arXiv
  2606.05433 (`notes/moe-router-binding.md`).

The MoE retraction is the single most complete statement of mechanisms (b)+(c)
together:

> *"Two papers refute it, and **both were already sitting in `~/paperbin/`,
> pulled and correctly named, on the same day the absence was declared** …
> The sweep that reported the absence read first-2-page caches; both papers bury
> MoE in a §4.3 and an appendix A.5. **A keyword sweep over abstracts cannot see
> a contribution that lives in a subsection**, and 'verified absence, twice' was
> two runs of the same blind instrument, not two witnesses. This is a
> `documented ≠ detected` instance with the documents in our own hands."*

### Two subtler shapes than "we searched badly"

⚑ **A SWEEP'S ABSENCE RESULT IS EVIDENCE ABOUT THE SWEEP.** A sweep reported our
*"+286-bit margin at α=7"* as not found in any paper and supplied replacements.
**A correction saying our own notes were wrong by 40–80 bits was drafted AND
COMMITTED.** Reading `notes/poseidon2-audit-verdict.md` at source showed the
refutation was the error: **the number is our own derivation, at our own bar
(2^123.6) and our parameter set, and the note says so on its face** — the sweep
had searched for *a published literal that was never claimed*. The false
correction is still in history at `c68d228`, superseded by `de70388` — **fixed
forward, not rewritten.** (`notes/hash-landscape.md`)

⚑ **AN UNPUBLISHED PAPER IS ABSENT BY CONSTRUCTION.** Three independent
instruments failed to find BinarySpartan (`notes/binaryspartan-position.md`
§0.5: IACR full-text → ∅; a grep of all **810 papers numbered ≥ 242** in the
2026 mirror → ∅; `~/paperbin` 1,626 papers → ∅). **It exists — it is in the
eprint review queue.** `docs/BINARY-POSITION.md` makes it a standing rule:

> *"Absence from a published corpus is evidence about the corpus, never about
> reality, and a paper described as unpublished is not evidence at all."*

### ⚠ CHEAP DETECTION — a checklist, not a gate, plus one artifact worth building

`docs/VERDICTS.md` §6, the whole remedy:

> **No absence claim without**: grep `~/paperbin` first (full-text extracted for
> all **1,218** PDFs); the **corpus AND the instrument** named in the claim; at
> least one non-eprint corpus; and **an explicit flag if the evidence is
> metadata-only** (arXiv's `all:` field is).

⚑ **The one mechanical fix, named and not yet standing**: `pdftotext` over all
1,218 PDFs took **~2 minutes** and *"it is the single fix for four absence-claim
failures in a week"* — `notes/boundary-statements.md` §1.1 asks for it to be a
standing artifact rather than a per-lane rebuild. **Build it.**

⚠ **Live risk in the committed corpus**: `notes/speedup-ledger.md` Bin 2 still
states *"Binius×ML: zero papers in 7,090"* and *"'prove a 70B model on a 64 GB
box' exists in zero systems"*; `docs/AGENDA.md`'s unclaimed-claims ledger still
carries eight unstruck rows under a *"verified absent from the literature"*
header. **Those are unretracted, not verified.**

---

## 2. VACUITY, IN FIVE DISTINCT SHAPES

⚑ **The reason this class is dangerous is stated at source**: *"a vacuous
theorem is honestly proved"* — it builds green, passes `#print axioms`, and
**no axiom check will notice** (`notes/binaryspartan-position.md`).

### (a) A theorem over an UNINHABITED structure

`Selvage/Proximity.lean:190`'s `FoldingData F dom domSq` carries
`two_ne : (2 : F) ≠ 0` **as a structure field**, so the type is uninhabitable at
characteristic two:

> *"`FoldingData F dom domSq` is empty whenever `CharP F 2`, so **all 185
> declarations across 27 files that take a `FoldingData` or `FoldingTower` are
> vacuously true over a binary field** — on a green build, passing their
> `#print axioms` pins, with no diagnostic anywhere."*
> — `notes/char2-vacuity-census.md`, "Trap 1"

Named at declaration level in `notes/binaryspartan-position.md`: `proximity_sound`
(L689), `proximity_sound_prob` (L706), `proximity_complete` (L445),
`close_of_correlatedAgreement` (L1059), `fold_notMem_of_notMem` (L816),
*"and everything in the 11 downstream files."*

⚑ **The subtler sub-shape:** *"a theorem over `FoldingTower F ι m` with `m` free
is not fully vacuous at char 2 — it survives only at the degenerate `m = 0`."*

**Second instance, at a different carrier:** `merklePcs_empty_of_positive` proves
`¬Nonempty (MerklePcs ell)` for **every `0 < ell`**, so two Assurance modules
quantified over it were vacuous at every positive height — *"height zero is not a
rescue"*, and both are now **retracted with the refutation machine-checked
in-file** (`commonGameFamily_impossible`, `actualReductionFamily_impossible`).

⚑ **And a docstring that is true of the proof and false of the carrier:**
`foldDistanceTransition_halfThreshold` says *"No … characteristic assumption …
is used"* — **true of the proof, false of the carrier**, since it takes a
`FoldingData` (`notes/ingredient-inventory.md` §2.3).

**External specimens:** ArkLib's KZG evaluation-binding was vacuous
(`tSdhAssumption` is `Classical.choice`-false at every parameter); SP1
Hypercube's SLTI is *"vacuously true (contradictory hypotheses)"* and its JALR
proof *"hypothesized exactly the gap that was the bug."*

**The positive use of the same shape** — vacuity as a *tooth*:
`widened_relation_refuses_embedding` proves
`IsEmpty (VerifierEmbedding strictSystem widenedSystem)`, i.e. **the type refuses
a verifier gadget that accepts strictly more than the verifier it stands for.**

### (b) A bound over an EMPTY EVENT

⚑ **Self-caught, and only by construction order** — `notes/degree3-rung.md`:

> *"The soundness pipeline fires end to end (`cubic_cheat_caught` ≤ 3/7) on a
> **NONEMPTY** accept event — ⚠ the cheat had to be constructed BACKWARDS from a
> challenge that accepts it; **my first natural choice (constant message, false
> total 3) had NO accepting challenge over F₇, i.e. it would have been a true
> bound over an empty event.**"*

Other instances:
- **A bound that exceeds 1.** `composed_bound_is_vacuous_at_f7` proves
  `1 < 1/7 + 3/7 + 2/7 + 2/7 = 8/7` — at the toy parameters the composed bound is
  *"a true statement that constrains nothing."* And the note names it as a
  **distinct flavour**: *"a characteristic-free proof over a small field is a
  different flavour of vacuity from an uninhabitable hypothesis, and it is the
  flavour that will not be caught by a type-emptiness theorem."*
  (`notes/spartan-over-what-we-hold.md` §2.8, §5)
- **`q ≤ 0`.** *"A datacenter-local PRNG: G unbounded, q ≤ 0 — vacuous at any
  audit rate"* — `ε_beacon` swamps `p` (`notes/audit-theorem-statement.md`).
- **A product lower bound with an unbounded factor.** *"A SNARK verifier has
  unbounded space, so v is unbounded and the bound goes vacuous."*
  (`notes/boundary-statements.md` §2.7)
- **External specimen, the cleanest one**: Isabelle/STARK, 5,476 lemmas, 0
  `sorry`, *"and its headline soundness bound has never been exhibited below 1"*
  (`notes/formalization-frontier.md`).

**The discipline working** is worth copying: `sz_event_nonempty`,
`badZ_survives_at_one`, `rank1_wrong_accept_witness`,
`count_false_accept_witness` — *"the false-accept event is NONEMPTY"*, exhibited
rather than argued.

### (c) An `∃` that is TRIVIALLY SATISFIABLE

- ⚑ **Self-caught, and the note calls it exactly the sin.** *"Its first
  `RingSwitchSecure` was `∃ err : ℝ, err ≤ bound` — **trivially provable, i.e.
  exactly the sin.** Replaced with an assembly step constrained by a supplied
  accepting set (refutable by a wrong constant) plus a theorem that the
  antecedent is satisfiable."* (`docs/BINARY-POSITION.md`)
- **`fsKeystone_premise`** discharges *"an RBR-sound `Reduction` exists"* with
  `trivialReduction`/`trivialRbr`, where **`R = R' = True`, `verify ≡ some ((),0)`,
  `err ≡ 1`**. *The theorem is fine; the stated inhabitation evidence is
  degenerate.*
- **`SecurityEvidence.no_conflation`** — a structure with four fields of exactly
  the four `Prop`s it takes, and the "theorem" returns them. **Literally
  `P∧Q∧R∧S → P∧Q∧R∧S`.** *Disclosed in the file, so recorded not accused.*
- **`W = Unit`, extractor `fun _ _ _ => ()`** — so `RbrKnowledgeSoundness` at that
  leg is *"soundness with a trivial extractor, not extraction of the committed
  multilinear"* (`notes/basefold-rbr.md`).
- ⚑ **The identity-carrier form, pre-empted rather than found**: `bwd` must be
  refuted by a non-injective `encProof`, *"else `bwd` is `fun _ _ h => h`-shaped:
  the `minted-identity-carrier-vacuity` failure exactly."*
- ⚑ **And `Iff.rfl` refused entry to a theorem list, twice, deliberately** — *"a
  reader seeing it in the theorem list would credit the file with a check it does
  not perform"* (`notes/low-rank-updates.md`, `notes/rank1-gradient-check.md`).
- **A `Prop` that quietly reads as `True`** — `sparseEvalOracle_refutable` exists
  *"because a `Prop` that quietly reads as `True` is the standard way an
  obligation stops being one."*

### (d) ⚑ A MODEL TOO WEAK TO EXPRESS THE ATTACK IT RULES OUT

Minted at `notes/cross-limb-verdict.md`, and it is the sharpest shape here:

> *"**Every Lean BFV carrier in the tree makes the attack UNREPRESENTABLE** — and
> `Market/DarkBazaarSameOpeningPoly.lean:45` says so in its own residual list.
> **True of the model, and exactly why the model could not go red.**
>
> **A new vacuity shape: not a theorem about nothing, but a MODEL too weak to
> express the attack it is supposed to rule out. The check passes because the
> forgery cannot be written down.**"*

The mechanism, named at the file: `Market/PrivateBookBfvBindingAir.lean` binds
the limbs **in the type** (`witness.u : OrderIx → CoeffIx → Int`, one signed
vector pushed into every RNS row) — *"a faithful model of the intended layout and
an unfaithful model of the adversary, which is the whole reason this hole
survived in prose for months … **every instrument we had was constructed so that
it could not go red.**"*

Same shape elsewhere:
- **An idealized verifier.** *"A deployed verifier has no honest side. Left
  unstated, `spartan_outer_sound` would be a theorem about an idealized verifier
  — and that is precisely the shape of a vacuity that survives a green build and
  passes its axiom pins."*
- **Soundness as an opaque assumed `Prop`.** `PortalFloor.lean:71`'s
  `class VerifierKernel` makes soundness an assumed `extractable : Prop`, *"so it
  can never be derived"* from B proving A's verifier relation.
- ⚑ **A candidate fix that is a tautology.** The first-named repair for the
  cross-limb hole — *"a CRT-consistency relation over the limbs"* — **can never
  refuse, because the CRT map is a bijection and the exhibited forgery is itself
  CRT-consistent.**
- **And the instrument it costs you.** The narrow Poseidon2 arm *"has no tree
  spelling"* (one internal round multiplies a tree state ~16×, so thirteen is
  ~5·10^18 nodes), which means *"§6b's tree-vs-DAG agreement oracle has no narrow
  counterpart **by construction**. An instrument is lost, not just a cost saved."*
  (`docs/VERDICTS.md` §4)

### (e) ⚑ AN ANTI-VACUITY TOOTH THAT IS ITSELF VACUOUS

`breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean`:

> *"⚑ `EngineSound` / `real_engine_sound` — `abbrev RealProof := Unit`,
> `acceptAll : RealProof → Bool := fun _ => true`, every hash constant-zero. **The
> headline "EngineSound is INHABITED — the headline is not vacuous" is discharged
> at an instance where the verifier accepts everything.** That is a `P → P`
> witness with extra steps, and unlike the other two it is **not disclosed.**
> Flag it."* — `notes/leaf-vs-recursion.md` §8c

⚠ **Flagged, not fixed.** And its sibling `EngineSound.recursive_sound`
**assumes** in-circuit verifier soundness as a hypothesis.

### ⚠ CHEAP DETECTION — and it is the best gate in the repo

`scripts/check-char2-vacuity.sh` → `scripts/CharTwoVacuityCensus.lean` (in
`~/dev/minidregg`; this repo only records it). It walks the environment for
declarations mentioning a **char-2-refuted carrier** together with char-2
evidence, and **gates on the finding, not on a self-test.**

> ⚑ **"Proved red-capable twice, not assumed:**
> 1. Before the wall module got its structural exemption, the run reported **5
>    hits and exited 1**.
> 2. **Renaming the exempt module makes the run *fail*** — `wallModule names no
>    emptiness theorem` — rather than read clean. **Deleting
>    `Selvage/CharTwoWall.lean` cannot present as a green tree."**
> — `notes/char2-vacuity-census.md`

**Exemption is by home module, not a name list; allowlist empty by design.** The
registry (`charTwoDead`) holds two carriers and *"should grow whenever a new
char-2 wall is **proved** — never on a believed emptiness, since a registered
name with no evidence fails the self-test by design."*

⚠ **The declaration count is recorded at three different values across runs —
29,085 · 29,263 · 29,276 — all reporting 0 vacuous. Do not quote a count without
saying which run.**

⚠ **Stated blind spots**: *"any other empty regime; carriers not in its
registry"* — and separately, **the carrier census cannot see `private`
producers**: name mangling defeats its `ours` test, *"so it reports `FoldingData`
unwitnessed when `ReceiptClaim.data₄` builds one. A vacuity detector with a blind
spot for a whole visibility class."*

**The floor law that makes a tooth real** — each obligation must be
**SATISFIABLE, REFUTABLE, and NOT PROVABLE**. `HashFamily` discharges all three
(`collapsing_not_merkleObligation` axiom-free · `natChain_merkleObligation` a real
witness · `nodeCollision_of_finite_digest`, ⚑ *on a finite digest type a
compressing node map always collides, by pigeonhole* — so the obligation is a
cryptographic **assumption** and can never be upgraded to a theorem for any real
hash).

**And prior art bounds our confidence in all of it**: *"our completeness metric
was consistently lower when only considering **natural** bugs … **Synthetic teeth
overstate your teeth.** Our RED witnesses are hand-built mutations — they may be
systematically easier to catch than the failures that actually occur."*
(`notes/vacuity-prior-art.md`) ⚑ **Lean is why this is needed at all**:
*"Isabelle's locale interpretation and HOL's `typedef` impose a nonemptiness
obligation at definition time. **Lean does not.**"*

---

## 3. THE WRONG UNIT

The most common single error of the campaign. `docs/VERDICTS.md` §8 names the
signature: *"a plausible cost model, never converted into the unit that bills.
Counted multiplications instead of nanoseconds. Asymptotics instead of constants
at our sizes. **A ratio for a relation quoted as a ratio for a system.** A
distribution's tail read as a mean."*

### (a) Counted multiplications quoted as time — twice, on both dominant terms

- **The exchange rate.** *"78–308× is counted field multiplications; the
  conversion to wall-clock had never been taken."* Taken: **54.68 ns per marginal
  committed felt vs 10.97 ns per value per sumcheck layer ⇒ ~5× at lb=3.** *"The
  gap is ~8×, and it is the conversion"* — hashing SIMD-vectorizes harder than
  folding. **Every plan priced against 78–308× as a time budget needs
  re-pricing.** (`notes/poseidon2-virtualization.md` §4)
- ⚑ **The same error a second time, on the other dominant term.** *"1.33× is a
  counted-mult hash ratio whose wall-clock conversion **was** taken — by the field
  memo, to ~1.02× — and the counted number kept being carried anyway."* Native
  Poseidon2 throughput is bound by linear layers, Montgomery reductions and
  memory, **not** by the S-box multiply count, so halving S-box multiplies buys
  ~2%. (`notes/koalabear-migration.md`)
- ⚠ **And an agreement that was a coincidence, withdrawn**: *"'derived native
  ratio 1.69× vs the in-circuit measurement 1.82× — two instruments, 4% apart.'
  **Those are not two instruments on one object.** 1.69× is native multiplies per
  permutation; 1.82× is committed AIR columns per permutation (298 → 164). …
  **their agreeing to 4% is a coincidence, not a corroboration.**"*
- ⚑ **The inverse error, which manufactures a verdict.** A **packed** permutation
  against a **scalar** multiply gives `Y ≈ 245` instead of `898` — **a 3.7× error
  in the quantity the whole hash-bound verdict turns on.** The lane named the trap
  and measured both sides as packed-path lane rates.
  (`notes/field-op-counts.md` §4)

⚑ **And the correction of the correction, which is the real lesson.**
`docs/COST-MODEL.md`'s retraction: *"I then built a composition model on them
anyway — and worse, **used them to overturn an operation-count model** … **On a
box that contended, counted operations are the MORE reliable estimator, not the
less.**"* Getting a unit wrong is not automatically fixed by reaching for a clock.

### (b) A phase ratio quoted as a system ratio

- **"The prove-only part moves 6.92× but the system moves 3.61×"**, because grind
  does not shrink. **Grind alone caps any blowup-only speedup at 4×.**
- `notes/blowup-drop.md` states the rule at source: a ratio is bounded above by
  `1/grind_share`. *"Quoting `15.19×` where a reader will hear 'the prover gets
  15× faster' is the phase-ratio-as-system-ratio error, and quoting `3.50×` as
  'the blowup lever' undersells the lever by charging it for work the lever does
  not touch."*
- ⚑ **Order matters by 1.68×** — the grind fix is worth **1.15× alone** and
  **1.94× after the blowup drop**, because the drop takes grind's share from 15%
  to 56%.

### (c) ⚑ A batched throughput quoted beside a single-instance latency — **41×**

2 KiB + SHA-256 padding = 33 compressions. At 219,000 h/s that is **0.151 ms of
throughput-equivalent work against 6.2 ms of claimed latency.**

> *"Both figures can be true; **quoting them together as one system's
> characterization is the error.**"* — `docs/BINARY-POSITION.md`

⚑ **And we made the identical error ourselves.** Thaler's famous 0.18–0.33%
overhead is `1/B + 1/n`: **0.220% at B=512, 100.02% at B=1 — and autoregressive
decode IS B=1.** *"The most-cited number in sumcheck-for-ML does not apply to the
workload everyone wants to prove, and we have been quoting it."*
(`notes/prover-floor.md`)

⚑ **Third time, same shape, our own `fold_add`**: marginal accounting gives
`7(B−1)/5` → **715× at B=512**; total-system gives `(8B−7)/(B+5)` → **saturates
at 8×**. *"Neither is wrong; they answer different questions. **A claim of '690×'
must say which.**"* And the deployed batch is **B=4 ⇒ 4.2×**, plus the side
qualifier that was missing: **prover-side only** — the verifier moves the
opposite way (O(B) Merkle work against a polylogarithmic AIR verifier).

### (d) ⚑ A PERCENTAGE WITHOUT ITS DENOMINATOR

- **"Grind is 18% vs 23%"** — half a day of argument. The disclosure in
  `docs/COST-MODEL.md`: *"**My denominator is HASH WORK ONLY** … **A share of hash
  work is not a share of prove.** … The 23% vs 18% gap I cannot resolve from here
  and **do not average away.** … Whoever reconciles it should state the phase set
  on both sides."* Both sides recorded the discrepancy rather than splitting it.
  *[My inference: the numerator, not the phase set, is the gap — 18.1% =
  47,917 (one draw) / 265,031; 23.2% = 65,536 (the distribution MEAN) / 282,686.]*
- ⚑ **And the mechanism named**: *"This is the same disease as the 'grind is 18%
  vs 23%' argument that cost half a day: **two phase sets wearing one name.**"* —
  the `+36` between the two recorded "prover perms" conventions **is constant in
  `b`, so it never changes a ratio, only an absolute, which is exactly why it
  hides.** (`notes/hbox-rig.md`)
- **"The tower is ~75% in-circuit Poseidon2"** — the estimate every *"the tower is
  where this pays"* claim rested on. Measured **36.45% / 48.36% / 11.00%** on
  three denominators of the same table; apex **53.98%**. *"The closest any figure
  comes to 75 is the apex layer's main-only 65.77% — **the flattering half of a
  pair.**"* And substituting it into another lever's formula is *"a **category
  error**: the two percentages measure different objects that share the word
  'Poseidon2'."*
- **Three honest-looking denominators for one lever**: per-chip **2.3439× cells /
  1.9733× perms**, per-batch **1.0763×**, main-traces-only **1.1023×** — *"a third
  number, flattering, and reachable by an honest-looking choice of denominator."*
- **Same word, opposite verdicts.** *"What fraction of the in-circuit verifier is
  hashing?" = **36.45%, arithmetic-bound**; "is the wrap's own prover
  hash-bound?" = **yes, Y/X ≈ 3.1–3.3×**. "Same word, different denominators,
  opposite verdicts."* (`notes/leaf-vs-recursion.md` §3b)

### (e) Work composed with latency

**Two landed wins are LATENCY claims; the two carrying WORK claims are not cut
over.** Composed honestly: **work `1.0000×`, latency `1.4554×`, columns may not
be added.** Naive multiplication gives 38.8× — **a 26.6× overstatement.**

⚑ **And the trap inside one lever, stated by the lane against itself**: *"What
this lane bought is prover LATENCY on a multicore box, not prover work, and a
share-of-work percentage is exactly the wrong instrument to show it … **Stating a
latency win as a share-of-work reduction would be the compose-two-units error,
and it would be a fabrication.**"* ⚠ Plus the baseline trap it names: dividing
AFTER's work by BEFORE's work *at the same `T`* **would report a schedule change
as a work reduction of up to 6×. It is not.** (`notes/grind-fix.md`)

### (f) Four more unit flips worth carrying

- **Core-seconds quoted as wall-seconds.** *"719's 2.02 s is a **96-core wall
  clock** (~194 core-seconds); **the ~2,400× was not core-normalized.**"*
- **Bytes quoted as bits.** A LatticeFold ring element is 64 × 64 **bits** =
  512 B, not 4,096 B. **`128×` → `16×` — overstated 8×**, and the authors have
  since fixed it. *"Anyone quoting it is quoting a retracted typo."*
- **A subtracted floor printed as a ratio.** *"An early run printed **1541×**
  traffic-only for a case whose raw speedup was **1.83×** — the subtraction of a
  ~1.7 ms floor from a ~1.7 ms measurement, i.e. noise over noise."* Now printed
  only when both arms clear the floor by 2×. *"Quoting the flattering half of a
  pair is how a nothing result reads as a triumph."*
- **An overhead ratio whose unit is a baseline choice.** *"single-digit overhead
  for LLM proving"* relayed as established; derived **1.4–2.0× against a decode
  baseline and 123–241× against a prefill/throughput baseline** — and the vendor's
  own CEO says *"between 2x and, I don't know, 100x, really depending on the
  configuration."*
- **A width comparison inverting a cost comparison** (157 cols at blowup 8 =
  1,256 blowup-cells, *worse* than 298 cols at blowup 4 = 1,192), and **the
  ordering of two fixed primitives reversing with the arithmetization** (Blake3 >
  SHA-256 in a prime AIR; Blake3 < SHA-256 in BN254 R1CS).

### ⚠ CHEAP DETECTION — three of the six shapes are now structurally impossible

`circuit/tests/hbox_rig.rs` (`notes/hbox-rig.md` §1):

- **`Share` cannot render without its phase-set string** ⇒ (d) impossible.
- **`Claim::Work` / `Claim::Latency` are distinct variants; `compose()` returns
  `Err` on a mixed set** ⇒ (e) refused rather than computed.
- **`Counts` has no duration field; `Timing` has no count field** ⇒ (a) cannot be
  produced by the harness at all. ⚑ And the split is a *measurement fact*, not
  style: `CountingPerm`'s **217,114 atomics at b=6 land in exactly the phase being
  measured**, so *"a counting run's milliseconds are not 'slightly high', they are
  meaningless."*

> *"The four rules are now enforced BY CONSTRUCTION rather than by exhortation"*
> — because **a rule in a markdown file is a rule a lane forgets at 3am.**

For (b), (c) and (f) there is no gate, only the rule: **a proposed win must name
its PHASE and its UNIT**, since *"a phase whose milliseconds are 99% movement
cannot be improved by a win denominated in multiplications."*

---

## 4. INSTRUMENTS THAT STOPPED WORKING

### (a) A falsifier whose mutation became a no-op

> *"§E3 exists to show that grind is a random draw. Its first version re-proved
> **the same workload** three times and got `49,152` every time — reporting
> **`spread 1.00×`**, which reads as *'grind is stable and safe to difference'*,
> **the exact opposite of the finding it was written to deliver.** … This is the
> *falsifier that stopped falsifying* class, found in a cell written specifically
> to guard against a measurement error — **which is the argument for never
> trusting an instrument you have not seen fail.**"* — `notes/hbox-rig.md` §3

Real spread after the fix: **6.00×** (min 16,384 · max 98,304 · mean 51,883).

**Related shapes, all found:**
- ⚠ **A tooth that never tested what it was named for**: *"the six
  `InvalidPowWitness` rejections in `deployed_refines_verifier_teeth.rs` are all
  **transcript desyncs** — nothing ever mutated the witness."*
- ⚠ **A new check silently retargeting an old test**:
  `test_fri_verifier_rejects_zero_query_proof` *"would have been short-circuited
  by the new check and **gone on passing while testing something else**"*; and
  `test_fri_verifier_rejects_per_query_schedule_mismatch` likewise stops
  exercising what it names once a native check fires first.
- ⚠ **A red test hidden behind `#[ignore]`**: *"`apex_shrink_bn254_tooth` had been
  **RED since 2026-08-08**, `#[ignore]`d as `"SLOW"` — its sibling got a mint-split
  fix and the twin did not."*
- ⚑ **A round check made a TAUTOLOGY upstream**: at our pin the sumcheck round
  message is `[h(0), h(∞)]` and **`h(1)` is derived as `claimed_sum − h(0)`**, so
  `h(0)+h(1) = claimed_sum` holds by construction. *"The round check is not
  skipped, **it has been made a tautology** … The compression was chosen for
  prover speed and **deleted the check as a side effect.**"*
- ⚠ **A retained no-op that reads as a safety property** (a fixed-point gate value
  that rounds to 0), and **a gate that would pass on empty input** — `gates.sh`
  now exits 1 with *"no manifests found — the gate would pass vacuously."*

**⚠ CHEAP DETECTION, and it is now house style: build the mutation
CONSTRUCTIVELY and assert it happened before reading any verdict.**
`registry_tool.py`'s `cmd_tamper`: *"Every mode asserts that it actually changed
something — a mutation that silently becomes a no-op is how a tooth stops
biting"*, refusing with *"tamper mode {mode} produced an IDENTICAL manifest — the
falsifier is a no-op and would leave the gate green."* Same discipline in
`num-queries-pin.md` (`assert_ne!(len, before)` *before* any verdict),
`narrow-witness-gen.md` (157 columns bumped, each bump asserted), and
`low-rank-updates.md`.

### (b) A gate that froze an upstream bug as a law

> *"# The blowup drop — **fixing the bug we had frozen as a law**"*
> *"⚑⚑⚑ **The `log_blowup ≥ ⌈log₂(d−1)⌉` floor is gone. It was one
> `.bit_reverse_rows()` in a crate we already vendor, and our own gate had made
> it a law.**"* — `notes/blowup-drop.md`

The gate, verbatim before:

```rust
assert!(!chip_refusals.is_empty(),
    "no chip-bearing descriptor refused at (2,57). …");
```

> *"It was written to stop someone claiming `lb = 2` was free. It had become the
> thing stopping anyone from **discovering that it is** — and **it would have gone
> red the moment the bug was fixed.**"*

⚑ **The repair invokes the previous class**: the grid must contain at least one
chip-bearing descriptor *"(else the leg is vacuous — the falsifier-that-stopped-
falsifying class)"*, and none of them may refuse. **Three further inversions were
frozen alongside it**, including a docblock in `descriptor_ir2.rs` that had
written the bug up as *a property of the S-box*.

**The mirror image, same week**: a soundness parameter read off the proof rather
than pinned — `let num_queries = fri_proof_targets.query_proofs.len();`, so
*"every downstream check compared the proof against **itself**. Self-satisfying."*
A stale docstring even *"said the quiet part … and treated it as fine."*
⚑ **Red-capability measured by disarming the new pin: a one-query proof
verified.** *"The `Ok(())` in that panic is the finding, not just a failed
assertion."*

### (c) ⚑ A model fitted on a sample a bug had censored

> *"The two-regressor fit was calibrated on the descriptors that **could be
> measured at (2,57)** — which, while the bug stood, excluded **every chip-bearing
> one**. With the censoring removed it misses those rows by up to **99%** …
> **The class:** the bug did not only produce a wrong refusal. It **removed half
> the sample from a regression**, and the regression then reported a tidy `±63%`
> about a population it had never seen. **A gate that excludes the cases it cannot
> measure will report confidently about the ones it can.**"* — `notes/blowup-drop.md`

Refit error **76–99% → 0.0–4.3%**. ⚑ **The tell that the new term is structure and
not curve-fitting: adding it moved the other two coefficients by 0.01%**
(8.623 → 8.622, 43.613 → 43.617). ⚠ And one residual **named rather than
smoothed**: `presentation-freshness` at −63%, *"exactly where it was under the old
fit"* — so the `±63%` that constant always claimed was **a fact about that one
descriptor.**

`docs/VERDICTS.md` §7b states the general form: **"a bug that silently filters
your sample corrupts every model fitted downstream, and the model's own error
bars will look fine."**

### (d) Process-global counters, single-threading documented but never enforced

> *"The phase-totals map and both permutation counters are **one per process**, and
> **five** tests in that file bracket a `prove` with `reset_totals() … snapshot()`.
> … The file's header has prescribed `--test-threads=1` since it was written;
> **nothing enforced it**, so **the corruption arrived as a plausible number
> rather than as a failure** — latent in every number that file has ever printed
> from a default invocation."* — `notes/blowup-drop.md`

Magnitude: `q 19 → 57` read **+5 permutations run alone and thousands run with the
whole file.** Fixed with a file-scoped `serialize_measurement()` mutex rather than
by documenting harder — ⚑ *"**a gate whose verdict depends on how the harness was
invoked is not a gate.**"* **Verified the way that matters: all six tests pass
under default parallelism with a count table byte-identical to the serial run.**

⚠ A sibling lane still depends on the unenforced discipline:
`recursion_tower_profile.rs` needs `--test-threads=1` and says so.

⚠ **A neighbouring unit confusion the same assertions caught**: *"`TOTAL perms`
in that table is prove + SELF-VERIFY … Reading it as prover work attributes the
verifier's per-query Merkle paths to the prover — **which is exactly what the
first draft of this note said before the assertion caught it.**"*

### (e) The secondary instrument silently measuring a different machine

⛔ **hbox was running the SCALAR Poseidon2** — `packing width = 1.00` at every
blowup, because `<BabyBear as Field>::Packing` is selected by **target features,
not by the CPU that exists**, and NEON had been giving WIDTH=4 for free on the
laptop.

> *"**This is the nastiest shape a defect can have**: the counts are *unaffected*
> … while **every wall-clock number from such a build measures a different
> prover** — several times too slow on precisely the hash side, which is the
> numerator of `hash/arith`. **The primary instrument stays correct and the
> secondary one silently lies.**"*
> **Any hbox timing taken without `RUSTFLAGS="-C target-cpu=native"` should be
> discarded.**

### (f) Three more instruments that stopped measuring

- **A kernel sweep that hit a flat floor.** `§G5`: *"a **14,788-op** call measured
  3,773 µs and a **903,884-op** call measured 3,625 µs, i.e. **61× the work in
  less time.** … **The `ns/op` column §G5 prints is not evidence and is not used
  above.**"* Reported as not working rather than quietly dropped.
- ⚑ **A hardening commit that disarmed a cost model.** `90680ee7d` swapped
  `find_map_any` for `find_map_first` (correct — every byte-parity gate needs it)
  and **removed the grind's parallelism**: critical path 20,766 batches at 1
  thread and 20,766 at 12, **scale 1.00**, work up **5.9×**. A cost verdict in the
  tree still said *"there is no further thread multiplier to apply"* — written to
  stop double-counting, now making a reader count parallelism **that is no longer
  there.** *"A hardening commit that quietly disarmed a cost model."*
- ⚑ **A parallel primitive whose parallelism was conditional on scheduling luck.**
  rayon leaves `Range<u64>` unindexed, so the first windowed grind split only on
  steal and delivered **2.47×, not ~10×** — *"passes every correctness test, and
  it was caught only because derived and counted numbers were both printed."*

### ⚠ CHEAP DETECTION — prove red-capability, and prove it twice

The rig is the model. `self_check_is_red_capable` is *"a plain unit test — no
prover, runs in CI"* requiring the checker to reject a bent column, a
**single-permutation** drift at b=7, an affine-but-shifted column, **a 2-rung
input (a fit is not a check)**, a DFT slow-path event, and a work/latency mixed
compose. ⚑ **And it then fired for real on the first hbox run**, printing
`measured P = 3381·2^b + 766, pinned P = 3381·2^b + 730`.

> *"A gate nobody has seen fail is a gate nobody has tested."*

⚑ **The three ways it can go red are worth copying** — SHAPE (not affine at all),
PREDICTION (a fit on the two lowest rungs mispredicts a higher one), and **PIN (a
perfectly affine column with different constants — the prover still works, the
shape is intact, and the number has silently stopped being comparable to anything
recorded).**

And the design law from Binius64, after a gate that could not go red for weeks
(fix: **−15 lines**): *"The filler stops judging. It reads the transcript and
fills wires; the circuit decides."* Our analogue: **any emitter or witness
generator that validates its own output is a gate that cannot go red.**

---

## 5. IMPORT-GRAPH PATHOLOGIES

They share a mechanism: **the compiler's unit of checking is not the unit the
claim lives in.**

### (a) ⚑ An impossibility proof downstream of its subject cannot be cited by it

`Tower256MerkleBindingCardinality` **imports** the modules its cardinality
argument refutes, so those modules could not import their own retraction.

> **"When an impossibility proof lives downstream of its subject, the subject
> cannot cite it — and that is exactly how a refuted module stays in the build
> looking healthy."** — `notes/char2-vacuity-census.md`, "Trap 2"

The fix is **structural**: the argument moved into a new
`Assurance/Tower256MerkleCardinalityCore.lean` sitting **directly above**
`Compiler.Tower256AdditiveFriController`, so every module quantified over
`MerklePcs` can import its own retraction — now machine-checked in-file.
`docs/BINARY-POSITION.md` names it as a failure class in its own right.

⚠ **`scripts/CarrierCensus.lean:145-160` already knew, and "the modules still read
as results."** Documented ≠ detected, one import layer up.

### (b) An import boundary misleading an auditor about what is proved

Within `Theory/` the additive proximity gap genuinely **is** a hypothesis, because
the boundary forbids naming `Selvage` — so **4 files and 8 docstrings** labelled
it *"RESIDUAL HYPOTHESIS"* / *"NAMED, not proved"* while
**`additiveProximityGap_UD` proves it unconditionally one import layer up.**

> **"An auditor reading 'residual' as 'unproved anywhere' was being misled by an
> import edge."** — `docs/BINARY-POSITION.md`

⚑ **The repair kept the nuance instead of flattening it**: labels now read
*"hypothesis HERE; PROVED one import layer up"*, name the discharging theorem, and
state the genuine remainder.

**Same mechanism, benign direction**: `Selvage` cannot import the metatheory tree,
so `HashFamily` **restates** the finite-digest pigeonhole rather than citing the
two places it was already paid for.

### (c) A per-file green build cannot see a twin, BY CONSTRUCTION

A lane defined `matVec`; `Assurance/ZkmlLowRankUpdate.lean` had defined **the
identical object, character for character, in the same namespace**, since an
earlier pass. `lake build Assurance.SpartanR1CS` was **green** — the new file does
not import the old one, **so the two definitions never met.** Only the umbrella
said *"environment already contains `Minidregg.Assurance.matVec`."*

> **"A per-file green cannot see a twin, by construction, because a twin is
> precisely two definitions that never meet."**
> — `notes/spartan-over-what-we-hold.md` §2.7 (fixed in `b3fbde8`, 8,834 jobs)

⚠ **The compiler is the wrong instrument; text is the right one.** A name-blinded
SHA-1 over each declaration's full text measured **111 cross-module groups of
byte-identical declaration text.**

Same blindness from the other side: ArkLib's *"umbrella is greener than the
leaves"* — **33 `sorry`s across the Binius directory**, invisible from the top
file.

### (d) ⚑ An island does not close, it MOVES

`basefoldSumcheckRbr` had **zero consumers** — the ledger path ran through the
*operational* `basefoldIor_exact_sound` instead. *"A landed theorem nothing
consumes is the gating-defaults-to-silence class in Lean."* It was repaired with a
**same-file** consumer:

> **"The island did not close; it moved up one level."** `Selvage.BaseFoldRbr` is
> now a zero-consumption island module (**14 declarations, 0 consumed**).
> — `notes/ingredient-inventory.md` §4.3

**The rule, at source:**

> *"An island is closed by a consumer in a DIFFERENT module, on the path that
> actually reaches the top. **A consumer inside the same file relocates the
> island, and the relocation is invisible to the same instrument that found the
> original.** Same-file consumption is what a per-file build can see, which is
> precisely why it is the fix that suggests itself and precisely why it does not
> work."*

Scale: **17 modules with zero declarations consumed anywhere else**, including
**the whole additive/char-2 cone** — *"the char-2 lane is built and unwired."*

### (e) Reachability concluded from one lakefile stanza

`swarm/PREFLIGHT.md`'s own corrected entry: the claim *"`Bfv/Mul.lean` and
`Bfv/Smudging.lean` are in NO default build target"* was **wrong, and was quoted
by a later lane before anyone checked.**

> ⚑ **The class, worth more than the fact:** it was derived from *"the `Bfv`
> lean_lib has no globs"*, which is TRUE — and the wrong conclusion was drawn,
> because **a module can be rooted from a DIFFERENT library. Check reachability by
> grepping for importers across all targets, not by reading one lakefile
> stanza.**

### ⚠ CHEAP DETECTION

- **Build the umbrella, and use TEXT not the compiler.** *"Per-file green hides a
  red umbrella"* is standing lane instruction. Twins: name-blinded declaration
  hashing (`semtwins.py`). Islands: a token reverse-index over all 473 files.
- **A retraction must live UPSTREAM of what it retracts.** No automated check
  exists; the census found this one by walking declarations.
- **Grep for importers; do not read a lakefile.**

---

## 6. HANDOFF FAILURES

⚑ **From a transcript audit — the work was almost never the problem:**

> *"Every high-value loss in this project had the same mechanism: a lane produced
> the result and the **DELIVERY CHANNEL** failed — credits exhausted mid-write-up,
> `SendMessage` rejected as 'prompt too long', or a consolidation pass that kept
> the verdict and dropped the model. **The recording discipline is excellent; the
> handoff between a lane finishing and a note existing has none.**"*
> — `swarm/BRIEF-TEMPLATE.md` §9

### (a) Credits exhausted mid-write-up

- *"The predecessor design lane died on credits after writing three scripts and no
  prose. This file is the prose"* — and every number in it was produced by
  **re-running the scripts**, quoted not remembered (`notes/ring-hash-design.md`).
- **Both** verification lanes for the MoE absence re-check *"died on API usage
  credits without reporting"*, so the absence fell back to a `~/paperbin` grep —
  *narrower than the lanes would have been.*
- **Three lanes died on credits mid-work** in one window
  (`notes/archive/convergence-2026-08-13.md`), tracked in `swarm/OPEN-QUEUE.md` §F.
- And the silent variant: *"verdict: NOT ESTABLISHED (the lane that owned it never
  returned)."*

### (b) `SendMessage` too long

> *"A result computed by **three independent lanes** was lost to a `SendMessage`
> failure and never written down. This file is the handoff-rule remedy: **every
> number lands here as it is computed**, not at the end."*
> — `notes/koalabear-limb.md`

⚠ **No note records a threshold or byte count** — only the failure mode.

### (c) A consolidation that kept the verdict and dropped the model

`docs/COST-MODEL.md`'s own failure to populate is the costed instance: the notes
*"record **conclusions** … without the table the conclusion came from, without the
configuration each number was taken at, and without whether `pow` was on."* And
the sharpest single line, in its next-steps list:

> *"**Extract the profiler's actual per-phase table** into this file, with
> configurations. **It exists — it was in a lane's output and only the summary
> reached the notes.**"*

**The remedy that stuck** (`swarm/BRIEF-TEMPLATE.md` §9): write the note **FIRST
and incrementally** (*"a note that exists at 40% completeness beats a perfect
report that dies at 95%"*); **leave a pointer for every on-disk artifact**
(*"finished work with no pointer is deleted work"*); **never report a number only
in prose to the orchestrator — if it was computed, it goes in a file.**

### (d) The git hazards — all three, all fired

**`--only` is PATH-granular, not HUNK-granular.**
> *"The one-line `tracing-subscriber` dev-dep this harness needs was swept into a
> concurrent lane's commit `5a1b7e358` by `git commit --only`'s path granularity
> (it guards other *files*, not other *hunks* of a hot shared file)."*
> — `notes/phase-profile.md`

It fires both ways: `notes/ring-hash-tau-verdict.md` records sibling commits
absorbing *its* in-progress file; `notes/spartan-over-what-we-hold.md` records
`Assurance.lean`'s import line swept into `0dd9a48` **before the file it imported
was committed**, so HEAD briefly imported a file that did not exist in it. In
every case: **reported, not rewritten; fixed forward.** The workaround when a
sibling's hunk sits five lines from yours: stage a single extracted hunk with
`git apply --cached` (`notes/rank1-gradient-check.md`).

**⚑ `--only` gives NO protection against a later `--amend`.** `notes/degree3-rung.md`:

> The rung commit `6e934ec` was made correctly with `--only` over **9 named
> paths** in a tree where another lane had four `docs/LOOM-*` deletions STAGED —
> **2,176 insertions, 0 deletions, no foreign hunks.** Then a wrong number in the
> follow-up commit *message* was corrected with `git commit --amend -F msg`, which
> **took the INDEX and swept the other lane's four staged deletions, 732 lines,
> into a commit titled for something else.**

⚑ And the second lesson it draws is not about git at all: *"**the trigger was a
number I did arithmetic on instead of reading** … inventing a delta created the
need to amend, and **the amend is what did the damage.**"*

**⚑ `--only` LEAVES THE INDEX STALE** (`swarm/PREFLIGHT.md`, a *new route* to the
recorded mass-revert hazard):

> *"After committing with `--only`, the files still showed `MM` — **the index held
> pre-`rustfmt` versions, so a bare `git commit` by any lane would have reverted
> part of the work.** After an `--only` commit, **re-add your own paths.**"*

### ⚠ CHEAP DETECTION

- **Write the note first, incrementally.** The only remedy that addresses the
  actual mechanism.
- **`git status` immediately before committing; count deletions after.**
  `notes/low-rank-updates.md` shows the discipline working: two `--only` commits
  with the index re-added, **0 deletions in both** — *"meaning no foreign hunks
  were swept from a tree carrying three other lanes' uncommitted work"* — plus a
  re-check that caught three sibling files appearing and vanishing mid-build.
- **If you must amend, `--only` again on the same paths and verify the tree hash
  is unchanged** for a message-only fix.
- **Never `git add -A`. Never `git stash`** — it is not a swarm-safe operation.

---

## 7. RELAYING WITHOUT READING

### (a) ⚑ A Poseidon2 attack escalated on two premises, both wrong at source

`notes/poseidon2-audit-verdict.md`, in the author's own words:

> *"⚠ **two premises in my own escalation were wrong at the source** — I relayed a
> grey-lit summary of eprint 2026/306 without reading the paper, which is
> precisely the 'READ THE BLOCKER BEFORE YOU RELAY IT' failure."*

What the source actually said:

1. **The 2^106 figure is Poseidon2*b* — the BINARY-FIELD variant.** *"We deploy no
   binary-field Poseidon2."*
2. **The post-disclosure round increase was in Poseidon2b too.** *"There is no
   post-disclosure parameter set we are behind on."*
3. **The Plonky3 call-out is `(n,t) = (64,16)` — Goldilocks**, which we do not
   instantiate (verified: only `Poseidon2BabyBear<16>` ×30 and
   `Poseidon2Bn254<3>` ×26).
4. The paper's own bottom line, **omitted by the summary**: *"for all Poseidon
   instances we found no parameter set failed to meet its asserted 128-bit
   security level."*

⚑ **What survived is the part that was checked at source**: our external layer *is*
exactly `M_ε = P_{t/4} ⊗ M_4` (`p3-poseidon2/src/external.rs:135-159`) — so
**affected-but-below-threshold, not out of scope.** And the margin is robust
rather than merely large: reaching the bar needs `8·r_F + r_P > 59.0` and **the
maximum available in the paper's own model is 45** (the paper achieves 8).

⚠ **The escalation is preserved with an audit banner grafted on top** rather than
deleted (`notes/grey-lit-corrections.md` §1) — *a refuted claim with its
refutation attached is how we stop re-deriving it.* ⚠ And note the blast radius
that a relayed escalation nearly triggered: **7 hardcoded constant copies, 688
Lean files, 71 descriptors, a VK epoch, a re-genesis, and a fork of
`p3-poseidon2`.**

### (b) ⚑ A confession's LOCATION LIST needs the same grep as a claim

> *"A lane self-corrected with *'I cited this wrongly, including in file Y.'* That
> location list was **recalled, not grepped** — file Y had cited it correctly all
> along. I put the false accusation into a brief, and the next lane had to
> disprove it. **When a lane confesses, the WHERE is a claim too: grep it before
> propagating.**"* — `swarm/BRIEF-TEMPLATE.md` §7c

**De-anonymized: "file Y" is `notes/prover-floor.md`.** The confession itself
(`notes/virtualization-verdict.md` item 4) is correct and valuable — eprint
2026/1390 is a *lookup-specific, self-described restricted-model separation*, not
a general `Ω(m)` commitment floor; the floor we hold is the `Ω(|w|)` extraction
argument (GH98/GVW02). **Five of its six locations were grepped and are right.**
The one that was recalled was the false one, and the accused file's rebuttal now
sits in place:

> *"(`notes/virtualization-verdict.md` says this note mis-cites 1390; **it does
> not — the accusation is the one thing in that correction that is wrong at
> source.**)"* — `notes/prover-floor.md`

### (c) Two more relays in the same class

- **"net ≈65× worse per turn"** was relayed **twice** — into a note's own summary
  line *and* into a downstream lane brief — before anyone recomputed it. **65× is
  the ratio of the LOSS to the SAVING; the per-turn total is ×3.21** (independent
  grid ×2.96). *"My own brief for this lane carried the stronger sentence."*
- **"Single-digit overhead for LLM proving"** relayed as established, when the
  number is a **baseline choice** (§3(f)).

### ⚠ CHEAP DETECTION

- **`grep` the quote.** *"A quote you cannot re-find by grep does not exist. **(A
  lane fabricated one; the grep caught it.)**"* — `swarm/BRIEF-TEMPLATE.md` §8
- **Read the blocker at source before a brief's shape follows from it.** Labelling
  a relayed claim "unverified" is not a fix; a brief's whole structure inherits its
  premise.
- **A confession is a claim.** Grep its `where`, not only its `what`.

---

## 8. The one-line version

| class | the question that catches it |
|---|---|
| **absence** | *what corpus, what instrument — and did we grep our own holdings?* |
| **vacuity** | *is the premise inhabited, is the event nonempty, can the model even express the attack, and can the tooth go red?* |
| **wrong unit** | *what unit was this measured in, and does it bill in that unit?* |
| **dead instrument** | *have I ever seen this fail?* |
| **import graph** | *is the refutation upstream of its subject, and did the umbrella build?* |
| **handoff** | *does the note exist yet?* |
| **relaying** | *did I read the source — including the location list?* |

⚑ **And the through-line all seven share**, from `docs/VERDICTS.md` §8: *"every
estimate we carried without a measurement was wrong in the same direction —
**flattering the thing we had already decided to work on.**"*


---

## ADDENDUM (2026-08-16): the anti-vacuity class, closed and gated

The `real_engine_sound` vacuity is **fixed, not retracted** (`f42acad20`):
`RealProof` is now `inductive | honest | forged`, **`acceptAll` is deleted —
it had propagated into EIGHT files** — and `realVerify` refuses. Red-proofed
by two mutants: restoring the old degeneracy goes RED at all five new teeth
(**direct proof that none was provable at the old instance**), and a
forgery-stops-forging mutant goes RED at the mutation-happened assertion.

**Three refinements to the class definition, from verification at source:**
1. ⚑ **"A `P → P` witness" mis-located the defect.** The satisfying witness
   was *genuine*. The precise charge: **`EngineSound` could not be REFUTED
   from the verify side at any aggregate** — so exhibiting a satisfying
   instance established nothing. *The class test is refutability, not the
   witness's sincerity.* The theorem to cite is now
   `engineSound_is_a_real_boundary` (satisfiable ∧ refutable at one engine).
2. ⚑ **A free conclusion, printed on every build, unread**: baseline
   elaboration emitted `unnecessarySimpa` showing a light-client attestation
   hypothesis was **discarded** — `simp` alone closed the theorem. Same shape
   three more times. **The linter was reporting the vacuity all along.**
3. **Two negative results promoted from prose to theorems**
   (`zero_portal_chainBound_is_free` and twin): at the constant portal,
   `ChainBound` holds for *every* step list — so the ordering guarantee there
   was free.

**The gate**: `scripts/check-anti-vacuity-witness.py` (breadstuffs), wired
into `local-gates.sh`, gating on the finding against a ledger; both red arms
verified to exit 1 **without a pipe** — ⚑ *the lane's own first check reported
exit=0 because `head -5` was answering for the gate*, the exact PREFLIGHT
hazard, self-caught. **Baseline: 37 rows, labelled UNTRIAGED because they
are** — a detection surface, not absolution; each row is transmutable undone
work.

⚠ **Cross-repo citation hazard, new**: the brief cited
`check-char2-vacuity.sh` as precedent without naming its repo; it lives in
**minidregg** and the lane worked in **breadstuffs**, so the lane correctly
reported it "does not exist" and modelled on `check-guard-discipline.py`
instead. **A script citation without its repo is not a citation** — the two
trees now carry sibling gates with different mechanics.

⚠ **Perf note worth carrying**: multi-star line regexes over ~3k Lean files
(long lines) did not finish in 6+ minutes; line-based scanning: **3.8 s**.
