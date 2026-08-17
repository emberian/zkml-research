# The landscape — every direction explored, and its verdict

Reconstructed from the session transcripts, not from the notes corpus — so it
includes **the directions that were explored and closed before anything was
written down.** For each: what was asked, what came back, and where the
artifact is now.

---

## ⚠ TWO STRATA — read this before anything below

**Stratum 1 (2026-08-16)** is everything unmarked: the archaeology pass, written
from the transcripts, covering 08-10 → 08-16.

**Stratum 2 (2026-08-17)** is everything tagged **`[08-17]`**: the ~42 research
commits that landed *after* the archaeology pass. They are folded in **at the
pillar they belong to**, not appended, so this file reads as one landscape —
but the tag is there so you can always tell which pass a sentence came from.
Where stratum 2 **contradicts** stratum 1, the old text is kept and the
contradiction is stated **at the old entry**. Both strata are informative: the
first records what we believed, the second what measurement did to it.

⚠ **This file is still a snapshot.** The live documents are
`~/dev/zkml-research/SLVG_THOUGHT.md` (the shape) and `docs/VERDICTS.md` (the
facts). Read SLVG_THOUGHT first.

**Index of the `[08-17]` additions**, so the second stratum is findable as a
unit:

| where | what landed |
|---|---|
| §1.1 | ⚑ **the limb primes are greenfield** — 68/151 sieved candidates at 2-adicity 24, zero-emulation vFHE at overhead 1.00× |
| §1.3b | the Kagi sweep — CheapLunch / Perrin / Griffin at source; **Poseidon2's fourth independent confirmation** |
| §1.4b | the **aligned-hash space** charted — *the relation IS the attack surface* |
| §1.4c | **Weft** — proposed and killed exactly, in one day (⚠ Weft-2 is a live re-opening) |
| §1.4d | the **dual-mode ring object** — the absorb matrix was a commitment key all along |
| §1.5b | **ECFFT** — blocked by its own theorems (see `04-DEAD-ENDS.md` §E6) |
| §1.7b | the **Galois-lever sweep** and the batched reduced opening — the ×2.13 endpoint, reached by packing |
| §1.8b | **Lasso-over-LogUp** — the 3.2× lookup lever refuted at 1.96× |
| §1.9 | ⚑ **BinarySpartan read at source** — our own slide-era scrutiny partly refuted |
| §1.11 | **Nebula & Vega** at source, and the **PQ-Vega** path priced layer by layer |
| §1.12 | **PQ folding and committed memory** — `AccRbrFold`, `TwistContinuity` |
| §2.4b | the **Z_Q product-ring sumcheck** against cross-limb Hole A / Hole B |
| Pillar 7 | ⚑ **EVM decompilation into logic** — Futamura for circuits, Stage 0 landed |

---

## Scale, so you can calibrate

**369 top-level research/build lanes** across seven parent sessions,
2026-08-10 → 08-16, plus each lane's own sub-lanes (many report "all four lanes
are in", so the true count is materially higher — I did not enumerate the
second tier). Distribution:

| session | lanes | what it mostly was |
|---|---|---|
| `ca67a4c1` | 121 | the wide literature sweep — FHE, lattices, hardware, ring hashes, Attestable recon |
| `1b80977b` | 78 | PCS theorem extraction, zkVM reconnaissance, the build turn |
| `c352a91d` | 53 | grey literature, the prime paper, audit corpus, first implementation lanes |
| `5ba0dbe2` | 38 | binary fields, the BabyBear→KoalaBear census, the measurement fixes |
| `e68bba8f` | 38 | the hash decision, char-2 vacuity, the hbox rig, ingredient inventory |
| `3e64269c` | 33 | the zkML format pillar (this is where the campaign starts) |
| `b3c7abd2` | 8 | the current session — vacuity repair, sumcheck batching, this handoff |

⚠ **Sessions overlap heavily** because ember pruned context repeatedly and the
harness forked. The same lane can appear in several transcripts. The table
above counts each lane once, against the session that spawned it.

**`[08-17]`** The count above stops at the archaeology pass. **~42 further
research commits landed 08-16 21:30 → 08-17 02:50**, in a burst that is
structurally different from the first six days: it is almost entirely
*second-order* work — sweeps that price five pathways at once (Galois levers,
the mathematics sweep), papers read **at source** to settle claims we had made
from slides and abstracts (BinarySpartan, Nebula, Vega, CheapLunch, Perrin,
Lasso), and Lean artifacts that *close* obligations named earlier
(`AccRbrFold`, `TwistContinuity`, the ordered-basis binding). ⟨inference⟩ The
shape is what you get when a campaign stops generating hypotheses and starts
discharging them — which is also why the second stratum contains more
retractions per commit than the first.

---

# Pillar 1 — Proof system

## 1.1 Field choice

**Asked** (ember, 08-13 11:22): *"we're only using babybear because plonky3
already was"* — is that right?

**Explored**: BabyBear · KoalaBear · Goldilocks · Mersenne31 · the 127·2ⁿ+1
family · p61 = 2⁶¹−2⁵⁴+1 · binary towers · the BFV RNS limbs as a proof field.

**Found**:
- The prime family is **127·2ⁿ+1**; KoalaBear is n=24, p61 is n=54. Prime
  members {2,12,18,24,54,72,114}. The row is **Riesel 1994, Table 5, h=127** —
  i.e. the "family law" was already in a 1994 number-theory table. Maximal
  3-adic inertia iff n ≡ 0 or 2 (mod 6).
- **KoalaBear measured ≈1.05× on the leaf prover, not the 3.36× the case was
  built on.** All three factors failed, one of them by *inverting*. See
  `docs/VERDICTS.md` §1b — that section is the single densest thing in the repo.
- **Goldilocks**: the relayed "NoCap/Ceno/Neo choice" claim was "one-third
  right, one-third stale, one-third mislabeled." Its pre-crypto history is
  older than the ZK literature: **Mikko Tommila's `apfloat` 1.10, May 1996**,
  three years before Solinas.
- **SP1 moved BabyBear → KoalaBear** and never published a reason; the only
  rationale anywhere is one sentence in a crate README, and the substantive
  "why" is in a Plonky3 PR.
- Two-adicity is the axis that matters and it is **consumed by FRI, not by
  sumcheck** — which is why the field question and the "are we still an
  FRI system?" question are entangled.

⚑ **And a number that circulated and does not reproduce.** The KoalaBear-as-RNS-limb
result was recovered from a transcript as **"77 candidate towers"**. The
re-derivation found **479** in the honest search space — and, worse,
**33 different unstated companion-exponent windows hit exactly 77.**
`notes/koalabear-limb.md:69-84` says plainly: **"Do not quote 77 without the
window."** The substance survived; the number was an artifact of an unstated
parameter. ⟨inference⟩ This is the sharpest small instance of the campaign's
characteristic error — a figure that is *reproducible-looking* because many
wrong windows produce it.

**Artifacts**: `docs/VERDICTS.md` §1b · `notes/field-choice-verdict.md` ·
`notes/koalabear-limb.md`, `notes/koalabear-limb-verdict.md` ·
`notes/koalabear-migration.md` · `minidregg/Theory/CyclotomicInertia.lean` (the
family law, with a 67-digit counterexample) · the BabyBear→KoalaBear flag-day
census, split across four sweeps (450 files / 4,216 literals / **50
independent modulus declarations** in `breadstuffs/metatheory`; minidregg has
**1**).

### `[08-17]` ⚑ The field question has a third answer nobody had asked for: **the limb primes are ours**

The ECFFT lane (§1.5b) went looking for an exotic evaluation domain and came
back with a much duller and much larger result. Every prior framing treated the
**BFV RNS limb primes as given** — a fixed obstacle the prover had to emulate
around. They are not given. **Nothing is deployed; the limb primes are
greenfield, and choosing them differently deletes the emulation entirely.**

- Sieved: **68 candidate 36-bit primes and 151 candidate 37-bit primes with
  2-adicity 24.** Concrete triple `0xfed000001 / 0xfd9000001 / 0x1ff5000001`
  lands **log₂Q = 108.978 against the deployed 109.000** — same bit sizes, no
  FHE security change of consequence.
- With those, **classic FRI reaches trace height 2²¹ at blowup 8, over each
  limb's own prime, with ZERO emulation** — banking the measured **4.80×
  committed-element deletion at overhead 1.00×**.
- **Cost: a re-genesis flag day + an H1 re-measure + an `[UNRUN]` fhe.rs smoke
  test.** *The greenfield doctrine paying exactly as written — the answer to
  "what does it cost" is "a rebuild."*
- ⚠ **It re-opens §2.4's cross-limb provenance hole**, which row-interleaving
  had closed: limb-native proving means the limbs are no longer in one row. The
  Z_Q-sumcheck lane (§2.4b) is the candidate binding, and its verdict is mixed.

`docs/VERDICTS.md` §3b · `notes/ecfft.md`.

⚠ **This does not resolve the KoalaBear-vs-BabyBear disagreement below** — it
is orthogonal to it. It changes which *limb* primes we pick, not which *proof*
field we prove over.

⚠ **A live disagreement, and it is the sharpest one in this handoff.** A
decision memo published as a claude.ai artifact on 08-13 recommends
**"KoalaBear everywhere"** (v4, `d671d644-…`, see `07-ARTIFACTS.md`).
`docs/VERDICTS.md` §1b, written later the same day, says **"KoalaBear is NOT
recommended on this evidence."** VERDICTS is current truth and the memo is
history — but the memo's *reasoning* (two-adicity 27 vs 24 is a property FRI
consumes and sumcheck does not; `3 | p−1` forcing a degree-7 S-box) is not
refuted by VERDICTS, only outweighed. **If the system moves off FRI, the memo
becomes live again.** Do not treat it as dead.

## 1.2 The prime hunt, and the paper that grew out of it

**Asked** (ember, 08-13 14:50): *"if we do a lil bit of number theory work up
front on the representation we can achieve a boon that nobody had thought to
find? a rock nobody turned over?"*

**Explored**: an exhaustive scan of `2^a − 2^b + 1` for a ∈ [96,130]
(**exactly 117 primes, exactly 93 with 2-adicity ≥ 20** — reproduced
independently); prior use of p61 = 2287828610704211969; whether tabulating
NTT-friendly primes *by 2-adicity* is novel; whether the joint FHE-modulus /
proof-field optimization had been posed.

**Found — and this is a case study in the campaign's characteristic error**:
- **"Nobody has posed the joint optimization" — FALSIFIED.** HELIOPOLIS
  (2023/1949 §6.2) derives a genuine two-sided feasibility region. What is
  *actually* absent is the **search**, not the posing.
- **"p61 appears exactly once in the public record (a 2014 Lisp comment)" —
  FALSE.** It is in the published number-theory literature with four
  independent listings, including a textbook table. A narrowed claim ("no prior
  *deployed* use") survives.
- Tabulating NTT primes by 2-adicity is **known and old**, named and standard
  in three independent literatures. It is not a proof-system idea.
- Bloemen's published scan **omits k=2** (Φ₆(2²)=13) — a real, small correction
  we can make.

**Artifacts**: `paper/DRAFT.md` + `paper/CLAIM-LEDGER.md` (title recommendation
*"Choosing the Modulus Together"*) · `paper/scripts/` · the red-team pass that
forced two claims to change before submission.

⟨inference⟩ **The pattern to inherit**: every "nobody has done X" claim this
campaign made against the eprint cache was wrong at least once, and the
refutation was usually *already in `~/paperbin`*. See `05-ERROR-CLASSES.md`.

## 1.3 Hash choice

**Asked** (ember, 08-14 16:47): *"why **are** we using poseidon2, are we stuck
with it?"*

**Explored**: Poseidon2 · Poseidon2b (binary-field variant) · a hypothetical
Poseidon3 · Monolith-31 · RPO-M31 / XHash-M31 · Skyscraper · Rescue · Griffin ·
Anemoi · Reinforced Concrete · Tip5 · Arion · Keccak/SHA-256/BLAKE3 ·
Keccacheck · SWIFFTX · Chaghri/Vision (extension-field AO hashes) ·
a **ring-native** hash of our own design.

**Found**:
- **Poseidon2 stays — but now for a measured reason, not an inherited one.**
  In-circuit it wins 30.6×–210×; natively it loses 5.82×; the crossover from
  our own shares is 2.0–4.5× against a measured 30.6×.
- ⚑ **The reason we had it at all: Plonky3 handed it to us.** Nobody had
  written that down until the design stopped being treated as fixed.
- **Poseidon3 does not exist.** Both mirror mentions are name collisions.
- **Poseidon2b is real** (GKK+25, by the actual Poseidon designers) and its
  2^106 figure is about the *binary* variant — a fact that killed a
  round-skipping panic before it cost anything.
- **Monolith-31 does not exist for our field**, and where it does it is **21×
  more expensive in-circuit** than Poseidon2-KoalaBear at equal degree.
- The **invariant-subfield attack** is a named published class whose standard
  dismissal is explicitly conditioned on *"q is prime"* — a condition an
  extension-field design breaks. That closed the τ=4 extension-field S-box
  direction.
- Binary fields collapse the *proving* advantage of algebraic hashes but **not
  the verifier/recursion advantage** — proving converges, verification does not,
  and recursion cost *is* verifier cost.

**Artifacts**: `notes/hash-landscape.md` (1,036 lines) + `notes/hash-verdict.md` ·
`minidregg/Selvage/HashFamily.lean` · `notes/poseidon2-audit-verdict.md` ·
`notes/ring-hash-design.md` (1,077 lines), `notes/ring-hash-cryptanalysis.md`,
`notes/ring-hash-tau-verdict.md`, `notes/ring-hash-build-verdict.md`,
`notes/ring-hash-scripts/` · a decision memo as a claude.ai artifact
(`1167978c-…`, `07-ARTIFACTS.md`).

## 1.3b `[08-17]` The Kagi sweep — three papers we did not have, read at source

**Asked**: is the AO security record we priced against actually the current
record? (Three papers were pulled that no earlier sweep had.)

**Found**:
- ⚑ **"XHash8 is FreeLunch-UNMODELABLE" is superseded — and the replacement
  is STRONGER evidence.** **CheapLunch (eprint 2025/2040)** extends FreeLunch
  past CICO-1 to multiple outputs and **reaches XHash8**, proving
  `7³⁰ ≤ D_I ≤ 7^{24+6k}` for CICO-(12−k,k) — **validating XHash's own
  Conjecture 1** — and confirming round-skips apply. Its own conclusion:
  *"our results do not threaten the security of any full-round hash function."*
  > ⚑ **"Unmodelable" was an ABSENCE OF ANALYSIS wearing a security costume.**
  > *Modeled-by-the-strongest-current-framework-and-surviving-at-full-rounds*
  > is a strictly better epistemic position.
- **Perrin (eprint 2024/605)** is a dedicated XHash analysis we never had. It
  **generalizes FreeLunch itself** and concludes both variants safe, with the
  SAGE-validated bound **under-estimating** their security; the only padding
  vulnerability is *"plausibly applicable only in the multi-rate setting — for
  which the authors make no claim."* ⚑ Its methodological rule is ours now
  too: **base the argument on the ELIMINATION step, not on computing the
  Gröbner basis** — the latter is hard to estimate and *"sometimes literally
  non-existent."*
- ⚑ **A fourth independent confirmation of Poseidon2, this time from the
  attack side**: *"even with ω = 2, we found no attacks on full Poseidon with
  its security margin for realistic security levels (80 ≤ λ ≤ 256)"* — though
  the analysis does outperform the designers' at some 256-bit instances
  **without margin** (2^253.59). Griffin's full-round k=1 breaks confirmed at
  source (our recorded 2^51–64 stands).
- **Consequence for the post-Weft successor: *adopt, do not design* is
  STRENGTHENED.** XHash8 carries a dedicated analysis, a generalized-FreeLunch
  argument, a CheapLunch modeling that validates its own conjecture, and no
  full-round attack. **That is more cryptanalytic age than any candidate we
  could author**, and `Selvage/HashRelation.lean` is where it should land.
  > ⚠ **`[08-17, later the same night — `bc94ec6`]` The *adopt* half stands and
  > the *what to adopt* half changed.** XHash8 read at source **"has the
  > strongest record on our books and fits us in NONE of three ways."** The
  > successor recommendation is now **build nothing now; if the slot opens,
  > adopt Vision Mark-32** — see §1.4c. ⚑ **And the slot does not currently
  > exist**: the dissolve-check found that terminal binary proofs keep cSHAKE
  > and wrap-recursed ones take deployed Poseidon2 plus a packing codec, so the
  > only scenario needing a char-2 hash is **char-2-native recursion, and no
  > char-2 circuit prover exists in either tree.**
- **Collateral, from the norm-growth literature we were missing**:
  LatticeFold+ with ℓ2-norm checks says the **ℓ∞ range checks our budget uses
  are the dominant prover cost**, with a modular ℓ2 replacement. Our T = 2⁴⁷
  wall (§1.12) stands; **what this answers is the question we never asked —
  what *enforcing* the budget costs.** Now `06-OPEN.md` item 9.

**Artifacts**: `notes/hash-landscape.md` Addendum 4 · `~/paperbin` (both papers).

## 1.4 The ring-native arithmetization-friendly hash

⚑ **The campaign's most original construction, and it survived cryptanalysis.**

**Asked**: ember, twice — *"ring-native arithmetization friendly hash is
important"* (08-13 14:50) and *"also what's up with that ring hash we were
working on?"* (08-13 19:42, recovering it after it had gone silent).

**The idea**: `End_{Z_q}(R_q) ≅ R_q ⋊ Gal` — the ring's own automorphisms are
free constraint terms, and eprint 2026/1127's own Definition 9 already carries
σ₅ and σ₋₁ as native terms, used only for constant checks. Those two generate
the full slot-permutation group of their own ring. So the paper's §D open
problem is **substantially an arithmetization gap, not a design gap.**

**Cryptanalysis verdict**: *"the direction SURVIVES — no feasible break found
on the reference instance"*, against three controls at τ=1 and τ=2.
**τ=2 leads**: the challenge space kills τ=1, integral cryptanalysis punishes
τ=4. `docs/VERDICTS.md` §7.4 lists it as open with **one named experiment that
settles it.**

**The competing option was priced and lost**: the "delegation escape" —
delegate the hash rather than build a ring-native one — measured against
σ-Poseidon at **302,141 R_q constraints** and gadget-Feistel at **92,257**,
versus **2,417,127** today. See `04-DEAD-ENDS.md`.

**Artifacts**: `notes/ring-hash-design.md`, `notes/ring-hash-scripts/`, and
⚑ **`~/src/ring-ro-hash/design_*.py`, which is NOT a git repository** —
see `07-ARTIFACTS.md`. **`[08-17]` ⚠ That last clause is now FALSE and the fix
is the good news: `~/src/ring-ro-hash` was `git init`'d on 08-16 and the
tooling is versioned.** See `07-ARTIFACTS.md` O1.

## 1.4b `[08-17]` The aligned-hash space, charted — *the relation IS the attack surface*

**Asked**: the standing pitch was **"design for a cheap verification
*relation*, not a cheap *function*"** — is that a real design axis, and what
does the attack literature say about it?

**Found — it survives as ECONOMICS and splits as CRYPTOGRAPHY**, and the
attack papers say the second half in their own words:

- ⚑ **FreeLunch Remark 1, at source**: the Griffin attack's polynomial
  modelling *"was proposed by the authors of this algorithm for their initial
  security analysis"* — **the attackers used the designers' own verification
  relation and changed only the monomial order.** A cheap relation is not a
  free lunch; it is *the model you hand the attacker*.
- The whole sub-Poseidon prime-field band (`R ≈ 0.3–0.6×`) is **broken or
  unanalyzed**: Griffin 2^51–64 · Anemoi ℓ=1 2^70 · Rescue-Prime α=3 2^112
  (α=5 *exactly* 2^128) · Vision **zero papers**.
- > **The sharpened target: a relation cheap in the PROOF SYSTEM'S operations
  > and expensive in the ADVERSARY'S algebra.** Lookups and dense linear
  > layers qualify; **witnessed low-degree relations do not.**
- ⚑ **`x⁻¹` is simultaneously extremal** — F₂-degree n−1 (most
  Frobenius-opaque) *and* relation degree 2–3 (cheapest) — **and it is the one
  shape FreeLunch's authors say they cannot directly model** (XHash8 survives
  at 2^214). So "spend Frobenius in the linear layer, keep the nonlinearity
  opaque" has an **affirmative existing witness**, which is what made Weft
  (§1.4c) worth trying at all.
- ⚠ **Correction to the record**: **Anemoi's checked relation is degree α, not
  2** (Eq. 5 at source). The family's only degree-2 verification is Vision's
  inverse S-box.
- ⚑ **The char-2 question is answered by the record's own repair**: the
  Chaghri fix **densified** the linearized mixing layer (one Frobenius term
  broke it, three fixed it, the designers adopted it).

**Artifacts**: `notes/aligned-hash-space.md` · `minidregg/Selvage/HashRelation.lean`
(`c2dd38c`, green, axiom-pinned teeth: `GraphSound` as a named-not-carried
obligation, `slack_not_graphSound` refuting the free lunch, the
degree-3-relation/degree-7-function asymmetry machine-checked, the deployed
BabyBear instance graph-sound `by ring`). ⚑ **That build's first axiom pin
caught a `decide` degraded to a `sorry`** — the tripwire class firing in the
wild again (`05-ERROR-CLASSES.md`).

## 1.4c `[08-17]` Weft — proposed and killed exactly, inside one day

**The proposal** (from §1.4b): a hash whose **mixing layer is the already-proved
`novelPack` / additive-NTT transform** and whose S-box is lane-wise `x⁻¹` — the
"one proved linear object" prize, priced against the measured 64.9%
leaf-sponge share. Additive-BaseFold rung only; never a deployment proposal.

**The kill, and it is exact rather than approximate** — `branch(M) = branch(M⁻¹)`
duality lets four exact passes exhaust every codeword with min-side ≤ 2, so the
answer **self-certifies**:

> **branch(Weft, t=24) = 6**, against **MDS 25** and against **Poseidon2's own
> layer at 8 (exact, t=16) / ≤10 (t=24)**.

⚑ **And the structural epitaph is worth more than the number**: the mixing
matrix is **block-triangular along a subspace flag** — lanes ≥ 2ᵇ map into
themselves for b = 1..4 — and the 0-fixing lane-wise `x⁻¹` S-box **preserves
them**. That is a **4-deep chain of round-invariant lane subspaces, the
2026/306 subspace-trail shape BY CONSTRUCTION**, and *branch number does not
see it*.

> ***The alignment thesis imports the code's triangularity, and triangularity
> is the opposite of diffusion.***

The Chaghri caveat resolves the other way — the mixing spends **zero** Frobenius
terms, so this is the **Starkad/HADES structured-layer death**, not Chaghri's.
Basis-independent (three random domain bases identical); random-matrix control
reads 25.

⚠⚑ **Record this as KILLED-AS-SPECIFIED, not as a closed question.** **Weft-2
is a live re-opening** (`06-OPEN.md` §5, `08-ATTACK-BRIEFS.md` BRIEF 2):
`novelPack` in **internal rounds only**, dense in external (Poseidon2's own
architecture), plus a **free lane rotation** — because the flag subspaces are
contiguous *suffixes* and a rotation maps a suffix to a wrapped set. **We
verified the rotation kills THAT flag; killing one flag is not the absence of
flags**, and the structure is tower-triangular by construction, so a second
flag is the expected finding. Also open: branch 6 + `x⁻¹` clears 128 bits in
two rounds by our differential accounting — **and we never did the
linear/correlation side.**

⚑ **The reusable gate**: `swarm/BRIEF-TEMPLATE.md` gained a **branch-number-first
design gate**, paid for by exactly this lane — *compute the branch number of any
proposed linear layer before pricing anything about it.*

### ⚑⚑ `[08-17, later the same night — `bc94ec6`]` The alignment thesis is REDEEMED, and Weft died one decision from the theorem

**This is the update that changes what the kill MEANS**, and it arrived hours
after the kill:

> **Found in Vision Mark-32: the killed transform, interpolated on its window
> and evaluated on a DISJOINT point set, is systematic Reed–Solomon — and
> therefore MDS BY THEOREM. Branch 25. Flag destroyed. Same proved butterflies.
> Basis-free.**
>
> ***The structure was never the problem; the POINT SET was.***

So the epitaph above — *"the alignment thesis imports the code's
triangularity"* — is true of **Weft-1's point set** and **not of the alignment
thesis.** Weft died **one point-set decision away from the theorem-carrying
form** it was reaching for, and a sibling lane converged on the same axis
independently.

⚑ **A method law came out of the same pass, and it is a floor/identity
distinction worth carrying**: **the branch passes are a FLOOR instrument, not
an IDENTITY instrument** — a published matrix typo was caught by re-derivation
only because the typo'd matrix **floors identically**. *A branch number
agreeing is not evidence that you have the right matrix.*

**Recommendation as it now stands**: **build nothing now**; if the char-2 hash
slot opens, **adopt Vision Mark-32 — whose MDS is our transform's systematic
form and whose geometry is Weft's.** (And per §1.3b, the slot does not
currently exist.)

**Artifacts**: `notes/hash-landscape.md` Addendum 3 · `notes/k16-proof-and-weft.md`
· `notes/weft2.md` (sibling lane, live) · `~/src/ring-ro-hash/weft_branch.py`
(`737ea7b`) — ⚠ **and the successor branch scripts are the untracked ones,
`07-ARTIFACTS.md` O1.**

## 1.4d `[08-17]` The dual-mode ring object — the absorb matrix was a commitment key all along

**Asked**: `04-DEAD-ENDS.md` §E9 / §1.7b says the ×2.13 lever dies because **a Merkle
leaf supports no evaluation opening.** So: is there an evaluation-binding
commitment that is neither a curve nor hash-based? And can it be *the same
artifact* as the ring hash?

**Found — yes, and the parameter set was found in the same session:**

> ⚑ **One primitive, two modes.** The **linear mode** is the `P = 0`, round-0
> projection of the gadget-Feistel — an **Ajtai/MSIS gadget commitment
> `C = A·G⁻¹(v + a₀)`** — with the de-linearizer strictly *after* the read-out,
> so **linear-mode openings never cross it.** The **full mode** is the FS hash.
> *The hash's own absorb matrix is the commitment key.*

**Parameters**, found by search this session: **q = 2⁶⁴ − 257** (γ = 257,
`ord₃₂ = 2` so **τ = 2**, α = 7 legal since `q ≡ 4 mod 7`), `R_q = Z_q[X]/(X¹⁶+1)`,
**d = 16, B = 2¹⁶, K = 4 planes, κ ≈ 24**, challenge space `q² = 2¹²⁸`.

**Verdict, and it splits by world** — both halves earned:

- ⚑ **The wrap transplant is DEAD, twice over, and by arithmetic not taste.**
  Priced against the deployed wrap's Horner chains (216,330 ext4 MACs ≈ 2.16×10⁶
  BabyBear-mult-equivalents) the lattice shape lands at **×0.7–×13 — parity at
  the most favourable representation, an order worse at the deployed-style
  one** — *and the comparison is already unfair in the lattice side's favour*
  (it prices no witness generation and no substrate migration; the
  `PROVEN-IN-LEAN ≠ ROUTABLE` grep test fails maximally here). ⚑ **And the
  goalposts moved underneath it**: §1.7b's packing result means any wrap-side
  case for a lattice PCS must now beat the **residual**, not the original — and
  it does not beat even the original.
- ✅ **The R_q-native artifact is coherent and cheap at the margin**: opening
  verify **1.5–3.0×10⁴ R_q rows ≈ 16–33% of the gadget-Feistel FS bill (92,396
  rows), ≈ 4–8% of the σ-Poseidon τ=2 bill (363,513)** `[DERIVED — structural
  round-shape counts; no implementation exists]`. ⚑ **The opening verify is
  ~95% transcript hashing**, so the hash choice moves it by ×3.8.

⚠ **Said plainly, against inflation**: *"the modes do not share one
assumption."* Linear-mode binding is **provable (MSIS)**; full-mode RO-likeness
stays **the ideal-permutation heuristic it always was.** What they share is
arithmetic, parameters, a cost table, and a one-way implication.

⚠ **Correction carried from the brief, in place**: the σ-Poseidon bar figure
**302,141 is the τ=4 point.** At the standing **τ=2** verdict the same table
gives **363,513**. (`04-DEAD-ENDS.md` §D3's table quotes the τ=4 row.)

**The residual that is a wall, not undone work**: **O2 — sponge
indifferentiability of π is stated, not proved**, and *"it predates the
question."* Everything else on the eight-item obligation list is transmutable;
the un-run **lattice-estimator run for κ** (κ=24 is a root-Hermite *sketch*)
matters because the field's "128-bit" labels have re-derived to ~98-bit
core-SVP before.

**Artifacts**: `notes/ring-hash-dual-mode.md` · `notes/ring-hash-tau-verdict.md`
· `notes/ring-hash-scripts/dual_mode_costs.py`, `dual_mode_modsearch.py` ·
`08-ATTACK-BRIEFS.md` BRIEF 3.

## 1.5 Polynomial commitment schemes

**Asked**: what can we actually build on, and what is provable about it?

**Read at theorem level** (each lane extracted exact statements, page-pinned):
BaseFold family · WHIR · STIR · DeepFold · UltraFold · SwitchFold · Ligerito ·
Jagged PCS · Zinc / Zinc+ / Relaxed Mod-PCS · Galois-ring BaseFold ·
tensor-code / linear-code multilinear PCS · the whole Ligero/Brakedown descent ·
a SoK on hash-based PCS (Skatharoudis, 2026).

**Found**:
- ⚑ **The brief's premise was wrong in a way that shrank the job.**
  `openAt : … → (Fin m → F) → Op` is the **KZG/homomorphic** shape. **No
  hash-based multilinear PCS has it** — the commitment is a Merkle vector
  commitment to a codeword, which is our existing `OpeningScheme`, unchanged.
  That prediction was made and then held.
- **Jagged PCS has no cryptographic content** — which is precisely why it is
  tractable. A convenience layer on top of a PCS that does the security work.
- **Ligerito**: exploratory formalization found the errata are **display-only**;
  the *general-code* bound sits where our proximity gap is proved
  unconditionally, while the *headline RS* bound is the expensive one — so the
  sequencing inverts from what a dismissal would have assumed.

**Artifacts**: `notes/multilinear-pcs-landscape.md` (1,692 lines) +
`notes/multilinear-pcs-verdict.md` · `notes/ligerito-exploration.md` ·
`minidregg/Selvage/LigeritoInterleaved.lean` · `docs/SELVAGE.md` §4.2, §5.2
(corrected in place).

## 1.5b `[08-17]` ECFFT and exotic evaluation domains — and the question it answered instead

**Asked** (two questions, and the second one is ember's): would ECFFT / EC-FRI
unlock **limb-native** proving over the 36/37-bit BFV limb primes, whose
2-adicity was believed too low for classic FRI? And **is ECFFT
post-quantum**, or does the elliptic curve cost us the PQ story?

**The PQ answer is clean and was the easy half**: ⚑ **PQ-NEUTRAL, confirmed at
source.** eprint 2022/1542 Remark 2: Kilian–Micali/BCS compilation is
*"secure in the quantum random oracle model, and these generic transformations
apply to all our results."* Nothing is committed in the curve group; soundness
is information-theoretic on BCIKS proximity gaps; `Find_Curve`'s output is
**advice depending only on `|F|` and `T`, deterministically checkable**, so
there is no weak curve to plant. *"Not one assumption more, not one fewer."*
**No hedge was needed.**

**The useful answer is a dead end, and it is the good kind** — see
`04-DEAD-ENDS.md` §E6 for the theorems. In one line: **it dies on REACH, not on
price.** Constants would have been affordable (~4–6× on the LDE, ≈nil on a
hash-bound prover); the *theorems* cap the trace height below what we need.

⚑ **And the lane's real output is §1.1's**: it went looking for an exotic tool
and found that the constraint it was routing around **is one we chose.**
> ***ECFFT is the tool for fields imposed from outside (secp256k1, P-256). Our
> limb fields are not imposed.***

⚠ **Two of my own premises were wrong and are corrected at source**: the fold
set is **degree 4096, not 8192**, and the measured limb 2-adicities are
**13/14/17**, not "≥14."

**If EC-FRI is ever wanted**: it reduces to plain RS over exotic domains, our
cone is ready **at the definition level** (`FoldingData`'s `dom : ι ↪ F` is
already domain-agnostic; **0 `IsPrimitiveRoot` tree-wide**, re-confirmed), and
the fold needs **6 named missing lemmas — only one with real algebraic-geometry
content** (Hasse + Vélu + 2-descent), *"and that one exists in no proof
assistant I know of."*

**Artifacts**: `notes/ecfft.md` · `docs/VERDICTS.md` §3b. No Lean was written —
this lane read the cone rather than extending it.

## 1.6 Soundness accounting

**Explored**: the three regimes (unique-decoding / Johnson / capacity), the
withdrawal of the capacity regime, grinding, `num_queries`, `max_log_arity`,
extension degree, proximity gaps, correlated agreement, sponge
indifferentiability, Fiat–Shamir in the ROM.

**Found** — the parts that are not obvious from `VERDICTS.md`:
- **"Conjectured 130" is capacity-shaped — the regime `ethereum/soundcalc`
  deleted in Nov 2025.** 57 of the 130-vs-73 headroom is a *withdrawal*, not a
  knob. **Never quote 130.**
- ⚑ **A real soundness hole was found and pinned**: `num_queries` was read off
  the inner proof and never checked. The falsifier proved it: with the pin
  disarmed, **a one-query proof verified.** 16 → 34 bits at UDR.
  ⚠ **The pin does not reach breadstuffs yet** — `breadstuffs/Cargo.toml:370-373`
  pins an older rev; it needs a push (outward-facing, so left for ember).
- ⚑ **A second hole found by the same mechanism and deliberately left open and
  unquantified**: `max_log_arity` is unpinned; the partition is attacker-chosen
  and `log_arity = 0` is unrejected.
- ⚑ **Our own hardening commit un-parallelised the grind.** `find_map_any` →
  `find_map_first` was correct for determinism and destroyed the parallel
  scaling (1 thread 20,766 batches; 12 threads 20,766 — **scale 1.00**). Fixed
  08-14 with a windowed parallel min at all five sites: **10.6× mean / 11.8×
  p99 critical path, +12.6% total work, byte-identical witnesses.**
- **A `sorry` was found in a theorem's *statement*** — caught only by the
  `#guard_msgs`-pinned `#print axioms` on `sorryAx`. First time seen in the
  wild.

**Artifacts**: `docs/VERDICTS.md` §2 · `notes/grind-fix.md`, `notes/grind-phase.md` ·
`notes/num-queries-pin.md` · `notes/two-regime-calculator.md` ·
`minidregg/Assurance/TwoRegimeQueryBudget.lean` (**regime in the type**; the
withdrawn capacity regime is *unrepresentable*) · `~/dev/plonky3-recursion`
commit `52e1fab`.

## 1.7 Recursion and the tower

**Asked** (ember, 08-14 17:14): should the leaf and the recursion layer be
*different proof systems*?

**Found**:
- **SP1 and OpenVM both keep one proof system across layers**, changing
  parameters plus a hash-field swap. The deciding quantity is **`K = wrap/leaf`:
  ours is 26.9, theirs is < 1.**
  > ***Our problem is not the proof system. It is that the leaf is too small.***
- ⚑ **A measured identity, twice, with no shared code path**: the child's
  **native verify** permutations = **38,168**; the leaf wrap's **in-circuit**
  `poseidon2_perm` ops = **38,168**. *A wrap's biggest table IS its child's
  verifier, row for row.* So verifier cost and prover cost are the same
  quantity at different layers.
- ⚑ **The in-circuit Poseidon2 share is 36.45%, not the ~75% every "the tower
  is where this pays" claim rested on.**
- ⚑ **The blowup trade is net ≈65× WORSE per turn** once the tower is counted —
  every grid we had priced one layer of five.
- **Arbitrary-length extendability is priced at ×27.9 per turn**, paid whether
  or not a chain is ever extended. That was ember's suspicion and it was right.

**Artifacts**: `notes/recursion-tower-profile.md` ·
`notes/leaf-vs-recursion.md`, `docs/LEAF-VS-RECURSION.md` ·
`breadstuffs/circuit-prove/tests/recursion_tower_profile.rs`,
`.../leaf_vs_recursion_sweep.rs` · `docs/VERDICTS.md` §4c.

## 1.7b `[08-17]` The reduced opening, and the Galois-lever sweep

**Asked** (ember, 08-16): the ×2.13 sumcheck-batched reduced opening had been
standing as *"the biggest measured available win"* for days and nobody had
taken it. Why not — and is there another route to the same endpoint?

**Both halves came back, and they came back opposite ways.**

**(a) The sumcheck route is NOT reachable over two-adic FRI.** A sumcheck over
`Σ_k α^k v_k` terminates in a claim about **the MLE of the opened values at a
random point**, which the verifier can discharge only by recomputing it (Θ(N),
no saving) or by opening it from a commitment to `V` — and **`V`'s only
commitment is a Merkle leaf, which supports no evaluation opening.** The
verifier already holds every value in the clear.

> ***Lever 3(b) is a PCS REPLACEMENT, not a backend rewrite*** — the
> Jagged→BaseFold / Stacked→WHIR move that SP1 6.4 and OpenVM 2.0 both made.
> **The ×2.13 was the sumcheck endpoint, priced against an assumption that the
> terminal claim is free. It is not free.**

⚠ **And three of our own docs carried three different verdicts on the same
phrase, about three different circuits, which nobody had noticed**: pure
upside · an *ownership* obstruction ("it's in the fork") · and "now MARGINAL",
true **of gnark only**. See `04-DEAD-ENDS.md` §E9 and `05-ERROR-CLASSES.md`.

**(b) The algebraic half was reachable and LANDED** (`emberian/plonky3-recursion@0ed1182`):
a matrix opened at `P` points was paying `P` Horner chains per query **over the
same opened row**; restructured `q·P·n → q·n + P·n`. **`HornerAcc` ×1.806 ·
`Alu` ×1.651 · wrap cells 58,249,216 → 40,554,496 = ×1.436** — see
`03-MEASUREMENTS.md` §1.9 for conditions. ⚑ **The Poseidon2 share moves 36.45%
→ 52.36%**, so "a free hash" goes from ×1.57 to ×2.10.

**(c) `[08-17]` Then the Galois sweep found the endpoint by another road, and
ember's challenge was vindicated: ×2.13 IS reachable — via PACKING, not the
sumcheck.** Five pathways priced (`notes/galois-levers.md`), and *two of them
closed by proof, which is worth nearly as much as the one that opened, because
they will not be re-proposed*:

| pathway | verdict |
|---|---|
| **Frobenius / minpoly** | **CLOSED BY PROOF.** OOD absorption is already at the information floor (`observe_ext` = exactly 4 base felts = one Ext4 value — *the same object*), and the conjugate-point move is **unsatisfiable**: it needs `ord(g) \| 4` and the trace generator has `ord ≥ 16`. A two-line cyclic-group argument, Lean-statable. ⚠ And our ethSTARK attribution was a misreading — §3.8.2 spends Frobenius to prove **F_p-ness of committed columns**, which our base-felt MMCS leaves make *structural*, not to cut costs. |
| **Deferred accumulation** | **CLOSED over Merkle-only commitments** — see `04-DEAD-ENDS.md` §E10. |
| ⚑ **Ring-switching / packing** | **THE LIVE ONE.** **90.1% of `HornerAcc` is a fixed K-linear map of base data**; gnark already evaluates it in coordinate form. *The BabyBear wrap was the last rung manufacturing L×L products.* |
| **Fold-orbit** | **null at source** — p3 already spends the ±x orbit fully, which *explains the measured null arity knob* (§1.7). |
| **Trace / norm** | **mathematically identical to packing** (`packEquiv`). |

**The packing result, measured**: deployed `p1/a4/K2` is **×1.400 from its own
family's minimum `a4/K16`** — **wrap 40,554,496 → 28,971,008 cells, ×2.011
cumulative against pre-split** — optimum at `chains/K ≈ others/lanes`, K ≈ 16.9;
`rec4` additionally drops the global max height **2¹⁸ → 2¹⁶**. **Every point is
VK-rotation-only.** A dedicated Lean-authored chain table prices the remainder
to **≈×2.23 cumulative `[DERIVED]`**. Then, later the same night, the wrap was
**PROVEN at K16/rec4** through the deployed pipeline — the standing tooth
closed. `03-MEASUREMENTS.md` §1.10.

> ⚑ **The shape of the answer: the waste was GEOMETRIC, not ALGEBRAIC.** Every
> Galois-theoretic lever we reached for was either already spent or provably
> unavailable; the win was in how the cells were laid out.

**Next lever, newly visible**: `recompose` now sets the wrap's global max
height — 2¹⁸ rows for 160,263 ops at `npo_lanes = 1`, **3.9% of its cells, and
the lane count has never been priced.**

⚠ **Substrate, said out loud**: the in-circuit FRI verifier is pre-existing
**Rust-authored** circuit logic — *debt by the house law*. The (b) change
authored no constraint, and **nothing in this section is Lean-authored or
verified.** The packing remainder in (c) is explicitly costed as a
**Lean-authored** chain table.

**Artifacts**: `notes/galois-levers.md` · `notes/sumcheck-batched-opening.md` ·
`notes/k16-proof-and-weft.md` · `docs/LEAF-VS-RECURSION.md`.

## 1.8 Lookups and RAM

**Explored**: LogUp · LogUp-GKR · logup* (2025/946) · Lasso · Twist & Shout ·
Shout one-hot · cq / Caulk / Caulk+ / Baloo / Flookup / µ-seek · Deep Thought
(2024/325) · Celer (2026/1453) · SP1 Hypercube's memory argument · OpenVM /
SWIRL · Ceno · RISC Zero · Nexus · ring-native lookups over Z_{2^k}.

**Found**:
- ⚑ **Two structural facts kill most of the table-efficiency literature for
  us before any detail**: our table is 2^16 rows and *public*, so the verifier
  can evaluate its MLE directly; and m ≈ 2^28 ≫ n, so sublinear-in-n is
  worthless.
- The "43m/10m" constants everyone quotes trace to **LogUp-GKR §3.3 Eq. (5)**,
  not to Celer, and **43 is not derived in Celer at all.**
- **~502 trace cells per general RAM touch in SP1** against 39–44 for the
  instruction itself. This number is the empirical backbone of `docs/SYSTEM.md`'s
  thesis — *we did not arrive at a faster prover, we arrived at a different
  statement.*
- **Deep Thought has no implementation and no benchmarks** — every number in it
  is an analytic operation count. Nobody has transplanted it to a hash-based or
  lattice commitment. Clean negative.

**Artifacts**: `notes/lookup-ram-verdicts.md` · `docs/SYSTEM.md` ·
`minidregg/Selvage/BinaryLookup.lean` (proves the one-hot equality vector *is*
the χ vector of the address bits, not merely "boolean + sums to one").

## 1.8b `[08-17]` Lasso over LogUp — and the 3.2× lookup lever, refuted

**Asked**: `03-MEASUREMENTS.md` §1.8 records that **`R` is a property of the
arithmetization, not of the hash**, and that a lookup argument prices the
Poseidon2-vs-Blake gap at **~3.2×** rather than 30.6× — flagged there as *"a
pointer, not a result."* This lane turned the pointer into a measurement, by
reading Lasso at source and counting a **deployed** lookup AIR.

**Found — the lever is real and far too small**, counted cell-by-cell on
**Stwo's deployed lookup/LogUp Blake AIR** (384 main + 260 interaction cells
per round row, carries virtual, five xor tables at relation arity 3):

> **Blake3 under lookups ≈ 4,680 cells/compression → R ≈ 15.7× against our
> 300-cell Poseidon2.** Lookups buy **1.96×, not the ~10× needed**; the flip
> bar (< 4,000 blowup-cells) is **missed by 4.7×.**

⚠ ⚑ **The 3.16× figure was a FAT-DENOMINATOR ARTIFACT** — 7.9 gates/S-box for
*their* Poseidon against our 2.1 cells/S-box. **It had been quoted repeatedly
as "the highest-value open measurement"; it is now the measured answer, and
the answer is no.** Riders: 2²⁴ amortized table cells (break-even ~2¹²
compressions), and the table relation lands at **98.7 bits at BabyBear⁴
without grinding** — below the bar on its own. Keccak under lookups: **wash to
negative.**

⇒ **Poseidon2's position is now TRIPLE-CONFIRMED**: in-circuit 30.6×–210×
directly · recursion pinning it in both characteristics · **the lookup escape
measured shut.** (`[08-17]` and with §1.3b's Kagi sweep, a fourth, from the
attack side.)

**What the lane established beyond the refutation:**
- **The sparse vector never meets the PCS.** Spark reduces everything to
  *dense* multilinear commitments, so **BaseFold RBR suffices in kind**; the
  real gaps are extraction (`W = Unit`) and batched openings. ⚑ **Lasso's
  "small elements" headline is MSM-denominated and COLLAPSES under a
  hash-based PCS.**
- **SPARK subsumption is definitional** — `spark_table_decomposes` makes
  "sparse eval IS a decomposable lookup" a theorem: **one gap, not two.**
- **The full error expression is root counts throughout, with no Regime
  anywhere** — the one new shape feature is a *precondition*, `m < char F`,
  which in char 2 wears the multiplicity-cancellation costume that
  `BinaryLookup` already refutes. The two-regime calculator needs two more
  knobs (a sumcheck leg, a validity-precondition field); **E3 is literally
  `LogUpCfg (K=α, H=m+M, R=3)`.**
- **Teeth**: `splitEq_not_decomposable`, a *general* non-decomposability
  theorem refutable over every field (per `GUARD-DISCIPLINE`); the
  all-accepting oracle refuted; three obligations named, not built.

**Artifacts**: `notes/lasso-over-logup.md` · `minidregg/Selvage/DecomposableTable.lean`
(`feef028`) · `notes/hash-landscape.md` Addendum 2.

## 1.9 Binary fields and the char-2 cone

**Trigger**: the Ethereum Foundation's public pivot on 08-14 (`01b` §27).

**Found**:
- ⚑ **13 of 18 keystones are field-agnostic.** The multiplicative dependency
  is concentrated in **exactly one Lean structure** (`Selvage.FoldingData`,
  carrying `two_ne : (2:F) ≠ 0`) and **one deployed sampler**
  (`BaseFoldBcsQuerySampling`). Both are single, named, replaceable objects,
  and the char-2 replacement for the first **already existed on disk**
  (`AdditiveFriTower`).
- **The char-2 vacuity census found exactly one trap tree-wide**, and it was
  latent rather than live. Both traps closed 08-14.
- `grep -rn 'IsPrimitiveRoot\|rootsOfUnity\|primitiveRoot\|nthRoots'` over
  minidregg → **0 hits, tree-wide.** Four distinct domain constructions, none
  multiplicative.
- ⚑ **BinarySpartan: two lanes searched soundly and drew the wrong conclusion.**
  `notes/binaryspartan-position.md` and `notes/neo-superneo-read.md` both say it
  could not be verified to exist (five independent instruments, all ∅).
  **`docs/BINARY-POSITION.md` corrects this: it EXISTS** — ember holds its title
  page and abstract from the eprint *review queue*, plus an EF slide with its
  benchmark table. It is awaiting publication, so **by construction it is in no
  mirror and no author listing.** `docs/VERDICTS.md` is silent, so there is no
  tiebreak from the file that normally wins. **The rule that came out of it:**
  *absence from a published corpus is evidence about the corpus, never about
  reality, and a paper described as unpublished is not evidence at all.*
  What survives from the search either way: the name traces to **Irreducible's
  Binius64 blueprint §1.2, "Why Not Binary Spartan?" — a rejected strawman.**
  Irreducible considered this design and rejected it; Setty built it and it is
  the fastest scheme in the EF client-side benchmark.

  ⚠⚑ **`[08-17]` RESOLVED — the paper went public and was read at source, and
  it refuted OUR OWN SCRUTINY, not just the absence claim.** Both directions
  of the disagreement above are now settled, and the correction runs against
  us:
  - **"Vega 44.2" is the real Vega_MC, measured 44.23 ms — NOT `spartan2` at
    541.72 ms.** *Our identification was wrong*, and it was the load-bearing
    step in the "the benchmark table is mislabelled" argument.
  - **The M1-vs-M4 harness discrepancy dissolves**: all rows are same-machine
    M4 Max through Flock's pinned harness, best-of-five, disclosed.
  - > ⚑ **Our scrutiny was scrutiny of the SLIDE. The paper is cleaner than
    > the slide.** That is a general lesson about reading a preprint through
    > its conference deck, and it is now `05-ERROR-CLASSES.md` material.
  - **What survives**: **Flock-wins-in-aggregate is conceded and measured at
    1.96× in the paper's own Table 1**; the residual criticisms are
    peak-of-sweep reporting and an "additive optimizations" claim that elides
    the **JBR-vs-UDR regime difference**.
  - ⚠ **One earlier claim of ours is NOT refuted and should not be quietly
    dropped**: `04-DEAD-ENDS.md` §L6 recorded *"'Vega' is P-256 + Hyrax —
    discrete-log, NOT post-quantum."* Vega = eprint 2025/2094, and
    **P-256 + Hyrax/DL is re-confirmed independently at §4.3/§7** by the
    Nebula/Vega read (§1.11). **A post-quantum comparison table still has a
    discrete-log entry in it.** What changed is *which row we mis-identified*,
    not what Vega is.

  **Artifacts**: `notes/binaryspartan-read.md` · `docs/BINARY-POSITION.md`
  (corrected in place, with the retraction visible).

**Artifacts**: `docs/BINARY-POSITION.md` · `notes/binaryspartan-position.md`
(1,203 lines) · `notes/neo-superneo-read.md`, `notes/neo-verdict.md` ·
`notes/char2-vacuity-census.md` · `notes/basefold-additive.md` ·
`minidregg/Selvage/AdditiveBaseFold.lean` (838 lines, 13 axiom pins) ·
`notes/ring-switching-connectors.md`.

## 1.10 Reconnaissance on the fast systems

**Asked** (ember, implicitly, throughout): why *are* they fast?

**Read at source, at HEAD**: SP1 / SP1 Hypercube / SLOP · OpenVM + SWIRL ·
`openvm-stark-backend` · Ceno + gkr-backend · Expander (Polyhedra) · RISC Zero ·
Nexus · Jolt (+ Akita) · Binius64 · leanMultisig · ezkl · Stwo.

**Found**:
- **SP1 Hypercube targets 100 bits, not 128** — one named constant.
- Its production FRI/BaseFold parameters are derived in the **unique-decoding**
  regime: *no proximity-gap conjecture.* Four of five production systems refuse
  the capacity conjecture; **we are the outlier.**
- **Binius64 commits no end-to-end prover profile.** Everything quantitative
  lives in PR and commit messages.
- **Expander's `benchmark_results.json` is 0 bytes.**
- `~/src/leanMultisig` is a **dead personal fork**, 8 commits, empty scaffolding
  — a wrong-repo hazard now recorded.
- **NVIDIA shipped `clmad`** (carryless multiply-accumulate, SM80+, CUDA 13.3),
  measured 4.1–12.9× on B200 for sumcheck vs bitsliced, and cites Binius
  explicitly. ⚑ Found by the hardware sweep and **it never reached a note.**

**Artifacts**: `notes/fast-systems-recon.md` · `notes/prover-floor.md` +
a claude.ai artifact (`ea569fc8-…`) + `paper/scripts/prover_floor.py`.

## 1.11 `[08-17]` Nebula and Vega at source — and the PQ-Vega path

**Asked**: the fast folding-based systems are winning on measured latency. *Why*
— and is the mechanism something we can have without giving up
post-quantum security?

**Found — the mechanism is named, and it is not cleverness, it is the group:**

- ⚑ **The DL dividend is ~10³× at the seam.** Their Nova fold verifier is
  ≈**10,000 R1CS gates**; our wrap's 38,168 permutations are ≈**9.5M
  constraint-equivalents by their own conversion.** The mechanism is
  *Pedersen adds, Merkle opens*, plus the shape change: **fold now, verify
  once at the end.**
- ⚑ **The switchboard rides THIS path, not the deployed stack**: pay-per-use
  requires a **free zero-commitment — true of Pedersen AND Ajtai, false of
  Merkle.**
- ⚑ **Nebula's memory lemma IS our `TwistContinuity` keystone, and it is NOT
  DL-bound** — Lemma 2 (multiset invariant ⟺ sequential consistency, both
  directions) plus a fingerprint corollary and two-layer IVC. **Top-ranked
  transfer: pure combinatorics, and the LogUp + roots-before-challenge
  machinery was already on the shelf.** ⚠ Their model has no `free`; ours
  does. (§1.12 — that gap dissolved.)
- **Their fold schedule IS `AccRbrBcsShifted`'s lagged-root residual.** They
  **cannot state any concrete bound** (negl(λ) formalism), so our depth
  refutation and repaired `(t+k)·ε` are expressible *only on our side*.
- ⚠ **A printed formula bug found in Nebula** (p.23's input-consistency
  direction would zero the global input; Lemma 3's proof and the worked
  witness give the right one) — and the silent invariant named:
  **block-support discipline**, which is *our widened-gadget wound* in their
  notation.
- **NovaBlindFold**: dead on Merkle; transfers in shape to the dual-mode with
  an **unpriced smudging tax**; against our recorded VEIL ~3% it is **parity,
  not a class gap.**
- ⚠ **Do not conflate Nebula's two numbers**: **the 30× is the MEMORY
  technique; the 260× is the SWITCHBOARD** — different mechanisms. (Our own
  earlier attribution had this wrong; see Pillar 7.)

⚑ **THE PQ-VEGA PRICING `[DERIVED]`, which is the reason this section exists**:
a Nova-shaped fold over the **dual-mode MSIS commitment** costs
**≈4–7×10³ R_q rows/step ≈ 4–8% of the 92,396-row FS bill it rides beside.**
Ordering: **DL fold 1× < PQ fold ~4–50× < Merkle wrap ~10³×.** γ-grinding under
folding is negligible and class-unchanged; the genuinely new term is
`Q·ε_MSIS` per absorbed commitment. **Neo's configuration is killed twice by
the dual-mode** (ring-native absorb at 27.4 rows/element; the κ=24
commit-not-absorb cap).

**The surpass table, honest**: they win **measured latency and memory
maturity**; we win **PQ, formal content** (their repos verified zero this
session, instruments named), **and the depth bound**; transparency ties.

**The composed architecture this yields** — every layer either held or priced:

```
EVM decompilation          ← Pillar 7; ~60–140× past the switchboard
switchboard (pay-per-use)  ← needs the free zero-commitment
committed memory           ← Nebula Lemma 2 ⟺ our TwistContinuity
PQ folding                 ← Nova-shape over the dual-mode MSIS commitment
dual-mode ring object      ← §1.4d; q = 2⁶⁴−257, τ = 2
```

**Artifacts**: `notes/nebula-vega-lessons.md` · `docs/VERDICTS.md` §3c ·
`SLVG_THOUGHT.md` §III.

## 1.12 `[08-17]` PQ folding and committed memory — two keystones discharged

Both of these were **named obligations** in the first stratum and are now
theorems. They are recorded here as *directions* because each changed what the
architecture can assume.

**`TwistContinuity` — DISCHARGED** (2026-08-17, minidregg `820f0cb`), Nebula's
Lemma 2 formalized **both directions** over our richer carriers:
- `twistContinuity_iff_grandEquation`: TC ⟺ frame-outside-dom ∧ ∃ stamps,
  `IS + WS = RS + FS` — the Spice-shaped list induction over Mathlib multisets,
  none hand-rolled.
- ⚑ **The `free` gap was ABSORBED as a theorem rather than carried as an
  obligation**: with `Option`-valued cells, **`free` is a write of `none`**, so
  the soundness induction has *no free case split* at all.
  *The model difference the Nebula read warned about dissolved into the carrier
  choice.* `stale_read_after_free_refused` exhibits the flagged hazard closed.
- The fingerprint lands at the **sharp** bound `max(|A|,|B|)·(k+1)/|F|` (not the
  crude pairwise one); injectivity is honestly `Set.InjOn` — **global is
  UNINHABITABLE for Nat-stamped tuples.**
- **Nine teeth**, including a quantifier-order exhibit: **∀γ, a post-γ forgery
  PASSES** — the γ-before-values ordering shown load-bearing, not assumed.
- ⚑ **Bonus: this engine IS the gap `[SPARTAN-sparse]` recorded** — SPARK's
  combinatorial core now exists; its sparse-matrix instantiation does not.
- **One obligation remains**: `[TWIST-FP-BIND]`, six named legs. `06-OPEN.md` §3.

**`AccRbrFold` — LANDED** (2026-08-17, minidregg `bc29222`), folding at the
**commitment alphabet**:
- **The norm budget is DATA**: `budget b₀ T = b₀ + T·(ρ·B)` — additive, the
  Cyclo flat-fold regime — and the RBR knowledge state through a fold is a
  genuine Def-4.1 instance.
- ⚑ **The norm wall, tight both ways** (`03-MEASUREMENTS.md` §1.13).
- ⚑ **The `AccRbrBcsShifted` lagged-root residual DISSOLVES at the additive
  alphabet** — every fold root is verifier-computable, no inert challenge.
  **The trade: the norm budget is the new residual, and it is now a field of
  the structure instead of a comment.**
- ⚑ **The Z=∅ depth corner RECURS under additivity** —
  **because it lives in the ERROR algebra, not the message algebra.**
- Consumer wired three ways into `VerifierEmbedding`, including the fail-open
  hazard as an `IsEmpty` theorem (`dropped_norm_check_refuses_embedding`:
  infinite kernel coset vs finite norm ball).
- ⚠ **Honest label, and it is the one that matters**: `MsisHardEx` is
  *nonexistence* — proved at a toy and **expected false at production sizes by
  pigeonhole.** The computational reading is the named residual `[FOLD-msis]`,
  and `08-ATTACK-BRIEFS.md` BRIEF 3 says plainly that **that gap is where a
  real attack would live.**

**Artifacts**: `notes/twist-continuity.md` · `notes/acc-rbr-fold.md` ·
`minidregg/Selvage/AccRbrFold.lean`, `.../MultisetFingerprint.lean`,
`Assurance/TwistMemoryFingerprintJoin.lean`, `Compiler/TwistMultisetInvariant.lean`.

---

# Pillar 2 — vFHE

## 2.1 The two directions

Ember's framing, 08-13 12:09: **stark-in-fhe and fhe-in-stark achieve
different constructional outcomes** and both are wanted. That split survived
into `docs/SYSTEM.md` and `docs/COMPOSITIONS.md`.

## 2.2 What we actually deploy, measured rather than assumed

Three separate lanes had to correct the brief on ground truth:
- **Deployed depth is 2** (measured, 40/40) — not the 1–3 that was assumed.
- **The secret is CBD(20)** (variance 10, support ±20) — **not ternary**,
  which is what every noise formula in the literature and in our own briefs
  assumed. `vendor/fhe-dregg/src/bfv/keys/secret_key.rs:43`. This is the single
  most load-bearing parameter in every noise bound and it was wrong in the
  brief.
- **`t = 2²⁰` binds any BFV polynomial nonlinearity to degree ≤ 2 regardless
  of levels.** Encrypted attention at depth ≤ 3 is refuted, three independent
  ways, two of which the lane computed rather than found.
- **Exactly two parameter sets exist in the whole tree**, from one source of
  truth (`fhegg-core/src/params.rs:10-15`).

## 2.3 Directions explored under vFHE

| direction | verdict | where |
|---|---|---|
| Transciphering | **dead** — 269 bits of noise against a 109-bit modulus | `04-DEAD-ENDS.md` |
| Bootstrapping | **dead** — depth 13–17 crossover against our 2 | `04-DEAD-ENDS.md` |
| Amortized / batched bootstrapping | **does not apply to BFV**; the one method that uses BFV internally says in its own footnote it becomes impractical at exactly our 20-bit precision | `notes/fhe-scout-verdicts.md` |
| Scheme switching | **hazardous** — a working CPA-D proof of concept | `docs/VERDICTS.md` §3 |
| NTRU-based FHE | **all 11 parameter sets across 6 papers sit above the Ducas–van Woerden fatigue point**; 5 of 6 apply the wrong test | `04-DEAD-ENDS.md` |
| GBFV | measured directly in Fheanor at our parameters | `notes/fhe-core-theory.md` |
| Coefficient-encoded matmul | ✅ **built and measured** — 12 bits/matmul with split-sign, depth 2 after, 466 µs at 512×31 | `fhegg-fhe/src/bfv_coeff_matmul.rs`, `notes/coeff-matmul-landed.md` |
| Single joint prime (H1/H2) | **net loss at 109 bits, wins at 61**; the deciding variable is the 64-bit machine word | `notes/h2-verdict.md`, `phase0/h2-rns-vs-single-prime/` |
| The KPZ encoding fix | ⚑ **NO-OP** — already in force; the "fix" had nothing to fix | `notes/kpz-noop-and-the-model-gap.md` |
| PIR for the embedding table | ⚑ **LIVE, not closed** — "PIR rotation keys cost **2.01 MB at our parameters** (12 keys × 0.33 MB at N=4096; the literature's **857 MB** horror is N=2^16). **The field's rotation-phobia does not transfer to us.**" Un-promoted to VERDICTS, so neither confirmed nor closed. | `notes/fhe-scout-verdicts.md:28-30` |
| Circuit privacy / sanitization | **smudging does NOT give circuit privacy**, and the literature says so in as many words (2025/275) | `notes/fhe-core-theory.md` |
| RLWE worst-case reductions vs our deployment | a √n hides in a convention gap between two normalizations | `notes/fhe-core-theory.md` |
| Post-quantum status of our parameters | ⚑ **OPEN and unfavourable.** `docs/VERDICTS.md` §7.8: it is a *classical*-line set nobody ships; Apple ships N=4096 at **83 bits** for `.quantum128`, and N=8192 / 148 bits when it wants log t ≈ 20. ⚠ **A sharper pair of figures exists only in a transcript and never reached the notes** — lane `a0cbd2ee` ("2024-26 attacks and parameters") concluded *"~125.1 bits — about 3 bits short — and `log q = 109` is 3 bits over the current recommended maximum of 106… we are sitting on the 2018 table's number."* **Not in any file.** The nearest recorded numbers are deployed **98.1 core-SVP / 119.9 MATZOV / 130.5 HE-standard** (`notes/koalabear-limb.md:145-152`) — a ~32-bit spread that is **the model, not the parameters.** | `docs/VERDICTS.md` §7.8 · transcript only |

## 2.4 ⚑ Cross-limb binding — the pillar's real finding

**Exhibited in Lean, 08-14.** It was **two holes under one name**:

- **Hole A — provenance.** The checked system is `∀ i, ∃ source`; the honest
  one is `∃ source, ∀ i`. A quantifier swap, invisible to every completeness
  test. The exhibit takes limbs from *different* ciphertexts, satisfies every
  per-limb equation, and reconstructs to a value **no honest pair can
  produce** — a wrong *answer*, not merely an unbound proof.
- **Hole B — expressibility.** `⌊t·x/Q⌉` reads the CRT reconstruction, so there
  is no per-limb equation to bind at all.
- ⚑ **The obvious fix is a tautology.** "A CRT-consistency relation over the
  limbs" can never refuse: the CRT map is a bijection and the forgery is itself
  CRT-consistent.
- ⚑ **Why nobody had exhibited it**: every Lean BFV carrier in the tree makes
  the attack *unrepresentable* — and one file said so in its own residual list.
  **Documented ≠ detected, in our own tree.**
- **The fix is a layout decision and the free one exists**: interleave the
  limbs into one row and the row *is* the shared opening. +0 felts, +0
  permutations.

**Artifacts**: `breadstuffs/metatheory/Bfv/CrossLimb.lean` (`5b653ba5d`) ·
`notes/cross-limb-binding.md`, `notes/cross-limb-verdict.md` ·
`metatheory/Bfv/Ring.lean` (the noise model lifted to the ring).

## 2.4b `[08-17]` The Z_Q product-ring sumcheck — Hole A dissolves, Hole B closes against the approach

**Asked**: run the sumcheck **natively over `Z_Q = F_q₀ × F_q₁ × F_q₂`** (the
deployed BFV CRT tower), so the cross-limb forgery has **no per-limb slot to
satisfy**. Does Selvage's Lean sumcheck cone survive the move from `Field` to a
product ring?

**Found**: *"the mathematics is real and small"* — and the two holes go opposite
ways.

- ⚑ **Hole A (provenance) is closed by UNSTATABILITY, which is the strongest
  closure class there is.** `boundMul_iff_zqBound` makes the honest
  `∃ pair, ∀ limb` relation **one ring equation**, and `zq_same_forgery_refused`
  shows the identical CrossLimb frankenstein is **a flatly false ring
  statement.** *The hole moves from "unchecked" to "unwritable."*
- ⚑⚑ **Hole B (expressibility) is closed AGAINST THE WHOLE APPROACH, and this
  half-refutes our own earlier hope.** `rescale_not_zq_polynomial`: polynomials
  over a product ring compute **exactly the limb-local functions**, and
  `⌊t·x/Q⌉` is not limb-local ⇒ **no `p ∈ Z_Q[X]` computes the rescale, ever.**
  It is *nameable as a function, never arithmetizable as a Z_Q-polynomial
  identity.* Any proof of the rescale must go through the **redundant-basis
  witness** or the **single-prime** route.
  > **Corroboration from the other side**: CCKP19 chose `Z_{p^e}` — *local, not
  > a CRT product* — **precisely so that base-p rounding stays polynomial.**
  > That is the contrapositive of our theorem, in someone else's design choice.
- ⚑ **A negative control that forced a statement change**: **field-wide
  Schwartz–Zippel is FALSE over `Z_Q`** — proved by exhibit
  (`zq_fieldwide_sz_false`), repaired to `A`-relative counting
  (`zq_agree_card_lt`). ⚑ **`Field` is load-bearing in exactly ONE lemma
  tree-wide** (`Sumcheck.lean:77` ← `ReedSolomon.lean:122`) — **and the bite is
  not cosmetic**: it is the statement, not the binder, that has to change.

**The prices** — see `03-MEASUREMENTS.md` §1.14 for the ceiling and the
amplification table. Headline: `|A| ≤ min qᵢ ≈ 2³⁶` is a **theorem**, not a
design choice; **shared Ext4 (2¹⁴⁴) clears our ~124-bit bar and shared Ext2
(2⁷²) does not.**

⚠ **Corrections this lane made to its own brief, all in place**: *"3× the
sumcheck work"* was priced against **the wrong baseline** (a single-limb field
sumcheck **is not a sound rival — it IS the per-limb hole**); against the
row-interleaved closure it is **~1× at count resolution**. *"36 bits/round"* is
a **per-round error**, and **rounds ADD by union bound**, not compound. And
*"extension of each factor"* vs *"one shared extension of Z_Q"* are **the same
object** — getting that wrong means sampling three extension challenges
independently, which **reopens a provenance-style seam one layer down.**

⚠ **The live residual, and it is the shape of the original hole**: the
**one-handle PCS obligation.** *If each limb had an independently-openable
handle, per-limb selection reappears at the opening index.* `06-OPEN.md` §2,
`08-ATTACK-BRIEFS.md` BRIEF 4.

⚠ **And say the substrate**: `PROVEN-IN-LEAN ≠ ROUTABLE` applies at full
strength. **Grep confirms no Z_Q witness-gen anywhere in Rust.** The Selvage
protocol port is not done; §3 of the note is the exact work order, and its own
blocker line reads *"Blocker: none mathematical."*

**Artifacts**: `breadstuffs/metatheory/Bfv/ZqSumcheck.lean` (`c4c1e5835`,
407 lines, 0 `sorry`; `#assert_namespace_axioms Bfv` **113 → 137 kernel-clean
theorems**) · `notes/zq-sumcheck.md` · `notes/cross-limb-verdict.md` addendum.

## 2.5 The applied vFHE literature

Read in depth: Laminate (2025/2285) · packed sumcheck over small
characteristic (2025/719) · Zama's matvecmul (2026/027) · Dinocchio (2026/159) ·
Rinocchio · HELIOPOLIS · the whole "proofs over rings" line (LaBRADOR,
Greyhound, LaZer, SLAP, LatticeFold/+, Neo/SuperNeo, Cyclo, Symphony).

⚑ **The one structural move that dominates**: *make the FHE modulus and the
proof field the same object.* Two papers do it from opposite ends. That is what
made the joint-prime question (H1/H2) worth asking at all.

⚑ **And a clean negative that took several lanes to establish**: **nobody has a
ring-native RO-like hash.** Every lattice proof system either drops to a
coefficient-field/byte hash and eats the conversion, or is non-recursive so the
hash is never arithmetized. That absence is what the ring-hash pillar (§1.4)
aims at.

---

# Pillar 3 — zkML

## 3.1 Numeric format — where the campaign started

**Asked** (ember, 08-12 13:37): Attestable quantises matmuls to int8; *"we
don't need to accept the limitations, we can do actual floating point stuff."*

**Explored**: bf16 exact tables · MXFP4 / MXINT8 / NVFP4 microscaling ·
block floating point generally · IEEE-754 in-circuit · fixed point · int8 ·
Ozaki-scheme limb splitting · unary lookup tables.

**Found**:
- ⚑ **The bf16 4× thesis measured at 1.4×.** A clean negative, and the honest
  number. `docs/PHASE0-RESULT.md`.
- ⚑ **MXFP4 within-block exactness holds; NVFP4 preserves exactness but
  destroys the power-of-two-scale shift argument** — so our arithmetization is
  MXFP4-specific, not "block-float-generic."
- ⚑ **Measured on gpt-oss: 100% of 1,382,400 sampled reduction rows fit a
  width-8 exponent window** (max observed spread = 8, in exactly 2 rows). So
  the cheap ~1,050-constraint alignment path is not the common case — it is the
  **only** case, covering 100% of the 78.9% of per-token FLOPs that are MXFP4.
- **Block-float / shared-exponent structure inside a ZK proof system is
  essentially unwritten.** eprint searches for `microscaling`, `bfloat16 FP8`
  return literally zero. One arXiv paper (2606.05433) names the mechanism once.
  ⚠ That is a *scoped* absence, and the scoping matters — see `05-ERROR-CLASSES.md`.

**Artifacts**: `docs/PHASE0-RESULT.md` · `docs/mx-formats.md` ·
`docs/bf16-exact-arithmetization.md` · `phase0/` · `notes/float-in-zk-three-regimes.md`.

## 3.2 Nonlinearity — where the cost actually is

**Found**, and it redirected the whole pillar:
- **The nonlinear part dominates and it is not close.** Measured across three
  systems: **DeepProve 67–75%, zkGPT ~59%, zkLLM ~34% from softmax alone.**
  **Matmul lands at 5–7%.**
- Consequently: *the lever you asked me to examine is the wrong one.* Several
  lanes independently reached this and said so.
- **Requantization is not eliminated by the good systems — it is promoted to a
  first-class protocol they pay for on every operator** (OpenLLM).
- **ZIP (CCS'25) is the only IEEE-754 system and needs 37 hours for an
  11M-parameter 4-layer mini-BERT.** ⚑ **Transcript-only** — lane `a4e77a94`
  ("Transformer ZK softmax/layernorm survey", session `3e64269c`). This figure
  is **in no file in the repo**; ZIP appears three times in the notes and none
  of those carries it. Re-source before publishing.
- **Spain (OSDI'26)** is the best 2026 float system and **loses to quantized** —
  by their own Figure 4, on the same workload (GPT-2, seq=32): prover 750 s vs
  zkGPT's 64 s (**11.7×**), verifier 78 s vs 5.8 s, proof 1.6 MB vs 88 KB. Their
  §8, unprompted: *"Spain's prover isn't the fastest in the literature; that
  honor belongs to zkGPT."*

**Artifacts**: `notes/zkml-landscape.md` · `notes/spain-celer-verdicts.md` ·
`notes/ml-to-crypto-mappings.md` · `docs/PHASES-AND-TENSOR.md`.

## 3.3 MoE and scale

**Asked** (ember, 08-13 17:21): *"kimi k3 is a 2.4T moe model with many active
parameters, so we need to keep that in mind."*

**Found**:
- ⚑ **Router binding must be ZERO-KNOWLEDGE** — expert selections recover
  **91% of tokens.** That was not in the brief and it changes the protocol.
- **Ties are a property of the scoring function**: sigmoid-scored routers are
  *structurally* tied (only **26 distinct bf16 values in [0.9,1.0) for 256
  experts**); raw-logit ~4%; DeepSeek-V4's Sqrt(Softplus) never saturates.
- **V4's early-block hash routing makes selection a public function of the
  token id — so binding is free there.**
- ⚑ **A retraction worth reading**: *"MoE router binding — zero papers across
  7,090 swept, verified absence twice"* was **wrong**, and both refuting papers
  **were already in `~/paperbin`, pulled and correctly named on the same day
  the absence was declared.**

**Artifacts**: `notes/moe-router-binding.md` + `notes/moe-router-binding-cost.py`.

## 3.4 The matmul contraction, and verifiable training

Landed work, not survey:
- **`foldl → Finset.sum` bridge**, built in two *named* steps so the discard
  point is a line you can point at. ⚑ The load-bearing property is
  **associativity, not commutativity** — IEEE-754 addition *is* commutative and
  is *not* associative; and step 2 has **no counterexample at all**, because
  `Finset.sum` over `Fin k` cannot be written without commutativity, so its
  refutation is a *type error*.
- **Measured**: `[2,1024]·[1024,128]` gives a **51-field-element / 408-byte
  transcript** against the AIR route's **314,000 gates ≈ 27 MB descriptor** —
  but **the sumcheck is 5% of the prover**; the lever is the partial evaluation.
  ⚠ And the 408 bytes omits two multilinear openings that do not exist yet.
- **Rank-1 gradient check**: proved over any `CommRing`, `≤ (mᵢ+mⱼ)/|F|`, no
  rank hypothesis — so *every other rank-1 matrix* is refused by theorem, not
  by testing. **7×10⁴× cheaper than the circuit at 4096×4096.**
  ⚠ **The honest half**: it removes the n² *proof*, not the n² *commitment* —
  and once the proof is 10⁴× cheaper, **the commitment IS the step.**
- **Low-rank updates**: break-even rank is `d/2` = 2048, so **the commitment is
  never the reason to stop**; the constraint that actually binds is **steps** —
  T = 128 at d=4096, r=16.
  ⚑ And the natural `d×r` layout costs **2.0× more permutations** than
  transposing, for *identical felts* — invisible in a felt count.

**Artifacts**: `minidregg/Theory/ZkmlMatmulSum.lean` ·
`minidregg/Selvage/Rank1GradientCheck.lean` (545 lines) ·
`minidregg/Assurance/ZkmlLowRankUpdate.lean` (758 lines) ·
`notes/contraction-sumcheck.md`, `notes/rank1-gradient-check.md`,
`notes/low-rank-updates.md` · `docs/DARK-TRAINING.md`.

## 3.5 catgrad — the compiler seam

**Asked** (ember, the origin steer): can we ship zk attestability for catgrad?

**Found**: catgrad is real (MIT, 31 stars, 4 contributors, active), and
`catena-lang` is its compiler workspace. The seam verdict: **the pillar lives
in minidregg** — op vocabulary in `Theory/` (candidate-independent,
mechanically enforced), per-op semantics in `Selvage/`, emission in
`Compiler/`, engine = the Selvage sumcheck prover. The breadstuffs interim
should be dropped.

⚑ **Tripwire held**: no constraint was written in Rust. Nothing in
`~/src/catgrad-spike` was touched. All arithmetization is Lean-authored.

**Artifacts**: `notes/catgrad-seam.md` · `notes/zkml-integration-architecture.md` ·
`minidregg/Theory/Zkml*.lean` · `phase0/v0_to_v1.py` · `notes/zkml-build-log.md`.

## 3.6 The weight-commitment registry — built, then rejected

Shipped `zkml-research/registry/` (`registry_tool.py`, `MANIFEST-FORMAT.md`,
`COMMITMENTS.md`, 8 manifests, gates, run logs). Ember, immediately:

> *"bruv you just built a complete toy registry for a commitment that is
> irrelevant to all possible proof systems and patted yourself on the back"*

**The objection is exact**: a SHA-256 manifest commits to weights in a way no
prover can open inside a circuit. `docs/VERDICTS.md` §5 records the correct
object: **Poseidon2 over the field-element encoding, at a leaf granularity the
circuit opens, in the layout the prover reads.** Nobody has built that.

⚠ Also found while building it: **`deepseek-ai/DeepSeek-V4` returns HTTP 404
with credentials** — it does not exist on HuggingFace — yet two notes still
cited it as a *measured* Tier-1 exemplar.

---

# Pillar 4 — Hardware

**Asked** (ember, repeatedly): *"AWS F2 fpga i remind you, and also dreams of
custom ASICs"*; *"we should also definitely be thinking about our own TPUs
code."*

**Explored**: Zama HPU (the open SystemVerilog FHE processor) · DARPA DPRIVE ·
the FHE ASIC line (F1, CraterLake, BTS, ARK, SHARP, Trinity) · Intel HERACLES ·
ZK prover silicon · MORPH / MoMA (AI-ASIC-for-ZK) · NVIDIA `clmad` · AWS F2 ·
wgpu / GPU kernels.

**Found**:
- ⚑ **Exactly zero of the academic FHE ASIC designs have ever been
  fabricated.** Every number they report is from a cycle-accurate simulator.
  Exactly one DPRIVE chip became real silicon (Intel HERACLES), at the very end
  of the program.
- **Zama's HPU is real, open, and complete** — 553 `.sv` files, 162,770 LOC
  under `hw/`, a full processor rather than a kernel. Three shipped build
  configs. An "audit-sample instruction" was studied at ISA level and is
  feasible.
- ⚑ **The Amdahl ceiling for tensor silicon is 1.26× at the deployed point.**
  GEMM-shaped work is only the two LDE rows — **20.8% of prove** — and **MLE
  folding is under 0.1%.** Trace height does not rescue it.
- **CROSS's BAT transfers to BabyBear with zero modification** (31 bits ⇒ K=4,
  exactly CROSS's K), bit-exact four ways, **3.05× over three-limb Montgomery
  on hardware with no INT8 unit.** ⚠ **But BAT needs one operand preknown** —
  free for NTT twiddles, *not* free for an MLE fold or a sumcheck round.
- ⚑ **Four-step NTT does not survive to LDE sizes**: the extra-multiply factor
  grows as √N/log N — 341× at N=2^12, **3277× at N=2^20.**
- ⚑ **Drop MoMA and MORPH from the tensor thread**: MoMA does not use tensor
  cores at all; MORPH's GEMM is base *conversion* for 256–753-bit moduli.
- ✅ **The GPU fusion thesis holds and compounds** — 2.7–7.1× at 2^20–2^22 on
  memory traffic alone. ⚑ **Structural finding: two wgpu devices cannot share a
  buffer, so fusion was unreachable by construction** until the arena
  consolidation landed (9 device sites → 1).

**Artifacts**: `docs/HARDWARE.md` · `notes/hpu-seam-study.md` ·
`notes/ntt-as-gemm.md` · `notes/wgpu-fusion.md` · `notes/arena-consolidation.md` ·
`breadstuffs/fhegg-fhe/src/gpu_arena.rs`, `.../bin/ntt_four_step_bench.rs`.

⚑ **Not recorded anywhere until now**: NVIDIA's `clmad` instruction (CUDA 13.3,
SM80+, 4.1–12.9× on B200 for sumcheck vs bitsliced, citing Binius). The
hardware sweep found it and no note carries it.

---

# Pillar 5 — Audit economics

**Origin**: ember's recognition that Attestable's "random sampling" is the
technique we already used on the Mina bridge.

**Explored**: commit-then-audit sampling · beacon grinding (2025/1974,
"Taming Iterative Grinding Attacks on Blockchain Beacons") · the RAND SL1–SL5
framework · TEE/attestation as a competing primitive · the published ZK
audit-bug corpus.

**Found**:
- ✅ **The commit-then-audit theorem is LANDED and, as far as we can establish,
  the first machine-checked one anywhere.**
  `minidregg/Selvage/AuditSampling.lean`, 1,173 lines, sorry-free, **20 axiom
  pins**, all clean. It carries the **fail-open wound class as a theorem**.
- ⚑ **Deployed attestation gives a signed statement about *platform state*, not
  about *computation*.** Exactly one deployed system (Apple PCC) binds model
  weights into its attestation — and deliberately declines to publish them, so
  the binding is a commitment nobody outside Apple can open. **Nothing deployed
  binds "this output came from this model."**
- A **93-artifact, ~1.4 GB audit corpus** was assembled (59 audit PDFs, 29 blog
  texts, the zkbugs dataset with 139 bugs, the 0xPARC tracker). The single
  largest bug class is **Fiat–Shamir transcript ordering** — a public claim not
  absorbed before challenge derivation.
- **The beacon leg is open**: we hold the grinding mechanism and no beacon
  model. `ε_beacon` and `ε_chk` are both uninstantiated.

**Artifacts**: `minidregg/Selvage/AuditSampling.lean` ·
`notes/audit-theorem-statement.md`, `notes/audit-sampling-prior-art.md` ·
`notes/attestable-calibration.md` · `~/paperbin/attestable/` (22 files) ·
`~/paperbin/audit-*` (93 artifacts).

⚑ **The Attestable recon deserves its own line.** Five lanes established the
team, funding, lineage, Vitalik's public comment verbatim, and located,
mirrored and **transcribed a 54-minute founder interview** with whisper
large-v3-turbo. The CEO states the overhead range himself and **it matches our
independent derivation.** That is a calibration point we own and nobody else
has written down.

---

# Pillar 6 — Formalization landscape

**Asked**: what does the formal-methods world already hold, and where are we
actually unique?

**Found**:
- ⚑ **Nobody has machine-checked FRI soundness or the Reed–Solomon proximity
  gap / correlated agreement in the list-decoding (Johnson) regime.** But far
  more exists than expected: ArkLib has the Johnson bound and Guruswami–Sudan.
- **ArkLib's composition theorems are `sorry`.** That is the gap we sit in:
  we hold the **compilation layer** — between "an interactive protocol is
  round-by-round sound" and "a deployed non-interactive verifier accepts only
  true things" — and nobody else has both legs.
- **The Verified-zkEVM effort (ArkLib + CompPoly) is the only serious binary-
  field formalization**, and it is in Lean 4. Everyone else is prime-field.
- ⚑ **StarkWare + Avigad's `formal-proofs` (arXiv 2606.04311) verifies the
  LogUp protocol inside the S-two AIR** — which retracted our framing of our own
  LogUp work as "narrow but unclaimed."
- **CatCrypt** (Spitters, eprint 2026/604) — 172 game-based constructions in
  Lean 4, including FHE-adjacent material.
- ⚑ **`~/dev/minidregg/Selvage` is a 48,522-line, 96-file, zero-`sorry`
  zero-`axiom` Lean formalization of exactly the technique the literature says
  you should adopt** (WARP-style hash-based accumulation with WHIR's
  constrained-RS claim object). A survey lane found that out about *us*.
- **The carrier census / vacuity-detection methodology has a name in two
  literatures**, and its deductive-verification version was published **four
  months ago** (FMCAD 2025) — so the area is live, not closed. This is the
  finding that produced ember's "vacuity-checking is tacit behavior" correction.

**Artifacts**: `notes/formalization-frontier.md` · `notes/avigad-stwo-verdict.md` ·
`notes/vacuity-prior-art.md` · `notes/ingredient-inventory.md` (1,077 lines —
minidregg surveyed as a *library of composable primitives*: 473 files, 16,097
declarations, a name-blinded body-hash twin detector, an island detector) ·
`docs/INGREDIENTS.md`.

---

# `[08-17]` Pillar 7 — EVM decompilation into logic

⚑ **A genuinely new pillar, opened and taken to a landed Stage 0 in one day.**
It is ember's steer, and it is the only direction in this file whose *prize* is
stated in someone else's unit and still comes out two orders of magnitude
ahead.

**Asked**: a zkVM proves *"the machine ran"*. Why are we proving the machine at
all, rather than specializing the interpreter at the program and proving only
what the program means?

**The framing — Futamura for circuits — holds, with two amendments that
strengthen it:**

1. **Circuits have no loops**, so residualization becomes **unroll / fold /
   refuse**: gas statically bounds every EVM loop; the fold is the IVC seam;
   everything else is refused. And classical PE's *"residual interpreter"* **IS
   a switchboard** — so the two techniques are the **static and dynamic halves
   of one mixed computation**, priced per program point by the virtualization
   threshold (§1.7 / `SLVG_THOUGHT.md` §II.1).
2. ⚠ **A self-correction at source**: our 30× attribution was wrong. **Nebula's
   30× is the MEMORY technique; the switchboard is the 260×, at UNCHANGED
   structure — the switchboard never shrinks the machine at all.**
   *Decompilation's case is stronger for it, not weaker.*

**Prior art, with instruments named** (this is an `[ABSENCE]`-shaped claim and
was scoped accordingly): pieces exist — **Buffet 2014** (*"circuits are not
universal"*) · ⚑ **powdr autoprecompiles = automatic PE of zkVM circuits per
basic block, WITH a Lean-4-verified optimizer** (the closest neighbour, and
it is **instruction-anchored and block-granular**, not semantics-anchored) ·
**Singh–McKay PE-of-hardware, 1998** · **EquiVM is the front half alive in
Lean** · **EVMYulLean passes 22,330/22,332 Cancun tests**. **The
semantics-anchored, program-granular, no-machine-left version is unclaimed —
and the back half (proved emission) is exactly `EmitByName` /
`ZkmlEltwiseAir`, which we already hold.**

**The shape**: a **10-constructor residual vocabulary** (an ERC20 transfer is
**15–20 semantic ops from 635 machine steps**; stack, PC, decode and static RAM
all die); correctness stated as `descriptor_means_semantics` **iff** plus
`encode_injective` = *"does ONLY that program"*; trusted base enumerated; and
⚑ **the decompiler itself UNTRUSTED, via per-output translation validation.**
Hard parts routed rather than waved at: jumps → **refuse** (Elipmoc: 99.5% of
real contracts still feasible) · loops → gas-bounded unroll or `SelfEmbedding`
fold · storage → `TwistContinuity` (⚠ **Nebula's memory does NOT port here** —
it needs the free zero-commitment) · calls → one `VerifierEmbedding` rung ·
**gas → refused, with the premise visible.**

**The prize `[DERIVED, their unit]`**: ≈3–4K vs ≈0.25–0.43M active constraints
— **~60–140× beyond the switchboard** — with three honesty clauses stated up
front: keccak is a common ~100× elephant; the win **saturates at our own proof
floor** (`P(b) = 3381·2^b + 766` ⇒ batch transfers); and **Merkle-root binding
would eat the prize.**

## ✅ Stage 0 LANDED (2026-08-17, minidregg `8c5a732`) — five opcodes end to end

⚑ **And the decompilation theorem is literally `rfl`.** With the program
concrete and the calldata symbolic, **the stack, the PC, the decode, MSTORE and
RETURN reduce away DEFINITIONALLY**:

```
fragment_faithful : ∀ cd, evmRun … cd = .ok (beBytes (residual.denote cd))
```

costs the kernel nothing.

> ***The Futamura claim, realized: specialize the interpreter at a program and
> the machine is not proved away — it reduces away.***

Trust lives **only** in the per-output TV pair; **no theorem quantifies over
the decompiler.**

The chain, in order: real 15-byte bytecode · **conformance vectors from a real
EVM** (anvil/revm via `eth_call`; five kernel-decided named theorems including
wraparound and past-the-end calldata) · a **refusing** symbolic-stack
decompiler (STOP, data-dependent offsets and foreign opcodes all refused) ·
**256-bit faced as 16 limbs × 16 bits** (⚑ **8×32 is IMPOSSIBLE — `p < 2³²`**),
with **the ABSENT top-carry pin BEING the mod-2²⁵⁶ semantics** · soundness
*and* completeness with executable Lean witness-gen · the iff descriptor
theorem + `encodeBoundary_injective` · teeth written mutation-first ·
**3,298 gates / 4,131 wires emitted** (231 KB JSON).

⚠ **Two flags carried at the landing, both said loudly:**
- The design note's *"≈3–4K per transfer"* is **Nebula's R1CS unit — NOT
  comparable to these gates.** Range checks (768 wires) are the
  lookup-collapsible dominant term; **re-derive at Stage 3.** *(This is the
  unit-mismatch class from `05-ERROR-CLASSES.md`, caught before it propagated
  rather than after.)*
- ⚑ **`Compiler/EvmAddAir.lean` is COMMITTED BUT UNROOTED from the committed
  umbrella** — `Compiler.lean` carries a sibling lane's *uncommitted* import of
  an untracked file, so the rooting line waits. **The
  gating-defaults-to-silence shape, declared this time instead of discovered
  later.** See `07-ARTIFACTS.md`.

**Artifacts**: `notes/evm-decompilation.md` · `notes/evm-stage0.md` ·
`docs/VERDICTS.md` §3d · `minidregg/Theory/EvmFragment.lean`,
`Theory/EvmResidual.lean`, `Compiler/EvmAddAir.lean`.

---

# Directions that were explored and then simply stopped

Not closed by a number — **stalled**, which is a different thing. Ember swept
for these on 08-13 16:34 and the sweep is worth reproducing, because the *shape*
of the stalls is diagnostic: work dies here when it is (a) small-but-formal
(no lane feels "worth" a 200-line change), (b) deployment glue falling between
pillars, or (c) **gated on something whose gate silently cleared and nobody
re-checked.**

**Gates that cleared without anyone noticing**
- Phase 0′ — the MXFP4 alignment-window *constraint* harness. Gated on the
  Spain/Celer reads; both landed days earlier. The data side is answered
  (width-8 covers 100%); the constraint-count harness was never dispatched.
- The Celer grand-product spike, gated on a re-pricing that landed.

**High-value, fully specified, never dispatched**
- ✅ *The two-regime security calculator* — this one later landed
  (`Assurance/TwoRegimeQueryBudget.lean`).
- **The sponge re-aim: extraction-friendly indifferentiability.** Vanilla
  indifferentiability does not close [FS-ROM] for knowledge soundness; the
  re-aim "gets the first and the closure." Never became a card. ⚑ *Arguably
  Selvage's deepest open formal item.*
- **Verified table contents** — queued since the first week, cheap, zero motion.
- **Chiesa–Orrù Corollary 1 plug** — FRI into the state-restoration framework,
  where our assets are the scarce half.

**Deployment glue for the audit theorem** (the theorem landed; its deployment
did not)
- **The beacon assembly** — `pqvrf` + fhegg's threshold ceremonies = the G=1
  threshold VUF that makes ε_beacon → 0. Nobody has checked `pqvrf`'s state.
- **The inference ledger** — the audit game's Merkle ledger as a minidregg
  Hyperdocument instantiation. The registry covers weights; nobody designed the
  per-turn ledger.
- AuditSampling's own ten named residuals.

**Small-but-formal batch**
`Ext5` (Ext6 buys zero bits by their own lemma) · the hardware rate spreadsheet
(hours of work, "prices everything else", never done) · the `fhegg-rtl`
word-level BitVec layer verdict · G3 ring noise lift · G4 CPA-D/determinism
hinge.

**`[08-17]` Newly stalled, or stalled in a new way**
- ⚑ **An unreconciled contradiction BETWEEN TWO SIBLING NOTES of the same
  night.** `notes/aligned-hash-space.md` §0.3 / §5 / §7.2 still asserts
  `R ≈ 3.2×` for lookup-Blake2s as *"the one route that crosses `R*`"* and
  calls the lookup measurement **"the highest-value open measurement."**
  `notes/lasso-over-logup.md` §2.4 refutes exactly that figure and §6.1 asks
  for the pointer to be marked RESOLVED. **Nobody made the edit.** ⟨inference⟩
  This is the stall shape the campaign is worst at: two lanes running the same
  night, one answering the other's open question, and no third pass to close
  the loop. It cost nothing this time only because both notes are in the same
  directory.
- **The Selvage-side port of the Z_Q sumcheck** (§2.4b) — the note carries the
  exact four-item work order and the line *"Blocker: none mathematical."*
  Repo boundary, not difficulty: `Bfv` is in breadstuffs, `Selvage` in
  minidregg.
- ⚠ **Three committed Lean modules that `lake build` has never compiled** —
  1,593 lines, rooted only by an uncommitted umbrella edit. See
  `07-ARTIFACTS.md` O5; this is the gating-defaults-to-silence class, and only
  one of the three was known.

**Zero motion since first mention**
- ⚑ **`zkQMC`** — "proving randomized computations via quasi-[Monte Carlo]",
  described in-window as *"the mine's genuine surprise"*, **truncated
  mid-sentence by the safety classifier and never picked back up.** No note, no
  lane, no artifact. See `01b-STEERS-RECOVERED.md` §16.
- **The vacuity-methodology blog post** for `~/dev/dregg-site` — ember named
  the venue explicitly; the page was never written.
- **The Twist/Shout one-hot expert-select lane** and **the S-two carrier
  census** — both died to credit exhaustion mid-write-up and were never re-run.
