# BinarySpartan read at source — the regime-labeled account, the basis verdict, and the push-past map

2026-08-17. DEEP-READ + POSITION lane. Charge: *"read the actual paper and try and push past it,
or understand why it cannot be pushed past."*

> ⚠ 2026-09-04: the eprint has been revised **four times, last 09-03**. v4 reports
> BLAKE3 **872k** / SHA-256 **401k** / Keccak **287k** h/s — 2.13× / 1.83× / 1.76×
> the v1 read below; the mirror and `~/paperbin` hold v1; still **no artifact**
> (gh repo search ∅, abstract carries no URL). Read below as the v1 account.
> `systems-delta-2026-09-04.md` §3.1.

**Source**: eprint 2026/1656, Srinath Setty (Microsoft Research), *"BinarySpartan: Spartan over
binary fields"* — read in full, all 11 pages (10 + Appendix A), from
`~/paperbin/2026-1656-binaryspartan-setty.pdf` (copied from `~/Desktop/2026-1656.pdf`, 283 KB).
Read against: `docs/BINARY-POSITION.md`, `notes/spartan-over-what-we-hold.md`,
`notes/ligerito-exploration.md`, `notes/ring-switching-connectors.md`, `notes/basis-binding.md`,
`notes/lasso-over-logup.md`, `notes/two-regime-calculator.md`, `notes/leaf-vs-recursion.md`.

Provenance legend: **[READ]** quoted from the paper at page cited · **[DERIVED]** my arithmetic
from named inputs · **[INFERRED]** consistent reconstruction the paper does not state ·
**[OURS]** measured/proved in our tree, cited by note.

---

## 0. What the paper is, structurally — read this before any verdict

- **11 pages.** ~4.5 pages of protocol description and related work, ~3 pages of evaluation,
  2.5 pages of references, 1 page of Bitcoin-target appendix.
- ⚑ **Zero theorem environments.** No numbered theorem, lemma, or definition anywhere. The
  entire security argument is ONE paragraph (§3 "Security", p. 5). Same shape as Ligerito
  itself (`ligerito-exploration.md` §0: "no `Theorem` environment anywhere").
- ⚑ **No artifact.** "We implement BinarySpartan as a single Rust crate" [READ p. 5] — and no
  repository URL appears anywhere; the reference list links repos for Binius64, Plonky3,
  Hashcaster, Flock's harness, leanVM, ProveKit, spartan-whir — **not for BinarySpartan.**
- **The paper's own framing is priority, not novelty**: *"BinarySpartan is not a new proof
  system but rather a natural instantiation of Spartan over binary fields"* [READ abstract],
  and *"BinarySpartan includes only optimizations that pre-date Flock"* [READ p. 5]. It is a
  claims-priority paper: Spartan + pre-existing techniques already clears the PQ-Ethereum bar.
- **Ingredients** [READ pp. 1–2]: Spartan [37] + Ligerito [32] as the multilinear PCS +
  Diamond–Posen ring-switching [12]; optimizations: Phalanx SIMD R1CS [41], SuperSpartan's
  `next` MLE [39], Gruen's univariate skip + eq factorization [14], Dao–Thaler decomposed eq
  tables [10 = eprint 2024/1210], Bagad–Dao–Domb–Thaler round computation [2 = 2025/1117],
  Binius64-style position-specific byte tables [19,20].
- **Field** [READ p. 5]: *"Arithmetic is in F_{2^128} modulo x^128 + x^7 + x^2 + x + 1"* —
  the GCM/GHASH polynomial, a **monomial-basis field, not a Fan–Paar tower**. *"The witness is
  a vector of bits: ring-switching packs 2^7 = 128 of them into one field element, so
  committing to 128 witness bits is equivalent to committing to a single field element."*
  κ = 7, exactly the `biniusCubeBasis` shape (`ring-switching-connectors.md` §2), though over
  a non-tower extension — our `cubeBasis` needs only `finrank K L = 2^κ`, which F_{2^128}/F_2
  satisfies, so our connectors cover this instantiation unchanged.
- **Headline numbers, with their conditions attached** [READ abstract + §3]: MacBook Pro M4
  Max, 12 P-cores, no GPU/Metal, witness generation included — BLAKE3 410,166 h/s, SHA-256
  218,735 h/s, Keccak-f 163,375 perm/s (batch peaks 2^15 / 2^15 / 24,576); single SHA-256 of
  2 KiB in 6.15 ms on the EF client-side benchmark.

---

## 1. ⚑ Q1 — The soundness accounting, regime-labeled

### 1.1 What the paper actually configures — the whole paragraph, verbatim [READ p. 5]

> "We target 100 bits of security. We configure Ligerito to recurse until at most 8 variables
> remain, then send the terminal polynomial in the clear. Our soundness accounting assumes
> only the unique-decoding bound, not the wider Johnson radius, and the query count alone
> provides the 100 bits: we run no proof of work, so no grinding is counted. Summing the
> query-consistency and proximity-gap terms over every Ligerito level leaves a soundness
> error of at most 2^{−102.6} at the sizes evaluated here, and the bound stays below 2^{−100}
> up to 2^{28} committed coefficients."

That is the entire security section. What it **states**: regime (UD), grinding (none),
terminal (≤ 8 variables in the clear = ≤ 2^8 coefficients), a total (2^{−102.6}), and a
validity ceiling (2^{28} committed coefficients). What it **omits**: the rate ρ, the query
count, the per-level parameters, the code, the level count, and any derivation. ⚑ **The
security claim is not reproducible from the paper** — there is no theorem, no parameter
table, and no artifact to read the constants out of.

### 1.2 In `TwoRegimeQueryBudget` terms

Our calculator's vocabulary (`two-regime-calculator.md`): regime in the TYPE — UDR
(**proven**), JBR (**idealised**, BCIKS20 at m→∞), CBR (**withdrawn**, DG25/CS25); knobs =
rate, queries, pow bits.

| system, per the paper's own normalization [READ p. 6] | regime | knobs | bits in the proven column |
|---|---|---|---|
| **BinarySpartan** | **UDR** | ρ unstated, q unstated, **pow 0** | **102.6 claimed** (valid ≤ 2^28 coeffs) |
| Flock | **JBR + grinding** — "extends Ligerito to the list-decoding regime, taking distance and proximity gaps up to the Johnson bound with proximity-gap grinding" [READ p. 5] | unstated | "roughly 100" |
| Plonky3 default | **CBR-shaped conjecture** — "targets 113 bits under proximity-gap conjectures and proves only 65" [READ p. 6] | — | **65** |
| Plonky3 as measured | UDR bought with queries — "Flock reconfigures it to 206 queries with 16-bit query grinding to reach roughly 100 proven bits" [READ p. 6] | q 206, pow 16 | ~100 |
| Binius64 / Hashcaster | unstated | — | 96 / 100 targets |

Three observations this table earns:

1. ⚑ **BinarySpartan is the UDR/proven-column system of its own suite, and it says so.**
   "Assumes only the unique-decoding bound, not the wider Johnson radius" is exactly our
   calculator's regime discipline, chosen in the conservative direction. The zkDTVM row of
   our calculator (buy 261 queries at UDR to publish an honest 128) is the same recipe.
2. ⚑ **The paper's baseline-normalization paragraph IS our calculator's type-separation,
   performed by hand in prose.** It refuses to compare Plonky3's conjectured 113 against
   proven numbers, reconfigures it to a proven ~100, measures the slower configuration, and
   discloses that Binius64's 96 makes the margin "if anything understated." A published
   evaluation doing regime hygiene this cleanly is rare and worth citing as precedent.
3. **The regime choice is load-bearing for the comparison with Flock**: at ρ = 1/4, UD buys
   0.678 bits/query ((1+ρ)/2 = 0.625) against Johnson's 1.0 (√ρ = 1/2) — so Flock's
   list-decoding configuration needs ~2/3 the queries for the same bits, before grinding.
   Part of the proof-size gap (§5) and all of the would-be recursion gap (§4) sits in this
   knob, not in prover optimizations.

### 1.3 [DERIVED] The reconstruction, under the one assumption the paper forces

Assuming Ligerito's own default ρ = 1/4 (the paper never states a rate): the corrected UD
base is (1+ρ)/2 = 0.625, i.e. 0.678 bits/query; Ligerito's recipe |S_i| =
⌈−(λ + log ℓ)/log₂ 0.625⌉ gives **148–151 queries per level** at λ = 100 and ℓ = 2–4
levels. "The query count alone provides the 100 bits" at a claimed 102.6 total is consistent
with ~151 queries at ρ = 1/4. **Labeled inference, not fact** — with no rate in the paper,
any (ρ, q) pair on the same curve fits.

### 1.4 ⚑ Does the bound survive the two errata we verified? YES — and it confirms both findings

`ligerito-exploration.md` §1.3 established at source: Ligerito's displayed equations carry
two typos (RS base printed `(m−n−1)/(2m)` instead of `(m+n−1)/(2m)`; general-code summand
missing its `1 −`), both display-only — the paper's own |S_i| = 148 proves §6.4/§7 computed
with the **corrected** base.

- **Erratum 1 (RS base)**: BinarySpartan's numbers are corrected-base numbers. A bound built
  on the printed base would credit 1.415 bits/query — at any query count in the plausible
  range the total would land near 2^{−200}, not 2^{−102.6}, and "query count alone provides
  the 100 bits" would be true at ~half the queries. The claimed figure is only consistent
  with the corrected arithmetic. [DERIVED]
- **Erratum 2 (general-code `1 −`)**: does not touch BinarySpartan — it instantiates
  Ligerito's RS path. (It would touch a general-code variant: 241 queries for 100 bits,
  §1.5 below.)
- ⚑ **The third observation — ours, not an erratum — is affirmatively incorporated, and the
  numbers agree.** Our note computed that Ligerito §6.4's *"|F| ≫ 2^λ so drop the 1/|F|
  terms"* has only **2^28 of headroom** at |F| = 2^128, λ = 100, with the first-round
  m₁k₁/|F| term landing at 2^{−99.5}–2^{−103.8} at N = 2^24 — at or above the query term.
  BinarySpartan does NOT drop those terms: "summing the query-consistency **and
  proximity-gap terms** over every Ligerito level," and its bound **degrades with committed
  size and fails below 100 bits beyond exactly 2^28 committed coefficients.** The paper's
  own validity ceiling is our headroom number. Two independent derivations, same constant.
  [DERIVED both sides; the convergence is the cross-check]
- Scale check [DERIVED]: at the evaluated peak (2^15 SHA-256 × 30,376 constraints ≈ 2^30
  witness bits, ring-switched ÷ 2^7 → ~2^23 committed field elements), linear 1/|F| terms
  sit ~2^{−104}-ish and the stated 2^{−102.6} is query-dominated with the field terms a
  close second — the same "approached from both sides" shape our note derived for Ligerito's
  own parameters.

**Verdict: the accounting is honest, conservative in regime, arithmetically consistent with
the corrected Ligerito bound including the terms Ligerito itself dropped — and completely
unreproducible from the published text.** The regime-labeled reconstruction above is a
contribution the paper leaves for someone else to write, and now it is written.

### 1.5 Priced on OUR proved floor [OURS]

The RS unique-decoding radius d/2 that BinarySpartan's accounting rests on is
Diamond–Gruen Cor 3.7 over **BCIKS Thm 4.1 — the Polishchuk–Spielman leg that
`Selvage/ProximityGapUDTight.lean` holds as a named open hypothesis.** Our unconditional
floor is the d/3 radius (`rs_proximityGap_UD`), which is Ligerito's *general-code* bound.
A machine-checked BinarySpartan on today's proved ground therefore prices at **241 queries
instead of ~148 for 100 bits at ρ = 1/4 — a 1.63× penalty on the Merkle openings**, which
are the dominant communication AND the dominant in-circuit verification cost (§4). Standing
entirely on proved ground costs 1.63×; discharging BCIKS/P–S buys it back. That is the same
sequencing fact `ligerito-exploration.md` §2.3 found, now with a deployed system attached
to the expensive side.

---

## 2. ⚑ Q2 — Ring-switching and the ordered basis: the paper is SILENT, at every layer

The question: does the transcript bind the ordered basis (our `keystone_basis_ambiguity` at
GF(16), D–P's own Cor. 4.5, closed in our tree 2026-08-16 — `basis-binding.md`)?

**The precise answer: the paper contains no transcript at any resolution, so it neither
binds nor fails to bind anything.** Read charitably and exactly:

- The words "Fiat–Shamir," "transcript," and "challenge derivation" **do not occur in the
  paper.** Security rests on "a hash function" [READ abstract]; how challenges are derived
  from commitments is never described.
- The packing basis is never named. The full extent of the packing description is
  *"ring-switching packs 2^7 = 128 of them into one field element"* [READ p. 5] and Fig. 1's
  slot label *"ring-switching: 128 witness bits → 1 field element"*. **Which ordered
  F_2-basis of F_{2^128} carries bit i to which coordinate is unstated** — and since the
  field is monomial-basis F_{2^128} rather than a tower, D–P's tower basis does not even
  apply verbatim; the implementation necessarily chose *some* ordered basis, and the paper
  does not say which, let alone whether anything hashes it.
- Ligerito's evaluation domain and encoder convention (the additive-subspace ordering our
  GF(16) counterexample lives on) are likewise absent — inherited by citation to [32].

**Why this is a finding to state carefully, not a gotcha.** Our counterexample
(`Selvage/AdditiveBaseFold.lean:786`) is: one codeword, one four-point domain over GF(16),
an honest commitment to **two different tables** under two orderings of the same basis —
same span, same evaluation points, same Merkle leaves, different terminal constants. The
consequence (`spanBoundPcs_not_extractable`) is that ring-switching's `Extractable` — the
straight-line Def-2.9 emulator BinarySpartan's own Theorem-3.5 inheritance runs through —
is **FALSE** for any scheme in which the ordered basis is statement-dependent and unbound.
But the hole is **live** only when the basis varies per statement or is negotiated; a
single-implementation system with the basis fixed as a compile-time constant forecloses it
*de facto* — the decode map is pinned by the code rather than by the transcript. Nothing in
the paper says which situation BinarySpartan is in, and with no artifact, nobody can check.

So the verdict, stated at the resolution the evidence supports:

> **BinarySpartan's security paragraph prices query-consistency and proximity terms and
> takes the code — hence the encoder, hence the ordered basis — as given. The object that
> Diamond–Posen's own Corollary 4.5 makes load-bearing ("the domains fold WITH their ordered
> bases"), that broke `Extractable` in our tree until 2026-08-16, and that we closed with
> `basisPrefix` spliced into both sponge inputs, is invisible in the paper at every layer:
> not in the security accounting, not in the protocol description, not in any transcript
> spec, because there is no transcript spec.** For a paper whose soundness inheritance runs
> through D–P Theorem 3.5, the extraction-side precondition of that very theorem is the one
> thing its security paragraph could not have summed, and did not.

What our tree holds that the paper cannot claim: `transcript_determines_table` proved in
both controllers, FALSE before the binding commit; `no_span_indexed_decoder`;
`lchRingSwitchTarget` with `Extractable` discharged and its refutation twin. That pair —
a machine-checked statement that the binding is necessary AND sufficient at the decode
layer — is a genuine past-the-paper contribution, already landed. [OURS, `9679a16`]

---

## 3. Q3 — The optimization triage, settled at source

Our model (`spartan-over-what-we-hold.md` §3) classified Gruen §3 / univariate skip /
Dao–Thaler constraint packing / BDT Alg. 4 as protocol-changes-needing-reproof. What does
the paper apply, and with what soundness statements?

### 3.1 With what soundness statements: NONE

The security paragraph (§1.1 above) prices **only the PCS**. No sumcheck term, no
univariate-skip bound, no Phalanx relation lemma, no composed statement appears anywhere in
the paper. Every optimization's soundness is inherited by citation. (At |F| = 2^128 the
sumcheck-side terms are ~2^{−120} and genuinely negligible — our M6 arithmetic — but the
paper does not say even that.)

### 3.2 ⚑ The two Dao–Thaler papers are different papers, and the triage question dissolves

The brief asked: does the paper carry the tower-basis linear-independence lemma Dao–Thaler
packing needs? **The paper does not use that optimization.** Its reference [10] is
**eprint 2024/1210** ("More optimizations to sum-check proving") — the *decomposed eq
tables*, which that line of work itself states "leave the protocol, verifier, and soundness
unchanged" — **not eprint 2024/1038** (constraint packing, the one that derandomizes 7
coordinates and needs the GF(2)-linear-independence of 128 tower-basis products). Our triage
row for 2024/1038 stands, and BinarySpartan is not evidence about it either way. Structural
corroboration: 2024/1038's packing consumes tower structure, and BinarySpartan's field is
monomial-basis F_{2^128} — it could not apply verbatim.

### 3.3 The settled table

| applied by the paper [READ p. 2, p. 5] | our triage verdict | carried soundness statement in the paper |
|---|---|---|
| Phalanx SIMD R1CS (shared matrices across the batch) | relation change, re-prove from the relation up; its own paper's folding bound is informal | none |
| SuperSpartan `next` MLE (IO consistency across SIMD instances) | soundness-neutral in the IOP, removes indexer-honesty | none |
| Gruen eq factorization (§3) | protocol change, bound improves | none |
| Gruen univariate skip, **first 4 rounds** [READ p. 5] | protocol change, new bound `(d(2^k−1)+(n−k)(d+1))/|G|`, k = 4 | none |
| Dao–Thaler decomposed eq tables (2024/1210) | FREE (prover-side, their own words) | n/a |
| BDT round computation (2025/1117) | FREE except Alg. 4 (trivial re-prove); which parts used is unstated | none |
| Binius64 byte tables | FREE — and the paper's own wording confirms our reading: *"for each byte position, we precompute the 256 subset sums of its basis images and XOR one selected entry per byte"* [READ p. 2] — a memoized public linear map, not a lookup argument | n/a |

Two confirmations worth flagging:

- ⚑ **"BinarySpartan never invokes Spark, Spartan's sparse polynomial commitment"** [READ
  p. 4]: *"Sparse polynomial evaluation proofs do not arise at all: the shared matrices are
  small enough for the verifier to evaluate directly."* This is our M2 verdict — **the
  cheapest path to Spartan does not go through SPARK** — deployed and load-bearing in the
  fastest published binary-field Spartan. Mechanism differs from our `ñext` route (SIMD
  sharing makes the matrices small; `next` handles only the IO chaining) but the conclusion
  is the same one, and the paper's Phalanx paragraph even prices the alternative: "Even if a
  large enough block made Spark worthwhile, it would apply only to the shared matrices, and
  so would scale with the block and not the batch."
- The Phalanx *sub-protocol* for IO consistency is NOT used — `next` replaces it — so the
  informal-folding-bound hole in Phalanx's own paper is dodged, at the price of the
  Holmgren–Rothblum `next` extension, which the paper's Antecedents paragraph correctly
  attributes [READ p. 5].

**Net: our triage classification survives contact unchanged; the paper adds no soundness
content to any row; the one lemma we thought might be owed (tower-basis independence) is
not owed because the optimization that needs it is not the one applied.**

---

## 4. Q4 — Where the prover time goes, and the recursion answer

### 4.1 The breakdown the paper does NOT give

**There is no phase breakdown anywhere in the paper** — no witness-gen vs commit vs
sumcheck vs opening table, no profile, no figure. The complete list of performance-shape
facts [READ p. 6]:

- "BinarySpartan is already **bandwidth-bound** on [the 12 P-cores], so the efficiency
  cores add no headroom" (E-cores change throughput ≤ 2% either way).
- Reported times include witness generation; peaks at batch 2^15 (BLAKE3/SHA-256) and
  24,576 (Keccak); "throughput declines past each peak."
- Circuits: SHA-256 30,376 constraints/compression (31,656 with the tail matrix), BLAKE3
  14,000, Keccak-f 38,400/permutation, three Keccak permutations packed per instance (61% →
  92% fill, ×1.2).

"Bandwidth-bound" is the single profiling word in the paper, and it is the load-bearing
one: a memory-bandwidth-saturated prover on 12 CPU cores is precisely the workload a GPU's
bandwidth advantage moves. The paper concedes the lever explicitly [READ p. 4]: *"All
performance reported in this paper is CPU-only… Doing so can produce a significant increase
in throughput on top of what we report… We expect similar speedups in BinarySpartan when
offloading work to the GPU."* **The push-past map on the prover side cannot be read out of
the paper — it must be measured, and there is no artifact to measure. What can be read is
that the ceiling is bandwidth, which is our wgpu/arena lane's exact axis.** [OURS]

### 4.2 The verifier, concretely [READ pp. 7–8]

- Verification: **2.6 ms** at 2^15 BLAKE3 and at 2^15 SHA-256; **4.7 ms** at 24,576 Keccak.
  "Verifier time grows slowly in the batch size: sixteen times more SHA-256 hashes costs
  1.3×."
- Proof size at a common 2^14 BLAKE3 batch: **519 KiB vs Flock's 357 KiB**. Cause named:
  "BinarySpartan sends an independent Merkle path for every query instead of deduplicating
  the nodes those paths share." gzip −9 as a dedup proxy: 422 KiB vs 355 KiB.
- Terminal: the ≤ 8-variable polynomial in the clear = up to 2^8 · 16 bytes = 4 KiB of the
  proof.

### 4.3 ⚑ The recursion answer (ember's standing question)

**The paper's entire treatment of recursion is one prospective sentence**, in Appendix A's
caveats [READ p. 11]:

> "Keeping the on-chain proof small may also call for recursion: rather than posting a
> single monolithic proof over an entire block, the per-batch proofs would be recursively
> composed into one succinct proof."

Unimplemented, unpriced, not evaluated. So: **BinarySpartan does not support recursion
today; nothing structural forbids it; but every parameter choice it made prices recursion
badly, and our leaf-vs-recursion law says exactly how badly.** [OURS,
`leaf-vs-recursion.md`: ~94% of a wrap's in-circuit cost scales with q × opened columns —
the PCS opening — and the IOP flavor is 0.2% of the bill.]

Four concrete instances of one-shot speed bought at recursion's expense:

1. **UD with pow 0 maximizes q.** Queries are the multiplier on the whole in-circuit bill.
   16 grind bits — costing the prover a 2^16 hash search, invisible against 410k hashes/s —
   would cut ~24 queries (16/0.678) at ρ = 1/4, ~16% of the dominant cost, and the paper
   explicitly runs zero. Flock's Johnson+grinding configuration on the *same PCS* needs
   ~2/3 the queries; the regime knob alone is a ~1.5× in-circuit verifier lever that the
   paper's conservatism leaves on the table. (For a one-shot proof, UD-no-grind is the
   defensible choice; for a recursion leaf it is the wrong end of the curve.)
2. **Un-deduplicated Merkle paths** — the 519-vs-422 KiB gap is redundant hashing that an
   in-circuit verifier would re-perform per path.
3. **Whole-row openings.** Ligero-family queries open entire rows (that is what makes the
   prover commit cheap and the batch throughput high); in-circuit, opened-row width is
   exactly the committed-width term our law says dominates.
4. **A 4 KiB clear terminal** is absorbed transcript, cheap natively, non-trivial
   in-circuit.

And the counterpoint, stated fairly: the verifier is 2.6–4.7 ms native with sub-linear
batch growth — as a **one-shot** system for a prover-side-constrained deployment (the EF
client-side benchmark is exactly that), the configuration is coherent. The paper optimizes
the regime it evaluates. It simply does not evaluate the regime our stack lives in, where
the verifier is the next circuit's workload.

---

## 5. Q5 — The benchmark table, at source

### 5.1 The comparison conditions, exactly [READ p. 6]

> "All measurements are on a MacBook Pro M4 Max with 12 performance cores, 4 efficiency
> cores, and 128 GB of memory, without GPU acceleration, on an otherwise idle machine. We
> run every prover on the 12 performance cores, and leave the efficiency cores idle."

> "We follow Flock's experimental setup: the baselines, their pinned commits, and their
> configurations are Flock's, and we run all of them through Flock's own benchmark harness
> at 8790722, which builds each baseline from its pinned commit and runs it, and which is
> also where we measure Flock itself. That harness pins Binius64 at 8f21b348, Plonky3 at
> 109e95c1, and Hashcaster through the bench-hash-in-snark harness at 1af6fc55; it also
> patches Binius64 to generate its witness in parallel, since its stock witness generator
> is single-threaded, a change in Binius64's favor."

Sweep over batch sizes, each prover's own encoder, **peak reported, best of five
repetitions**, witness generation included, proof sizes uncompressed bincode. Table 1
(12 threads): Flock 805,556 / 384,714 / 290,068 vs BinarySpartan 410,166 / 218,735 /
163,375 (BLAKE3 / SHA-256 / Keccak-f). Table 2 (single SHA-256, ms): BinarySpartan
3.32–6.15 across 128 B–2 KiB, vs Flock 24.26–26.01, Binius64 49.31–62.02, Vega_SC
24.65–104.19, Vega_MC 25.35–44.23 — with the disclosure that **"Binius64 and both Vega
configurations are zero-knowledge, which BinarySpartan and Flock are not"** and the Vega
columns are online-phase-only.

### 5.2 Our position's benchmark scrutiny, re-judged against the paper

| BINARY-POSITION.md claim | verdict at the paper |
|---|---|
| "The EF harness runs on an M1/8-core, not an M4 Max" — our M1 measurements differed | **DISSOLVES.** All numbers are same-machine M4 Max through one pinned harness; the slide's numbers are the paper's own runs, not the EF repo's CI. Our M1 numbers were a different machine answering a different question. |
| "The slide's 'Vega 44.2' corresponds to spartan2 at 541.72 ms" | **REFUTED as an identification.** Vega 44.23 is Table 2's Vega_MC at 2 KiB — a real measured system [22, Kaviani–Setty, S&P 2026], not a mislabeled spartan2. |
| ⚑ "Vega is P-256+Hyrax — discrete-log in a post-quantum table" | **Applies to the slide, not the paper.** The paper never claims Vega is PQ; Table 2 is a latency table, and its caption discloses the asymmetry in *both* directions ("Vega targets statements over signed data… its native 256-bit field arithmetic is an advantage on that workload that the binary-field provers here lack. This comparison does not reflect it."). The substantive point (Vega is not a PQ system) is uncontradicted; the *rhetorical* sin was the slide's framing and is absent from the paper. |
| ⚑ "Flock 82k/core × cores beats 410k in aggregate — it wins outright" | **CONCEDED AND MEASURED by the paper itself**: Table 1 has Flock 1.96×/1.76×/1.78× higher, stated in the abstract-adjacent text ("under 2× lower than Flock's"). The paper's answer is priority + additivity: "BinarySpartan includes only optimizations that pre-date Flock… Those optimizations are additive rather than structural, so applying them to BinarySpartan would eliminate the gap" [READ p. 5]. ⚠ That additivity claim is asserted, not demonstrated — and it elides the regime difference (§1.2): part of Flock's edge is JBR-vs-UDR configuration of the same PCS, which is not an "optimization" one applies but a soundness-accounting choice. |
| "6.2 ms and 219k h/s differ by ~41× — quoting them together is the error" | **Mostly avoided in the paper.** Both appear in the abstract, but each carries its condition (batch throughput vs single-hash latency), the sections are separate, peak batch sizes are disclosed, and "Flock is optimized for throughput, not necessarily for latency" names the trade explicitly. The B=1-vs-batched pair is presented as a pair, not laundered into one number. |

**Residual scrutiny that stands**: peak-of-sweep + best-of-five is favorable-point
reporting (disclosed, but a median-over-runs system would look worse); the gzip proxy for
path dedup is a proxy; and the security levels being *close* (96–100–~100–~100) is managed
in prose rather than equalized. None of these is the slide's class of error. **The paper's
evaluation section is markedly more careful than the slide that preceded it, and most of
our scrutiny was scrutiny of the slide.**

---

## 6. ⚑ Q6 — The push-past verdict, in four parts

### (a) What it leaves on the table

1. **GPU/Metal** — conceded in its own §"GPU/Metal proving", with the Flock-Metal contest
   as precedent. A bandwidth-bound CPU prover is the best possible starting point for the
   claim that the unspent lever is large. Our wgpu/arena work is on exactly this axis.
2. **Recursion** — one prospective sentence (§4.3). The whole leaf-vs-recursion axis —
   where our measured law says the game is q × opened width — is unplayed.
3. **The regime knob** — UD/pow-0 is the most query-expensive point on the curve; Johnson +
   grinding on the same PCS is demonstrated by Flock in the same table. Even staying
   UDR-proven, 16 pow bits ≈ −16% queries for a trivial grind.
4. **Batching regime** — the 6.15 ms/B=1 and 219k/s/B=2^15 pair brackets a curve the paper
   reports only the endpoints of; nothing between, no crossover.
5. **Proof-size engineering** — path dedup (519→~422 KiB left to gzip), terminal size.
6. **Zero-knowledge** — absent, disclosed (Binius64 and Vega have it).
7. **The 2^28 ceiling** — beyond 2^28 committed coefficients the stated accounting fails
   its own 100-bit bar; larger statements need a parameter change the paper does not
   discuss (more queries, or grinding, or a bigger field).
8. **E-core scheduling** ("future work"), and per-core efficiency generally — Flock's
   own single-core number (82k, its abstract) against BinarySpartan's ~34k/thread at 12.

### (b) What we add in kind that it cannot claim — verified, not presumed

**Confirmed: the paper has zero formal content.** No theorem environment, no lemma, no
stated bound beyond one prose paragraph, no transcript specification, no artifact. That is
not a criticism of its genre — it is a fast-systems paper — but it fixes what
parity-in-kind means. Against it we hold, machine-checked and green:

- The corrected Ligerito bound **as theorems** with the errata refutations
  (`printed_rs_bound_is_optimistic`, `LigeritoInterleaved.lean`), where the paper's
  accounting is one unreproducible paragraph over the same mathematics.
- The regime calculator with **the regime in the type** (`TwoRegimeQueryBudget.lean`) —
  §1.2's table is the paper's normalization paragraph made mechanical.
- **The ordered-basis binding closed in both directions** (`basis-binding.md`) — the
  extraction precondition of the very theorem (D–P 3.5) the paper's security inherits,
  which the paper cannot even state for lack of a transcript object.
- Spartan's two reductions composed against a **deployed-shape** verifier
  (`spartan_sound`, no honest side in the acceptance predicate), the ring-switching
  connectors with `packEquiv.symm` as the extractor, and the char-2 wall named, refuted
  as satisfiable-and-refutable, and detector-gated.

### (c) The honest gap list — ours, to parity-in-kind

What a machine-checked BinarySpartan-shaped stack still needs from our tree, priced by the
binder findings (several items cheaper than the pre-August estimates):

1. **[SPARTAN-pcs] the Ligerito opening protocol** — 12 named lemmas
   (`ligerito-exploration.md` §4), of which **one is substantial** (DG24 Thm 3.1, the
   ℓ = m interleaved proximity gap); A6/A7 are the binder-class retypings already shown
   cosmetic; the interleaved code object and column metric are **landed**.
2. **The d/2 leg or the 1.63× toll** (§1.5): BCIKS/Polishchuk–Spielman behind
   `ProximityGapUDTight`, or 241 queries on the proved d/3 floor. This is the one place the
   paper's exact configuration and our proved ground genuinely diverge.
3. **`RingSwitchSecure` assembly** — the two named legs (`ring-switching-connectors.md`
   §6): marginalization plumbing + the degree-2 sumcheck over A·t′ connected to the tensor
   row/column decompositions. The SZ leg and the extractor direction are already
   discharged.
4. **M3 Fiat–Shamir** of the composed two-phase protocol — and note our transcript work is
   *ahead* of the paper here: we have a transcript object with the basis bound; it has none.
5. **M5 knowledge soundness** — mitigated by exactly the paper's own stack: D–P Def 2.9 is
   straight-line (no rewinding), which is why it composes; the remaining obligation is the
   proximity realization of `Extractable` (`basis-binding.md` §7.2 residual: decode-map
   well-definedness is proved; FRI/Merkle realization is not).
6. **The SIMD relation + `next`** — Phalanx's shared-matrix relation (its own paper's
   informal folding bound is dodged if, like BinarySpartan, we use `next` for IO), the
   Holmgren–Rothblum closed form, and a trace/row notion `Compiler/Air.lean` still lacks.
7. **Gruen §3 + univariate-skip re-proofs** (k = 4) — real, bounded, cited-not-novel.
8. **Calculator growth**: a Ligerito-shaped term family (per-level query base + the k/|F|
   legs) beside the FRI-shaped one; the sumcheck-legs knob already named in
   `lasso-over-logup.md` §6.3.
9. ⚑ **The prover.** PROVEN-IN-LEAN ≠ ROUTABLE: there is no Ligerito prover, no
   ring-switching witness path, no SIMD R1CS witness-gen anywhere in our tree. The paper is
   above all an *implementation* result (bandwidth-bound at 410k hashes/s); that entire
   layer is BUILD for us, not route.

### (d) What refutes or supersedes something we hold — looked for hard

1. **Refuted: BINARY-POSITION's Vega-as-spartan2 identification** (§5.2). The note should
   be corrected: Vega 44.2 is Vega_MC measured at 2 KiB on the paper's M4 Max, online
   phase only.
2. **Superseded: the M1-harness discrepancy** as a criticism of the numbers — the paper's
   are same-machine, pinned-commit, one-harness measurements. Our M1 data points are
   obsolete for this comparison.
3. **Confirmed against us — nothing found.** Looked specifically for: a soundness statement
   contradicting the corrected Ligerito bound (none — consistent, §1.4); a transcript
   construction contradicting the basis-binding necessity (none — silent, §2); a use of
   Dao–Thaler packing that would test our tower-lemma claim (not used, §3.2); a lookup
   *argument* behind the byte tables (confirmed prover-side memoization, §3.3); a Spark
   deployment contradicting the ñext/uniformity reroute (opposite — "never invokes Spark",
   §3.3); a recursion result contradicting leaf-vs-recursion (none exists, §4.3).
4. **Two of our findings independently corroborated by the paper's own numbers**: the
   corrected-base arithmetic (its 102.6 is a corrected-base number) and the 2^28 field-term
   headroom (its own validity ceiling, §1.4). The paper is, unknowingly, the second witness
   to both.

---

## 7. The one-breath summary

**BinarySpartan can be pushed past, and the paper itself names the directions: it is a
bandwidth-bound, CPU-only, one-shot, UD-regime, non-recursive, formally-unspecified
instantiation whose security paragraph is honest but unreproducible.** Its genuine
contributions — the priority demonstration that pre-Flock techniques clear 200k hashes/s,
the cleanest regime-normalization prose in any evaluation we have read, and the deployed
proof that Spartan-without-Spark works — all survive scrutiny, and two of its numbers
independently corroborate our Ligerito errata arithmetic. What it cannot claim is exactly
what we build: the machine-checked layer (the corrected bound as theorems, the regime in
the type, the ordered-basis binding its own inherited Theorem 3.5 silently requires), and
the two levers it concedes or ignores (GPU bandwidth; the recursion regime, where its
UD/pow-0/whole-row/no-dedup choices are each the wrong end of the measured in-circuit cost
law). The honest toll for parity on proved ground is one substantial lemma (DG24 3.1),
one open classical leg (P–S at d/2, or a 1.63× query toll), and an entire prover that is
BUILD, not route.
