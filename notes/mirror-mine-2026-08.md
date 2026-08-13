# Corpus mine of the local ePrint mirror — 7,090 papers, 2023–2026

2026-08-12. Opus lane, first-2-page cache, zero extraction failures, deduped
against holdings. 20 must-reads copied into `~/paperbin`. What follows is what
changes because of it.

## 1. The proximity-gap race — consequential for the HOME tree, not just zkML

The mine's biggest find was not in the keyword battery: **~12 papers in late
2025/early 2026 on Reed–Solomon proximity gaps, driven by the Ethereum
Proximity Prize, including refutations of conjectures deployed systems rely
on.**

- `2025/2046` (Crites–Stewart) **disproves** correlated-agreement-up-to-capacity,
  WHIR's mutual-CA conjecture, and DEEP-FRI's list-decodability conjecture, and
  proposes minimal repairs.
- `2025/2197` — a generic attack on **small-field hash-based SNARGs** whose
  success scales with list size, aimed at extension codes over small base
  fields. That is our BabyBear/M31 configuration, by name.
- `2025/2055` (Ben-Sasson, Carmon, Haböck, Kopparty, Saraf) — improved positive
  *and* negative results.
- `2026/680` (Arnon, Boneh, Fenzi) — the open-problems survey; a roadmap of
  exactly the correlated-agreement campaign minidregg's Loom ran.

Loom's `HalfThresholdRegime`/`JohnsonRegime` headers already know the 2025–26
literature moved (capacity conjectures refuted; half-threshold needs no
conjecture). **What needs doing: check the four papers against the exact
regimes Loom states, and re-price the "conjectured 130 / proven 51–73" pair in
the breadstuffs FRI-reality record.** These four papers are the source of truth
for that number now.

## 2. A correction to our own record: Attestable DOES publish security accounting

`2026/532` — **S-two whitepaper, by StarkWare *and Attestable***. An M31 IOP
with example parameters given for **both the proven and the conjectured
regime**, citing the 2025 proximity-gap results above.

Our landscape note said Attestable's "100 bits" named "no proof system, field,
hash, or soundness analysis." That was true of their *blog post*; it is not
true of their literature presence. They are S-two co-authors, the field is M31,
and the two-regime accounting is exactly the honest form we said was missing.
Correct the note; and S-two's parameter tables are now the reference for what a
deployed M31 system claims under proven vs conjectured soundness.

## 3. Commit-then-audit has direct ePrint prior art — read before writing

`2026/541` — **Campanelli, Gennaro et al., "Towards Verifiable AI with
Lightweight Cryptographic Proofs of Inference."** Merkle-commits the inference
trace, opens a few randomly sampled output→input paths, and formalizes **trace
separation between functionally dissimilar models** as the security condition.
Explicitly trades soundness for efficiency in the audit deployment.

This is the closest prior art to `missed-threads.md` item 1 and it must be read
before we write our own theorem. Note what it does NOT appear to do: the
`q = p(1−ε_snd) − ε_bind − ε_beacon` composition and the machine-checking. Our
residual claims likely survive, but narrowed again — the pattern of the week.

## 4. The decode-loop folding substrate exists: Neo/SuperNeo

`2026/242` (Nguyen, Setty) — first folding scheme that is **post-quantum,
pay-per-bit, field-native sumcheck over a small field (Goldilocks), general
CCS, low recursion overhead.** That is the missing substrate for
`ml-to-crypto-mappings` item "IVC over the decode loop" — and lattice folding
generally is a live race (LatticeFold+, Cyclo, Lova, Symphony, SALSAA), so the
substrate question will be settled by others while we build on top.

## 5. The beacon term is not a constant

`2025/1974` (iterative grinding capacity) and `2025/037` (RANDAO manipulation):
**if the audit beacon is grindable, `ε_beacon` in our bound is a function of
adversary compute, not a constant.** Any deployment note for the sampling layer
must price grinding — this is exactly the kind of term that gets written as
"negligible" and isn't. (Connects to Relect/SSLE as the transparent-setup
selector.)

## 6. Negative findings — three claims stay clean, one frontier is small

Across 7,090 papers:

- **MoE router binding: zero papers.** Mapping C is the whole literature.
- **LoRA proofs: zero in ePrint** — the NDSS/arXiv cluster we hold is
  everything. Mapping B's inference-side remains open.
- **Microscaling / MX / block float: essentially zero.** Mapping G's co-design
  thread has no cryptographic literature to collide with.
- **Streaming provers: six real papers**, and `2025/1473` just proved the
  time-space tradeoff optimal (O(kN) time / O(N^{1/k}) space, non-adaptive).
  Narrow, tractable, with a fresh theory floor: Scribe (`2024/1970`, disk
  streaming), Jolt-in-small-space (`2025/611`, <2× runtime without recursion),
  Hobbit. The "70B on a 64 GB box" capability is genuinely buildable.

## 7. Kin to the home tree's discipline

- `2026/192` **"Verification Theatre"** — 13 vulnerabilities escaping formal
  verification in libcrux/hpke-rs, **four inside verified spec/proof code**.
  The same class as minidregg's vacuity findings (carrier census, materializer
  emptiness). Worth citing whenever the census discipline needs external
  motivation.
- `2024/1841` — Jolt's Lasso subtable semantics for all RV32I instructions
  **formally verified in ACL2**. The direct precedent for "the lookup table is
  proved correct" (worthwhile work item), and evidence the idea has legs outside our tree.
- `2025/1993` — FRI round-by-round soundness *simplified explicitly to enable
  formal verification*. A bridge paper for Loom.
- `2026/604` **CatCrypt** — 172 protocols machine-checked in Lean, 110 with a
  Rust→Lean (hax) pipeline. The Lean-crypto ecosystem is no longer just
  ArkLib/VCVio.

## 8. Sweep hygiene for next time

"Neural network" is a low-precision keyword: ~60 FHE/MPC private-inference
papers (different problem — input privacy, not execution integrity) and ~40
deep-learning side-channel papers swamp it. Filter both clusters. Verifiable
RAG (`2026/637`, `2026/709`) and zkPoT (SUMMER, ZKBoost, VeriDP…) are new
subfields worth a keyword each in future sweeps.
