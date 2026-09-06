# notes/ — what is in here and how to read it

**Start with `docs/VERDICTS.md`.** It is the single current-truth file: what we
believe now, in final form, no history, no ⚠ markers. Open questions are its §7.

> **The rule: where a note and VERDICTS disagree, VERDICTS wins and the note is
> history.** Notes are *evidence* — what a lane measured, derived, or read at
> source. VERDICTS is the *conclusion*. Cite a note for its measurement; cite
> VERDICTS for what we think.

**When a note is wrong, the fix is ordering, not deletion.** Current truth goes
at the top, superseded reasoning stays below it, and every measurement is kept —
a refuted claim with its refutation attached is how we stop re-deriving it. If a
file's *central* claim dies, it moves to `archive/` rather than being edited into
something it never said.

---

## The five things that were contradicting each other, and where they now live

| question | answer | files that hold it |
|---|---|---|
| **Is the prover hash-bound?** | ⚑ **OPEN.** Derived 94% at lb=6, measured 19–40% at ρ=1/2. One profiling run settles it. VERDICTS §7.1 | `prover-floor.md` (derived side), `fast-systems-recon.md` (measured side) — both lead with the contradiction |
| **Which field?** | **BabyBear deployed, both trees. KoalaBear recommended and UNEXECUTED.** Never "our KoalaBear parameters" | `field-choice-verdict.md`, `hash-verdict.md`, `koalabear-limb*.md` |
| **"Conjectured 130"?** | **CBR-shaped, from a regime deleted upstream. Never quote it.** Ours is UDR 34 / JBR 73 | `two-regime-calculator.md`, `grey-lit-corrections.md` §4 |
| **The `fold_add` ratio** | **= B, PROVER-SIDE ONLY**, and deployed B is **4** (4.2×), not 512 | `fold-as-opening-verdict.md`, `fold-as-opening.md` §0 |
| **eprint 2026/1390** | A **lookup-specific restricted-model separation** — *not* a general Ω(m) commitment floor. The floor we hold is the `Ω(\|w\|)` extraction argument | `boundary-statements.md` §2.5(b), `virtualization-verdict.md` §4 |

## Evidence — what each file measured

**Prover cost and proof-system design**
- `prover-floor.md` — the cost function per committed felt; sumcheck is 2–17% of prover time; lb=6 is 2.9× off the optimum
- `fast-systems-recon.md` — six systems read at source, hashing/LDE timed here; the base→ext 2.95× cliff; our soundness posture against five production systems
- `boundary-statements.md` + `virtualization-verdict.md` — the exchange rate: one committed base felt ≈ 3,120 mults at lb=4, 12,331 at lb=6; virtualizing one ≈ 40/layer
- `two-regime-calculator.md` — the regime in the type, 22 theorems, 0 sorry; the CBR withdrawal
- `multilinear-pcs-landscape.md` + `multilinear-pcs-verdict.md` — the seam is one `RbrKnowledgeSoundness` instance; route is BaseFold at RS
- `gkr-substrate-design.md` + `gkr-substrate-findings.md` — the Lean-authored substrate design; our proximity leg has no query-count term
- `fold-as-opening.md` + `fold-as-opening-verdict.md` — built and measured; three of four briefed numbers wrong
- `formalization-frontier.md` — ArkLib measured: 416 sorry-tainted declarations, 133 security results
- `avigad-stwo-verdict.md` — the StarkWare/Avigad formalization is the twin, and carries a real theorem anyway
- `lookup-ram-verdicts.md` — the lookup/RAM frontier, both halves; the three-member one-hot law (Twist/Shout is closed to our stack, by its authors)
- `spain-celer-verdicts.md`, `ozaki-limbs-verdict.md` — read at source, both rejected as imports with the reason kept
- `field-choice-verdict.md`, `hash-verdict.md`, `field-recursion-evidence.md`, `koalabear-limb*.md`, `poseidon2-audit-verdict.md` — the field/hash campaign
- `grey-lit-corrections.md` — five of our verdicts refuted from outside the eprint corpus
- `sis-lattice-verdict.md`, `two-ladder-composition.md`, `shared-arithmetic.md`, `system-primitives.md`, `joint-representation.md` — adjacent design threads

**FHE / vFHE**
- `h2-verdict.md` — measured both directions: 109-bit joint prime is a net loss, 61-bit wins, costs one depth level
- `coeff-matmul-landed.md` — built: 12 bits/matmul split-sign, depth 2 after, 466 µs at 512×31
- `fhe-core-theory.md` — the secret is CBD(20); the honest security ledger
- `kpz-noop-and-the-model-gap.md` — the KPZ fix is a no-op, derived and measured
- `fhe-scout-verdicts.md` — the FHE frontier scan with its coverage gaps named
- `hpu-seam-study.md` — 162,770 lines of Zama SystemVerilog read; the ring is ℤ/2⁶⁴
- `ring-hash-design.md`, `ring-hash-cryptanalysis.md`, `ring-hash-{build,tau}-verdict.md`, `ring-hash-scripts/` — build it, τ=2; FS 52% → 4%

**zkML**
- `moe-router-binding.md` (+ `-cost.py`) — router binding must be zero-knowledge; expert selections recover 91% of tokens
- `ml-systems-corrections.md`, `kv-cache-correction.md` — append-dominant KV is true of the computation, false of serving
- `ml-to-crypto-mappings.md`, `speedup-ledger.md` — the mapping tricks and every measured speedup in one place
- `float-in-zk-three-regimes.md` — the three regimes; ⚠ its bf16 framing is superseded
- `zkml-landscape.md`, `zkml-integration-architecture.md`, `catgrad-seam.md` — the open position, and where the pillar lives
- `attestable-calibration.md` — the overhead number is a baseline choice, not a measurement
- `audit-sampling-prior-art.md`, `audit-theorem-statement.md`, `impl-readiness.md` — the audit game: prior art, the Lean spec, and what is mechanically verified
- `zkqmc-read.md` — eprint 2022/1007 read in full (2026-09-04): a prover-held quasi-random shift is `BeaconRefutation` (ε_beacon = p, q ≤ 0), a warden-secret shift is learned from ≈ ℓ/log₂(1/p) observed fires; trap for audit selection, real-but-off-axis for the paper's own claim
- `rank1-gradient-check.md` — a linear layer's gradient is CHECKED, not proved: the MLE of an outer product factors, so no sumcheck round at all; Lean-authored, measured at 4096×4096, and honest that it removes the n² proof but not the n² commitment

**Deltas, 2026-09-04** (what moved outside since 08-18, each with corpus+instrument):
`proximity-delta-2026-09-04.md` (BCSS25's personal communications are 2026/532 and
2025/2110; Plonky3 labels our 130 "legacy"; nothing moves UDR 34 / JBR 73),
`systems-delta-2026-09-04.md` (PR #1982 merged; leanVM v0.10 binary+BLAKE2s;
BinarySpartan v4; Jolt to lattice PCS; Plonky3 v0.7.0 has GKR), `formal-delta-2026-09-04.md`
(ArkLib 416→314 tainted, statements admitted not absent; better.codes; VCVio Merkle extractability),
`hash-delta-2026-09-04.md` (no hash verdict moves; 2026/1792's compression-mode trail
window is 16 ≥ R_P=13 at our Merkle internal node — cost at our prime uncomputed;
1760 is a rules artefact and a design rule), `eprint-delta-2026-09-04.md` (all 142
ids 1719–1861 triaged: 19 relevant, 19 maybe; 1838 FS-on-program-generated-instances
is a new requirement for the EVM route; 1835 k-tree regime missing from BRIEF 3),
`nst-1792-at-our-node.md` (+ `gsr-scripts/nst_1792.py`) — 1792's cost model reproduced
58/58 + 21/21 with no fitted constant, then evaluated at our Merkle node: ≥ 2^511.9,
R_P=20 changes nothing at the floor; the binding quantity is d=8 × the p−2 cap, not R_P.

**Algebra candidates, 2026-09-04** (the joint-algebra question, `swarm/ASTRA-ALGEBRA-PROMPT.md`):
`circle-aligned-vfhe.md` (+ `circle-scripts/circle_m31.py`) — M31's negacyclic NTT and the
circle STARK share one twiddle table exactly, and it buys nothing: the BFV relation is
coefficient-domain; cosmetic. `galois-ring-stack.md` (+ `galois-scripts/`) — Z/2^64 as one
algebra is a trap: residue-field soundness (1/64 per challenge bit), local ring so challenge
sets have size ≤ 2, T-function hashes (preimage kill test ran); by-products: q = 2^64−257 is
load-bearing, rescale at power-of-two q is a shift. `inert-cyclotomic-tower.md` (+
`galois-scripts/inert_tower.py`) — the Φ_{3⁸} tower dissolves the residue-field obstruction and
dies on dense GR(2⁶⁴,162) proof messages (270–480× per mult); by-product: commit-to-the-ciphertext
at 5.5×. `astra-algebra-read.md` — the adversarial read of the external model's answer: what it
corrected in us, what we priced, what it got wrong. `exceptional-set-lean.md` — the
Lean side (minidregg `Theory/ExceptionalSetLocalRing.lean`, `Theory/CyclotomicExceptionalSet.lean`):
exceptional sets ⟺ injective residues over any local hom into a field, the ceiling |A| ≤ |residue
field|, fixed-weight sets over (ZMod n)[X]/(f) for p | n | pᵉ via `AdjoinRoot`, counting C(deg f, h)
over any monic f, conductor 6561 proved; teeth on ZMod 4 and (ZMod 4)[X]/(X²+1). `lova-neo-rmfe-read.md` (+
`galois-scripts/rmfe_toy.py`) — Lova read at source (q = 2^64, unstructured SIS, t = 330,
16–47 MB/fold: the unstructured PQ fold is outside VERDICTS §3c's 4–50× band); Neo now has
implementations (Nightstream) but still no verifier constraint count; RMFE toy verified,
rates 0.279 at D = 2. `nightstream-read.md` — Nightstream's Lean audited at main and tip: 5,621
theorems, 0 sorry, 185 native_decide, a paper twin plus R1CS layout, no FS/BCS/depth theorem; the
recursive step costs 27,537,894 rows by their own theorem; "both legs" stands. `dual-mode-ideal-quotient-gate.md` (+ `ring-hash-scripts/ideal_quotient_gate.py`)
— the CRT-slot congruence gate on both full modes at the real modulus: both escape; σ₃₁ is the
Frobenius; the τ=2 cost row is mis-counted. `descriptor-reader-scout.md` — what d55ef32/b297c7d
deleted and why (quoted), the emit→consume map (the Stage-0 descriptor JSON has no consumer),
the lawful build brief (Lean witness fill + exhibits; generated-glue reader; p3 as throwaway
oracle), and the blocker: `GateMleExt6.lean:246 CommittedTerminal` has no realizer.
`unit-witness-census.md` — every soundness/knowledge/extraction declaration in Selvage classified K/S/U/H
with consumers: the genuine extractors are never wired into any `RbrKnowledgeSoundness.extract`, the deployed
2⁻⁵⁵ sums only (S)/CR bounds, the IVC tower's `KnowledgeSound` has identity extractors and zero consumers;
top-3 upgrades named with exact statement changes. `fold-extractor-upgrade.md` — upgrade 3 resolved
the other way: FoldRoundBound is false for every extractor (zero-absorb attack, proved at toy and
production); the carried-witness reduction has error 0 at the cost of succinctness and half the capacity.

**The learn/infer-only resident (2026-09-06)** — `swarm/astra-handoff/` holds the external
handoff + our companion; `streaming-fe-credential-audit.md` — the SFE writer state IS the inner
master secret: appending and reading are the same credential (dissertation §3.2 = GKS23 §6.2,
derived path reproduced); not a theorem break, a structural mismatch with the host-appends model.
`pre-constrained-encryption-read.md` — PCE is one-hop: sPCE fixes every function at setup, the learn
chain dies at hop two; delegating PCE with closure needs general-circuit constraints = iO (the paper
says so); the extractor warning confirmed and sharpened; DARK-TRAINING §6 reclassified to tier-C custody.
`private-trace-lemma.md` — minidregg `Theory/PrivateTrace.lean`: trace privacy from a preserved relation
(no axioms), the byte toy honest (equal HIGH bit), +1 as the preservation falsifier, recovery in 8 decided
by kernel and 7 insufficient for every policy.

**Sweeps and corpora** — `mirror-mine-2026-08.md`, `inspiration-sweep{,-cc,-pl}.md`,
`inspiration-verdicts.md`, `vacuity-prior-art.md`. Each names its corpus AND its
instrument; absence claims are only as good as those two lines.

**Method and process** — `soundness-theater-correction.md`, `the-absence-problem.md`,
`missed-threads.md`, `context-window-compositions.md`, `window-review-2026-08-13.md`,
`what-remains.md`, `kpz-noop-and-the-model-gap.md` §"model gap". Keep as-is; they are
about how the work went, not what is true.

## archive/

**History, not truth. Do not cite it.** Files whose central claim died, kept
whole with their reasoning and measurements, each labelled with what replaced
it. `archive/README.md` is the table.
