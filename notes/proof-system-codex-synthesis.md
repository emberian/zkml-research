# Cross-model synthesis: proof-system space and Selvage foundations (2026-11-05)

Two exchanges with `codex exec -c model="gpt-6-astra" --sandbox read-only`, run from
`/Users/ember/dev/zkml-research`. The prompts and raw outputs are in this session's scratchpad
(`codex/prompt_{a,b}.txt`, `codex/out_{a,b}.txt`). They were not committed, because the outputs
embed ~10k lines of tool traces. Below is each claim, my check, and the verdict: **ACCEPT**
(verified and adopted), **ACCEPT-QUALIFIED** (adopted with a correction), **REJECT** (refuted,
with reason). Codex used 157k and 69k tokens.

---

## A. Exchange 1: attack Selvage's foundations and the certificate chain

| # | codex claim | my check | verdict |
|---|---|---|---|
| A1 | 0/153 Selvage modules Host-reached; Rust `sumcheck.rs` is a self-declared unverified mirror; challenges caller-supplied (`:31`); `additive_ntt.rs` has no commitment or transcript | census `:36` [READ]; `prover/src/lib.rs` docblock and `hash_kernels.rs` (cSHAKE only, "owns no framing, tree layout, authentication path") [READ] | **ACCEPT**. Critique W7: Selvage is not yet a prover |
| A2 | `PositionBinding` (`Commitment.lean:113`) is perfect binding with no adversary; its only inhabitant is the identity root (`:220-228`); a compressing scheme cannot inhabit it (pigeonhole) | read both sites [READ]. The docstring says binding "rests on collision-resistance in deployment, so it enters as CARRIED STRUCTURE", which concedes the realizer is missing | **ACCEPT**. This is the sharpest foundational point of the day. Critique W4, CERTIFICATES P1. I had read this file in August through a summary and missed it |
| A3 | the audit theorem's bounds are conditional; the honest grindable-beacon instance gives `q = 0` (`AuditSampling.lean:882`); fail-open checking has no positive-rate instance (`:933`) | `grind_honest_q_eq_zero` [READ], whose docstring says so honestly ("vacuity reached honestly") | **ACCEPT-QUALIFIED**. Not a hidden defect: the file names it. But it means the deployed audit guarantee is zero until a non-grindable beacon is instantiated (W8) |
| A4 | the "UD" label outruns the proved one-third event (`ProximityGapUDSharp.lean:54`: `d < (1−3δ)n`); the Johnson branch needs `HaboeckTheorem2` **and** `hPG` and returns MCA-failure evidence, not an FRI acceptance bound (`RateRegimeSelector.lean:62, 157`) | `:54` [READ]; `JohnsonMcaBridge.lean:8` "consume that conclusion as an explicit hypothesis" [READ] | **ACCEPT**. Combined with the ArkLib helper's finding that ArkLib proves full UDR and Johnson MCA, this became the import verdict (W2, W3) |
| A5 | `FriLedger.lean:250, 270` stale (BCIKS20; "neither public"); BCSS25 improves Johnson exceptional slopes `O(n²)→O(n)`; do not transplant circle-FRI numbers | matches VERDICTS §1b 09-04 note [READ]. The `O(n)` claim I did not verify at source | **ACCEPT-QUALIFIED**. Adopted the "second ε_C column, no transplant" rule; tagged the `O(n)` claim [CLAIM] |
| A6 | the absence chain is semantically disconnected before any hash: `Dfa.Statement` has no word, index or root, so `dfa_verify_sound` concludes only `∃ trace accepting` (`Dfa.lean:169, 200`), giving a zero-work "splice" falsifier; `zkOracle_sound` leaves its three inputs independent; whole-word complement ≠ substring absence; Weld8 denotation lane 0 and unrouted; `AttestedQuery` assumes sponge injectivity refuted at the deployed hash; scalar binding ≈ 15.45-bit collision / 30.91-bit second preimage | `Dfa.lean:169-205` [READ, verbatim]; Weld8 header [READ]; zkOracle docstring [READ] | **ACCEPT**, with one correction: codex's "MMR remains scalar" is about the Lean model's abstract `hash : List ℤ → ℤ`. Its bit security is whatever instantiates it (`Blake3Mmr` in Rust ≈ 128-bit). The 15.45 applies at the one-felt Poseidon2 instantiation and at Weld8's lane-0 denotation. This became CERTIFICATES §0 and laws L0, L1 and L3 |
| A7 | FlashProve is stronger end-to-end; Selvage more general compositionally; Selvage's depth/FS transport is genuinely proved (`Depth.lean:1956`, `FiatShamir.lean:512`); neither certifies its native verifier | consistent with the FlashProve helper digest (GAPS gap 14: nothing proved of `cp_verify`) [READ] | **ACCEPT**. Critique §2.3 |

**What exchange 1 changed in my plan.** I had intended CERTIFICATES to start from the existing
Dregg2 theorems and compose them. After A6, it starts from **law L0 (the statement binds the
content)**, because the existing DFA theorem cannot be composed into an absence claim at all.

---

## B. Exchange 2: unoccupied design points and the counts model

| # | codex claim | my check | verdict |
|---|---|---|---|
| B1 | U1 plausibly unoccupied as an integration; strongest objection: at 1% audit a single fraud escapes w.p. 0.99, so it is not per-request correctness | arithmetic trivially right | **ACCEPT**. PROOF-SYSTEM-SPACE U1 now leads with the guarantee change and prices U1-per-request separately |
| B2 | U2 bridge cost: 4 KiB → ≥ 64 BLAKE3 blocks → 896,000 binary constraints; it can exceed the certificate | 4096/64 = 64; × 14,000 = 896,000 [checked] | **ACCEPT**. It pushed me to U3-fused |
| B3 | my "substring as one batched multilinear evaluation" is wrong: it is k Boolean-point evaluations batched by a linear functional, and the terminal opening still scans the document (128× for 32 B in 4 KiB); Reef already does match/non-match on committed documents | the O(n) opening is right for hash PCS [INFERRED]; Reef abstract [READ via search] | **ACCEPT**. Original U3 retired; CERTIFICATES L6 (Merkle openings for a public position) and §6 (Reef as prior art for absence) |
| B4 | U4 per-token folding at Nightstream's 27.5M rows = 28.16B rows for 1,024 tokens | 27,537,894 × 1024 = 2.82e10 [checked] | **ACCEPT**. U4 is refuted per token, viable only block-folded |
| B5 | the GKR branch in `space.py` dropped the virtualized linear-map term, flattering it 8.74× | read my own code: true | **ACCEPT**. Fixed in `space.py`, with a comment naming the catch |
| B6 | new point: proof-carrying prefix/KV DAGs, 14.66× fewer proved positions for 100 × (4096 + 256) | (100·4352)/(4096+100·256) = 435,200/29,696 = 14.66 [checked] | **ACCEPT** as U6. I added the KV-opening cost (2.7e8 values/request under GQA), which codex left as "separate accounting" |
| B7 | new point: delayed teacher-forced block replay; weight-opening share 91.4M → 17.1M/token at block 128; one fold per block = 214,844 rows/token | 27.5M/128 = 2.15e5 [checked]; the 91.4M follows from `space.py`'s weight term | **ACCEPT** as U7, merged with U4 |
| B8 | new point: fuse the policy automaton into inference's output boundary, so no second commitment; 64-state byte DFA = 16,384 entries, 4,096 lookups per 4 KiB | 64 × 256 = 16,384 [checked] | **ACCEPT** as the new U3. **Best idea of the exchange**: it dissolves the bridge problem that U2 and CERTIFICATES L4 pay for, whenever we own the inference prover |
| B9a | model bug: SASH's 79M already includes lookup columns; the script double-counted to 95.59M | true | **ACCEPT**. Fixed (`lookup_cells_included`) |
| B9b | one generic query law cannot price every PCS; accumulation multipliers 0.35/0.25 are placeholders; "65×" was loss/saving, corrected to ×3.21 | the 65×→3.21 retraction is in `LEAF-VS-RECURSION.md`; VERDICTS §4c still prints 65× | **ACCEPT**. The placeholders were already tagged [A]; PROOF-SYSTEM-SPACE U8 uses ×3.21 and flags VERDICTS §4c as stale |
| B9c | optimizing the hardware proxy is wrong when crypto is 5%: infinite crypto speedup = 1.053× | true (Amdahl) | **ACCEPT**. The script now carries a calibrated witness-generation phase, and tensor cores accelerate only `crypto_s`. That is why the space doc reports tc as 1.01× on SASH's shape and 1.49× on U1's |

**One thing codex did not catch, which I then found in my own model:** the `AIR` PIOP had
`virt_mult = 0`, so "boundary-only AIR" was not paying for matmul virtualization. It looked 5×
cheaper than it is. Fixed in `space.py` with a comment.

---

## C. Where I disagree with codex, or go further

1. **Codex's A5 frames the stale ledger as "conservative underclaiming".** For the Johnson column
   that holds. For the **UD column** the deployed number is 34 bits, and the frontier now reports
   UD only (Setty: 100/120 provable UD bits, 2026/1656 §4 and 2026/2423 §6.1). Calling 34 bits
   conservative would be softening. It is the headline (critique §0.1).
2. **Codex treats U9 (wrapping FlashProve) as out of scope; I priced it.** The hash half is about
   15 s on 12 cores at BinarySpartan's rates. The non-native Goldilocks half is unknown and
   probably dominant. The deciding count is one instrumented `cp_verify` run.
3. **On ArkLib, codex had no information** (it read only Selvage and FlashProve). The import
   verdicts in the critique come from the ArkLib helper lane's census plus my toolchain check
   (identical `v4.35.0` and Mathlib `56a00585`), not from codex.

---

## D. Process note

Both exchanges paid for themselves: codex found three real defects in my own artifacts before I
committed them (B5, B9a, and the B3 refutation of my U3), and two load-bearing foundational facts
(A2, A6) that the repo's own notes had not recorded. The pattern that worked: give it **file
paths and the real numbers**, ask for **falsifiers with numbers**, and then **verify every
load-bearing claim at source before adopting it**. One claim needed correction (A6's MMR
scalar) and one needed a tag downgrade (A5's `O(n)`).
