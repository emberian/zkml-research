# Workstreams — dispatchable cards (steering: ember + Fable; execution: Opus swarms)

Status: QUEUED / IN-FLIGHT / LANDED / BLOCKED(on). Every card names its spec
and gate. Order within tiers = dispatch order.

## Paper 1 — the joint representation (IN-FLIGHT, 4 fable lanes)
red-team re-derivation · modulus-swap experiment · family-law Lean ·
scaffold+claim-ledger. Gate: red team clears; experiment verdict in.

## Build tier (Opus-ready now)
1. **M0 sumcheck wiring** — QUEUED→dispatching. Spec: notes/vfhe-shortest-path.md.
   Gate: product-of-MLEs toy proves+verifies end-to-end at our pin.
2. **Weight registry** — QUEUED→dispatching. Spec: composition B
   (notes/context-window-compositions.md) + range-request technique
   (phase0/e8m0_spread.py). Gate: published commitments for ≥3 Tier-1 models
   + tooling, reproducible.
3. **KPZ encryption fix** — QUEUED. Spec: notes/fhe-scout-verdicts.md item 1.
   Gate: Fheanor depth harness shows depth 1→2.
4. **wgpu fusion toy** — QUEUED. Spec: hpu-seam-study de-risk #3
   (gpu_arena multi-pipeline). Gate: A/B with/without download, measured.
5. **Verified table contents** — QUEUED. Spec: AGENDA pillar V item 1.
6. **Tuple-compression lemma** — QUEUED. Spec: compositions item I.
7. **num_queries pin** — QUEUED. Spec: field-choice-verdict prerequisite.
   (Soundness; field-independent; do before flag day.)

## Verification tier
8. **census-on-Avigad** — QUEUED. Spec: compositions item A. Collegial gift.
9. **KB-vs-Goldilocks recursion benchmark** — QUEUED. Gates the flag day;
   the study exists nowhere.

## Research tier (needs Fable steering before dispatch)
10. **Ring-hash cryptanalysis** — BLOCKED(on: framing a safe adversarial
    brief). Candidate exists (~/src/ring-ro-hash); no security analysis yet.
11. **Three-tree FRI-RBR composition** — QUEUED; window contested.
12. **G-series vFHE gates** (single-prime consequences, N=8192 fork, ring
    noise lift, CPA-D/determinism hinge) — specs in docs/FRONTIER-QUEUE.md.

## Flag day (single re-genesis, when gated items land)
KoalaBear migration + Poseidon2 matrix transpose fix + (pending G1/G2) the
FHE parameter re-choice. Spec: field-choice-verdict + hash-verdict.
