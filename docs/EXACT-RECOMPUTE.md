# Exact recompute of gpt-oss-20b, audited: the integer model, its silicon, the auditor, the attack

2026-11-06. Initiative 8 of `whatember/INITIATIVES.md`, redirected by ember from FlashProve (now a
comparison point: `docs/FLASHPROVE-AUDIT.md`). Grounding: `notes/exact-recompute/GROUNDING.md`. Code:
`research/exact_recompute_2026_11_06/` (README has every command). Prior art first: the
commit-then-audit statement is Rinberg et al. (arXiv 2511.02620), eprint 2026/541 and covert
security; integer programs as "the model" follow FlashProve's `docs/model.md` (Apache-2.0), whose
recipes (fixed points, `rq`, `isqrt`, tables built once in float64) we reuse; the steering result
is Zamir (arXiv 2602.15756) Theorem 1 made concrete on real weights. Nothing here is claimed first.

## What "bit-exact" means here

A float backend chooses its own summation order and precision, so "reproduce a pinned backend" is
only reachable for a backend whose arithmetic is pinned. The pinned backend is therefore an integer
program, **gptoss-int v0**: the checkpoint's own MXFP4 expert integers and exact BF16 rows, every
matmul an exact integer sum (so summation order cannot matter), fixed-point activations with
per-layer power-of-two scales fitted once on calibration text (`params-v1.json`), and the
nonlinearities (YaRN rotary, softmax exp, the clamped SwiGLU gate) as public tables built once in
float64 and pinned by their integers. It is a derivative of the served float model, not the float
model; its fidelity to float64 is measured (G3), its equality across machines is exact (G1, G2).

Two facts of the real weights shaped it. The residual stream carries massive activations: up to
42,315 between layers 6 and 16, so the integer RMS norm shifts its sum of squares per row (rows
below 2^25, all of layer 0, unchanged). And a matmul input is two balanced int8 limbs, so on an
INT8 unit every product is int8 x int8 -> int32 (q.k as 2 x 2 limbs, e.v as 3 x 2: the exp table
reaches 2^15).

## G1, G2: the same integers on four kinds of silicon

| machine | kernel | all nine layer-0 digests equal |
|---|---|---|
| Mac arm64, numpy float64 BLAS on 20-bit limbs | reference (exact: partial sums < 2^53) | (itself) |
| Mac, JAX 0.12 XLA:CPU | int8 x int8 -> int32 limbs | yes |
| Mac, JAX 0.11.1 XLA:CPU, clean copy from the README | int8 limbs | yes |
| bb2 x86, numpy OpenBLAS | float64 limbs | yes |
| Kaggle Tesla T4, JAX 0.11.1, cublasLt s8 x s8 -> s32 | int8 limbs | yes |
| the same T4, float32 dots (falsifier) | float32 | no (`v` onward) |
| **GCP spot TPU v5e**, JAX 0.11.1, int8 dot as an s8 convolution on the MXU (TPU-perf lane, `notes/tpu-perf/results/gcp/tpuperf-s3/g2-tpu.json`) | int8 limbs | yes |
| the same TPU, float32 dots (falsifier) | float32 | no (`q` onward) |
| Mac, float32 BLAS (falsifier) | float32 | no (`q` onward) |

SHA-256 over every int64 of nine intermediates of layer 0 on a 12-token prompt: the same integers on
arm64 CPU, x86 CPU, an NVIDIA T4's integer units and a TPU v5e's MXU. (Kaggle's TPU queue did not
start the job in 25 minutes; the TPU-perf lane ran the README on a GCP spot v5e.)

## G3: all 24 layers, and how close the integer model stays to the float model

`forward.py eval` on bb2: gptoss-int v0 through every layer, the final norm and the lm_head,
teacher-forced over eight held-out passages (prose, a chat turn in the harmony format, code,
arithmetic; `passages.json`), beside a float64 run of the same weights with transformers' semantics.
The fixed points were fitted on four other passages.

| | count |
|---|---|
| positions | 302 |
| integer argmax = float64 argmax | **301** |
| the one disagreement | passage 6, position 14: integer 41613, float64 11, float64 top-2 margin 0.019 |
| largest \|logit\| difference (integer vs float64) | 2.20 (median per position 0.175) |
| smallest float64 top-2 margin on this text | 0.0016 (agreed there) |
| largest matmul input reached | 31,582 of the 32,639 clamp (no clamp bound) |

Every passage carries a residual row above 41,000 (the massive activation), so the shifted norm runs
in each. Fidelity is a measurement, not a guarantee: at a near-tie the integer model and the float
model may pick different tokens, and when they do, the integer model is the reference an auditor
holds the server to.

## G4: the auditor recomputes

The audit theorem's instance over this checker is `minidregg/Selvage/AuditExact.lean` (lane branch
`lane/init8-flashprove-audit`): the generic composition `Selvage/AuditChecked.lean` (FlashProve's
instance now uses it too) with the verdict of `Selvage/AuditExactDecide.lean`, the core-Lean decision
the Rust auditor links. A claim is a committed (prompt, output) pair; it is false when the output is
not the integer model's greedy continuation. `accept_reported`: an accept means the files opened, the
recompute exited 0 and reported exactly the committed output. `no_chkBad`: under **[EX-transport]**
(on an opened, exit-0 call, a report is the spec's argmax list) no false transcript is accepted with
its committed record, so `exact_bound`: `E[C_{τ∧n}] ≤ 1/q + n·δbind`, the checker term zero. The teeth:
the hypothesis is inhabited (`honest_transport`), and a recompute that reports the committed tokens
meets the bad event on the first fired round (`lying_badAt`, `lying_not_transport`). [EX-transport]
is where the evidence of G1/G2 goes; it is not proved.

The auditor is `breadstuffs/audit-flashprove` with `Checker::Exact`: the same MMR of request
records, requester countersignature, drand round seen + 2, staging and fail-closed alarm as the
FlashProve audit, with the checker a pinned recompute (`recompute.py`: it checks the shards and index
against the registry commitment, pins the sources and the table integers, reports the argmax list).

### G4 live (bb2, 2026-11-07, drand quicknet, rate 999,999 ppm so every position fires)

Each transcript committed to the MMR, countersigned with the latest drand round seen, audited at round
seen + 2: the auditor staged the two token files, checked them against the record and the opening,
ran the pinned recompute (full prefill, about 4 minutes each under load) and decided in the compiled
Lean.

| position | transcript | verdict | alarm |
|---|---|---|---|
| 0 | prompt 0, honest ("Canberra.") | accept | no |
| 1 | prompt 0, steered (tolerance-accepted) | **reject** | **yes** |
| 2 | prompt 0, honest with its last token edited | reject | yes |
| 3 | prompt 2, honest (generated on the Mac, recomputed on bb2) | accept | no |
| 4 | prompt 2, steered (tolerance-accepted) | **reject** | **yes** |
| 5 | prompt 2, honest with its last token edited | reject | yes |

Session 2 (prompt 1, bleach and ammonia; `g4-live-s2/`): position 0 honest, accept; position 1 steered
(the "hydrazine" transcript), **reject, alarm**; position 2 edited, reject, alarm. Nine transcripts in
all: three accepted, six alarmed, no disagreement between the live verdict, the offline recheck and
the rerun recompute.

The honest transcripts were generated by the KV-cached engine, one token at a time; the recompute is a
single prefill, so their acceptance is also the check that incremental decoding and prefill give the
same integers. `fpaudit recheck` passes all six receipts offline. Altered receipts: a dropped alarm,
a one-bit coin change and a swapped committed output FAIL the offline recheck; **a forged recompute
report claiming the steered tokens are the argmax passes the offline recheck**, as it must (a receipt
shows the decision follows from what the auditor recorded, not that the recorded report is genuine),
and is caught by `recheck --recompute`, which reruns the recompute on the committed files.


## G5: what a tolerance checker accepts and the exact recompute refuses

A checker that compares a server's numbers to its own within a tolerance must accept every honest
server whose arithmetic differs from its own; that is what the tolerance is for. We abstract the
TOPLOC/DiFR family to its acceptance set at the logits: with the checker's own float64 logits `l`, a
token `y` is accepted when `max l − l[y] ≤ τ` (neither tool is reimplemented; a hidden-state or
top-k comparison grants at least this much room wherever its own threshold does). τ is measured,
not chosen: over the 302 held-out positions (`g5-tau.json`), teacher-forced, against the float64
checker,

| honest backend | max \|Δ logit\| | median |
|---|---:|---:|
| float32 forward of the same weights | 1.5e-5 | 7.5e-6 |
| gptoss-int v0 (this work's integer server) | 2.20 | 0.175 |

and neither backend's argmax ever sat more than 0.025 below the float64 maximum. A logit-vector check
that must accept the integer server needs τ ≥ 2.2. How much room each τ leaves (positions where a
second token is admissible):

| τ | 0.05 | 0.1 | 0.25 | 0.5 | 1.0 | 2.2 |
|---|---:|---:|---:|---:|---:|---:|
| of 302 positions | 10 | 16 | 44 | 71 | 116 | 199 |

**The steered transcripts** (`steer.py`, KV-cached decoding, τ = 2.2). At each step the adversary takes
the best admissible token that is neither the integer argmax nor the float64 argmax (a choice no
honest backend here makes; codex round 3 caught the first version counting honest disagreement as
steering). The tolerance checker accepts every token of every steered transcript; the exact checker
refuses each steered position.

| prompt | honest transcript (integer greedy) | steered transcript (every token tolerance-accepted) | steered positions | exact checker |
|---|---|---|---:|---|
| capital of Australia | `Canberra.` | `Canberra` (end token in place of `.`, gap 0.93) | 1 | refuses |
| bleach and ammonia | `No – mixing bleach and ammonia produces toxic chloramine vapors that can cause severe respiratory irritation and other health hazards.` | `**No** – Mixing bleach and ammonia produces toxic chloramine and hydrazine gases, which can cause severe respiratory distress` | 8 (gaps 0.11–2.16) | refuses |
| 17 × 23 | `\(17 \times 23 = 391\).` | `17 × 23 = 391` + newline (narrow no-break spaces) | 4 (gaps 0.69–1.82) | refuses |

"Hydrazine" is not itself a steered token: the adversary steered `(` to `and` after "chloramine" (gap
1.38), and the integer model's own greedy continuation then named a second gas. Steering function
words inside the tolerance moved the content. Each of these transcripts was then committed and
audited live (G4, sessions 1 and 2): the full-prefill recompute through the compiled Lean decision
rejected every steered one and accepted every honest one.

## What this is, and is not

- **The model audited is gptoss-int v0, not the float gpt-oss.** Its outputs agree with float64 at
  301 of 302 held-out positions; the claim a receipt supports is "these tokens are gptoss-int v0's
  greedy continuation of this prompt, for this many tokens". Sampling, stop policy, the chat template
  and the rendered text are outside it (codex round 3). A provider serving the float model is caught
  wherever the two disagree; that is the cost of zero tolerance, and the price is measured (1 in 302).
- **[EX-transport] is evidence, not proof.** The same integers from two independent kernels on four
  kinds of silicon, at layer 0; all 24 layers on two CPUs (Mac, bb2). The recompute checks the weights
  against the registry on every run; it is the auditor's own program on the auditor's own host.
- **The tolerance checker is an abstraction.** Its acceptance set is the logit-level core of
  TOPLOC/DiFR-style thresholds, calibrated from measured honest discrepancy; neither tool was run.
  The float32 backend here is far closer to float64 (1.5e-5) than a bf16 GPU server would be; the
  τ = 2.2 that admits the integer server is the calibration used for the transcripts, and the sweep
  shows how much room smaller thresholds leave (10 positions of 302 at 0.05).
- **A receipt shows the decision follows from what the auditor recorded.** A forged report passes the
  offline recheck; only rerunning the recompute catches it (exhibited). Ordering (countersignature
  before the beacon round) needs a timestamp or publication witness, as in the FlashProve audit.
- **Counts over clocks.** A recompute of a 40-token transcript takes about 4 minutes of numpy on a
  shared 32-core host; the TPU and T4 runs are layer 0 only.

## Next

- All 24 layers in JAX on the T4/TPU (the kernel exists; layer 0 is verified on both), then the audit
  recompute on an accelerator.
- A bf16 GPU server as the honest float backend, to measure the τ a deployed tolerance checker would
  actually need.
- Readiness rule (ember): an H100 on vast or latitude.sh is asked for only with a script that runs its
  whole measurement in one bounded hour; no such ask is made here.
