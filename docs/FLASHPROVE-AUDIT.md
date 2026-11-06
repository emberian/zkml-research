# Commit-then-audit over FlashProve: the theorem instantiated over a real verifier

2026-11-06. Initiative 8 of `whatember/INITIATIVES.md`. Grounding and the bar:
`notes/flashprove-audit/GROUNDING.md`. Prior art first: the commit-then-audit statement is Rinberg
et al. (arXiv 2511.02620), eprint 2026/541 and covert security (Aumann–Lindell); nothing here is
claimed as a first. What is here is the machine-checked composition of
`minidregg/Selvage/AuditSampling.lean` instantiated over FlashProve's shipped verifier `cp_verify`,
with the audit decision compiled from that instance's Lean and measured on real calls.

## What exists, by path

| Piece | Where | State |
|---|---|---|
| Decision, core Lean, `@[export]`ed | minidregg `Selvage/AuditFlashProveDecide.lean` (lane branch `lane/init8-flashprove-audit`) | `fires`, `verdictOf` (FlashProve's acceptance rule), `auditVerdict`, `openingOk`, `auditRoundOk`, `pNumOfPpm`, `alarm` (fail-closed), `alarmOpen` (falsifier) |
| Instance | minidregg `Selvage/AuditFlashProve.lean` | the `Round` built from those constants; `round_failClosed`, `agree_ideal`, `expected_count_le`, `beacon_ideal`, `fpSoundErr`, `flashprove_p001`; teeth `FailOpen.collapse`, `failOpen_beats_bound`; 15 axiom pins, `[propext, Classical.choice, Quot.sound]` |
| Auditor | breadstuffs `audit-flashprove/` (`fpaudit`) | dregg-query BLAKE3 MMR, drand quicknet + blst, staging, `cp_verify` under limits, receipts, offline `recheck`, `experiment` |

## The composed statement

Draw the random oracle once; run `n` rounds, each with a fresh coin. With `p − εb` the per-round
fire probability,

    E[C_{τ∧n}]  ≤  1/(p − εb)  +  n·(δchk + δbind)

(`expected_count_le`). `δchk` is the probability, over the oracle and the run, that a live corrupt
fired round is accepted with its committed record: named **[FP-chk-transport]**, valued by
FlashProve's `sound` at the run-to-one-game reduction's query count, `fpSoundErr(Q + n·(2^23+1))`
(below 2^-59 at `Q = 2^64`, `n = 2^20`: `fpSoundErr_reduction`). `δbind` is the probability that
one named reduction outputs a BLAKE3 or SHA-256 collision from an accepted opening that is not the
served record. The horizon term is the honest price of one oracle shared by every round; the
brief's per-round `εchk` was not justified by a theorem about a shared oracle (GROUNDING §3).

## The table (hbox, 2026-11-06)

Corrupt rounds before the first alarm, mean over seeds, against the ideal 1/p. Every fired audit is a real `cp_verify` call; 27,635 calls in all.

| arm | adversary | p | seeds | mean corrupt before alarm (± s.e.) | 1/p | censored at horizon | cp_verify calls | false claims accepted | honest rounds not accepted |
|---|---|---|---|---|---|---|---|---|---|
| E1-rate-p01 | rate f=0.25, fixed schedule | 0.01 | 1000 | 101.44 ± 3.25 | 100 | 0 of 1000 (n=6000) | 4206 | 0 | 0 |
| E2-rate-p05 | rate f=0.25, fixed schedule | 0.05 | 1000 | 19.68 ± 0.63 | 20 | 0 of 1000 (n=1200) | 3850 | 0 | 0 |
| E3-rate-p20 | rate f=0.25, fixed schedule | 0.20 | 1000 | 4.98 ± 0.13 | 5 | 0 of 1000 (n=300) | 3996 | 0 | 0 |
| E4-burst-p05 | burst: f=0.1 + 20 rounds after each fired audit | 0.05 | 1000 | 19.61 ± 0.60 | 20 | 0 of 1000 (n=1200) | 2300 | 0 | 0 |
| E5-always-p05 | always corrupt | 0.05 | 1000 | 20.69 ± 0.65 | 20 | 0 of 1000 (n=1200) | 1000 | 0 | 0 |
| E6-fullsize-p20 | rate f=0.5, full-size proof (1,001 tokens) | 0.20 | 60 | 3.83 ± 0.37 | 5 | 0 of 60 (n=300) | 103 | 0 | 0 |
| F1-open-p05 | FALSIFIER fail-open: withholds proofs | 0.05 | 200 | 100.11 ± 0.63 | 20 | 200 of 200 (n=400) | 4090 | 0 | 0 |
| F2-peek-p05 | FALSIFIER commit-after-coin | 0.05 | 200 | 379.55 ± 0.31 | 20 | 200 of 200 (n=400) | 4090 | 0 | 0 |

- E1-rate-p01: exits {'0': 3206, '1': 805, '2': 107, 'signal': 88}; verdicts {'Equivocate/Reject': 88, 'Honest/Accept': 3206, 'ReplyToken/Reject': 393, 'Withheld/NoVerdict': 107, 'YToken/Reject': 412}; staging faults 88; call seconds 8317
- E2-rate-p05: exits {'0': 2850, '1': 800, '2': 100, 'signal': 100}; verdicts {'Equivocate/Reject': 100, 'Honest/Accept': 2850, 'ReplyToken/Reject': 368, 'Withheld/NoVerdict': 100, 'YToken/Reject': 432}; staging faults 100; call seconds 4680
- E3-rate-p20: exits {'0': 2996, '1': 819, '2': 81, 'signal': 100}; verdicts {'Equivocate/Reject': 100, 'Honest/Accept': 2996, 'ReplyToken/Reject': 372, 'Withheld/NoVerdict': 81, 'YToken/Reject': 447}; staging faults 100; call seconds 7012
- E4-burst-p05: exits {'0': 1300, '1': 790, '2': 102, 'signal': 108}; verdicts {'Equivocate/Reject': 108, 'Honest/Accept': 1300, 'ReplyToken/Reject': 375, 'Withheld/NoVerdict': 102, 'YToken/Reject': 415}; staging faults 108; call seconds 3974
- E5-always-p05: exits {'1': 784, '2': 107, 'signal': 109}; verdicts {'Equivocate/Reject': 109, 'ReplyToken/Reject': 388, 'Withheld/NoVerdict': 107, 'YToken/Reject': 396}; staging faults 109; call seconds 1090
- E6-fullsize-p20: exits {'0': 43, '1': 49, '2': 7, 'signal': 4}; verdicts {'Equivocate/Reject': 4, 'Honest/Accept': 43, 'ReplyToken/Reject': 20, 'Withheld/NoVerdict': 7, 'YToken/Reject': 29}; staging faults 4; call seconds 1204
- F1-open-p05: exits {'0': 3076, '2': 1014}; verdicts {'Honest/Accept': 3076, 'Withheld/NoVerdict': 1014}; staging faults 0; call seconds 6467
- F2-peek-p05: exits {'0': 4090}; verdicts {'Honest/Accept': 4090}; staging faults 0; call seconds 6465

Reading it. Every closed-arm mean on the small proof is within 1.3 standard errors of 1/p: the bound is attained, as it must be for a checker that accepted no false claim and a fresh coin, and the adaptive burst adversary gains nothing (19.61 against 20). E6 (60 seeds, full-size proof) sits below its bound (3.83 against 5), which an upper bound allows; 60 seeds is a small sample. The falsifiers run to the horizon in every seed: under fail-open the withholding prover served 100 corrupt rounds of 400 with no alarm, and the prover that commits after seeing the coin served 379.55 of 400 with no alarm. "signal" in the exit counts is a call not made because staging refused the handed files (the equivocation kind); each is a failed opening, a rejection, an alarm. Wall clock: 27,635 calls took 46,209 call-seconds on 6 workers (secondary).

## What the measurement is, and is not

- **Real calls, replayed proofs.** Every fired audit ran FlashProve's `cp_verify` (built from
  9e2bdd8f, `build=93afdaf5…9595`, checked by the decision) on files staged by the auditor. The
  honest payload is the stored exact-match proof (`examples/accepted-proof`, 8 synthetic layers,
  r=60, e=64), replayed with a fresh nonce per position; E6 uses `examples/full-size` (1,001 tokens).
  We cannot make new proofs (H100, 330 GB host memory).
- **Corruption means a false claim**, never "a proof byte changed": another next token, another
  checked reply token, a withheld proof (committed as "no proof"), or an equivocation (the record
  commits the honest proof's digest, the provider hands a symlink to `/dev/zero`; staging refuses
  the non-regular file, which is a failed opening). FlashProve's verifier may accept proof edits that
  leave a claim true (their `lean/THEOREM.md`, "Altered proof files"), so those are not corruption.
- **Coins.** One historical drand quicknet round per seed (rounds 30,000,000 + seed, each
  BLS-verified), expanded by position: a simulation of fresh coins, not a deployment. The closed-arm
  adversaries read only a fixed schedule and past fire decisions; `peek` reads the current coin, as
  the ordering falsifier.
- **The comparison is to the ideal `1/p`** (the bound at `εbeacon = 0`); the `n·(δchk + δbind)` term
  is not estimated. The count of false claims accepted is a count over these runs, not a bound on
  `δ`. Seeds that reach the horizon are censored and reported.
- **Counts over clocks.** Wall-clock figures are secondary and come from a shared host.

## Live receipts

`fpaudit live` on hbox, 2026-11-06, a 99.9999% rate so every position fired: positions 0 and 1 (honest)
`accept`, position 2 (false next token, honest proof) `cp_verify` exit 1 `NO: reply-differs`,
`reject`, alarm. `fpaudit recheck` passes all three offline and, with `--rerun`, re-runs
`cp_verify` and agrees. Altered copies: a one-bit coin change, a dropped alarm, an older drand round
and a swapped record digest each FAIL; a **forged accepting transcript passes the offline recheck**
and is caught only by `--rerun` (`RERUN DISAGREES Reject`). A receipt shows the decision follows from
what the auditor recorded, not that it recorded the truth.

## Cross-model attacks (gpt-6-astra, two rounds)

Round 1 (the Lean instance) refuted the first composition (a bad event over every history,
counterfactual branches included; openings fixed before the coin; binding charged to garbage
openings; prose and duplicate tags accepted by the parser) and checked `fpSoundErr` against
FlashProve's `soundnessErrorInQueries` (faithful). Round 2 (the Rust fail-closed path) found staging
failures that bypassed the alarm, stale staged files passing an empty-digest opening, a 100% rate
wrapping to 0%, a timestamp-derived requester key, unbounded output and pipe waits, Rust-side
eligibility rules, and that receipts cannot prove ordering or that the transcript is genuine. All
are repaired (minidregg lane commits after `ad6c678a2`; breadstuffs `3eb0d1853`) except the last two,
which are limits and are stated as such.

## Next step that needs ember: an H100 run (VCF cluster)

What the stored proofs cannot give: fresh proofs of different requests, proofs of a real model, and
a *cheating prover's* output rather than false claims attached to honest proofs. The run:

1. One H100 80 GB, 24 CPUs, ≥ 330 GB host memory, 245 GB disk, CUDA 13.2 U2, gcc 13
   (`README.md`, route 4). Meta's access grant for the calibration set first.
2. Commit Llama 4 Maverick (public 4-bit files) once: about 39 minutes, about 300 GB.
3. Serve N = 2,000 requests at 24 per batch (about 9 s per request; about 5 hours), a fraction f of
   them answered by a cheating front end (another model's token, a sampled non-argmax token, a
   withheld proof), every request committed to the MMR with the requester's countersignature.
4. Audit at p ∈ {0.01, 0.05, 0.2} with live drand rounds (seen + 2); `cp_verify` at about 21 s per
   full-size proof on one thread runs on the CPUs, not the GPU.
5. One `lean-verify` call per arm on a fired false claim, as the transport evidence.

Cost is a few GPU-hours plus commitment; the scarce resource is the 330 GB host. This is a decision
only ember can make (the application to Lucid's VCF cluster).
