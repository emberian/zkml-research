# Initiative 8: commit-then-audit over FlashProve, grounding

2026-11-06. Lane: initiative 8 of `whatember/INITIATIVES.md`. This file says what exists, what is
reused, what is replaced and why, and where the bar in the brief is wrong. It is written before any
build. Prior art first, so nobody reads this as a first: the commit-then-audit statement is
Rinberg et al. (arXiv 2511.02620), eprint 2026/541, and covert security (Aumann–Lindell) under six
older names (`notes/audit-sampling-prior-art.md`). What is ours is the machine-checked composition
in `Selvage/AuditSampling.lean`, and what this initiative adds is an instance of it over a real
proof system's real verifier.

## 1. What exists

**The theorem** (minidregg `Selvage/AuditSampling.lean`, 1,173 lines, 0 sorry, 20 axiom pins).
`AuditParams {p, εchk, εbind, εbeacon}`, `q = p(1−εchk) − εbind − εbeacon`. `Round Ω` carries
`corrupt : List Ω → Bool` (cannot read the current coin: commit-before-beacon is in the type),
`fires`, `alarms`, `chkErr`, `chkAbort`, `bindBreak`. `DetectionLegs = BeaconLeg ∧ ChkLeg ∧
BindLeg ∧ MissDecomp`; `Round.detect` (per round `Pr[alarm] ≥ q`); `sequential_bound_of_legs`
(`E[C_{τ∧n}] ≤ 1/q` at every finite horizon, fully adaptive adversary); `FailClosed`,
`FailOpen`, `missDecomp_of_failClosed`, `FailOpenRefutation.failOpen_no_legs`;
`chkLeg_of_product` (the ε_chk leg from checker coins independent of the beacon). §8 names its
residuals, among them **fresh i.i.d. coins per round** and **ChkLeg's product form**, both of
which this instance runs into (§3 below). `Selvage/AuditDisplacement.lean` (main) prices
displacement; not needed for this instance. `Selvage/BindingFixedHash.lean` (main):
`secureAt_false_of_compressing` (an adversary-class binding bound is vacuous at a fixed hash) and
`cert_and_of_collisionExtractor` (the binding term is the probability that one named
deterministic reduction outputs a collision). The Mac checkout of minidregg is 182 commits behind
origin/main; Lean work goes in a lane clone on bb2, not in the shared tree.

**The Rust.** `breadstuffs/dregg-query/src/mmr.rs` is the MMR to reuse: `Mmr<Blake3Mmr>`
(domain-tagged BLAKE3 leaf/node/bag/empty), `open_range`/`verify_range` with the length recomputed
from root-pinned peak heights and directions derived from the offset, and a Lean model
(`metatheory/Dregg2/Lightclient/MMR.lean`, `mroot_injective`, `server_cannot_omit_position`).
`breadstuffs/audit` (4-ary Merkle `AuditLog`, Count/Range/Budget/Consistency proofs) is a token
audit trail, not an audit sampler; `dreggnet-audit` is a bot-envelope JSONL log; the
`degg-research/experiments/inclusion-availability` MMR is zero-dep and has no Lean model. No
sampling auditor exists in Rust anywhere in the tree. `pqvrf` is a **one-time** LB-VRF (Esgin et
al. Set I): one key per evaluation, and whoever holds the key can choose not to publish, so it is
not a public beacon. `blst 0.3.16` is already in the breadstuffs lockfile. The Lean FFI precedent
is `dregg-lean-ffi` (an ~8,200-object Mathlib closure archive); its lesson is not to link Mathlib
for a decision that needs none.

**FlashProve** (cloned at `/Users/ember/src/FlashProve`, 9e2bdd8f, v0.16.0-rc.26; and on bb2 at
`/home/build/fp-audit/FlashProve`). Measured on bb2 today: `verifier/build.sh` built `cp_verify`
in under two minutes (build digest 93afdaf5…9595, matching their README); `examples/accepted-proof`
exit 0 `YES` in 1.67 s / 158 MB; `examples/full-size` (1,001 tokens) exit 0 `YES` in 20.9 s /
3.4 GB. No-verdict probes on the small example: proof file missing → exit 2
(`input-unreadable-proof`); empty proof → exit 1 (`NO: cp-proof-length`); `timeout 0.3` → 124;
`prlimit --nproc=1` → exit 5 (`NOT CHECKED: internal-stage`). Their own limits page says
`cp_verify` follows symlinks and reads each file in full with no time or memory bound, so a
prover-supplied hostile file can force a timeout: the no-verdict path is adversary-reachable, not
only environmental.

**Their theorem** (`lean/THEOREM.md`, `lean/Ladder/Bits.lean:96`): `sound_of_verify_at` bounds,
in the random-oracle model, the probability that `verify` accepts a false claim by
`soundnessErrorInQueries Q 1 = 16·T/2^128 + (T+2)^2/2^256`, `T = Q + 1 + 2^23`, `Q` the
committer's and prover's hash queries (≈ 2^-60 at Q = 2^64). Conditions that bind us: (a) it is
about the Lean `verify`, not `cp_verify` (no theorem about the C++; `lean-verify` evaluates
`verify` at BLAKE2b but takes 19–39 min and 9–16 GB per full-size call); (b) exact match only:
clipped-gap proofs have no theorem of this strength; (c) public files fixed before the hash; (d)
the claim (ID, request, tokens) must be built by the checker's side, not taken from the server;
(e) altered proof bytes that leave the claim untouched can be accepted (9 of 41 in their runs), so
"corrupt" must mean a false claim, never "a byte of the proof changed". Their acceptance rule
(`docs/verifying.md`, "When to accept", 8 points) is the checker predicate, not "exit 0".

## 2. What is reused, what is new, what is replaced

| Need | Use | Why |
|---|---|---|
| ε_bind leg | `dregg-query::mmr::Mmr<Blake3Mmr>`, single-slot `open_range`/`verify_range` | already has a Lean model; a fourth MMR is forbidden |
| binding term | `cert_and_of_collisionExtractor` form: ε_bind := Pr[the named extractor (two openings of one root at one position with different leaves) outputs a BLAKE3 collision] | `SecureAt` is false at a fixed hash |
| ε_beacon leg | drand quicknet (`bls-unchained-g1-rfc9380`, 3 s period; reachable from the Mac and bb2 today), verified with `blst` | public, unique, threshold; `pqvrf` is one-time and key-held |
| ε_chk | their `soundnessErrorInQueries Q 1`, transcribed as a rational with the source hash of `Ladder/Bits.lean` pinned | cannot import their Lean (v4.29.1, separate tree) |
| checker | `cp_verify` under our own time and memory limits | the shipped verifier |
| decision | new core-only Lean module, `@[export]`ed, linked into the Rust auditor | no Rust twin; no Mathlib in the link |
| auditor | new crate `breadstuffs/audit-flashprove` | nothing to extend |

## 3. Where the brief's bar is wrong, and the bar I am setting

**(1) ε_chk does not enter as a per-round `εchk`.** Their bound is over one random oracle shared by
every round and a total query budget Q. `ChkLeg` wants, per round, checker coins independent of the
beacon and fresh each round (`chkLeg_of_product`, residual "fresh coins" of §8). A fixed hash is
neither. Plugging `εchk := soundnessErrorInQueries Q 1` into `AuditParams` is numerically harmless
and formally unjustified. The instance I will prove instead: with the hash fixed, let `Good` be the
event that the checker rejects every false claim the adversary ever submits; on `Good` the
deterministic checker has `εchk = 0` and `sequential_bound_of_legs` gives
`E[C_{τ∧n}] ≤ 1/q₀`, `q₀ = p − εbind − εbeacon`; off `Good`, `C ≤ n`. Averaging,
`E[C_{τ∧n}] ≤ 1/q₀ + n·δ`, `δ = Pr[¬Good] ≤ soundnessErrorInQueries Q 1` by their `sound`. The
horizon appears, honestly: at n = 2^40 rounds and Q = 2^64 the additive term is about 2^-20. This
is the composition their number actually supports.

**(2) Their δ covers `verify`, not `cp_verify`.** The C++/Lean gap is a named transport hypothesis
of the instance, `[FP-chk-transport]`, the analogue of `[AUDIT-chk-anchor]`. I will run
`lean-verify` once on the full-size proof and on one false claim made from it, on bb2, as a spot
anchor; it is evidence, not a discharge.

**(3) Clipped-gap is out.** At a clipped-gap policy no Lean theorem of this strength exists, so the
honest `δ` is 1 and the instance is silent. The decision accepts only exact match (`YES`,
`policy=exact-match`, `sh=8`), and the population is the two exact-match stored proofs.

**(4) Fail-closed means every non-accept, not "exit 1 and exit 5".** Exits 2, 3, 4, 14, 15, 124
(timeout), 137 (killed), a last line that is not exactly `YES`, a `covered:` field that differs
from ours, and a missing proof all alarm. The falsifier is the auditor that treats "no verdict" as
no alarm; its adversary withholds the proof or hands a hostile file, and q collapses to 0
(`failOpen_no_legs`), measured as a count that runs to the horizon.

**(5) The ordering leg needs a clock the prover does not hold.** A fixed schedule "position t is
audited by drand round R0 + t" lets a prover that posts late see the round first. The receipt
therefore binds the audit round to the latest drand round named in the requester's countersigned
commitment plus a margin (Δ = 2 rounds); offline, a re-checker verifies the BLS signature, that
the round equals named-round + Δ, and the MMR opening. What it cannot check offline is that the
requester was honest about the round it had seen; that is the residual ε_beacon carries (drand
threshold honesty plus requester honesty), and the instance states ε_beacon as that named
assumption, not as a computed number. A third falsifier: the commit-after-coin auditor, measured.

**(6) "Real proofs" means: every fired audit is a real `cp_verify` call on real files.** We hold
two exact-match proofs and cannot make more (H100 + 330 GB RAM). The population is N request
records whose honest payload is one of the two stored (request, token, proof) triples, distinct
per position by the record's nonce and position in the MMR; corrupt payloads are false claims built
from them (another reply token, another checked reply token, another prompt token, another
commitment ID, proof withheld, hostile proof). No verdict cache: at corruption fraction f a seed
fires about 1/f audits before its first alarm, so 1,000 seeds at f = 0.25 is about 4,000 calls of
1.7 s, a few minutes on 16 cores. The coin per position is BLAKE3(drand signature of the seed's
round ‖ position), one real drand round per seed; the live path uses one drand round per request.
The expected result is the bound nearly attained (E[C_τ] ≈ 1/p with δ, ε_bind ≈ 0), and the
falsifiers diverging. That is the measurement, not a weakness of it.

## 4. Plan

1. Lean (bb2 lane clone of minidregg): `Selvage/AuditFlashProveDecide.lean` (core only: the
   verdict type, the acceptance rule over exit code, last line and `covered:` fields, `fires` on a
   64-bit coin, `alarm`; `@[export]`); `Selvage/AuditFlashProve.lean` (imports it and
   AuditSampling: the Round built from those exact functions, `FailClosed` proved, the Good-event
   composition, the parameter instance at p ∈ {0.01, 0.05, 0.2}, the fail-open falsifier, axioms
   pinned). Codex attack #1 on it.
2. Rust `breadstuffs/audit-flashprove`: MMR ingest, drand fetch + BLS verify, coin, `cp_verify`
   runner with limits, decision via the Lean export, receipt (MMR root and opening, drand round and
   signature, coin, verdict, cp_verify's last line and `result-v1`), offline `recheck`. Codex
   attack #2 on the fail-closed path.
3. Experiment on bb2; table in `docs/FLASHPROVE-AUDIT.md` and VERDICTS §9.
4. Microsite page under `/Users/ember/src/dregg-microsites/`.
5. Next step needing ember: an H100 run (VCF cluster) to prove fresh requests, so the population is
   not replays of two proofs and corruptions include a cheating prover's output.

## 5. Register row

| 8 | Audit theorem instantiated over FlashProve proofs | init-8 lane | zkml-research, minidregg, breadstuffs | L1 | as brief, with §3: ε_chk as a Good-oracle event (+n·δ), C++/Lean transport named, exact match only, fail-closed on every non-accept, requester-anchored beacon round | Lean instance + codex #1 | 2026-11-06 GROUNDING |
