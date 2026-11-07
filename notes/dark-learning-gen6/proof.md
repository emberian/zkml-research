# Gen 6, proof lane: the proof of the deployed step, per-step proofs in the run, the release proof

Owner: proof lane (a02632eb). Code: `native/darkproof` (except the handover files) and research
`cosnark_he.py`, `cosnark_gates.py` (RecEngine.he), `proofwire.py` (program), `darkproof_vectors.py` (flow `he`).
The gen 5 record is in `notes/dark-learning-gen5/proof.md`.

## 1. The proof of the step as deployed (HE matvec + HE outer)

**Construction**, agreed with the coordinator in gen 5:
- **Spine: unchanged.** Its sumchecks and rank-1 checks prove z1 = W1 x, z2 = W2 h, b = W2ᵀ d2 and
  W' = W - d ⊗ v on the committed vectors, whatever the SPDZ-level helpers did.
- **HE entries: digest only.** These entries are bound by the public transcript's digest only:
  - per matvec: d `he_auth`, d Freivalds Beaver products, one `freivalds`;
  - per outer: `he_outer_commit` (value 0), one product, `he_outer_check`.

  RecEngine records them as kind `he:<phase>` and adds no Hadamard rows for their triples, so none of them is in
  MIDDLE_PHASES. The middle's constraint system is the plain step's.
- **Commitment hashes: outside the proof.** The verifier requires every `he_outer_commit` value to be 0. The
  commitment hashes are not field elements and are not in the bundle. They are the SPDZ-level integrity check's
  business, not the proof's.
- **Carried steps.** Step 1 inputs W1, W2, x and y. Steps 2 and later take W1, W2 as the previous step's W1n and W2n
  shares and input only x and y. This is the deploy lane's party loop.
- **Field.** The field is the HE profile's plaintext modulus:
  - demo (N 8192, L 3): `P_DEMO`, which is the harness's prime;
  - ledger (N 16384, L 4): `P_LEDGER` = 2305843009210515457.

  `field::set_p` selects it once per process. The verifier refuses a deployed program over any other field.
- **Ledger genesis.** The genesis record pins `"program": {S1..K3, "he": true}`.

**Bit-exact** (`DL_DETERMINISTIC=7 darkproof_vectors.py VEC d PROFILE he`, then `darkproof check VEC <tag>_he`,
`darkproof_vectors.py verify`, and `darkproof ds-check`). [EXECUTED]

| profile, d | he1 (genesis) | he2 (carried) | he3 (carried) | native ⇄ Python verify | flipped byte | darkstep record → bundle |
|---|---|---|---|---|---|---|
| demo, 4 | equal, 7a2f24e5… (7,615,628 B) | equal, 0552e8ff… | equal, f4be6874… | accept both ways | refused by both | record = harness; bundle equal |
| demo, 16 | equal, bbce47f1… (9,478,868 B) | equal, 8ac9695f… | equal, aea3fd2c… | accept both ways | refused by both | record = harness; bundle equal |
| ledger, 4 / 16 | [OPEN] Python vectors running on bb2 | | | | | |

**The darkstep record check (`ds-check`)** covers darkstep's genesis HE step. Its ideal-dealer tapes carry the
Trhb proof atoms and `deal_proof_section`. The step runs in three custodian threads over darkstep's sockets, and the
proof rides the same Net (tag PROOF) through `run::TcpRef`.
- **Record equals the harness's witness.** Each party's ProofRecord equals it:
  - the alpha share;
  - the public values;
  - the middle atoms, which equal `RecEngine.atom_sh`, Trhb bits included;
  - every wire.
- **Bundle equals Python's bundle.** The bundle that `run::prove_step` builds from the record and the tape equals
  Python's.

## 2. Per-step proofs in the run

`darkproof::run::prove_step(pr, lp, tables, prm, net, ctx, PartyStep, carry) -> StepProof` is one custodian's
share of the proof. It has no dealer and no seed.
- **Inputs.** Its own ProofRecord (`run::from_darkstep`) and its own tape's proof section. That section holds
  `run::tape_triples(lp, d, n_had)` authenticated triples, in this order:
  1. the spine's Beaver products;
  2. the middle's Beaver products;
  3. the spine Ligero's products;
  4. the middle Ligero's products.
- **cozk's polynomial triple** is built pointwise from 2(k + t) - 1 tape triples. Each party picks its own share
  polynomials, and c is interpolated locally.
- **Output.** Every party ends with the same bundle bytes.
- **Threading.** The deploy lane owns it: one proof thread per custodian, fed (step k, record, w1n/w2n, tape
  triples), with the Net shared through Arc.

**`darkproof run-check VEC demo_d4_he`** is a production build: three custodian threads, each with only its own
shares and a seeded stand-in tape. The tape holds authenticated triples under the step's MAC key. [EXECUTED]
- **The chain verifies.** The parties agree, and he1 → he2 → he3 is accepted by the native verifier.
- **Bad c share: refused by the verifier.** A tape triple's c share off by one at one custodian gives a wrong
  product that is MAC-consistent, so proving completes. The verifier then refuses the bundle with
  `middle: Ligero linear test: the constraints do not hold`.
- **Bad a share: aborts in proving.** A tape triple's a share off by one makes the opened e wrong, and the proof
  aborts with `MAC check failed: an opened value is not the authenticated one`.

## Secret coins (audit, 2026-11-07)

**Where every coin comes from.** Every secret coin in darkproof comes from the OS CSPRNG: `rng::Coins::Os`, which
refills from getrandom in 64 KiB blocks. The secret coins are:
- PCS row tails, mask rows and leaf salts;
- cozk row tails, its three mask polynomials and its salts;
- the tape-mode polynomial triples' share polynomials;
- the owner commitment's shares;
- the MAC check's sigma nonce.

**Seeded streams.** `Det` (cosnark.det_rng, `DL_DETERMINISTIC`) is honoured only in builds with the TEST-ONLY
cargo feature `test-det`. Without that feature a `Det` carrying a seed is off. The CLI's bit-exact commands
(`check`, `rows`, `ds-check`) refuse to run without the feature.

**What gen 5 got wrong.** Before this audit the non-hook stream was MT19937 seeded from 256 OS bits. That is not a
CSPRNG: its state is GF(2)-linear in its outputs. `rng::secret_rng` (MT) remains only for the in-process
harness's ideal dealer stream, which the three simulated parties share in `witness::make_bundle`. That stream is
not part of the deployed path, and its doc comment says so.

**Public coins.** These are public by design and are not drawn from the secret coins:
- the Fiat-Shamir challenges (`transcript.rs`);
- the MAC check's coins, a SHA-256 chain over every opening that is fixed after the last broadcast;
- the harness's fixed dealer and HE seeds (`live.rs` and the vector scripts).

**The negative control** runs in a production build (`run-check`): two proofs of the same witness and tape.
[EXECUTED]

| | proof A | proof B |
|---|---|---|
| bytes | 7,615,628 | 7,615,628 |
| equal? | | **differ** |
| genesis roots | fresh | fresh, different |
| native verify (against its own genesis roots) | accept | accept |

## 3. The release (cosnark_release; policy by the train lane)

M public test examples (MNIST t10k 0..63 in the run); only (M, C) leaves custody, C = correctly classified count.
The custodians compute z1 = W1 X locally (X public), u1 = trunc, h = SIG lookup, the class rows' scores by Beaver
products, o = trunc, comparisons trunc(o_l - o_k - 1, 10, 10), ok_t = prod (1 + q_k), and open only C = sum ok_t.
- **The proof.** It is the ZK middle over the release program's record, in batch-friendly order:
  - external vectors W1 and W2 are the ledger head's commitments at their second life;
  - z1 and h are committed fresh;
  - z1 = W1 X is a linear IO constraint per entry, which the native build_q expands densely;
  - the transcript label is release-zk;
  - the context is (model, epoch, head step).
- **The ledger record is terminal.** It holds M, C and the sha256 of the bundle and of the policy. The head's
  commitments have no life left after it, so the ledger then refuses any further step, release or rotation.
- **Code.**
  - Python: `proofwire.encode_release` / `verify_release`, `Ledger.release`.
  - Native: `wire::encode_release` / `verify_release`, `run::release_mpc` / `prove_release`, `ledger::release`.

[EXECUTED] At d = 4, M = 4, head of the native pw chain, the release is byte-identical to Python both without and
with proved bounds:

| proved bounds | sha256 | bytes |
|---|---|---|
| without | 48dff323… | 4,780,998 |
| with | fccb1291… | 5,586,678 |

Python and native verify each other's release with C = 2, which equals the plaintext twin. These are REFUSED:
- a flipped byte;
- the released count raised by one;
- another label set;
- the genesis W1 root in place of the head's.

[EXECUTED] `ds-chain 16 demo 3 8` runs in one process: three custodians over sockets, one test tape each, 3
deployed steps proved and accepted by the native ledger, then the release MPC and proof. The ledger accepts
C = 4 of 8, equal to the plaintext twin, and then refuses a further step.

## 4. Truncation input bounds, PROVED (decision: coordinator, 2026-11-07)

**The control that forced this.** Before the change, the middle proved the SPDZ program as written: each truncation
is the floor of the canonical representative, and each lookup is the interpolated polynomial. The control
(`ds-chain` with `DP_W2SCALE` / `DP_W1SCALE`) showed:
- an out-of-bound z2, e or b g1 + R3 was ACCEPTED (still equal to the integer spec: no wrap);
- an off-table u1 was ACCEPTED with weights that differ from the spec.

**The check.** With program flag RC (genesis `"RC": true`), each truncation c = x + 2^K + r also proves its
declared interval x ∈ [a, a + 2^B):
- z1 uses the table's domain: (T_LO 2^S1, S1 + 8) = (-2^18, 19) in GEN6;
- z2, e, b g1 + R3, the release's scores and its comparisons each use (-2^K, K + 1).

**How it works.** r's bits R are already committed: trb holds the low s bits, trhb the K + 40 - s high bits. c is
public. Let c' = c - (2^K + a), also public. The rows are the borrow chain of c' - r over L = K + 41 bits:
- β_0 = 0, t_i = R_i β_i (a Hadamard row), β_{i+1} = (c'_i ? t_i : R_i + β_i - t_i);
- β_L = 0;
- c'_i - R_i - β_i + 2 β_{i+1} = 0 for i ≥ B.

**Why the check excludes the wrap.**
- R is boolean (Hadamard), so β is boolean by induction. The rows are then exactly integer subtraction: the
  integer c' - r equals Σ_{i<B} 2^i (difference bits), which lies in [0, 2^B).
- In the field, x = c - 2^K - r = (c' - r) + a. That is a small integer in [a, a + 2^B). Its field value equals
  that integer, so x + 2^K + r < p and no reduction mod p happened.
- A public c' outside [0, 2^L) (honest c' < 2^B + 2^(K+40) ≤ 2^L) is refused by name before any proof work.

**Cost per checked truncation.** K + 40 proof-time Beaver products (tape proof section: `run::step_section`,
`run::release_section`), 2(K + 41) proof-only atoms and K + 40 Hadamard rows. Before committing, the custodians
open each truncation's violation indicator: β_L + Σ_{i≥B} difference bits, which is 0 when in bound. If any is
nonzero they refuse to prove, naming the truncation.

**Refusal rows** [EXECUTED], from `ds-chain 16 demo` with `DP_PROGRAM='{"RC": true}'`:

| row | result |
|---|---|
| honest 3-step chain and release | accepted; C = 4 = plaintext twin |
| W2 × 400 (z2, e and b g1 + R3 out of bound) | custodians refuse: `truncation input outside its proved bound: z2[1], z2[12], z2[15], e[1] ...` |
| W1 × 30, × 60 (u1 off the table) | custodians refuse: `... z1[11], ...` / `z1[2], z1[8], ...` |
| W2 × 400, bundle forced (check ignored) | ledger refuses: `middle: Ligero linear test: the constraints do not hold` |
| W1 × 30, bundle forced | ledger refuses (same) |
| release with X × 20 (z1 off the table) | custodians refuse (z1[0..]); forced bundle refused: `release: truncation input outside its proved bound (score[0], public)` |

The verifier's refusal of a forced bundle cannot name the truncation (only the custodians see which one). The
public c' check names it when it fires.

**Privacy note (for the budget).** The check DETECTS a violation; it does not undo the opening that already
happened. A truncation input with |x| > 2^K was opened as c = x + 2^K + r, masked by r < 2^(K+40). That loses about
log2(|x| / 2^K) of the 40 statistical bits for that element; at |x| ≥ 2^(K+40) nothing is masked. A refused step
halts the run: dl-custodian exits with the named reason, and the ledger accepts nothing after it. So the loss is
bounded by one step's openings.

## [OPEN]


- **Ledger-profile bit-exactness.** The ledger-profile HE vectors (d = 4 and 16, `~/lanes/dl-gen6-proof/vec`
  on bb2) are still being generated by Python.
- **The HE step with RC, bit-exact at d = 4.** Running locally: `scratchpad/dl-gen6/proof/he_rc_d4.log`, tag
  `demo_d4_rc_he`.
- **GEN6 three-way agreement.** For the train lane, my proof should ACCEPT native_ref's GEN6 step. Still to do:
  the Python he flow with the GEN6 program plus RC, and native ds-check.
- **The run, on three boxes.** The deploy lane's dl-custodian proves each step over TLS (571825d0, with rc). Then
  the d = 4096 sizes and times in the run, and the release in the run.
- **d = 4096 cost of RC.** Measured on bb2 (`~/lanes/dl-gen6-proof/rc4096_{on,off}.log`, PID file `rc4096.pid`);
  the estimate is +40%.

## Continuation

- **APIs for the deploy lane.** `run::prove_step(pr, lp, tables, prm, net, ctx, PartyStep, carry)` and
  `run::from_darkstep_n`. `run::step_section` sizes each step's tape proof section. For the release:
  `run::release_mpc`, `release_section` and `prove_release`. The ledger side is `ledger::Ledger::{accept, release}`.
- **What it all looks like run end to end:** `ds_chain` in bin/darkproof.rs.
- **Check commands.**
  - Bit-exact checks: `check`, `ds-check`, `rel-check`; they need `--features tcp,test-det`.
  - Production-coin runs: `run-check`, `ds-bench`, `ds-chain`.

- **Vectors.** They live in `scratchpad/dl-gen6/proof/vec` (local) and on bb2 under `~/lanes/dl-gen6-proof/vec`,
  with PID files `he_*.pid` there.
- **Builds.** `target-proof` uses `--features tcp,test-det`; `target-proof-prod` uses `--features tcp`.
