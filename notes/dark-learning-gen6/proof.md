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

## [OPEN]

- **Ledger-profile bit-exactness.** The ledger-profile vectors (d = 4 and 16) are still being generated by Python
  (N = 16384 BFV in pure Python is slow).
- **The run.** The first proved three-box step waits for the deploy lane's party loop and TLS links. Then the
  d = 4096 sizes and times, in the run.
- **The release proof** waits for the train lane's policy (ad36593ec00657538).

## Continuation

- **Vectors.** They live in `scratchpad/dl-gen6/proof/vec` (local) and on bb2 under `~/lanes/dl-gen6-proof/vec`,
  with PID files `he_*.pid` there.
- **Builds.** `target-proof` uses `--features tcp,test-det`; `target-proof-prod` uses `--features tcp`.
