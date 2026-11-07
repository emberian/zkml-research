# Gen 6, proof lane: the proof of the deployed step, per-step proofs in the run, the release proof

Owner: proof lane (a02632eb; gen 6 successor from §8 on). Code: `native/darkproof` (except the handover files) and research
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
| ledger, 4 / 16 | see §8 | | | | | |

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

## 5. Proof-time triples: the zerocheck cut, counts, authentication

**The cut.** The zerocheck draws ONE Beaver product per live pair per round, down from four per padded pair
(cosnark_gates_zk.zround, middle::zc_round):
- f·g is quadratic in X, so its values at X = 0 and 1 are already known. In round 0 they are the C atoms. In later
  rounds they are the previous round's pair products interpolated at r.
- X = 2 is the one product; X = 3 follows by interpolation.
- Pairs inside the zero padding are zero.
- Soundness does not depend on how the prover computed its values, since the verifier's final check uses the
  PCS evaluations of A, B and C.
- `middle::beaver_count(n) = Σ_i ceil(n_i / 2)`, with n_0 = n and n_(i+1) = ceil(n_i / 2).
- [EXECUTED] Byte-identical with Python: `rel-check` demo d = 4 (2daefc89), and the HE steps below.

**Counts per custodian** at d = 4096, GEN6 (`darkproof counts 4096 ledger`):

| section | gen 5 method | now |
|---|---|---|
| step, no RC | 16,831,944 | 2,291,149 |
| step, RC: spine | | 53,235 = 13(d - 1) |
| step, RC: range products | | 905,216 = 221 d |
| step, RC: zerocheck | | 3,141,633 |
| step, RC: Ligero | | 1,497 |
| step, RC: total | | 4,101,581 |
| release, M = 64, RC: zerocheck | 536,870,908 | 105,275,336 |
| release, M = 64, RC: total | | 120,545,778 |

Row formulas:
- A step's n_had is d [254 + Σ_truncs (K + 40 + 2(s - 1)) + 1], plus d Σ_truncs (K + 39) with RC.
- A checked truncation adds K + 39 range products.
- The Ligero uses 2(2(k + t) - 1) + 7 products.

**Authentication** (coordinator's decision, following my default).
- **Authenticated (SPDZ, MAC-checked before the bundle leaves custody):** spine, zerocheck and range products.
  Without MACs, a custodian could add δ to its share of an opened e = x - a. The product becomes xy + δ y, so the
  proof fails iff y ≠ 0. That is a selective-failure zero test on a secret operand (a mask bit, a borrow bit, a
  lookup power, or "these 2^i consecutive atoms are all zero"; folding by r does not remove it, since zero atoms
  stay zero). With MACs the check aborts independently of the secret.
- **Unauthenticated:** only the Ligero's 1,497 products. Their operands are PCS evaluations combined with uniformly
  random tail coefficients, so an operand is 0 with probability 1/p and a zero test on it reveals nothing.

**d = 4096, GEN6, RC on vs off** [EXECUTED]. The runs were on bb2 (three custodians in one process, 8 threads
each, shared box) with the gen 5 zerocheck. Proof time is within noise:

| | proof | bundle | verify |
|---|---|---|---|
| RC on | 405.7 s | 520,030,532 B | 10.5 s accept |
| RC off | 437.0 s | 519,350,924 B | 8.9 s accept |

The PCS commitments of the d² matrices dominate. Peak RSS was 21.0 GB vs 19.6 GB.

## 6. GEN6 agreement (train lane's request) [EXECUTED]

- **Inputs.** The deployed step under GEN6 + RC at d = 64, demo HE profile, with native_ref.inputs_for(64, GEN6).
- **Agreement.** The Python reference (cosnark_he over RecEngine), darkstep's record and the native proof agree:
  - the record equals the harness's witness: 17,803 public values and 44,096 middle atoms;
  - the bundle is byte-identical (sha256 052e5156…, 13,456,604 B);
  - Python verifies the native bundle and refuses a flipped byte.
- **HE + RC at d = 4.** Steps he1, he2 and he3 are byte-identical (eac6a540…, f8be9d38…, e9240e7f…), and so is
  ds-check.

## 7. The lookup: LogUp priced, and the alternative (analysis, not built)

**LogUp is not cheaper here.** With secret lookup inputs, LogUp needs these, per element unless noted:
- **Inverses** w = 1/(α - v) on the secret v, by masked inversion: one random authenticated value, one Beaver
  product and one opening (of (α - v) ρ, which is uniform). Plus one Hadamard row for w (α - v) = 1.
- **Multiplicities** m_t over the table, which must stay committed and hidden. The custodians would have to compute
  them in MPC. That is a histogram of secret values: an equality test of each element against each of the 256
  entries, or building every element's 8-bit eq basis (255 products per element), or an MPC sort. Each of these
  costs at least as much as the 254-row power chain.

So LogUp at our sizes does NOT beat the power chain. Stopped there, as the condition said.

**The cheaper route: a bit circuit on the bits the range check already proves.**
- With RC, the z1 truncation's borrow chain yields the bits of z1 + 2^18 as linear forms. Its top 8 bits are
  exactly the table index u1 + 128.
- So h = SIG[u1] = clamp(floor(u1 / 4), -7, 7) and g1 = DSIG[u1] = [-28 ≤ u1 < 32] can be proved by a small
  circuit on those bits:
  - two comparisons of a 6-bit value with constants, plus 2 products, for h;
  - two 8-bit window comparisons for g1;
  - about 27 products per element in all, instead of 254.
- The step's MPC keeps its masked-power lookup. The proof then checks h and g1 against u1 directly, so the power
  atoms no longer need well-formedness rows.

Estimated savings:

| | rows per element now | rows per element with the circuit | saving |
|---|---|---|---|
| step | 767 d | ≈ 540 d | about 30% |
| release | 391 d M | ≈ 164 d M | 2.4x fewer rows |

The release case cuts its 105M zerocheck triples to about 45M. It is table-specific (SIG/DSIG), Python reference
first. **[OPEN] awaiting the coordinator's go.**

## 8. The remaining vectors (bb2), range check on [EXECUTED]

Each row runs `darkproof check VEC TAG`, `darkproof ds-check VEC TAG` (built with `--features tcp,test-det`) and
`darkproof_vectors.py verify VEC TAG`, on bb2 under `~/lanes/dl-gen6-proof` (`checks.sh`):

| vectors | program | steps | result |
|---|---|---|---|
| demo_d16_rc_he | harness + RC | 3 | EQUAL (5bac7b9b…, 668f9c12…, faeb753a…), ds-check EQUAL, Python accepts native, flipped byte refused |
| demo_d16_g6rc_he | GEN6 + RC, native_ref.inputs_for(16, GEN6) | 3 | EQUAL (899121f7…, 2b86f102…, 8a9c73cc…), 16,004 proof-section triples; ds-check and Python verify PASS |
| ledger_d4_rc_he | harness + RC, ledger profile | 2 | EQUAL (ea37453d…, 71d36899…), ds-check and Python verify PASS |
| ledger_d4_he, ledger_d16_he (non-RC) | harness | 3 | first set DIFFER: generated at 03:10-03:52 UTC, before the zerocheck cut reached bb2's Python (04:11). Regenerated: EQUAL (d = 4: 2c2b6de9…, 4b938185…, 5415a1c9…; d = 16: 5ab9a9ec…, f91f21f1…, 4634a892…), ds-check and Python verify PASS (x_j = j + 1 domain) |

## 9. The lookup by a bit circuit (program flag "LB"; coordinator's GO) [EXECUTED]

**What it proves.** With RC on, z1's borrow chain already proves the integer z1 - a in [0, 2^(s1 + 8)), where
a = t_lo 2^s1. It does so through the difference bits diff_i = c'_i - R_i - beta_i + 2 beta_(i+1). Each diff_i is
boolean, because the chain is integer subtraction: diff_i = c'_i xor R_i xor beta_i, given the borrow rows. The top
8 bits are v = u1 - t_lo, the table index. Per lookup, after the range rows:
- v_j = diff_(s1 + j) for j < 8: 8 atoms, each with a linear row;
- w = v >> 2 (an atom) and q = t_lo / 4;
- lo = [w < -7 - q], Bf = [w < 8 - q];
- h = w Bf - w lo + (q - 7) Bf - (q + 7) lo + 7, which is clamp(floor(u1 / 4), -7, 7) = SIG[u1];
- g1 = [v < 32 - t_lo] - [v < -28 - t_lo] = DSIG[u1] (the step only; the release has no g1 column);
- the rows tie this h and g1 to the external atoms h[k], g1[k].

**The comparisons.** Each comparison with a public constant is a bit chain, least significant bit first:
lt_(i+1) = c_i ? 1 - b_i + b_i lt_i : lt_i - b_i lt_i, with constants folded. A product b * v whose v has more than
one atom first makes v an atom.

**Cost.** At GEN6 (t_lo = -128) each element costs:
- 16 proof-time Beaver products and 16 Hadamard rows (9 for the release's h alone);
- 37 atoms and 23 linear rows.

That replaces 255 power atoms and 254 Hadamard rows. The products run level by level: the circuit's depth is 6, so
6 rounds batched over every lookup.

**Requirements.** "LB" needs "RC", t_lo divisible by 4, and z1's default interval. The replay refuses anything else
(`Short::Program`).

**What changes and what does not.**
- **The MPC is unchanged.** The masked-power lookup still runs.
- **Only the proof's view changes.**
  - The lookup's opening has kind `lookup-lb`, outside MIDDLE_PHASES, so the power atoms enter no middle
    constraint.
  - The outputs are the external atoms themselves.
  - darkstep's ProofRecord still carries the powers; `Rec::witness_atoms` drops that block (`lp_drop`).
- **Code.**
  - Python: `cosnark_gates.append_lookup` / `fill_lookup` (RecEngine `lb`, `lb_req`, `lb_rows`), Prog `lb`
    (genesis "LB").
  - Native: `step::Rec::append_lookup`, `middle::fill_lookup`, `Rec::proof_products` (every section count uses it),
    `StepParams.lb`.
  - The ledger's genesis writer pins "LB". That pin was missing in cebe43b4 and is fixed in d0b170b7.

**Bit-exact** (cebe43b4):

| vectors | steps | sha256 | rows |
|---|---|---|---|
| demo_d4_lb_he (harness + RC + LB) | 3 | efb4c5ff…, b9f1d61a…, 00ae29f8… | check, ds-check (darkstep record → bundle), Python verify PASS |
| demo_d16_lb_he | 3 | 20686bd3…, 0f927186…, 404f2263… | PASS; 11,109 triples (RC alone: 14,662) |
| demo_d16_g6lb_he (GEN6 + RC + LB) | 3 | 2f69b7f6…, 395c7e1a…, b4ec6512… | PASS; 12,458 triples (RC alone: 16,004), 6,944 middle atoms (11,024) |
| ledger_d4 release (RC + LB, M = 4) | | ac21fa45… (17,712,782 B) | rel-check EQUAL. Python and native accept each other, C = 2 = plaintext twin. Refused: a flipped byte, C + 1, another label set, the genesis W1 |

**Refusal rows.**
- **h or g1 off by one.** A colluding custodian set shifts lookup 1's h (or g1) share by one, MAC-consistently (MAC
  share + alpha). `DP_ATTACK=lb_h` / `lb_g1` exercises it.
  - The MPC's MAC check passes.
  - Python refuses: `middle: Ligero linear test`, first violated row "linear batch".
  - Native refuses the Python bundle the same way.
  - Native's own bundle for that witness is byte-identical.
- **Off-table u1, refused by the range check** (`ds-chain 16 demo 2 8`, RC + LB):
  - with W1 × 30 or × 60, the custodians refuse with `truncation input outside its proved bound: z1[11], ...`;
  - the forced bundle is refused by the ledger (`middle: Ligero linear test`).
- **Plaintext check of the circuit** (`scratchpad/dl-gen6/proof/lb_plain.py`):
  - all 256 inputs satisfy every row with the honest h and g1, at four programs: (t_lo, s1) = (-128, 11),
    (-128, 5), (-64, 5), (-200, 6);
  - all 256 fail with h + 1, with h - 1, and with g1 flipped.

**Counts and times at d = 4096**: §11.

## 10. Public genesis (program "PG"; the deploy lane's request, the coordinator's decision) [EXECUTED]

**The setup.** The initial weights are public: W = darktrain::init(train_genesis_gen6.json). They enter custody as
the public constant: custodian 0's share is W, the others hold 0, and the MAC shares are alpha_i W.
`StepParams.pg` = sha256 of the cfg's bytes, pinned in genesis as "PG". With it every step is the carried
program, step 1's parent being W's public commitment.

**The pieces.**
- `run::public_genesis(pr, d, i, w1, w2, n) -> (carry, roots)`.
  - Its commitments use PUBLIC coins: `rng::Coins::Public`, SHA-256 in counter mode keyed by the share's hash
    (`PcsParty::commit_public`).
  - So every custodian and every verifier computes the same roots.
  - Equal shares commit equally, so the cost is two d² commitments whatever n.
  - Hiding is not needed: W is public, and step 1's openings of it reveal combinations of public rows.
- `Ledger::check_public_genesis(cfg)`.
  - It checks the cfg's hash against the pinned one.
  - It recomputes W and its commitment, and compares them to the genesis roots.
  - Until it succeeds the ledger accepts no step and no release (fail closed). darkproof's `tcp` feature now pulls
    in darktrain for this.
- `prove_step` refuses a public-genesis step 1 without the carry.
- Native only: Python's proofwire has no PG.

**Run** (`DP_PG_CFG=<a d = 16 darktrain cfg> ds-chain 16 demo 3 8`, RC + LB, production coins):
- **Accepted:** three proved steps and the release. C = 1 = plaintext twin, and the ledger then refuses a further
  step.
- **Refused:**

| attempt | refusal |
|---|---|
| a step before the cfg check | `public genesis not checked against its cfg` |
| another cfg (one byte appended) | `the cfg is not the one the genesis record pins` |
| the roots of another W (W1[0][0] + 1) under the pinned cfg | `the genesis roots are not the public commitment of the cfg's W` |
| custody holding W1 + e_00 under the true public commitment (`DP_PG_TAMPER`) | the ledger refuses step 1: `spine: Ligero linear test` |

## 11. d = 4096, GEN6: counts and the timed rerun on the new zerocheck [EXECUTED]

**Counts** (`DP_PROGRAM='{GEN6, "RC": true[, "LB": true]}' darkproof counts 4096 ledger`, per custodian; the same for a
carried step):

| | RC | RC + LB | |
|---|---|---|---|
| step Hadamard rows | 3,141,632 = 767 d | 2,166,784 = 529 d | estimate was 540 d |
| step middle atoms | 4,665,344 | 3,772,416 | |
| step: spine Beaver | 53,235 = 13(d - 1) | 53,235 | |
| step: range products | 905,216 = 221 d | 905,216 | |
| step: lookup products | 0 | 65,536 = 16 d | |
| step: zerocheck | 3,141,633 | 2,166,791 | |
| step: Ligero (unauthenticated) | 1,497 | 1,497 | |
| **step section** (`run::step_section`) | **4,101,581** | **3,192,275** | -22% |
| release M = 64: Hadamard rows | 105,275,328 | 41,050,048 | 245 fewer per lookup (254 → 9) |
| release: range products | 15,269,696 | 15,269,696 | |
| release: lookup products | 0 | 2,359,296 = 9 d M | |
| release: zerocheck | 105,275,336 | 41,050,055 | estimate was about 45M |
| **release section** (`run::release_section`) | **120,545,778** | **58,679,793** | 2.05x fewer |

**Section formulas** (GEN6, LB; t = the program's checked truncations, each with its K and s):
- **step:** 13(d - 1) + d Σ_t (K + 39) + 16 d + beaver_count(n_had) + 2(2(k + t) - 1) + 7,
  where n_had = d [16 + Σ_t (K + 40 + 2(s - 1)) + 1] + d Σ_t (K + 39);
- **release:** the same with 9 per lookup in place of 16.
- 16 and 9 are GEN6's comparison constants (t_lo = -128). Other t_lo give other counts: `Rec::lookup_products`.
- beaver_count(n) = Σ_i ceil(n_i / 2), with n_0 = n and n_(i+1) = ceil(n_i / 2), which is about n.

**Timed rerun** (bb2, `rc4096b.sh`): three custodians in one process, 8 threads each, `ds-bench 4096 ledger`. The
box was shared:
- before: load 12.2, 94 GB available, the other tenant's ACL2 (sbcl ×7), clang, Lean and two of my single-core
  Python jobs;
- during: load about 30 (`rc4096b_box.log`).

| | gen 5 zerocheck, RC (§5) | new zerocheck, RC | new zerocheck, RC + LB |
|---|---|---|---|
| prove | 405.7 s (load about 12) | 466.5 s | 408.2 s |
| of which: spine commitments, middle vectors and commitments | 148.4 s, 69.1 s | 163.1 s, 76.1 s | 169.3 s, 49.6 s |
| bundle | 520,030,532 B | 520,030,532 B | 519,350,924 B |
| verify | 10.5 s accept | 10.5 s accept | 6.9 s accept |
| proof sent per custodian (both peers) | 733.6 MB | 297.2 MB | 267.7 MB |
| triples per custodian | 17,737,160 | 4,101,581 | 3,192,275 |
| peak RSS (all three) | 21.0 GB | 16.4 GB | 15.4 GB |

**What the numbers say.**
- The commitments of the d² matrices dominate the prover; the triple cuts do not move them.
- The zerocheck cut shows up in the bytes on the wire: 734 → 297 MB per custodian.
- LB shows up in the middle's commitments (fewer atoms and rows) and in verify time.
- The bundle size is set by power-of-two padding and the d² PCS. Per link and direction a custodian sends about half
  of "proof sent": about 134 MB per step with LB.

## 12. Proving fast: the PCS on a coset domain by NTT (coordinator's request) [EXECUTED]

**Where the time went.** The PCS encoded every row by naive evaluation at x_j = j + 1, a dot product with the powers
of x_j per column. That is R w npts multiply-adds per commitment: 4098 · 4714 · 18856 ≈ 3.6·10^11 for one d² matrix
at d = 4096 (ledger: hide 618, blow 4). The commitments were 169 s + 50 s of the 408 s proof.

**The domain** (profile parameter DOMAIN = "coset" for ledger and demo; "ledger-int" / "demo-int" keep the old points;
28769b6a).
- **The points.** The HE plaintext moduli are NTT-friendly: p_ledger - 1 has 2-adicity 15, p_demo - 1 has 14. The
  points are x_j = z^t ω^i with (t, i) = (j div 2^k, j mod 2^k). That is T disjoint cosets z^t H of the order-2^k
  subgroup H, each in natural NTT order.
- **The parameters** (`cosnark.coset_params`, `pcs::coset_params`):
  - k minimises T (2^(k-1) k + w), ties to the larger k;
  - ω = h^((p-1)/2^k), with h the least quadratic non-residue ≥ 2, so ω has order exactly 2^k;
  - z is the least a ≥ 2 with a^t ∉ H for 0 < t < T.
  - At d = 4096, ledger: k = 12, T = 5, z = 2.
- **Encoding.** Natively each row is encoded by one NTT per coset: the coefficients are scaled by c^i, c = z^t, and
  folded mod 2^k. The work runs in blocks of 64 rows, written into the column-major codeword. The codeword is held
  until the commitment's first opening (`open_batch`) and re-encoded once for a later life.
- **What follows the points.** Every check at an opened column computes the point as `Dom::point(j)`: the PCS
  proximity test, the spine and middle evaluation consistency, and handover (through the shared code).

**Soundness and hiding are unchanged.**
- **The code.** It is Reed-Solomon of dimension w on npts = blow · w distinct points, so it is MDS with distance
  npts - w + 1, whatever the distinct points. Its rate is 1/blow = 1/4 as before.
- **Proximity and column soundness.** Both depend only on the rate and distance, and on T_COLS = 309 opened columns:
  (3/4)^309 = 2^-128.25 for the ledger, as before.
- **Hiding.** Each row's tail occupies the monomials x^c .. x^(w-1). For any ≤ hide opened points, all distinct and
  nonzero, the map from tail to openings is diag(x_j^c) times a Vandermonde matrix, which is invertible. So the
  opened values stay uniform, the same argument as for x_j = j + 1. 0 is not a point: every point lies in F_p^*.
- **Ligero (cozk)** keeps its own small codewords and is unchanged.

**Bit-exact under the coset domain.**
- demo d = 4, RC + LB, three chained steps: 2eecde7b…, c8aee97f…, 605c460f…. They pass check, ds-check and Python
  verify. A flipped byte is refused by both.
- **Old vectors.** With DP_DOMAIN=int they pass with their old digests. Under the coset domain they fail
  (`genesis roots differ`): the negative control.
- `pcs-bench`: the NTT columns equal direct evaluation at the domain's points.

**Times.**

| | x_j = j + 1 | coset NTT |
|---|---|---|
| one commitment, m = 20 (Mac, 12 threads) | 4.77 s | 0.42 s |
| one d² commitment, m = 24 (Mac) | about 100 s (est.) | 2.6 s, 1.0 GB process peak (1.0 s of it leaf hashing) |
| d = 4096 GEN6 + RC + LB, bb2, three custodians in one process: prove | 408.2 s | **21.3 s** |
| of which: spine commitments, middle commitments | 169.3 s, 49.6 s | 4.1 s, 2.7 s |
| verify | 6.9 s | 7.0 s |
| peak RSS (all three, darkstep's step included) | 15.4 GB | 23.2 GB |

- **Memory.** About 7.7 GB per custodian including the step, under forge's 12 GB, but not yet measured per box.
- **Memory knob.** The 2.5 GB per custodian over the int run is the genesis step's four d² codewords, held until the
  spine opens them. Releasing them right after commit would cost about 5 s of re-encoding.
- **Next.**
  - Proving is no longer the critical path: the gated step is 94 s.
  - The one-custodian-per-box numbers come from the deploy lane's three-box run.
  - Pipelining (proof k beside step k + 1) needs no change to the proof: proof k uses step k's record and tape and
    proof k-1's children.

## [OPEN]

- **The three-box run** (forge seat 0, bb2, hbox), driven by the deploy lane (ae142f25de791a39c).
  - It is wiring `run::public_genesis` and `lb: true`, with pg = sha256 of train_genesis_gen6.json, into
    dl-custodian. The proof lane's part:
    - the first proved three-box step, every bundle accepted by the native ledger and chained;
    - per-custodian proof time and memory (seat 0 on forge under its 12 GB cap);
    - proof bytes per link from darkstep `Net::sent_per_peer()[peer][PROOF]` (about 134 MB each way per step
      expected at d = 4096);
    - pipelining contention (proof k beside step k + 1);
    - then the release: C over t10k 0..63 (train lane's policy), checked against the ledger head.
- **Proof bytes on hbox's link.** Today every custodian receives the whole bundle. A designated aggregator (one
  custodian assembles and publishes) would roughly halve hbox's proof traffic. Not built; raise it with measured bytes.
- **Memory knob.** The genesis step holds four d² codewords per custodian until the spine opens them (2.5 GB).
  Release them after commit (`cw = Vec::new()` at the end of `build_tree`) if seat 0 exceeds 12 GB; that costs about
  5 s.
- **Next kernel.** Leaf hashing (repr-format SHA-256, 1.0 s per d² commitment); changing it is a wire-format change.

## Continuation

**State** (HEAD 047a3601 and before):
- Proofs: RC (proved bounds), LB (bit lookup), PG (public genesis) and the coset-domain PCS (DOMAIN "coset").
- All of it is byte-identical with Python, except PG, which is native only.
- d = 4096 GEN6 + RC + LB: 3,192,275 triples per custodian (`run::step_section`) and a 21.3 s proof (three in one
  process on bb2).

**APIs the deploy lane uses.**
- `run::public_genesis(pr, d, i, &w1, &w2, 3) -> (carry, roots)` and `run::public_weights(cfg_bytes) -> (d, w1, w2)`.
- `StepParams { rc: true, lb: true, pg: Some(sha256(cfg_bytes)), ..}.deployed()`; `prm.carried(step)` is true from
  step 1.
- `run::from_darkstep_n(i, d, &record, &w1n, &w2n, &tape, Some(run::step_section(..)), Det::off())`, then
  `run::prove_step(pr, lp, tables, prm, &mut TcpRef(&net), &ctx, st, Some(carry))`. The carry is public_genesis's at
  step 1, then the previous StepProof.child.
- `Ledger::open(path, model, pr, Some(Genesis { program: prm, roots: <public roots>, .. }))`, then
  `lg.check_public_genesis(&cfg_bytes)?`, then `lg.accept(lp, &blob, &tables)` per step.
- Release: `run::release_mpc`, `run::release_section`, `run::prove_release`, then `lg.release(lp, &blob, &pol)`.

**Exact commands** (from `/Users/ember/dev/zkml-research/native`).
- **Builds.**
  - `CARGO_TARGET_DIR=$PWD/target-proof cargo build --release -p darkproof --features tcp,test-det --bin darkproof`
    (the bit-exact checks);
  - `CARGO_TARGET_DIR=$PWD/target-proof-prod cargo build --release -p darkproof --features tcp --bin darkproof`
    (production coins).
- **The proved chain in one process, as a reference before the three-box step.** This gives three steps, ledger
  acceptance, the release and its refusals:
  `DP_PG_CFG=<cfg.json> DP_PROGRAM='{"he": true, "RC": true, "LB": true}' ./target-proof-prod/release/darkproof ds-chain 16 demo 3 8`.
  At d = 4096 use the GEN6 program:
  `DP_PROGRAM='{"S1": 11, "K1": 19, "S2": 7, "K2": 8, "S3": 8, "K3": 19, "R3": 128, "he": true, "RC": true, "LB": true}'`,
  with the cfg `research/dark_learning_2026_11_06/train_genesis_gen6.json`, profile `ledger`.
- **Timed d = 4096 proof** (three in one process):
  `DS_THREADS=8 DP_TRACE=1 DP_PROGRAM='{GEN6, "RC": true, "LB": true}' ./target/release/darkproof ds-bench 4096 ledger`.
  On bb2 this is `~/lanes/dl-gen6-proof/cos4096.sh`, which records the box before and after.
- **Counts:** `DP_PROGRAM=... darkproof counts 4096 ledger`. **One commitment:** `darkproof pcs-bench 24 ledger`.
- **Bit-exact:** `darkproof check VEC TAG`, `ds-check VEC TAG`, `rel-check VEC TAG`, plus
  `python3 darkproof_vectors.py verify VEC TAG`. Vectors made before 28769b6a need `DP_DOMAIN=int`.
- **New vectors:** `DL_DETERMINISTIC=7 DP_PROGRAM='{..}' [DP_INPUTS=GEN6] [DP_TAGSUFFIX=_x] python3 darkproof_vectors.py OUT d demo|ledger he`.
  For the release: `DP_RC=1 DP_LB=1 ... OUT d PROFILE pw rel`. Refusal rows: `DP_ATTACK=lb_h|lb_g1`.
- **The three-box step itself** is the deploy lane's orchestrator (darkdeploy, dl-custodian, TLS, its scripts under
  native/deploy/). Ask it for the invocation.

**Where the vectors live.**
- Local, under `/private/tmp/claude-501/-Users-ember-dev-aidev/78fef112-a52f-425f-8503-f3fa24ff087c/scratchpad/dl-gen6/proof/`:
  - `vec`: the x_j = j + 1 domain;
  - `lb`: LB, int domain, with the attack rows;
  - `cos`: the coset domain (demo_d4_lb_he; plus demo_d4 pw/rel, from a Python job that may still be finishing:
    `rel_d4.log`, `rel_d4.pid`);
  - `pg/cfg16.json`: a d = 16 darktrain cfg;
  - `lb_plain.py`: the circuit's plaintext check.
- bb2, `~/lanes/dl-gen6-proof/`:
  - `vec`: every int-domain set; checks.sh, the checks*.log files, rc4096b_* and cos4096_* logs;
  - builds: `target-det` (pre-coset), `target` (coset, a40857d1). Rebuild after syncing `native/`.
  - No jobs of mine are running there.
