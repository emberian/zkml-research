# Gen 6: exact truncation (program flag "XT")

Lane: gen 6 "exact truncation" (initiative #3). Status: design [DERIVED, checked by script]; build in progress.
Checks: `notes/dark-learning-gen6/xtrunc_check.py` (called check_circuit.py below); scratch `scratchpad/dl-gen5/xt/` (`budget_xt.py`).

## 1. The construction

Today (statistical): the step opens c = x + 2^K + r with r uniform in [0, 2^(K+40)). The opening is 2^-40-close to
uniform per truncation, and 16,384 truncations per step make it the run's dominant privacy term (2^-15 for 2000 steps
plus the release).

**XT.** The mask r is uniform in [0, p), as an integer, with all 61 bits authenticated. The online phase is the
statistical one unchanged, plus one public rule:

    c = x + 2^K + r mod p is opened (uniform in F_p for every x);
    if c < 2^(K+1): the step aborts ("XT: opening in the wrap zone"), and it is redone with fresh preprocessing;
    otherwise u = (c >> s) - 2^(K-s) - rhi - [c mod 2^s < r mod 2^s], exactly as today.

**Why it is exact.** Write x' = x + 2^K, in [0, 2^(K+1)) when |x| <= 2^K (the proved bound). Over the integers
x' + r = c + w p with the wrap w in {0, 1}, since x' + r < 2p. If w = 1, then c = x' + r - p < x' < 2^(K+1). So an
opening outside the wrap zone has w = 0 and c = x' + r over the integers. The low-bit comparison is then the borrow of
an integer subtraction, and the formula is floor(x / 2^s) exactly. The wrap bit is excluded publicly, so no secret
wrap bit is computed.

**Where exactness comes from.** The floor is the existing low-bit borrow. It is computed from r's authenticated low
bits (the s Trb entries) against the public c mod 2^s by the same prefix chain as today: 2(s - 1) Beaver products.
The high part is rhi = r >> s (Trh). XT adds no new comparison. It only guarantees that the integer identity
c = x' + r, which the borrow formula assumes, actually holds.

**The redo keeps the MAC key** (coordinator's point 1).
- An opening c < 2^(K+1) is a public event that does not depend on the data. Its probability is 2^(K+1)/p for every
  x, and nobody deviated.
- So it is not a MAC failure and must not retire the key. darkstep returns `Err(XT_REDO ...)` (prefix
  `party::XT_REDO`), distinct from "MAC check failed". The orchestrator redoes the step on the next fresh tape under
  the same MAC key.
- A step whose opening is in the band is never accepted:
  - `run_step_shares` stops after that truncation;
  - `mac_check` refuses after it as a backstop;
  - the proof's public check refuses such a bundle by name (§4).
- [EXECUTED: `run_xtrunc.py`, rows 2a and 2b] A wrap aborts before the MAC check. The redo on the same dealer has
  alpha unchanged and fresh masks (no mask reused); it is accepted and refines the spec. Row 3 runs the same wrap
  with the rule ignored: the MAC check passes but the step does not refine. So only the rule, not the MAC check,
  stops it.
- [EXECUTED: darkstep `tests/xt_reference.rs` `wrap_zone_is_a_redo`] All three native custodians stop with
  XT_REDO on a tape whose first mask was moved so that c = 0.

**Why it is perfectly hiding.** r is uniform on F_p, so c is uniform on F_p and independent of x. The abort depends on
c alone. It has probability 2^(K+1)/p for every x (2^-41 at K = 19, 2^-52 at K = 8; about 2^-27.4 per d = 4096 step,
2^-16.4 per 2000-step run). Given no abort, c is uniform on [2^(K+1), p), independent of x. An aborted step's openings
are fresh uniform masks, and its redo uses fresh preprocessing throughout. A custodian that shifts its share of c into
the zone causes only an abort, and it already knew c. The MAC check catches the shift in any case.
[EXECUTED: `check_circuit.py` enumerates every x and r in toy fields (p = 1021, 2039, 4093). Accepted c is uniform on
[2^(K+1), p) for every x, and every accepted opening has x' + r < p.]

Rejected alternatives:
- **Catrina-de Hoogh / BitLT on the full wrap.** This computes w = [c < r] with a 61-bit comparison circuit online:
  about 61 more products and 6 to 61 more rounds per truncation, every step. The public rule gets the same exactness
  for the price of an abort with probability 2^-41.
- **Escudero et al.'s edaBits (CRYPTO 2020).** These are built for mixed arithmetic-binary circuits. darkstep has no
  binary domain: its bits are F_p-authenticated (daBits-like, MP-SPDZ `get_random_bit`). Our need is a uniform-mod-p
  mask with its bits, which strict edaBits also give, but MP-SPDZ builds them with binary-circuit cut-and-choose. The
  check below is about 22 products per mask.
- **Rejected openings that leak.** Taking r uniform in [0, 2^61) and widening the zone to absorb r >= p does not
  work: the zone's own openings are then biased toward x (statistical distance (2^61 - p)/2^61 = 2^-39.4 per mask).
  A perfect mask needs support exactly [0, p).

## 2. The mask in preprocessing (darkprep)

A mask is 61 random authenticated bits b_i (MP-SPDZ `get_random_bit`), r = sum 2^i b_i, kept only if r < p.

**The test (opens one bit, `[r >= p]`, nothing else).** p = 2^61 - delta has T leading one bits. Let L = 61 - T and
P = p mod 2^L (bit L - 1 of P is 0).
- a = T - sum_(i >= L) b_i (linear, in [0, T]; 0 iff the top T bits are all ones).
- lt = [r mod 2^L < P] by the prefix chain against the public P, from the top: E_L = 1, E_i = E_(i+1) e_i with
  e_i = b_i if P_i = 1 else 1 - b_i. Then lt = sum over P_i = 1 of (E_(i+1) - E_i). This is L - 1 - m products,
  m the lowest set bit of P.
- y = a + lt is in [0, T + 1] and is 0 iff r >= p.
- Open rho y with rho a fresh joint random element (one product). It is 0 iff y = 0 (or rho = 0, probability 1/p,
  independent of r). Otherwise it is uniform on F_p*.

**The accepted masks are uniform on [0, p)** (coordinator's point 3).
- The 61 bits are uniform and independent, and r = sum 2^i b_i is uniform on [0, 2^61).
- A chunk is kept iff every opened rho_k y_k is nonzero, i.e. every r_k < p and every rho_k != 0. The rho_k are
  independent of the r's.
- Given acceptance, the r_k are therefore independent and each is uniform on [0, 2^61) conditioned on r_k < p, which
  is uniform on [0, p).
- What was opened about a kept mask is rho_k y_k. Given y_k != 0 it is uniform on F_p* and independent of r_k
  (rho_k is uniform and independent), so it carries nothing about r_k.
- A rejected chunk is discarded whole and nothing of it is used, so rejection cannot bias the masks that are kept.

If any opened rho y in a chunk is 0, the chunk is discarded and regenerated. This happens with probability 2^-39.4
per mask and 2^-25.4 per step chunk. It reveals nothing about the masks kept: given acceptance, each is uniform on
[0, p), independent of everything opened. A fixed layout keeps the tape format unchanged.
[EXECUTED: `check_circuit.py`. y = 0 iff r >= p for every odd prime of 3 to 10 bits and every r, and for 20,000 random
and near-p r at each deployed p.]

| profile | p | T | L | P | products per mask (chain + rho y) | reject per mask |
|---|---|---:|---:|---|---:|---:|
| N = 4096 | 0x1ffffffffff92001 | 42 | 19 | 0x12001 | 19 | 2^-42.2 |
| demo, N = 8192 | 0x1fffffffffec4001 | 40 | 21 | 0xc4001 | 21 | 2^-40.7 |
| ledger, N = 16384 | 0x1fffffffffcf8001 | 39 | 22 | 0xf8001 | 22 | 2^-39.4 |

**Per truncation, ledger:**

| | statistical | XT |
|---|---|---|
| bits | K + 40 (59, or 48 at K = 8) | 61 |
| online products | 2(s - 1) | 2(s - 1) |
| check products | 0 | 22 (21 sequential rounds, batched over the chunk) |
| check openings | 0 | 1 (rho y) |
| joint randoms | 0 | 1 (rho) |

## 3. The tape (darkstep, darkproof)

**The layout is unchanged.** Each truncation still deals Tr, its s Trb bits, Trh, the K + 1 - s Trhb bits (RS), then
2(s - 1) triples. Only the distribution changes: r is uniform in [0, p) and Trh = r >> s has 61 - s bits. All of these
are linear in the 61 bits, which darkprep's assembly already uses. The ideal dealers (spdz.Dealer, darkstep
tape::Dealer, darkproof live) draw r = randrange(p) under XT, from the same stream position. The extra 61 - (K + 40)
bits and the check products stay inside darkprep's MPC run and are never dealt.

## 4. What the proof constrains

XT needs RS (and so RC). Under RS the proof is sound for any r and rhi (proof.md section 23, R1 and R2). The rows are
field identities, and only an honest witness needs no wrap, which the public rule now gives. So the rows are
unchanged: the TruncMask row, the low-bit borrow rows, the R1 chain to bit B with its high row, and the masked zero
test.

The one change is the public check on c. Today a c' = c - (2^K + a) outside [0, 2^(K+41)) is refused by name, which is
the statistical mask's honest range. Under XT an honest c is anywhere in [2^(K+1), p). The check becomes:
- the verifier refuses an opened c < 2^(K+1) by name ("XT: truncation opening in the wrap zone");
- c' >= 0 follows, since lo = 2^K + a <= 2^(K+1);
- R1's C_hi = floor(c' / 2^B) < p / 2^B, as R1 requires.

Refusal rows (to be EXECUTED):
1. **Wrong wrap.** The dealer's r is forced so that x' + r >= p, which puts c in the zone. The custodians ignore the
   abort and continue, so the MPC's u is wrong.
   - The verifier refuses by name (the public check).
   - With that check bypassed, the custodians' masked zero test refuses: the high row cannot hold, since the low B
     bits of c' - r are x - a - p, not x - a.
   - With the custodians' refusal also bypassed (a forced bundle), the ledger refuses (Ligero linear test).
2. **Wrong low-bit comparison.** A colluding custodian set flips a truncation's borrow (u off by one,
   MAC-consistently). The low-bit rows refuse it (Ligero linear test).

## 5. Privacy budget (privacy_budget.py's gen6 terms; `budget_xt.py`)

Under XT the trunc term is exactly 0. The objects per step rise by 438,272 (to 4,920,519) and the release's by
5,139,732 (to 68,586,614), which moves the sacrifice and authentication terms by about 0.1 bit.
[DERIVED: `budget_xt.py`; LowGear's drowning term is not rescaled for the extra batches (about +10%, 0.14 bit).]

| run | backend | statistical (today) | XT | dominant under XT |
|---|---|---:|---:|---|
| run of record (8 steps + release) | LowGear | 2^-21.6 | **2^-30.3** | prep_drowning |
| run of record | MASCOT tau = 5 | 2^-21.6 | 2^-32.1 | prep_auth |
| 2000 steps + release | LowGear | 2^-15.0 | **2^-23.8** | prep_drowning |
| 2000 steps + release | MASCOT tau = 5 | 2^-15.0 | 2^-25.5 | prep_auth |

The abort rule adds no term: its decision is a function of uniform public openings, and so is the chunk rejection.

## 6. Cost (d = 4096, GEN6, ledger-x2de + RS) [DERIVED from prep.md's measured unit prices; measurement in section 7]

Per step:
- bits rise from 225 d = 921,600 to 244 d = 999,424 (+77,824);
- check products 22 x 16,384 = 360,448;
- plus 16,384 joint randoms and 16,384 openings.

So +438,272 triple-equivalents on 4.48M (+9.8%). The release (213,980 truncations) adds about 5.14M on 63.4M (+8.1%).

| | MASCOT tau = 5 (362 kbit / triple-eq) | LowGear (37.8 kbit) |
|---|---:|---:|
| extra wire per step, all parties | 159 Gbit | 16.6 Gbit |
| extra per step on a 1 Gbit/s seat (a third of it) | 53 s | 5.5 s |
| 2000 steps on a 1 Gbit/s seat | **+29 h** | **+3.1 h** |
| extra per step via hbox (19.3 Mbit/s) | 46 min | 4.8 min |
| release extra via hbox | 8.9 h | 0.93 h (on 27.2 h) |

Online: the same openings, rounds and bytes, plus one public comparison per truncation. Proof: the same rows, atoms
and bundle size, and one public check per truncation instead of another.

## 7. Build log

**Python reference** (2c11f069) [EXECUTED]:
- `spdz.Engine.xt` and `native_ref.py --xt`. `cosnark_he.Prog` "XT" requires RS. Under XT, `cosnark_gates.append_range`
  refuses a c < 2^(K+1) by name ("<name>: XT wrap zone").
- Control: the default is byte-identical. `native_ref.py 4096 3 118 8` gives transcript d649f46f… and the committed
  party digests and sigmas.
- `native_ref.py 4096 3 118 8 --xt` and `... 64 --program GEN6 --xt` both ACCEPT and refine the spec. They are
  committed as `native_ref_results/*_XT.json`.
- `run_xtrunc.py 8`:
  - four seeds refine the spec, with masks reaching 2^61;
  - a wrap aborts with "XT: ..." before the MAC check;
  - the redo on the same alpha accepts;
  - controls: the wrap with the rule ignored, and a flipped borrow, each pass the MAC check and do not refine;
  - the statistical default is unchanged.

**Native darkstep, bit-exact** (2c11f069) [EXECUTED: `cargo test --release -p darkstep --test xt_reference`]:
- XT d = 8 (N = 4096) and GEN6 d = 64 equal `native_ref.py --xt`: transcript, every party's share digest and sigma,
  and wire counts. Negative control: the statistical reference's transcript differs.
- `wrap_zone_is_a_redo`.
- Default unchanged: `vs_reference` d8, d64, ledger d64, the attacks and the proof-atoms test all pass.

**darkprep** (bd1ebdfb) [EXECUTED, bb2 loopback, MASCOT tau = 5, d = 64 harness, `--xt`]:
- The chunk verifies: 34,438 entries, every r < p, MACs consistent.
- 17.59 Gbit against 15.08 Gbit statistical (+16.7%, about 314 kbit per added triple-equivalent); 4.27 s against
  2.96 s.
- `darkstep party --xt` on the exported tapes: ACCEPT x 3, `reveal` refines_spec.
- Negative control: the same .mpc with a fake prime 2^60 + 2^59 + 1 crashes with "darkprep XT: a mask r >= p ...".
  So the check fires when it should.

**Native chain with release** [EXECUTED, Mac, `DP_PROGRAM='{"RC","LB","RS","XT"}' darkproof ds-chain 16 demo-x2de 3 8`]:
- Three steps and the release are accepted by the ledger.
- The head weights after 3 steps EQUAL the plaintext twin's chain, and C = 1 = the twin.
- The same without XT: EQUAL, C = 1.

**The proof, byte-equal, with refusal rows** [EXECUTED]:
- Vectors: `DL_DETERMINISTIC=7 DP_STEPS=2 DP_PROGRAM='{"RC","LB","RS","XT"}' darkproof_vectors.py VEC 4 demo-x2de he`.
  Python verifies he1 and he2.
- `darkproof check`: he1 523f85f6… (2,143,980 B) and he2 a103b91f… (2,281,732 B), EQUAL.
- `darkproof ds-check`: darkstep's XT dealer, its online step and the native prover give a bundle EQUAL to Python's
  he1. The record equals the harness's.
- `run_xtrunc_proof.py demo-x2de` (Python, deployed step, d = 4):

| row | result |
|---|---|
| honest XT step | ACCEPT |
| xt_wrap: the first mask wraps (c = 0), the custodians ignore the redo | the custodians refuse to prove (the RS masked zero test) |
| xt_wrap, bundle forced past that | REFUSED by name: `middle: truncation input outside its proved bound (z1: XT wrap zone[0], public)` |
| xt_wrap, forced, with the public check bypassed in-process | REFUSED: `middle: Ligero linear test: the constraints do not hold` |
| borrow_flip: the first e truncation's borrow flipped (d2 off by one), MAC-consistent; the MAC check passes | REFUSED: Ligero linear test |

The borrow_flip row needed a first attempt to be corrected:
- The first attempt flipped the borrow at z1[0]. It was ACCEPTED, and that is correct: under LB, h is proved from
  z1's range bits, u1 is not an output, and SIG(u1 +/- 1) was unchanged there.
- A wrong low-bit comparison matters only where its truncation's output is semantic (d2, d1). There the proof
  refuses it.

Native refusal: `darkproof --test xt_replay`.
- Under XT the replay records the first wrap-zone opening, and `Rec::xt_refusal` names it. The ledger
  (`wire::verify_step` / `verify_release`) and the custodians (`run::prove_step`, `release`) call it.
- Without XT, the same transcript passes.

## 8. Measurements at d = 4096 (bb2 loopback, three custodians; GEN6, ledger-x2de + RC + LB + RS) [EXECUTED]

**Preprocessing per step** (MASCOT tau = 5, `darkprep run --d 4096 --mode steady --truncs 11,19,7,8,8,19 --rs
[--xt] --threads 8`, the step's MPC part; the proof section's 2,225,349 triples are the same under both):

| | statistical | XT | delta |
|---|---:|---:|---:|
| bits on the wire, all parties | 810.03 Gbit | 967.81 Gbit | **+157.8 Gbit (+19.5%)** |
| wall (loopback, 8 threads) | 43.2 s | 49.3 s | +6.2 s |

- The delta equals the model: 438,272 triple-equivalents x 362 kbit = 158.7 Gbit (x 0.994).
- Over the whole proved step (4.48M triple-eq, about 1.62 Tbit) it is +9.7%.
- On a 1 Gbit/s seat that is +53 s per step under MASCOT.
- Under LowGear it is +16.6 Gbit (+5.5 s at 1 Gbit/s; +4.8 min per step through hbox), at the measured unit price.

**Online and proof** (`DP_PROGRAM=<GEN6 + RC LB RS [XT]> darkproof ds-bench 4096 ledger-x2de`):

| | statistical | XT |
|---|---:|---:|
| online step (party 0) | 51.4 s | 51.1 s |
| prove | 32.8 s | 32.4 s |
| proof sent per party | 12,937,129 elements | 12,937,129 elements |
| bundle | 311,673,692 B | 311,690,684 B (+17 kB, the public transcript's larger values) |
| verify | 14.1 s, accept | 14.0 s, accept |
| peak RSS (three in one process) | 22.33 GB | 22.08 GB |
| proof-section triples | 2,225,349 | 2,225,349 |

The online phase opens the same values in the same rounds. The proof has the same rows. XT changes only the masks'
distribution and the public check.

**Few-step chain and release** (`ds-chain 16 demo-x2de 3 8`, native, both modes):
- three steps and the release are accepted;
- the head weights equal the plaintext twin's chain;
- C equals the twin (C = 1).

That is d = 16. A d = 4096 chain is the run itself.

## 9. In the run of record (coordinator's decision: XT goes in if ready and tested) [EXECUTED unless marked]

The run of record uses LowGear (N = 16,384, -S 60).
- `darkprep --xt` under `lowgear-party.x` 38adf2bf (PairwiseParams 5.77 MB = N = 16,384) on bb2 loopback, fresh
  key, d = 4 harness chunk: it verifies with 16 masks, every r < p.
- MASCOT at d = 64 and d = 4096 is in sections 7 and 8.

Run-side changes (b1a485f8):
- **Genesis.** `dl-custodian --xt` (needs `--rs`) pins `"XT": true` in the genesis record. A replica opened without
  it is refused.
- **Parties.** Every party runs with `Party::xt`. `test-deal` deals XT masks.
- **The redo** is never a refusal, so never a self-handover:
  - with `--xt-spare-tapes`, the step is redone on a spare under the same key;
  - without one, the custodians exit with code 5 (verdict REDO) and the checkpoint stays at the step before.
    `run.py resume` then continues once fresh preprocessing for that step exists. rec has no spare chunk: the event
    has probability about 2^-24 over its 8 steps, and a spare would cost 1.92 h of hbox's uplink.
- **The release** never opens C after a wrap-zone opening. That event has probability about 2^-23 per release; the
  release is then redone on a new release tape.
- **Preprocessing.** `rec-stream.sh` passes `--xt`, with darkprep and its .mpc from ws14. `rec.json` adds `--xt` to
  the flags and points every seat and the owner at `ws-target-r14`.
- **The r14 build** (b1a485f8 via `git archive`) is in `<deploy root>/ws14` and `ws-target-r14` on forge, bb2 and
  hbox. `dl-custodian proof-triples ... --rs --xt` gives 2,225,349 on all three, rec's count.
- `tests/xt_redo.rs` covers the proved run: a forced wrap-zone step is redone on its spare, every proof verifies on
  every replica, the genesis pins XT, and the weights equal the twin.

Still to do: the prep streams A and B were waiting on the key setups and must be restarted to pick up the new script.

## Continuation (XT lane, gen 6)

- **State.** XT is built, tested and switched on for the run of record (991b29fd). What remains is the prep lane's
  restart of `rec-stream.sh` A and B (PID files in `research/dark_learning_2026_11_06/runs/rec/prep/`).
  - They were in their key-wait loops on the pre-XT script.
  - If they are not restarted before lg64n (about 09:45 Nov 8) and lg64f (about 11:45 Nov 8), the chunks come out
    statistical.
  - That mismatches the custodians' `--xt` only in the public check: a statistical c is always >= 2^(K+1) with
    overwhelming probability, so such a run works but is not XT.
  - Check `events.log` and a chunk JSON's prog name containing `xt2305843009210515457`.
- **Tests.**
  - Python: `run_xtrunc.py 8`, `DL_DETERMINISTIC=7 run_xtrunc_proof.py demo-x2de [row]` (about 25 min per row).
  - Native:
    - darkstep `--test xt_reference`;
    - darkstep `--features test-harness --test serve_xt`;
    - darkproof `--features tcp --test xt_replay`;
    - darkdeploy `--features test-harness --test xt_redo`;
    - darkprep `--test assemble xt_plan`.
  - Vectors: `scratchpad/dl-gen5/xt/vec/{xt,rs}`.
- **bb2 lane dir** `~/lanes/dl-gen6-xt` (1.1 GB): the XT MP-SPDZ test runtime with a test LowGear key, and the
  measurement runs. These are test-only and safe to delete. The r14 build is in the deploy roots (`ws14`,
  `ws-target-r14`).
- **Open.**
  - run.py has no code-5 (REDO) handling.
  - No spare chunk exists for rec.
  - The privacy_budget.py gen6 terms with XT (truncs 0, objs +438,272 per step and +5,139,732 for the release) are
    the coordinator's file: `scratchpad/dl-gen5/xt/budget_xt.py` has the numbers.
