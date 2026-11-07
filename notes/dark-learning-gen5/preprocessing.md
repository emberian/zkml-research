# Real preprocessing for the MPC fork: MASCOT over MP-SPDZ, measured against the count model

Lane `prep`, dark-learning gen 5, 2026-11-06. Replaces the ideal dealer (`spdz.Dealer`) with real, maliciously
secure preprocessing run by three custodian processes, emits per-party tapes in the online step's program order,
runs both the Python harness and the native `darkstep` custodians on them, and prices the real thing against the
Astra scholar's MASCOT count model.

## 1. Backend: MP-SPDZ's MASCOT, release v0.4.4

| candidate | what it has for us | license |
|---|---|---|
| **MP-SPDZ** (CSIRO/Data61) | MASCOT (OT, malicious, dishonest majority) over any prime field incl. our 61-bit p; also SPDZ2k, LowGear/HighGear/CowGear (HE-based); triples, bits, squares, randoms; writes authenticated shares + MACs to files | BSD-3-Clause (CSIRO), plus University of Bristol "Open Access Software Licence" for the SPDZ-2/SPDZ-BMR-ORAM parts (BSD-2-style, with a request to report scientific/commercial use to Bristol, ref. 1914, "for impact monitoring only") and SCALE-MAMBA's licence; bundled deps (libOTe, cryptoTools MIT-style; boost, GMP LGPL, libsodium ISC, OpenSSL Apache-2) |
| swanky (Galois) | OT/VOLE primitives (ocelot), no prime-field SPDZ triple generator | MIT |
| emp-toolkit | OT extension, boolean circuits (emp-agmpc is Boolean) | MIT |
| SCALE-MAMBA | HE-based SPDZ, archived | Bristol/KU Leuven |

[SOURCE] MP-SPDZ README, "Preface": "this does not mean that the software has undergone a security review as should
be done with critical production code." So it is a published, widely used research implementation, **not an
audited library**; no audited library implements prime-field SPDZ preprocessing.

Why MASCOT and not the others:
- **SPDZ2k** works over Z_2^k, not F_p: the harness's arithmetic (HE plaintext modulus t = p, Taylor-shifted table
  lookups, inverses) needs the field. Rejected, as the scholar did.
- **LowGear/HighGear (Overdrive) / TopGear**: HE-based; their BGV parameters are chosen by MP-SPDZ for the field and
  need NTL plus a ZKPoPK per batch. Communication can be lower, but they add a second, independent lattice parameter
  set and ZK soundness term to the security budget. A fair follow-up measurement, not the first backend.
- **MASCOT** is exactly the scholar's priced protocol, so the comparison is row for row.

The release binaries run on dregg-forge (Linux, ADX). For tau = 4 (below) MP-SPDZ was built from source on the Mac
(`N_AMPLIFY` 3 -> 4 in `OT/NPartyTripleGenerator.h`, `ERROR =` and Homebrew OpenSSL paths in `CONFIG.mine`).

## 2. What was built

- `native/darkprep/mpc/darkprep.mpc`: the MP-SPDZ program. Generates, for one step: input-tuple triples (owner
  check), joint randoms (`auth_plain` masks), Beaver triples, K + 40 random bits per truncation, and 255-power chains
  (a joint random r and 254 authenticated products, doubling schedule, 8 rounds). Each section is component-major in
  `Persistence/Transactions-P<i>.data`; batches of 1000, optionally multithreaded (positions are explicit, the file is
  pre-sized so concurrent writers never zero-fill over each other).
- `native/darkprep` (Rust): `schedule` (the program order of `run_step` with both HE helpers; 34,438 entries at
  d = 64, equal to `spdz.Dealer.count`), `mpspdz` (parses the party file: header "SPDZ gfp", the prime, alpha_i,
  Montgomery residues with R = 2^64 mod p; drives `compile.py` and three `mascot-party.x` processes on 127.0.0.1 with
  PID files; retires the MAC keys after an abort), `tape` (assembly, party-local: r = sum 2^j b_j, low bits,
  r >> s = sum_{j>=s} 2^{j-s} b_j by linear maps on (share, MAC)), `owner` (client input: the custodians send their
  plain shares of (a, b, c), the owner checks a b = c and keeps r = a), `verify` (TEST-ONLY: reconstructs every
  entry with all alpha_i and checks MACs, tags, triples, truncation tuples with range, power chains, owner masks).
- CLI: `darkprep run|assemble|verify|corrupt|export-darkstep|plan`. Tape format in `src/lib.rs` (DLTAPE1);
  `export-darkstep` writes the coordinator's DLTAPE01 layout (`darkstep::tape::Tape`) plus `public.bin` (the
  owner's broadcasts c = v - r).
- `research/dark_learning_2026_11_06/tape_dealer.py` (TapeDealer + TapeEngine, new file; spdz.py untouched),
  `run_tape_step.py`, `prep_measured_vs_model.py` (+ `.out.json`), `darkprep_measurements.json`.

Tests: `cargo test --release -p darkprep --test assemble` (5 tests: schedule count = 34,438; synthetic tapes in
MP-SPDZ's byte format verify and round-trip; a flipped MAC share, share, tag and owner mask are each refused; a
custodian's shifted input-tuple share fails the owner's a b = c; wrong prime and truncated file refused).

## 3. Correctness on real tapes (d = 64, ledger prime p = 2305843009210515457)

[EXECUTED] `darkprep run --d 64 --mode harness --verify` on dregg-forge: 34,438 entries per party, 8,320 owner masks;
every MAC (103,314), 2,562 triples, 256 truncation tuples, 64 chains and every owner mask check out. 2.9 s, 460 MB
sent per party.

[EXECUTED] **Native online step, unchanged, on the real tapes**: `darkprep export-darkstep` then three
`darkstep party I 16384 4 175 64` processes over 127.0.0.1 and `darkstep reveal`: all three ACCEPT,
`refines_spec: true`, 0.56 s.
Negative controls (same command, one tape entry changed with `darkprep corrupt`):
- party 1's MAC share of entry 8,384 (the first Freivalds product's `ta`): all three custodians REFUSED, "MAC check
  failed: an opened value is not the authenticated one";
- party 2's share of entry 34,389 (the last `trh`; a wrong value that no Freivalds check sees): REFUSED by the MAC check.
- (`darkprep verify` refuses both tapes too, naming the entry.)

[EXECUTED] **Python harness on the same tapes** (`python3 run_tape_step.py <tapes> honest|mac|share|tag`; TapeDealer +
TapeEngine, `he_matvec.HEMatvec` and `he_outer.HEOuter` at N = 16384, L = 4; 1,686 s each on the Mac, three in
parallel; results in `tape_step_results_{honest,mac,share,tag}.json`):
- honest: ACCEPT, `refines_spec: true`, MAC check passes, all 34,438 entries and 8,320 owner masks consumed;
- mac (party 1's MAC share of entry 8,384): REFUSED at the MAC check; the values were right (`refines_spec: true`);
- share (party 2's share of the last `trh`): REFUSED at the MAC check (`refines_spec: false`: the value was wrong);
- tag (party 0's entry 0 relabelled): REFUSED at once, "party 0 entry 0 is 'ta', the step asks for 'in'".

## 4. Measured cost, against the count model

Steady state (x, y input; weights stay shared: the scholar's row), all three parties' bytes from MP-SPDZ's own
counter, 1 MB = 10^6 B, plus 549 bits per input for the owner messages. dregg-forge, `-d` (direct channels).

| d | measured, full step (Tbit) | model (he_mpc_outer, Tbit) | measured / model | wall, 1 thread/party | wall, 4 threads/party | bytes per party |
|---:|---:|---:|---:|---:|---:|---:|
| 64 | 0.00869 | 0.01287 | 0.675 | 2.2 s | — | 0.362 GB |
| 1024 | 0.1453 | 0.2206 | 0.659 | 34.9 s | 27.7 s | 6.05 GB |
| **4096** | **0.599** | **0.912** | **0.657** | **143.5 s** | **40.9 s** | **24.98 GB** |

The d = 4096 step was run in full (not extrapolated) and its tapes (2,195,462 entries per party) verified.

Row by row at d = 4096 (unit prices measured with one object kind alone, 100,000 objects; the control is
additivity: counts x unit prices = 1.0018 of the full run at d = 4096, 1.000 at d = 1024, 0.976 at d = 64 where fixed
setup counts):

| row | count | model unit (bits) | measured unit | model (Gbit) | measured (Gbit) | ratio |
|---|---:|---:|---:|---:|---:|---:|
| owner input tuple | 8,192 | 7,564 (Protocol 5) | 262,398 | 0.06 | 2.15 | 34.7 |
| joint random | 16,384 | 22,692 | 23,457 | 0.37 | 0.38 | 1.03 |
| Beaver triple | 311,298 | 390,888 | 261,849 | 121.7 | 81.5 | 0.67 |
| power-chain product | 1,040,384 | 391,620 | 263,786 | 407.4 | 274.4 | 0.67 |
| random bit | 921,600 | 414,678 | 262,617 | 382.2 | 242.0 | 0.63 |
| **total** | | | | **911.7** | **599.4** (run) | **0.657** |

Why they diverge:
- **Triples, products, bits (x 0.63-0.67).** MP-SPDZ uses tau = 3, not 4 (`N_AMPLIFY 3`), and SoftSpokenOT with
  k = 2, which sends lambda / 2 = 64 bits per extended OT, not lambda = 128. The scholar's own formula at those
  parameters predicts 251,442 bits per triple; measured 261,849 (x 1.041). At tau = 4: formula 297,192, measured
  309,849 (x 1.043). The 4 % residue is MASCOT's batch/MAC-check/commitment traffic the model leaves out.
- **Random bits (x 0.63).** MP-SPDZ makes a bit from a square drawn from a triple's own a (one triple + two
  openings), not from a separate joint random r plus a triple (the model's B = R + T + 3 O).
- **Input tuples (x 34.7).** The model prices Protocol 5, where the owner is one of the MASCOT parties. Our data
  owner is outside custody, so each mask costs a whole triple (client-input protocol, the owner checks a b = c). It
  is 0.36 % of the d = 4096 step. A data owner that runs a MASCOT party would pay I but enlarge every other row.
- **Random (x 1.03)**: as modelled (each party inputs a random value; MP-SPDZ adds its check traffic).

Knobs, measured at d = 4096 (bits, all parties):

| variant | Tbit | wall | note |
|---|---:|---:|---|
| as above (tau 3, SoftSpoken k = 2, plaintext TCP) | 0.599 | 40.9 s (4 thr) | |
| **tau = 4** (source build, Mac; bytes are platform-independent) | **0.709** | (118 s on the Mac, not comparable) | 0.778 of the model; needed for the k-bit statistical claim (§5) |
| TLS on every channel (`-e`) | 0.599 | 55.3 s (4 thr) | +35 % time; MASCOT needs authenticated channels, the dishonest-majority default is unencrypted |
| SoftSpoken k = 4 | 0.515 | 44.5 s (5 thr) | per triple: k = 1 x 1.28, k = 4 x 0.86, k = 8 x 0.79 (2 x the time) of k = 2 |

So the deployable configuration (tau = 4, TLS) is about **0.71 Tbit per step at d = 4096**, 0.78 of the model's
0.912 Tbit; with SoftSpoken k = 4 about 0.61 Tbit [DERIVED: 0.709 x 0.86]. Wall time at d = 4096 with 4 threads per
party on 16 vCPU and loopback: about 41 s plain, 55 s with TLS (tau = 3); a tau = 4 run on forge was not done (the
release binary is tau = 3); expect about x 1.2 [DERIVED from the byte ratio].

## 5. Security notes, as terms for the million-step budget

What the backend claims [SOURCE: MASCOT, ePrint 2016/505, Thm 3 / Cor 1 / Thm 2; MP-SPDZ README]: UC security
against a static malicious adversary corrupting up to n - 1 = 2 of 3 custodians, with abort, in the (F_ROT, F_J.K)
hybrid; the OT extension is SoftSpokenOT (malicious, ePrint 2022/192) over SimplestOT base OTs (elliptic curve).
MP-SPDZ MAC-checks every opening inside preprocessing, but it writes shares to the file while the program runs and checks at the end, so a file is only valid if all three parties exit successfully: `darkprep run` assembles tapes only then, and retires the keys otherwise. It does **not** cover:
the channels (run with `-e`), post-quantum confidentiality (the base OTs are discrete-log: a recorded transcript plus
a future quantum computer gives the triple shares, hence the masks; the HE side is lattice-based, this is not),
fairness, and the derived correlations below.

Derived correlations and what they add:
- **Power chains**: computed by authenticated MASCOT products inside MP-SPDZ, so their correctness is the triples'
  (sacrifice) and their MACs are computed, not re-authenticated: no new term.
- **Truncation tuples**: r, its low bits and r >> s are linear maps of authenticated, checked bits, so the relation
  and the range r < 2^(K+40) hold by construction: no new term from preprocessing. The masking they provide is the
  first row below.
- **Input masks (client input)**: the owner's a b = c check has error 1/p per tuple (integrity of the owner's input).
  A custodian making the check fail learns nothing about the input (it happens before the input is sent).

Statistical terms, conservative union bounds (log2; per step at steady state; "run" = 10^6 steps = 2^19.93).
MASCOT triples per step, counting bits (each from a triple) and input tuples: d = 64: 2^14.97, d = 4096: 2^21.12.

| term | per object | d = 64 step | d = 4096 step | d = 4096, 10^6 steps |
|---|---|---:|---:|---:|
| truncation masking, KAPPA = 40 (opened c = x + 2^K + r): SD <= 2^(K+1) / 2^(K+40) | 2^-39 per opening, 4d openings | 2^-31.0 | 2^-25.0 | **2^-5.1** |
| MASCOT combine, **tau = 3** (as released; Cor. 1: k/2 = 30.5 bits) | 2^-30.5 per triple | 2^-15.5 | 2^-9.4 | vacuous |
| MASCOT combine, **tau = 4** (Thm 3: k = 61 bits) | 2^-61 per triple | 2^-46.0 | 2^-39.9 | 2^-19.9 |
| sacrifice (an incorrect triple passes), integrity | 1/p per triple | 2^-46.0 | 2^-39.9 | 2^-19.9 |
| online batched MAC check, integrity | 2/p per step | 2^-60 | 2^-60 | 2^-40.1 |
| owner's a b = c check, integrity | 1/p per input | 2^-54 | 2^-48 | 2^-28 |
| authentication (Thm 2: log|F| - 2 log log|F| = 49.1 bits per invocation; MP-SPDZ invokes it per batch, ~ triples/1000 [DERIVED, batch count not measured]) | 2^-49.1 per batch | 2^-44.1 | 2^-38.0 | 2^-18.0 |

Readings:
- **The truncation term dominates and cannot be fixed by KAPPA in this field**: c < p needs K + KAPPA + 1 <= 60, so
  KAPPA <= 40 at K = 19. A 2^-40 run bound at d = 4096 needs per-opening 2^-74. Options: exact truncation with r
  uniform in F_p and a comparison (no statistical term; 61 bits + an LT circuit per truncation, roughly 2 x 61 more
  products each, about +0.5 Tbit at d = 4096 [DERIVED, rough]); or a larger SPDZ field (breaks t = p with the HE
  helpers unless they move too). [OPEN: the coordinator's call; this is the online protocol, not preprocessing.]
- **tau = 3 is not acceptable at a 61-bit field**; tau = 4 is the configuration to deploy (+18 % bits, measured).
- **Every per-object term is ~2^-61 at best and a run has 2^41 objects**, so no per-object union bound reaches 2^-40
  for 10^6 steps at d = 4096 in this field: the same "failed sufficient run bound" the scholar reported, now with the
  real counts. The integrity terms can be cut by checking in an extension field (sacrifice and MAC check over F_{p^2}:
  error 2^-122 per object) — MP-SPDZ does not implement F_{p^2} MACs for gfp [OPEN, the "field-extension MACs" row
  of §22.3]. The privacy terms (combine) need a larger amplification (tau = 5 gives k(tau-2)/2 = 91.5 bits per triple
  by the proof's formula [DERIVED from App. C, eq. near "2^-k(tau-2)/2-c/2"], about +15 % bits over tau = 4 by the same formula).
- **Selective failure / abort**: preprocessing is input-independent, so an abort in preprocessing reveals nothing
  about W, x, y. What a selective failure can leak is bits of an honest alpha_i (MASCOT's COPE) or of an honest
  triple share (bounded by the combine term above). Rule implemented in `darkprep`: on any abort the MAC key files
  are retired (renamed, fresh keys next run) and unconsumed tapes under the old key must be regenerated. With that
  rule, preprocessing aborts need **not** enter the ledger's online abort term eps_abort = (k+1) p (§22); online
  aborts still do.

## 6. Open

- [OPEN] Exact (non-statistical) truncation, or a larger field: the dominant million-step term.
- [OPEN] F_{p^2} sacrifice and MAC check (not in MP-SPDZ for prime fields).
- [OPEN] A tau = 4 build on dregg-forge for wall time (needs GMP, libsodium, boost, cmake built in the lane dir: no
  system packages were installed).
- [OPEN] LowGear/HighGear measured on the same program (needs an NTL build).
- [OPEN] Cross-model review: not run for this lane.
