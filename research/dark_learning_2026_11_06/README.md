# Dark learning, 2026-11-06: experiment 1 (ct×ct certificate, crossing wire) and the d = 64 step

Pure Python 3.10+, no dependencies. Every number printed is a COUNT (elements, bits, wire elements,
openings); nothing is timed. Decisions these feed: `docs/DARK-LEARNING-SCHEME-DECISION.md`.

## Rerun

    python3 rescale_certificates.py A B B61 C   # experiment 1a: one ct×ct + integer rescale certificate, 4 designs
    python3 crossing_wire.py                    # experiment 1b: one fused sigma/sigma' crossing at N = 8192
    python3 run_d64.py mpc                      # d = 64 step, MPC fork (minutes)
    python3 run_d64.py fhe                      # d = 64 step, FHE fork (N = 8192 ciphertexts; a build box)
    python3 run_d64.py                          # both; writes d64_results.json
    python3 run_he_outer.py [64] [128] [attacks] # MPC fork with HE matvec + HE outer (build box)
    python3 inventory_he_outer.py > inventory_he_outer.out.json
    python3 run_cosnark_zk.py                   # ZK spine (minutes)
    python3 run_cosnark_gates_zk.py 4 16        # ZK middle (minutes)
    python3 zk_seed_falsifier.py; python3 mac_timing_falsifier.py
    python3 run_cosnark.py                      # MPC fork's collaborative proof at d = 16, 32, 64 (a minute)
    python3 step_counts.py [--validate|--layout-check]   # counts at any d; checks against the executed runs

On hbox they ran as `./launch.sh NAME MEM python3 -u <script> ...` (detached, under `swarm-build`, PID
file `NAME.pid`, log `NAME.log`). Design C (BabyBear row-interleaved) is the slow one: 42 digits per
coefficient means 42² digit products per term.

## Files

| file | what it is |
|---|---|
| `bfv_ref.py` | exact BFV over Python ints (Kronecker negacyclic products, centered message encoding) |
| `rescale_certificates.py` | designs A (native p61), B / B61 (PRISM-style per-prime fields), C (BabyBear digits) |
| `crossing_wire.py` | E2S and S2E executed and counted; lookup openings executed; preprocessing by formula |
| `step_spec.py` | the reference integer learner both forks must reproduce exactly |
| `spdz.py` | SPDZ-style engine: MACs, Beaver/matrix/outer triples, exact truncation, exact lookup, MPC-in-the-head audit by re-execution |
| `e2s_proof.py` | v2 crossings: masked public decryption with a well-formed partial-decryption proof (R_PD) per custodian; masked public encryption through SPDZ |
| `step_counts.py` | schedule-level counts at any width d (both forks), validated exactly against the executed runs; `--layout-check` executes the d = 4096 block layout at N = 8192 |
| `fs_binding_falsifiers.py` | adaptive-quotient forgeries that the LEGACY verifiers (public-data Fiat-Shamir point) accept and the fixed ones (point hashes the witness) refuse |
| `encoding_regressions.py` | falsifiers for the two large-t encoding fixes (fail under the broken encoding, pass under the fix) |
| `cosnark.py`, `run_cosnark.py` | the MPC fork's collaborative proof (per-party share-codeword PCS, MPC sumchecks, rank-1 checks, chaining), full-collusion attacks, count formula checked against execution |
| `cosnark_gates.py`, `run_cosnark_gates.py` | the middle of the collaborative proof: SPDZ execution integrity (openings, preprocessing well-formedness, IO), constraint system re-derived by the verifier from the public transcript; full-collusion attacks; exact count formula |
| `proofwire.py`, `run_proofwire.py` | the untrusted-input verifier (schema-driven bytes in, pinned PARAMS) and the durable Ledger (genesis record, rotation record, lock); tamper, replay, equivocation, rotation and restart rows |
| `owner_sig.py`, `run_signed_input.py` | signed-input binding: hash-based owner signature (Lamport + Merkle, durable leaf counter) over the batch commitments; substituted x/y, forged and replayed signatures refused |
| `fs_public_falsifier.py` | review3's forgery through the unbound public transcript, now REFUSED |
| `rerun19.log` | the hbox re-run of every falsifier and harness after the review repairs |
| `cozk.py` | collaborative zero-knowledge Ligero over additive shares (rows in groups, polynomial Beaver triple) |
| `cosnark_zk.py`, `run_cosnark_zk.py` | the spine with ZK layers 2-3: hidden rounds and evaluations, the verifier's checks as Ligero constraints (rank-1 check = one product gate); forgeries with the violated check; chain; exact counts |
| `cosnark_gates_zk.py`, `run_cosnark_gates_zk.py` | the middle with ZK layers 2-3 (lockstep linear sumchecks), gate forgeries, exact counts |
| `zk_seed_falsifier.py` | layer-1 tails seeded from public data do not hide; secret seeds do |
| `mac_timing_falsifier.py` | a rushing custodian beats an uncommitted sigma; commit-then-open refuses it |
| `he_outer.py`, `run_he_outer.py` | MPC fork's HE-assisted outer product (own-key pt x ct, MAC shares from the same exchange, one Freivalds-style check); honest d = 64/128 with both HE helpers, attacks, full-collusion forgery refused by the spine, exact counts |
| `inventory_he_outer.py` | the scholar's MASCOT inventory (imported unmodified, rows re-checked) plus the HE-outer row and ZKPoPK prices |
| `he_matvec.py`, `run_he_matvec.py` | MPC fork's HE-assisted matvec (own-key pt x ct cross terms + SPDZ Freivalds check), honest at d = 64/128, falsifiers, counts checked against execution |
| `cert_b61.py` | the FHE fork's ct×ct certificate: explicit witness + verifier (the decryption gate) |
| `fhe_fork.py` | FHE fork of the step: host ct×ct with certificates, custodian crossings, conversion audit |
| `mpc_fork.py` | MPC fork of the step: whole step in SPDZ |
| `run_d64.py` | the milestone: honest run + Codex's attack list on both forks, same counts columns |
| `*.log`, `d64_results*.json` | outputs of the recorded runs (`*_fhe_v1.*` = the sampled-conversion FHE fork, superseded) |

## What "proved" means here

Every relation a verifier would check is computed and checked, over the stated field, with the stated
bounds:
- certificate identities at Fiat–Shamir points;
- canonical base extensions;
- MAC equations;
- re-execution of opened views.

Compiling these checkers into a succinct argument is the next layer; it is priced, not run. Preprocessing
is an ideal dealer whose per-party streams are committed.

## Attacks (Codex round 1's list) and what refuses them

| attack | FHE fork | MPC fork |
|---|---|---|
| wrong δ | decryption gate: certificate input handle ≠ the custodians' committed δ ciphertext | online MAC check |
| mixed source limbs / sources | gate: opened residues do not hash to the committed handle | online MAC check |
| unrelated boundary shares | v1: NOT caught online (sampled conversion audit, 2 of 3). **v2: refused on every step by R_PD** | online MAC check |
| wrong quotient | gate: output base extension (pinned u) fails | online MAC check (truncation opening) |
| stale parent | gate: input handle ≠ current head | chain: input commitment ≠ head |
| missing audit response | fail-closed alarm | fail-closed alarm |

## Gen 4 (2026-11-06): batched ZKPoPK (decision doc §20)

| file | what |
|---|---|
| `zkpopk_ligero.py` | Batched Ligero ZKPoPK over a 255-bit NTT field: secret-key batches bound to the registered key (MPC helper sends), public-key batches (FHE (b) masks); per-prime folding with committed integer quotients; legacy statement-only transcript and a simulator, for the falsifier only |
| `run_zkpopk_ligero.py` | `python3 run_zkpopk_ligero.py [N L M T [honest]]`: honest batches, the attack table, the FS-ordering falsifier, Codex-trace regressions, the gate in front of `he_matvec.ptxct`; writes `zkpopk_ligero_results_N*_L*_M*.json` |
| `zkpopk_counts.py` | per-step proof bits at d = 64/1024/4096 for both forks, T = 97 and 309, N = 8192 and 16384; writes `zkpopk_counts.json` |
| `leaf_salt_falsifier.py` | unsalted Merkle leaves as a guess-confirmation oracle (n-1 custodians plus a guess of a committed row), refused once leaves are salted (`cosnark.SALT_LEAVES`) |
| `keygen_ceremony.py` | commit-reveal key-generation ceremony, key-only ZKPoPK per custodian, `CeremonyKey` for he_matvec/he_outer, the whole-ciphertext simulator, the envelopes and distances (decision doc §21) |
| `run_keygen_ceremony.py` | `python3 run_keygen_ceremony.py N L d F_bits T`: ceremony and its attacks, an MPC step (HE matvec + outer) on the ceremony's keys, realized shift versus envelope per return kind, the simulator on every return; writes `keygen_ceremony_results_N*_L*_d*.json` |

Profiles (gen 4): `proofwire.PROFILES` holds `ledger` (T = 309, the default) and `demo` (T = 97); run scripts and
`zkpopk_ligero` default to 309. Result files without a `_T97` suffix are the ledger profile.
| `rlwe_estimate.py` | lattice-estimator (malb, commit d8576372) under Sage for the exact RLWE instances at both HE parameter sets; run on dregg-forge; results `rlwe_estimate.json`, `rlwe_estimate.log` (decision doc §22) |
