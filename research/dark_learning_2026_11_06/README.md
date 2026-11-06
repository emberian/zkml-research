# Dark learning, 2026-11-06: experiment 1 (ct×ct certificate, crossing wire) and the d = 64 step

Pure Python 3.10+, no dependencies. Every number printed is a COUNT (elements, bits, wire elements,
openings); nothing is timed. Decisions these feed: `docs/DARK-LEARNING-SCHEME-DECISION.md`.

## Rerun

    python3 rescale_certificates.py A B B61 C   # experiment 1a: one ct×ct + integer rescale certificate, 4 designs
    python3 crossing_wire.py                    # experiment 1b: one fused sigma/sigma' crossing at N = 8192
    python3 run_d64.py mpc                      # d = 64 step, MPC fork (minutes)
    python3 run_d64.py fhe                      # d = 64 step, FHE fork (N = 8192 ciphertexts; a build box)
    python3 run_d64.py                          # both; writes d64_results.json

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
| `cert_b61.py` | the FHE fork's ct×ct certificate: explicit witness + verifier (the decryption gate) |
| `fhe_fork.py` | FHE fork of the step: host ct×ct with certificates, custodian crossings, conversion audit |
| `mpc_fork.py` | MPC fork of the step: whole step in SPDZ |
| `run_d64.py` | the milestone: honest run + Codex's attack list on both forks, same counts columns |
| `*.log`, `d64_results*.json` | outputs of the recorded runs |

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
| unrelated boundary shares | NOT caught online. The conversion audit catches it when the deviating custodian's view is opened (2 of 3 beacon selections) | online MAC check |
| wrong quotient | gate: output base extension (pinned u) fails | online MAC check (truncation opening) |
| stale parent | gate: input handle ≠ current head | chain: input commitment ≠ head |
| missing audit response | fail-closed alarm | fail-closed alarm |
