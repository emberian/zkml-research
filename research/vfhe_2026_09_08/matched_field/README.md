# Matched-field complete BFV update and linear prototype

[EXECUTED] The first complete real FIFO-expiry run succeeded without source fixes:
32 fresh update proofs and 352 fresh linear proofs were all independently
consumed. Both output ciphertexts are byte-identical to the retained lifecycle
captures. The exact evidence is `experiments/fifo-expiry-run001.json` and
`COSTS.csv`; large runtime/proof files remain under ignored `work/`.

| Complete operation | Produce wall | Consume wall | Distinct proof bytes |
|---|---:|---:|---:|
| Update, 32 chunks | 2.61 s | 1.20 s | 5,721,926 |
| Linear, 352 chunks | 45.05 s | 14.20 s | 64,336,438 |

[EXECUTED] These are shared-machine observations: this lane used one worker while
the parent reported four baseline workers. Linear producer/consumer maximum RSS
was 186,662,912 / 181,125,120 bytes. The linear native public FHE import took
0.370 seconds; direct MAC checking took 0.0108 seconds after row reconstruction.
The consumer spent 0.272 seconds reconstructing rows, 10.040 seconds committing
their preprocessing, and 2.780 seconds in cryptographic verification. Proof
consumption remains much more expensive than computing this small model directly.

[EXECUTED] After complete success, an altered proof commitment with its outer
manifest digest refreshed was rejected by the native consumer with `CapMismatch`;
a wrong caller accumulator digest was also rejected. Neither failure emitted a
success report. No new proofs were generated for these controls.

[DERIVED from `native/src/proof.rs` and `native/src/main.rs`] This isolated research
backend proves complete accumulator updates and the eleven-stage linear dot operation over the exact four
BFV RNS primes. Each of 352 chunks contains 1,024 coefficient rows, sixteen public
preprocessing columns, and one zero main column. Two MAC equations are asserted on
every row, including the last. There are no bit, carry, or range witnesses.

[OPEN] This is a new Rust AIR and field/PCS integration. It is not the predecessor's
generated Lean descriptor, a shipped backend, or a new end-to-end formal theorem.
Build and execution status, including failures, are retained in `STATUS.md` and
`experiments/`. No old backend numerical soundness claim transfers to this profile.

## Exact relation and public binding

[DERIVED] For each prime `q`, stage, and coefficient, the public row is
`(d0..d3,k00..k03,k10..k13,a0,a1,o0,o1)` and the AIR asserts
`a_c + sum_j d_j*k_cj = o_c` in `F_q`, for both `c=0,1`. Since every integer
operand is checked to lie in `[0,q)`, this field equation is exactly the desired
integer congruence modulo positive `q`. The native field/PCS interpretation also
needs prime `q` and correct Rust field operations; the field tests exercise those
premises.

[EXECUTED: Lean] `formal/matched-field-arithmetic.patch` proves the canonical
residue relation and composes an accepted FIFO update with all eleven existing BFV
linear stages. `MatchedFieldProgram.updateThenLinearSound` needs no carry, range
or lookup premise. The two-module package includes nonzero joined witnesses and
29 guarded axiom footprints. Native proof extraction and public IO/NTT
reconstruction remain outside that theorem; see `formal/README.md`.

[DERIVED] `linear::reconstruct` parses the caller-selected model, bounded query,
public evaluation key, and all eleven canonical trace ciphertexts once. It performs
public SIMD encoding, the fixed exponent permutations, residue lifts and NTTs once
per stage, then produces all 44 prime/stage groups. The fixed permutation formula
is checked against every entry of the supplied linear plan. Stage zero represents
ciphertext/plaintext multiplication. The remaining stages represent public
automorphism, switching MACs and affine additions. The final trace bytes must equal
the bound dot ciphertext bytes.

[DERIVED] Every consumer computes the public preprocessing commitments itself.
The transcript additionally binds the profile, modulus, chunk index, exact public
row digest, and the five digests for plan/model/query/evaluation-key/dot. The caller
must supply expected model/query/evaluation-key hashes and may additionally require
an expected dot hash. A producer's exported rows, metadata, verification key, and
self-check do not supply consumer acceptance. All 352 indexes are required in
order; an invalid/missing proof fails the complete operation.

[DERIVED] The update path uses the same AIR with
`d=(fresh0,fresh1,old0,old1)`, `k0=(1,0,q-1,0)`, `k1=(0,1,0,q-1)`,
`a=acc`, and `o=out`. Its 32 chunks cover both ciphertext components at all
8,192 coefficients of all four primes, asserting `out=acc+fresh-old`.
Its independent caller expectations pin `acc_sha256`, `fresh_sha256`,
`old_sha256`, and optionally `out_sha256`. The transcript distinguishes update
from linear statements even though they share the arithmetic relation.

## Profile and assumptions

[SOURCE: local implementation inspected] The dependency is Plonky3 revision
`82cfad73cd734d37a0d51953094f970c531817ec`, with the existing local `p3-fri` and
`p3-challenger` patches selected in `native/Cargo.toml`. `SerializingChallenger64`
samples a masked `ceil(log2(q))`-bit value from hash bytes and rejects values `>=q`;
it does not reduce a uniform `u64` modulo `q`. Under ideal uniform hash bytes this
gives uniform base-field samples. Quartic challenges use four such coefficients.

[DERIVED] The single experimental profile uses 8x LDE, 64 FRI queries, maximum
folding arity 8, final polynomial length 1, quartic challenges, and zero proof of
work. A 1,024-row trace has an 8,192-point LDE; all four primes have two-adicity 14.
Leaf hashing, internal-node hashing, and transcript hashing use standard SHA-256
with three disjoint explicit domains. There are no custom Poseidon parameters.

[OPEN] No numerical security level is asserted. The remaining assumptions include
the new field and canonical parser implementation, the Rust AIR-to-polynomial
semantics, public preprocessing commitments, the patched Plonky3 PCS/FRI verifier,
SHA-256 binding and Fiat-Shamir modeling, proof deserialization, and the application
controller. This profile needs its own security analysis, including composition
across all chunks. Algebraic tests and successful proofs are not such an analysis.

[DERIVED] The PCS is nonhiding. Every committed MAC operand is already a public
ciphertext, public evaluation-key coefficient, or deterministic public transform.
The API reads no private key and offers no decryption or release gate. Encryption
security and BFV decryption correctness remain separate assumptions.

## Cost interpretation

[DERIVED] Every relation input is public. A consumer could reconstruct the rows
and check the modular MAC equations directly, which is substantially less work
than constructing FRI preprocessing commitments and verifying their proofs.
`check-case` records that direct comparison separately; independent proof
consumption never substitutes this direct check for the proof verifier.

[REPORTED: parent continuing-lifecycle run, not a matched-field measurement] The
current small-model public FHE capture takes about 1.64–1.69 seconds per class,
versus 34.2–34.4 seconds for the predecessor's independent full proof verification
and 499–531 seconds for complete quadratic production. This matched-field backend
changes only the linear computation/proof design, so comparison with full quadratic
figures must preserve that difference. The older linear MAC prefix figures are
164.104 seconds of proving and 64,418,707 bytes in the retained
`nonlinear_performance_successor/runtime/run001/RESULT.json`. These are predecessor
measurements, not predictions for this backend.

[DERIVED from the two recorded byte totals] The new linear proof bundle is only
82,269 bytes smaller than that predecessor MAC prefix. Field matching did not
produce a substantial wire-size reduction in this chosen profile. The profiles
also use different query/grinding/hiding choices and lack a common derived
security level, so these observations are not a security-equivalent benchmark.

## Native interface

```text
vfhe-matched-field import PLAN MODEL QUERY EVALKEY NEW_CASE
vfhe-matched-field prove-linear PLAN CASE NEW_PROOFS
vfhe-matched-field verify-linear PLAN EXPECTED CASE PROOFS NEW_REPORT
vfhe-matched-field check-case PLAN CASE NEW_REPORT
vfhe-matched-field prove-chunk PLAN CASE INDEX NEW_PROOF
vfhe-matched-field verify-chunk PLAN EXPECTED CASE INDEX PROOF NEW_REPORT
vfhe-matched-field profile
vfhe-matched-field import-update ACC FRESH OLD NEW_CASE
vfhe-matched-field prove-update CASE NEW_PROOFS
vfhe-matched-field verify-update EXPECTED CASE PROOFS NEW_REPORT
```

[DERIVED] `caller.py` wraps the complete producer and independent consumer with
explicit executable/plan/source pins; see its CLI help. All source inputs are
caller-selected. The fixed plan comes from the retained linear-plan artifact.
Each output must be new. No command generates FHE keys, reads a private file,
decrypts a ciphertext, or modifies either companion tree.

```sh
CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 /Users/ember/.cargo/bin/cargo build \
  --release --offline --locked --manifest-path \
  research/vfhe_2026_09_08/matched_field/native/Cargo.toml
CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 /Users/ember/.cargo/bin/cargo test \
  --offline --locked --manifest-path \
  research/vfhe_2026_09_08/matched_field/native/Cargo.toml
```

[OPEN] The ignored full-profile proof test intentionally requires a coordinated
proof slot. The retained Cargo lock and absolute dependencies support this working
tree, not a portable fresh-clone build. Changes to source/binary/plan pins require
a deliberate new profile; no command silently repins an existing profile.
