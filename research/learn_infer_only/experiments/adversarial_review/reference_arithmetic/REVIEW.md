# Independent public arithmetic review

[DERIVED review, 2026-09-07] No defect found in the frozen packet's stated
public arithmetic and byte-correspondence claim. Independent inspection of the
primary Rust sources supports the power-basis wire interpretation, signed
negacyclic query equation, and normalized NTT index derivation. Replays and a
separate reviewer implementation agree on the retained positive samples. This
does not certify the full Rust implementation, noise correctness, provenance,
or privacy.

## Exact reviewed versions

[EXECUTED] [packet_inventory.json](packet_inventory.json) rehashes every one
of the author's 53 declared packet files, totaling 2,336,568 bytes. Every
declared size/hash matches. Core frozen versions under
`end_to_end/reference_arithmetic/`:

| File | SHA256 |
|---|---|
| `reference.py` | `304538f5114d990cd3ba7ab11a05081ef05a42ac196cdab4925a1a39cd7e2522` |
| `check.py` | `59df4e76988148c010aa342c0c1a5f0c335b9002225065446142d14ad70178d3` |
| `DERIVATION.md` | `56020189a1752f521942bfebcb2ac2884a2ee09d28af73d7d25e397eea51116a` |
| `README.md` | `f5d7278cd560832c741a1f0316089d64c91160cda20f4df7b70f51b19a48296f` |
| `source-map.json` | `316c1661f1c89e8a958f9d725a4fd6a945f30b7bb03440fcd66c47a36fc38f66` |

[EXECUTED] The author's read-only `pin_sources.py --verify` also succeeds:
21 exact source/build-evidence files rehashed. Its output is preserved in
[verify_sources.log](verify_sources.log). This checks current file identity,
including the captured binary's identity; it does not execute that binary or
prove that a compiler produced it from those sources.

## Independently checked substance

[SOURCE] `/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-math-0.1.1/src/rq/convert.rs:15`
serializes a power-basis clone while preserving the original representation
tag. The decoder at `:151` first constructs power-basis coefficients and then
changes representation. Thus tag `2` does **not** mean that the wire integers
are NTT evaluations. This important interpretation is correct in the packet.

[SOURCE/DERIVED] The same serializer follows modulus order; the fixed
moduli need 41 and 42 bits. The streaming routine at
`/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-util-0.1.1/src/lib.rs:58`
packs consecutive coefficient bits little-endian. Limb byte lengths are
20,992 and 21,504, totaling 42,496 per polynomial. The fixed polynomial
protobuf occupies 42,507 bytes; two length-delimited polynomial fields occupy
85,022; the outer 81-byte envelope gives 85,103. No per-coefficient byte
alignment or hidden limb delimiter is needed.

[EXECUTED] The reviewer independently parsed all 27 retained ciphertexts
using a cursor protobuf reader and **small byte windows per coefficient**,
then repacked every limb with a bounded streaming accumulator. All 442,368
residues agree with the author's giant-integer decoder and all limb bytes
round-trip. These are valid fixed-format samples, not a malformed-input audit
or a claim that the reviewer parser implements general protobuf.

[SOURCE/DERIVED] The actual public query route in
`end_to_end/crypto/src/main.rs:240` reverses the 577 signed coefficients,
constructs positive and negative plaintext polynomials, and subtracts their
ciphertext products. `/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/plaintext_vec.rs:93`
copies the polynomial prefix and zero-pads it; `bfv/ops/mod.rs:229` multiplies
each ciphertext component by that unscaled NTT plaintext. Therefore signed
integer bilinearity gives, with `b[j]=query[576-j]`,

```text
output[k] = ( Σ(j≤k) a[k-j] b[j]
             - Σ(j>k) a[4096+k-j] b[j] ) mod q,
```

where `0≤j≤576`. The second sum is essential below coefficient 576. This is
ordinary ciphertext–plaintext ring multiplication; the reviewed path has no
ciphertext–ciphertext scale/round/relinearization step. The BFV encoding/noise
already present in the input ciphertext does not change this public ring
operation equation.

[EXECUTED] The reviewer's output-indexed implementation of that formula,
distinct from the author's input-scatter schoolbook loop, matches all 16,384
RNS coefficients of the actual utility output. The query is dense: 270
positive, 269 negative, 38 zero coefficients. This check includes every
wrapped output position, both components, and both limbs.

[SOURCE/DERIVED] The native NTT constructor and loops in
`/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-math-0.1.1/src/ntt/native.rs:36`
support the packet's tables `ψ^rev_d(k)` and `ψ^-(rev_d(k)+1)`.
The forward descending-stride schedule evaluates at
`ψ^(2*rev_d(k)+1)`; the independently twisted cyclic transform uses the same
odd roots in natural order. At layer `m=2^r`, the matching forward/reverse
indices obey
`rev_d(N-2m+i)+1 = rev_d(m+i) = 2^(d-r-1)+2^(d-r)*rev_r(i)`.
The reverse butterfly therefore undoes the forward one up to a factor two;
the final `N^-1` removes the factor accumulated over all layers.

[EXECUTED] A separate integer bit-reversal implementation checks all 4,095
layer/block index identities at N4096. Direct polynomial Horner evaluation
at 12 selected odd roots for each of four actual utility arrays agrees with
the source-indexed forward routine: 48 independent evaluations, including
indices 0, 575, 576, and 4095. This supplements the reproduced full-array
twisted-NTT/source-indexed comparisons and 112 small basis inputs.

[DERIVED] The reference's different primitive-root selection is legitimate
for the final power-basis product. Any primitive 8192-th root permutes the
4096 odd evaluation roots, and a matching inverse removes that permutation.
The packet checks primality of both fixed moduli by trial division and
checks the selected root powers. It does not claim that its numeric roots
are the native implementation's ChaCha-selected roots. The latter's
bounded search and all literal lazy word operations remain outside this
normalized-equation derivation.

## Executed reproductions

[EXECUTED] Copied byte-identical author sources and manifests reside under
`replay_source/`; its fixture-directory symlinks point only to the retained
public packet and are ignored by git. Results are written only into this
reviewer's directory. The two suite denominators remain separate:

| Reproduction | Operations | Coefficients | Exact output bytes |
|---|---:|---:|---:|
| [Host replay](replay_source/results/run_001/report.json) | 8 Learn, 4 Infer | 196,608 | 1,021,236 |
| [Utility replay](replay_source/results/run_002/report.json) | 1 Infer | 16,384 | 85,103 |

[EXECUTED] Commands, all exit zero:

```sh
# From this review's replay_source directory:
python3 -B check.py --run run_001
python3 -B check.py --run run_002 --manifest utility-fixtures.json
# From this review directory:
python3 -B independent_check.py
# From the repository root; read-only verification:
python3 -B research/learn_infer_only/experiments/end_to_end/reference_arithmetic/pin_sources.py --verify
```

[EXECUTED] [independent_results.json](independent_results.json) pins the
reviewer script, exact reference, manifests and public input hashes.
[independent_check_002.log](independent_check_002.log) and
[utility_replay.log](utility_replay.log) preserve stdout; the host replay's
complete per-event output is preserved in its result JSON. The initial
reviewer harness call swapped the source routine's `(psi, modulus)` arguments
and failed its Horner comparison. That reviewer-only mistake was corrected;
[independent_check.log](independent_check.log) retains the failed attempt.
It is not a defect or failed test of the author packet.

## Scope that must remain explicit

[DERIVED] The four host "expiries" count operations with retained old
operands. This arithmetic check alone does not prove those operands were the
correct original queue entries. Similarly, the utility finalization packet
is a retained public provenance link: this checker does not verify its
signature, journal ancestry, or release path. These obligations remain with
the separately reviewed authority/reader implementation and any future
universal provenance proof.

[OPEN] The missing universal correspondence includes the actual source's
Shoup/Barrett/lazy bounds, unsafe memory access and representation changes,
literal protobuf/runtime domain, and source-to-binary execution. Positive
ring and byte agreement does not discharge decryption/noise correctness,
ciphertext key membership, honest input issuance, finality, or absence of
master-read credentials. These boundaries are already stated accurately in
the frozen README/DERIVATION; no author wording correction is required.

[EXECUTED scope] This review read no secret key/private vector, performed no
decryption or production arithmetic call, and ran no adversarial routing or
extraction experiment. All new numeric checks used saved public valid
samples. No companion, core, author or shared ledger file was edited; no
commit or metered query was made.
