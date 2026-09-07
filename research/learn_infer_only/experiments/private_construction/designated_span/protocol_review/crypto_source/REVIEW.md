# Frozen designated crypto source and data-flow review

[DERIVED verdict, 2026-09-07] No blocking defect found in the inspected normal
path. The source implements the reviewed designated projection equations,
separates its state/output/recipient-key envelopes, and makes the trusted
context-validation cache premise explicit. The recorded normal evidence is
consistent with that source and its stated 33-Learn/four-read/one-expiry scope.
This is source inspection plus read-only public artifact checks, not a new
cryptographic execution, universal source refinement or privacy implementation
proof.

## Versions and evidence actually checked

[EXECUTED] [source_inventory.json](source_inventory.json) rehashes all 25
files/dependencies declared by frozen `crypto/source_manifest.json`, SHA256
`325d8f4b858b7f3116dbe21c76199013cee38e057699db040469f15d66fde692`.
All declared hashes and lengths match, including the native library and
interpreter. Principal runtime source:

| Source | SHA256 |
|---|---|
| `crypto.py` | `d7dfc2f46044ea438e1de548b6f922720cf36418b02bc02dac095cbc5851adb0` |
| `group.py` | `80f59f9d5ca909953499adc06d19ca28750c50e33f01a382fcc719ca2f403fac` |
| `native_pow.py` | `88f146b24dd3c605231d2a1a2091731725aa1edd2df237534698690da5d242b7` |
| `rows.json` | `33cbd907a0499ccad3cd5fc1a23570daccec616c7598b05d456fa1a59998fae0` |

[SOURCE] Both drivers and the native helper were read in full. The author
positive suite report is `6c5fdf598bfcef1c199c77ba515dc39c1f8b93b7efba4791187463b4338439f5`;
its separate normal-artifact/private-integer validation is
`b1a0ea09e8ca067c6c7d93159c44fcbe3e21d3f62879f192e660238fe492595e`.
That validator reconstructs each window coordinate before taking its dot
product, independently of the driver's per-input-score summation. Its source
and retained booleans were inspected; this reviewer did not reread private
vectors/answers or rerun those comparisons. The older uncached source/result
remains a distinct historical version, rather than evidence executed under
the final source.

## Setup, surviving credentials and input coins

[SOURCE] `crypto.py:305` places all 577 master samples only in the
`initializer` child. Its save calls write public bootstrap h and 16 private
projection scalars `k_i`; they do not serialize s. Each `recipient-register`
child reads its designated scalar delivery, samples an independent `a_i`,
writes that pending scalar, and publishes `A_i,tau_i`. The parent collects
public registrations. `recipient-finalize` reads only its pending `a_i`,
checks `g^a_i=A_i`, and wraps it with the complete public context identity.
The normal orchestrator removes each k delivery after registration and each
pending a after finalization; its temporary setup directory is then removed.
The final zero state is the 578-component group identity.

[EXECUTED] The recorded setup contains one initializer, 16 registration and
16 finalization children. A metadata-only inspection of the existing final
recipient directory finds exactly 16 regular files, each 435 bytes/mode 0600,
inside a mode-0700 directory. There are no other entries in that directory.
No recipient file was opened or hashed by this reviewer. These observations
cover the successful recorded setup, not arbitrary crashes, hidden copies,
unlinked disk remnants or process memory.

[SOURCE/DERIVED] The master, each recipient mask and each fresh input r are
drawn with `secrets.randbelow(Q)`. There is no caller seed, persisted writer
master, or reused source variable between fresh issuer calls. Encryption
shares one r across one input's coordinates intentionally. The native helper
is constructed without its optional private recording list, so its default
path does not retain an audit list of secret exponents. BN clear/free does
not establish clearing Python integers, temporary byte strings or operating
system copies. All such erasure/isolation assumptions remain open.

[EXECUTED] All 33 recorded fresh public `c0` fields are distinct. This is
consistent with the source's independent sampling, but neither uniqueness
nor OS-backed API use is a proof of independence, unpredictability or the
private execution boundary. The issuer's original vectors remain private
runtime artifacts; an issuer coalition knowing their complete history is
outside host-only input privacy.

## Context cache and byte identities

[SOURCE] `load_context` at `crypto.py:174` has two clear modes. The ordinary
mode checks the public h/A subgroup elements and all 16 token equations in
addition to canonical JSON, fields, fixed rows and identities. The cache mode
first rehashes the complete file against a caller-supplied digest, then still
checks canonical parsing, shape, scalar/group ranges and every deterministic
identifier. It skips only the subgroup/token-equation checks. The
`validate-context` command refuses use of the cache flag and returns the
context digest with all four source hashes after its full check.

[DERIVED] The digest flag is trusted configuration derived from prior
validation; it is not a self-authenticating certificate or an implementation
of validation on its own. The caller must bind the successful uncached check,
exact bytes and actual validator/dependency version to trusted setup/genesis.
README and the corrected contract state that premise. Native/interpreter
trust still exists even when the four local source hashes match. This review
does not independently certify the sibling integration's trust chain.

[EXECUTED] In the recorded normal command sequence, the full validation and
matching source hashes precede all 83 cache-bearing calls. They use the same
context digest, `234506b710398f029b4d37505fbc66b80df28b55641cfd5b75e4683e1b676a78`.
The copied runtime sources match the frozen four-file package. The full
validation result records 593 subgroup checks and 16 token rows. These are
source-matching observations of this run, not acceptance of arbitrary cached
configurations.

[SOURCE/DERIVED] The header is exactly 179 bytes, big-endian, binding kind,
params/context, row index and row/recipient/token digests plus payload length.
State is 578 group elements (148,147 bytes), output is two (691 bytes), and
secret is one scalar (435 bytes). State uses its sentinel row and zero row
digests. Other kinds require exact registered identities. `unpack` checks
width/count, fixed context, canonical re-encoding, subgroup membership for
ciphertexts, and scalar range/registration for recipient secrets. Queries
must equal the exact canonical registered query object. The public inspect
branch refuses secret envelopes; private inspection removes the private-file
hash from its returned metadata. Same-account filesystem access is still
not a sandbox isolating arbitrary processes from key paths.

[EXECUTED] An independent read-only parser checked 71 existing public
operation outputs against recorded hashes, complete header lengths and
context/row identities. All four Infer outputs retain their input state's
public randomizer component. Exact bytes of the final transition replay
equal the recorded final accumulator. No ciphertext was modified or supplied
to a cryptographic program for this review.

## Arithmetic and honest integer semantics

[SOURCE/DERIVED] The private issuer accepts exactly 577 integer coordinates
in [-127,127]. Its lookup table is `g^x`; its ciphertext is
`(g^r, h_j^r*g^x_j)`. Learn multiplies components, then divides by the exact
bytes of the supplied old object when present. Infer uses the selected fixed
row and computes `product(c_j^y_ij)/c0^tau_i`. Recipient division by
`c0^a_i` therefore yields `g^<sum(active inputs),y_i>` under the reviewed
honest setup and caller-maintained window semantics.

[DERIVED] The bounded decoder uses `m=ceil(sqrt(2B+1))`, baby powers
`g^j`, and shifted target `g^(score+B)` with giant multiplier `g^-m`.
For every score in [-B,B], write `score+B=i*m+j`; the loop includes its i
and the table includes its j. The candidate-range check and final exponent
equality ensure the returned integer lies in that interval and encodes the
target. The asserted `q>2B` gives uniqueness. This is a source-level
mathematical derivation assuming correct group/native arithmetic, not a
formal proof of Python or OpenSSL.

[EXECUTED] From the frozen public rows, the reviewer independently
recomputed all 16 bounds `B_i=32*127*sum(abs(row_i))`. The maximum is
14,219,936, and the stated group q exceeds twice that bound. The four author
reads occur at admissions 0, 1, 32 and 33 on rows 0, 7, 8 and 15. Thus the
four private comparisons consist of a known zero control and three nonempty
reads; the evidence must not be described as four nonempty private examples.
The API's `sign` is signum (-1,0,1). A positive-tie classifier must separately
use `score>=0`, as the final README already explains.

[DERIVED provenance boundary] The metadata field
`expired_exact_supplied_original` records whether `--old` was supplied and
used. It does not establish that the object was the original queue entry.
Likewise `queue_capacity_and_old_identity_enforced_by_caller` describes a
caller obligation, not evidence that an arbitrary caller fulfilled it. The
documented standalone CLI does not attest origin, range, window capacity,
parent/finality or authorization. The normal driver's final old reference is
the original `fresh00.ct`; a composed authority/receiver still must enforce
the complete history for itself.

## Public and private records

[EXECUTED] [public_records.json](public_records.json) records 86 existing
top-level commands, 46 public-role calls with no secret-key argument, and
four private decoder calls whose stdout and individual elapsed time are
omitted. Source inspection and a recursive public-response key check find
no signed scores or BSGS timing/iteration fields in the nonprivate responses
of this normal run. The source suppresses private scalar/file hashes; public
context, ciphertext and token hashes are expected public data. Private
filenames/role identities and the fixed query schedule remain visible.

[DERIVED limit] Public setup/issuer timings and the aggregate benchmark
duration remain in the reports. Aggregate duration includes private decoding;
successful benchmark completion also depends on private comparison checks.
Consequently the complete benchmark report bytes are measurement evidence,
not a demonstration of the protocol's secret-independent public transcript.
They must remain outside that protected-transcript claim unless explicitly
modeled as additional leakage. RESULTS already cautions that its aggregate
timing is outside a timing-free model. The separate public acceptor/private
drain integration still needs its own data-flow correspondence review.

## Reproduction and final limits

[EXECUTED] The only new artifact-check command was:

```sh
python3 -B check_public_records.py > public_records.log 2>&1
```

It ran from this directory and exited zero. It reads existing public records,
source files and file metadata, and writes only reviewer output. It calls no
crypto/native arithmetic and reads no key, private vector or private answer
bytes. The separate manifest rehash likewise executed no listed dependency.

[DERIVED] Accept the frozen backend as inspected normal functional evidence
for the explicitly conditional construction. No source repair is requested
by this review. Actual erasure, OS/process isolation, secret-independent
diagnostics, arbitrary-input soundness, trusted cache provisioning, primitive
security instantiation and recipient-restricted communication enforcement
remain unproved. No expensive suite was rerun, no new adversarial/malformed/
routing/extraction runtime was run, and no author/core/shared/companion file
was changed or committed.
