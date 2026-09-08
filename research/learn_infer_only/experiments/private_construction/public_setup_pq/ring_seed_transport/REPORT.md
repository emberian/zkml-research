# Executed public-seed transport savings

[EXECUTED] The final public issuer bundle occupies **9, 471, 269 bytes**,
compared with **379, 390, 500 bytes** for the preceding ideal-uniform public
file: **40.057 x smaller**, or **97.504% fewer bytes**. The new bundle consists
of the 974-byte seeded manifest and the 9, 470, 295-byte explicitly packed
recipient registry. Both are actual written files and inputs to the issuer.
The separate605-byte initial A descriptor is embedded in the manifest and
is not an additional final-bundle dependency.

| Stored/transmittable item | Actual bytes |
|---|---:|
| Initial A-seed descriptor |605|
| Explicit16-row recipient registry |9, 470, 295|
| Seeded public manifest, including A descriptor |974|
| Final issuer bundle |9, 471, 269|
| Previous ideal-uniform public file |379, 390, 500|
| Fresh ciphertext, unchanged format |37, 901, 312|
| Private recipient key, unchanged format |3, 801, 648–3, 801, 649|

[EXECUTED scope] This measured file transport is local. The table gives
actual stored bytes and the serialized files required for an issuer transfer,
not a measured network-wire benchmark. Individual registration archives and
ciphertexts are retained separately. The comparison concerns the completed
public-key bundle, not the total disk use of all intermediate/output files.

[EXECUTED] One fresh full setup, three encodes, signed combination, exact
two-item expiry and 20 designated outputs passed across 45 new actor PIDs.
The complete workflow took **138.788 seconds**. All 16 recipients independently
read the final window; recipient 0 additionally read the three fresh inputs
and signed 2*C0-C1 state. Public roles read no private artifacts. Private keys
and decoded values remained in ignored recipient-specific directories.

| Actual work | Calls | Total seconds | Per-call seconds |
|---|---:|---:|---:|
| A-seed initialization |1|0.133|0.133|
| Fresh recipient key generation/registration |16|70.101|3.674–6.764|
| Registry packing and absent-seed finalization |1|0.248|0.248|
| Streamed seeded encoding |3|33.803|11.162–11.439|
| Signed combination |1|1.970|1.970|
| Window creation/update/expiry |3|8.583|1.761–3.908|
| Separate-process designated decode |20|23.763|1.144–1.268|

[EXECUTED] Peak actor RSS was 490, 242, 048 bytes. This issuer retains A and
the 16 explicit recipient rows; only one expanded absent row is retained at
a time. Expanded A and absent rows are not written to storage. These are
single shared-machine measurements. The previous transport had a different
public setup distribution; byte savings are compared directly, while no
security-equivalent performance guarantee is inferred.

## Concrete construction and interfaces

[DERIVED implementation] `seed_transport.py` implements init, register,
finalize and encode. `expansion/PublicExpander` provides canonical
domain-separated, index-addressable SHAKE256 chunks with exact rejection
into q. A's domain binds the fixed profile, parameters, setup identifier and
recipient policy before registration. Each recipient samples its own fresh
row and publishes its actual product. Finalization packs those products,
then samples an independent absent-row seed and binds its domain to the
exact A descriptor and registry digest. There is no circular A/registry
dependency and no generated absent-recipient secret.

[DERIVED/EXECUTED] The earlier uniform A was not reused: a compact seed
cannot retroactively encode it. Previous recipient rows were also not reused
against a different A, which would introduce additional public products
outside the one-setup analysis. Exactly 16 new private rows were generated in
this run. The old setup and private artifacts remain untouched.

[EXECUTED] Public residues are reconstructed by masking to the modulus bit
width and rejecting candidates at least q. Fixed addressed chunks avoid
re-hashing ever-growing XOF prefixes. The exact finite Gaussian sampler,
negacyclic ring arithmetic, packed ciphertext/key codecs and designated
integer decoder are the unchanged completed implementations. Signed
evaluation, expiry and decode invoke the previous `ring_transport` CLI.
The seeded manifest format records the new computational mode; it must not
be described as the old ideal-uniform mode merely because ciphertext bytes
use the same codec.

[EXECUTED process scope] Saved OS sandbox profiles deny the current private
artifact tree to public actors and other recipients' directories to each
recipient. Both benign canary reads were actually denied. Private directories
are mode 0700 and keys/outputs mode 0600. Actors share a host UID; these claims
concern the executed artifact-path policy, not malicious host administration
or sandbox escapes. The orchestrator/summary do not open private payloads.

## The theorem obligation remains separate

[DERIVED] A revealed seed and its expanded matrix cannot be replaced by that
same seed and an independent uniform matrix: recomputation distinguishes
them. Ordinary hidden-seed PRG security therefore supplies no such hybrid.
Exact rejection establishes uniform accepted residues only under the
independent ideal-XOF-word model; it is not statistical compression by
concrete public SHAKE256 seeds.

[OPEN] Seeded Ring-LWE for A alone is also insufficient for the previous
functional-encryption proof. Replacing seeded absent rows with Gaussian
products while retaining the unprogrammed absent seed violates another
recomputable relation. A consistent full joint programmable-XOF simulator,
including QROM/advice resources if claimed, or a different direct proof
covering the complete seeded setup is still required. The SHA256 binding
digests add their own computational collision-resistance premise. See
`SECURITY.md` and `expansion/SECURITY.md`; no PQ/full-privacy result is
asserted from the successful run.

## Exact saved execution

```sh
../ring_implementation/.venv/bin/python -B workflow.py --profile candidate_full --run candidate001 > candidate001.log 2> candidate001.stderr.log
../ring_implementation/.venv/bin/python -B summarize.py > SUMMARY.log
```

[EXECUTED] `results/candidate001/WORKFLOW.json` records all 45 commands,
public artifacts, recipient metadata and receipts. `SUMMARY.json` derives
the comparisons from those public receipts and the frozen baseline summary.
Runtime source hashes remained unchanged. A preceding small toy workflow
passed in 3.765 seconds; its source hash predates only the explicit deletion
of the transient absent-row reference. There was one full candidate run,
no benchmark grid, no estimator/attack invocation and no private-payload
collection. All previous packages remain unchanged.
