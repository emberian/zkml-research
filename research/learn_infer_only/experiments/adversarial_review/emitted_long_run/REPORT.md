# Independent review: completed emitted fixed-FFT workload

[DERIVED verdict] **Accepted within the finite execution scope stated by the
author.** The completed package supports two fresh encrypted histories with
384 Learn and 96 Infer events, all 480 complete-output-byte replay comparisons,
and public closure/verification before the authorized primary audit. The
private plaintext matches remain **[REPORTED]**, with their source procedure and
public artifact bindings independently checked here. No new crypto execution,
private-file read/hash, old failed-output access, or Lean build was performed.
This review does not authorize another run.

[SOURCE frozen target] The author directory is
`experiments/end_to_end/private_ema/emitted_long_run/`, relative to
`research/learn_infer_only/`. Exact review targets:

| File | SHA256 |
| --- | --- |
| `PACKAGE.json` | `0a9a15b6ca0784b3f6de03df83b77873469ef26f59164a5663882fe2065b6ba4` |
| `REPORT.md` | `0bfcfc46d5d469d4b113c1179f0147664207a0e3c5b511c4c87e98344d8e934a` |
| Original `freeze.json` | `6cc20a07b75330c2fb7aaa19a2021c6b495096c6b477b1554eb4a2a14c7943e8` |
| Original `summary.json` | `581d4d9fd602f63658bd3ad46feea58845f1d021863af812bf4bec2147686e5a` |
| Original `reports/run001/public_seal.json` | `b2f972552b5383d05207737939ddb2fe81e0c9ff68077104e13939f786dee566` |
| Later public-only `collection.json` | `e536a7027fd89bf849d86edda20fd72cd8396e1dc69cdc737cea17f455a3e16f` |

## Independent executed checks

[EXECUTED] From this review directory:
`python3 -B check_public.py > check.stdout.json 2> check.stderr.txt`.
The retained final run exited zero at 14:48:37 UTC, with empty stderr.
`results.json` preserves all 1,447 exact input pins and aggregate results.
The script uses Python standard-library parsing, SHA256, whole-byte comparison,
Boolean/integer arithmetic and statistics; it imports no author module and
launches no subprocess. Every input is rehashed after checking. Its read guard
rejects private path components and permits runtime reads only in this run's
`runtime/run001/public/`. Private argv paths are examined only as strings.

[EXECUTED] All 49 package-listed files, all 39 original frozen source/public
inputs, and four cached TFHE/FFT primary source files match their pins. This
includes the current fixed host, issuer/reader binaries, original public/server
keys, fixture, exact formal snapshots and emitted JSON descriptors. The 1,364
public ciphertext files exactly match the public inventory, total 97,500,084
bytes, and pass magic/kind/declared-length/Boolean-count envelope checks. This
review does not deserialize TFHE ciphertexts or independently establish the
Encrypted enum variant; that boundary is source-checked and reported by all
successful hosts. All author input files remained unchanged through the checks.

[EXECUTED] The 1,364 public operation records contain exactly 960 host launches
(768 Learn, 192 Infer) and 404 issuer launches (four initials, 384 Learn inputs,
16 queries), with consecutive operation indices, unique outputs, successful
return codes, no timeout, empty stderr and matching parsed stdout. Recorded
binary and public-input before/after identities match current bytes. Every host
argument tuple is the pinned binary, descriptor, server key, selected public
parent, public request and fresh output. The saved launch PIDs differ within
every primary/replay pair; source launches a new `/usr/bin/time`/host process
for each invocation. These are process-launch records, not external OS
attestation of process isolation.

[EXECUTED] All 480 primary/replay ciphertext pairs were independently compared
as complete byte strings. Their descriptor/server-key/parent/request tuples
match, all 960 host indices are used once, and all actual reported plan records
are `Plan { base_algo: Dif4, base_size: 512, fft_size: 512 }`, with polynomial
size 1024 and Fourier size 512. Both histories start from distinct fresh initial
route ciphertexts. The entire original event order, selected-parent continuity,
unchanged other route, read-only Infer behavior and six checkpoint bindings
reconstruct exactly. Each of 16 query artifacts is used at six original events.
There are zero expiry events.

[EXECUTED/DERIVED] Independent public integer arithmetic recomputes all 384
updates, including Python floor division for negative values. A small separate
Boolean interpreter inside the checker evaluates the exact pinned descriptors
on all 480 public fixture input rows. Every 32-bit Learn result decodes to the
same selected-route vector; every one-bit Infer result equals its score's sign.
This is a finite descriptor-to-fixture control, not a replacement for the Lean
proof or an independent proof of encrypted execution correctness.

## Public closure and attributed private results

[EXECUTED] All original seal links and the full pipeline record are consistent.
The sequential pipeline has exactly four entries, each exiting zero:
`run_public`, `verify_public`, `drain`, `seal`. Each following stage starts after
the preceding stage ends. The recorded boundaries on 2026-09-08 are:

| Boundary | UTC |
| --- | --- |
| All public operations and pairs closed | 08:09:56.356621 |
| Public verification passed | 08:09:57.110689 |
| Public seal, reader count zero | 08:09:57.111440 |
| Private audit started | 08:09:57.410243 |
| Private audit completed | 08:09:59.846219 |
| Provenance-only final seal | 08:10:00.180702 |

[SOURCE/DERIVED] `run_public.py` waits for each child to exit, completes all
pairs, and closes its public streams before writing closure. `pipeline.py`
waits for successful public verification before invoking `drain.py`. The drain
rechecks frozen sources, the public seal, all public ciphertext hashes and
deadline before its first reader call. The later `seal.py` performs provenance
and cost collection only. Thus the supplied source/records substantiate the
ordered public-before-private procedure; they do not prove an OS-enforced
prohibition on out-of-band access. The public execution took 9,687.876547333
seconds, and all stages completed before the 11:28:28.472235 six-hour cutoff
and the hard 15:00 deadline.

[EXECUTED] All 484 public reader records are bound, in order, to the four
initial primary states, 384 primary Learn selected-route states, and 96 primary
Infer outputs. All report successful return codes and the expected 32/1-bit
operation, using the pinned reader. None targets a replay artifact. The public
aggregate contains the same event identities and all-match flags.

[REPORTED] The original drain reports all four initial states, 384 whole
selected-route vectors and 96 signs matching the fixture. No private key or
plaintext audit file was inspected by this reviewer. Replay plaintexts were
independently opened **zero** times; their relation to the checked primary is
the complete byte equality above. The full unrestricted reader key is retained,
and these same-account roles are not a restricted-decryption construction.

[EXECUTED/DERIVED] Matching 96 oracle signs must not be presented as 96 correct
classification targets. Independently recomputing the reused public fixture
gives **76/96** target agreement over all checkpoints and **28/32** on the final
subset. The existing final EMA and W32 aggregates are both 28/32. The run adds
encrypted execution evidence, not a new utility estimate or an improvement.

## Costs, provenance boundary and remaining limits

[EXECUTED/DERIVED] All 1,848 CSV rows independently reconstruct from the saved
public and reader operation records. Every min/median/max/sum and available
RSS aggregate matches `collection.json`. Learn host median is 11.410984 seconds
(768 launches); Infer host median is 0.319239 seconds (192 launches). Maximum
recorded host RSS is 552,091,648 bytes, about 526.516 MiB. Total recorded gate
API calls are 263,808 XOR, 151,104 AND and 1,920 internal trivial constants.
These are API counts; a bootstrap count is explicitly not instrumented.
The measurements were taken on a shared machine with one sequential worker and
`RAYON_NUM_THREADS=1`; they are not isolated performance estimates.

[SOURCE] The source-to-report chain is concrete: generic descriptor validation
and evaluation, canonical typed ciphertext input/output, the same public
server-key buffers restored after plan observation, the feature-selected
TFHE `Fft::new` branch, the process-global plan cache and Boolean bootstrap's
use of that factory are inspected at the locations in `SOURCES.md`. The saved
compiler artifact reports exactly `boolean` plus
`experimental-force_fft_algo_dif4`. Independent hashing establishes the pinned
source/binary identities; it does not reproduce the build or attest all compiler,
library, loader, filesystem and hardware behavior. Those remain the TCB.

[SOURCE observed limitation] Preserved `progress.json` says phase
`public_closed` but its static `public_phase_closed=false` and
`reader_invocations=0` fields are stale as final status. The author now explicitly
documents this. They are neither the source phase gate nor the authoritative
final audit counter, so they do not overturn the separate successful phase/seal
records. No source or historical log was rewritten to hide the inconsistency.

[OPEN] This finite run is not a proof of general byte determinism, privacy on
unknown inputs, no-master custody, restricted output access, accepted-chain
composition, QPT security, or the cause of an older failure. The public fixture
is synthetic and reused. The previous failed outputs were not accessed. Raw
public ciphertexts remain ignored local files; a metadata-only checkout cannot
repeat the storage check without those files. No corrective author change is
required for the frozen report's stated scope.
