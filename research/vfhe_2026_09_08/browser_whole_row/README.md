# Three public proofs with arithmetic on the final row

[EXECUTED] The saved learner expiry and both saved `fast001` linear query
computations have **new proofs under all-row templates**. All three pass through
the unchanged existing IR2 WebAssembly verifier in Node. The published update
button's changed-output control also reaches that verifier and fails. These are
replacement proofs; the historical fixtures and their terminal-row gap remain
preserved.

| Saved computation | New proof bytes | Native proving | Node WASM acceptance |
| --- | ---: | ---: | ---: |
| Learner event 65, `acc + fresh − old` | 508,996 | 2,084.48 ms | 1,476.06 ms |
| `fast001`, `card_arrival` | 842,472 | 4,428.09 ms | 1,514.91 ms |
| `fast001`, `cash_withdrawal_charge` | 842,594 | 4,117.40 ms | 1,476.58 ms |

[EXECUTED] Each selected statement has 8,192 exact-public rows of width 57.
Native proving times come from the existing prover's `prove_ns`; each prover
also self-verifies once. The separate Node process performs four actual proof
checks: three acceptances and one changed-statement rejection. Changing update
row 0, column 43 from 26 to 27 with the genuine proof returns
`InvalidOpeningArgument(InvalidPowWitness)`. No malformed proof was produced or
repeated. The complete Node process took 5.993 seconds with empty stderr. These
are single shared-host Node v26.8.1 WebAssembly observations on darwin/arm64,
not browser-engine or network measurements. Commands and output are retained in
[results/](results/), particularly [verify-node.json](results/verify-node.json).

## What changed

[SOURCE/EXECUTED] The existing strict [whole-domain migration](sources/repair_template.py)
replaces 1,456 expiry or 2,744 query `gate` wrappers with
`window_gate/on_transition=false`. Every polynomial body, public lookup and
other descriptor field is preserved. The query template is byte-identical to
the already executed source-derived Lean whole-domain emitter. The expiry
uses its existing Lean-emitted row-local arithmetic with the same generic
strict migration; it has no newly compiled expiry-specific all-row theorem.
[The two migration records](templates/) retain original and replacement hashes
and exact body-preservation checks. [Source origins](sources/ORIGINS.json)
identify the emitter and source modules without introducing another AIR.

[SOURCE] The query arithmetic enforces both ciphertext/plaintext products and
their subtraction for the selected stored NTT coordinates. The expiry arithmetic
enforces the selected two-prime modular `acc + fresh − old` operation. These
equations now apply on the physical final row as well as every earlier row.
The [whole-domain source theorem](../../proof_frontier/2026-09-08/ir2_verifier_bridge/air_pcs_join/whole_domain/README.md)
and its public-multiset premise explain the mathematical scope. JSON serialization,
native parsing, exact-public lookup, PCS, Fiat–Shamir and the actual native/WASM
implementation remain separate proof and trust boundaries. This package does
not claim universal native acceptance implies correctness.

[EXECUTED] The same fixed public ciphertext cases, saved public rows and existing
Lean-derived witness traces were reused. No encryption, key generation, text
encoding, private read, decryption, witness emission or new WASM compilation was
performed. Only the selected arithmetic wrapper and resulting proof objects
changed. [SOURCE_PINS.json](SOURCE_PINS.json) pins the existing traces, public
case inputs and actual native binaries used. The 2,063,586-byte unchanged WASM
hash is `96137c1ed0ad5fc7584ca72ef006ff70ac1951831408ee12ab22ce3879f6f908`.

## Publish the corrected examples

[SOURCE] Root owns the site edit and publication. [ASSET_MAP.json](ASSET_MAP.json)
lists replacement assets and exact hashes; the existing generic verifier,
query consumer, shared worker and WASM assets remain byte-identical.

- Copy `update/fixtures/learner-expiry/` to the site's current expiry-fixture
  location. Replace the application's selected update-template hash with
  `112a0982fc384272c5b24da9f4c2f4617078be22afe27aca59dad08c73b479e5`.
  The existing public row-zero changed-output button was exercised here.
- Copy `query/fixtures/` to the site's existing `query-bundle/fixtures/`.
- Copy `web/query-case.js` to the site's existing `proof/query-case.js` and
  change the expected case ID to
  **`fast001-all-row-reproof-two-class-query`**. The new query-template hash is
  `504ec55e5421ec3116fff563974a1ef6f849fb08caea20daec3f0fcf72c9c933`.

[SOURCE] The query metadata retains source revision 2, model root
`742982ae2402dc944074f0df249d412040ef273df392803810a92c434c807204`,
request ID `new-two-class-query`, original query/output identities and class
labels. The historical source request is preserved byte-for-byte at
`query/original_request.json` and embedded in the new explicitly non-authorizing
reproof context. Its original proof/template pins are historical evidence; the
new `query-case.js` selects the replacement bytes. No journal receipt or original
request was rewritten or represented as a newly authorized live request.

[SOURCE] The shared worker API is unchanged: `{id, bundleBaseUrl}`, with a base
ending in `/`. It calls the same exported query consumer executed in Node here.
`query-consumer.js` retains its predecessor's default standalone layout; this
package's two sub-bundles use the provided explicit loader in `verify.mjs`, or the
existing shared worker's `bundleBaseUrl` loader. Browser UI execution was not
performed. A browser demo of these three equations does not verify the complete
116-proof nonlinear class, decryption, encoder, FIFO authorization, key membership
or current model head. No new cryptographic security estimate follows.

## Reproduce

[SOURCE] `python3 run_proofs.py` records the three native proofs using the pinned
public cases/traces in the workspace. `python3 package.py` creates the isolated
public bundles. `python3 run_node.py` records the four Node WASM decisions. Each
writer refuses to overwrite retained output. `node verify.mjs` directly replays
the public-only consumer with no native binaries or companion checkout required.
For a new prover experiment, copy the small scripts into a fresh sibling output
directory and explicitly change its source selection; do not rerun over this
frozen result. Source trace regeneration belongs to the existing expiry Lean
emitter and query native witness-plan emitter, whose origins are pinned here.

[EXECUTED] Web and Scry queries for this package: 0 and 0. No companion tree or
website checkout was modified by this lane.
