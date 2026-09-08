# Actual nonlinear continuing text learner

[EXECUTED] A reusable teach/query session now runs an eight-example-per-class polynomial-kernel memory under BFV. The encrypted continuing state participates in an actual ciphertext square at every class query. In the fixed integration workload, all 2,560 decrypted individual kernel values, 320 class sums and 48 class decisions matched the integer reference. Two new text teachings then changed the same live query from `cash_withdrawal_charge` to the newly learned `travel_insurance` class, with all 17 before/after class sums matching plaintext. See [encrypted_result.json](encrypted_result.json), [live_result.json](live_result.json) and [README.md](README.md) for commands.

[EXECUTED] This is a new nonlinear arithmetic capability; the saved utility comparison does **not** show a kernel-specific accuracy improvement. The final kernel and requantized linear control both score 270/320 (84.375%). The old-scale linear prototype scores 269/320 (84.0625%). All of these use previously examined data, so they are exploratory reused-data comparisons, not fresh held-out estimates.

## Learner and computation

[SOURCE] `model.py`, `session.py` and `crypto/src/{main,cached}.rs` implement the object. The existing E5 text encoder and fixed 768→576 projection are reused read-only. The only feature change is `numpy.rint(old_integer[:576]/4)`, ties to even. Each coordinate is bounded by 32 and each vector's squared norm by 20,000; the maximum in the saved fixture is 16,698. The classifier is

`score(label, q) = sum((x_i dot q)^2 for active x_i of label) / active_count`.

[SOURCE] Each class stores up to eight examples in one SIMD ciphertext, at slots `feature_index*8 + example_lane`, padded to 1,024 feature positions. Teaching adds one newly encrypted lane contribution and subtracts the old contribution when that lane expires. Inference multiplies by a public packed query, reduces each dot product using nine column rotations and one row swap, and squares the resulting ciphertext. This produces three components, with no relinearization or modulus switching. The recipient checks all 8,192 decrypted slots repeat the first eight values, sums those eight, and performs division and argmax using exact rational comparisons in Python. The mean of squared individual similarities differs from squaring a class prototype similarity.

[DERIVED] Cauchy–Schwarz and the two norm bounds give each squared dot product at most 400,000,000. Summing eight gives at most 3,200,000,000, below the plaintext modulus 4,294,475,777. This prevents intended plaintext-score wraparound; it is not a universal BFV noise-correctness theorem.

[SOURCE/EXECUTED] Parameters are N=8192, t=4294475777, variance=10, level=0 and q=[1125899906826241,1125899906629633,1125899905744897,1125899905351681]. Actual key generation emitted an 8,193,050-byte evaluation key and 204,851-byte public key. Each saved three-component kernel output is 614,445 bytes. The adapter uses the existing `fhe-dregg`/`fhe-math` RNS extension, tensor multiplication and directed fixed-point downscaler. It does not substitute ideal nearest rounding. All nine product-basis limbs and four output-basis limbs are retained for all three components in [public_trace/descriptor.json](public_trace/descriptor.json). For that captured query, the entire output ciphertext also equals the native `Multiplicator` output byte for byte.

## Comparison and actual execution

[EXECUTED] `evaluate.py` processes the same 128 teaching observations and 320 test texts as the original eight-intent study, with the same per-class FIFO order. It evaluates one nonlinear architecture, with no model forwards, hyperparameter search or test reselection. All score/prediction arrays are retained in [plaintext_result.json](plaintext_result.json).

| Teaching revision | Nonlinear correct /320 | Requantized linear /320 | Original linear /320 |
|---|---:|---:|---:|
| 32 | 150 | 150 | 151 |
| 64 | 267 | 268 | 270 |
| 96 | 278 | 278 | 279 |
| 128 | 270 | 270 | 269 |

[EXECUTED] At revision 64 the nonlinear rule changes two decisions relative to the same-feature linear control, losing one correct answer and gaining none. At revision 128 their decisions are identical. The decline from revision 96 is retained. These observations provide no evidence of a nonlinear utility gain on this fixed dataset.

[EXECUTED] The separate packing check used nine real saved text vectors, one FIFO expiry and one ciphertext square, checking eight values and the complete repeated-slot layout in 7.309 seconds. The main BFV workload then performed 128 Learn operations, 64 expiries, and the first two original test rows per class at revisions 32, 64 and 128: 48 multiclass queries, 320 ciphertext squares and 3,200 rotations. All public arithmetic completed before its separate private comparison phase. Public elapsed time was 582.284 seconds; total was 611.961 seconds. The retained integration slice is not a new utility estimate.

[EXECUTED] The live fixture was saved in [live_inputs.json](live_inputs.json): three new texts were encoded once each, the plaintext session took 6.382 seconds, and the BFV session reused exactly those cached vectors. Two teachings introduced `travel_insurance`; the query “Where can I buy a policy covering medical care on my trip overseas?” changed from `cash_withdrawal_charge` to `travel_insurance`. The encrypted session took 32.449 seconds and performed 17 ciphertext squares. It uses inline full-key receiving, unlike the main batch's deferred private phase. This is a concrete learning demonstration, not a measured generalization result.

## Cost correction and reusable host

[SOURCE/EXECUTED] The original wrapper accidentally recomputed the fixed public plaintext prime for every packed residue, including 4,608 calls per class query. Caching the evaluation key alone did not remove this overhead. `crypto/src/cached.rs` now returns the already recorded prime directly. Original `main.rs`, its binary and the captured trace are unchanged; the initial cached source and binary are preserved in `crypto/cache_revision_001/`.

[EXECUTED] A single public-only replay of the already completed final nine-class query checked all complete output ciphertext bytes against the original live outputs. Every output is identical. The optimized host took 0.147 seconds to start and 0.423 seconds for the nine class computations, 0.588 seconds overall. This check performed no new encryption, teaching, encoder forward or private read. [cached_replay_002/result.json](cached_replay_002/result.json) records source/binary/input/output hashes and per-class timings. This is the optimized public stage only, not a new timing for the whole live session or a controlled cross-machine benchmark. The original batch/live timing records remain unchanged.

## Boundaries and proof seam

[SOURCE] The issuer encodes texts in plaintext; queries, labels, lane selection and active counts are public. The public arithmetic process uses only the evaluation key, but it is a logical process split, not operating-system isolation. The recipient retains the full secret and can inspect individual similarities or other retained ciphertexts. Expiry removes an example from the active model; old ciphertext files remain as evidence. Averaging, ranking and all model-map/FIFO authorization are ordinary Python/Rust behavior, not encrypted or compiler-proved by this package. No security level or complete implementation-privacy claim is inferred from the parameter choice.

[EXECUTED/OPEN] The actual product and post-downscale PowerBasis residues, exact bases and native constructor constants are available in `public_trace/`. They support the separate bounded generic 9→4 rescale proof join being built by the formal/prover lanes. This report itself claims no whole-N8192 multiplication proof: the ring convolution, rotations, encoder, FIFO policy, Rust/serde/NTT implementation and cryptographic assumptions remain outside that proposed bounded relation. The complete earlier prototype-expiry arithmetic proof is a different operation and is not a proof of this square.
