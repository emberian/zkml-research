# Semantic learning with restricted query keys

[EXECUTED] A real two-class semantic learner now runs through the ring scheme's **recipient-specific projection keys**, without a universal reader. Six freshly encrypted observations produced six class updates and two FIFO expiries. Sixteen recipients then independently read their fixed text query's scores on the two class memories at three checkpoints. All **96 integer scores and 48 decisions matched** the cached reference. The sole full-profile run completed in **217.627 seconds**, with no failure or retry. [SUMMARY.json](SUMMARY.json) and [SCORES.csv](SCORES.csv) retain the result and every score.

[EXECUTED/SCOPE] This advances the credential boundary beyond the earlier full-BFV-reader learner. Each recipient actually generated, persisted and later loaded its own independent row. No missing-row secret or universal reader was constructed. The fixed query policy, known public benchmark data, honest setup, same-host administration and conditional cryptographic assumptions remain explicit limits. It is not evidence of full resident privacy or natural-language state ambiguity.

## Actual semantic computation

[SOURCE/EXECUTED] The registry contains the first eight saved test texts for each of two predetermined classes: `card_arrival` and `cash_withdrawal_charge`. Their actual cached 576-coordinate E5/projection vectors, plus the existing final zero, form the first 16 rows of a public 577-dimensional basis B. The rows have rank 16 over the unchanged plaintext field. Leftmost modular pivot columns identify an invertible 16×16 minor; identity rows on the 561 nonpivot columns complete B. `basis.py` implements the explicit inverse and `prepare.py` checked all six actual observations round-trip. No encoder execution, query search, requantization or tuning occurred in this join.

[DERIVED/EXECUTED] For registered query i and any allowed int8 observation x, `|q_i dot x| ≤ 127 ||q_i||_1`. The largest registered query L1 norm is 9,925. A two-example sum therefore has magnitude at most **2,520,950**, strictly below `floor(p/2)=14,219,946`. Every whole-window score has an unambiguous signed representative without changing p, Delta or the noise distribution. The recipient ranks per-class means with exact rational comparisons. The class counts happen to agree at each recorded checkpoint, so the raw-sum ordering is the same here.

[EXECUTED] The first three saved training observations of each class were encrypted in alternating order. Each class retained two items; its third teaching subtracted its actual first ciphertext. Both complete final state files were byte-identical to direct sums of the two remaining ciphertext files. All 32 registered query/class scores changed between revision 4 and revision 6 after expiry. Predictions remained correct for all 16 queries at all three checkpoints. This is a known reused slice, **not a fresh accuracy estimate** or evidence that the six examples improve a general learner.

| Fixed query | Revision | Card arrival sum | Cash withdrawal fee sum | Prediction |
|---|---:|---:|---:|---|
| “How do I locate my card?” | 2 | 215,361 | 198,734 | card_arrival |
| Same query | 4 | 447,965 | 401,795 | card_arrival |
| Same query | 6 | 470,157 | 402,003 | card_arrival |
| “I see some fees for cash withdraw.” | 2 | 197,869 | 209,171 | cash_withdrawal_charge |
| Same query | 4 | 382,856 | 440,710 | cash_withdrawal_charge |
| Same query | 6 | 378,601 | 464,780 | cash_withdrawal_charge |

## The narrower key construction

[SOURCE/EXECUTED] The full frozen ring profile is unchanged: N=16,384, w=64, d=577, r=16, p=28,439,893, q=4294967767·2^256+1, sigmaK=2^25, sigmae=2^10, F=2^247, W=32, D=8,204,908,842 and Delta=floor(q/D). The original cutoff correctness inequality remained strictly satisfied. The application uses capacity 2 within that W=32 arithmetic envelope. Copied fast ring arithmetic, finite sampler, native sampler library and packed codec bytes match their frozen origins; [SOURCE_PINS.json](SOURCE_PINS.json) records them.

[SOURCE/EXECUTED] The owned adapter changes the demonstrated sparse basis into this actual semantic query basis. A new `RINGSEM1` container binds the full registry digest through public A, every recipient key/registration, complete public setup and ciphertext. Each of 16 separate registration processes generated one private row and public product. Public finalization accepted those 16 products and sampled the other 561 public rows directly uniformly. It never received a private key path. The complete source difference is [transport.patch](transport.patch).

[EXECUTED] All setup, encryption, Learn, exact expiry reconstruction, source/hash/storage checks and public actor exits preceded the first recipient read. Public closure occurred at 128.995 seconds. Each later recipient process loaded only its own key and the six public class states. It deliberately published these known-public benchmark scores in its receipt. The orchestrator read no private payload, only private file size/mode metadata and public receipts. The 48 actor launches used the inherited network-denying OS profiles; public actors were denied the complete private tree and recipient i was denied the other recipients' paths. No extra sandbox probes or extraction tests were run.

## Measured costs and reusable interface

| Actual work | Calls | Total wall time |
|---|---:|---:|
| Public A initialization | 1 | 1.770 s |
| Recipient key generation/registration | 16 | 52.298 s |
| Public setup finalization | 1 | 10.454 s |
| Fresh ring encryption | 6 | 44.023 s |
| Learn/window update | 6 | 16.189 s |
| Exact final expiry reconstruction | 2 | 3.572 s |
| Recipient reads, six scores per key | 16 | 88.615 s |

[EXECUTED] Actual files include a 379,390,585-byte complete public package, a 37,901,397-byte fresh ciphertext and a 37,901,536-byte final class state. Recipient 0's key is 3,801,733 bytes with mode 0600 under a mode 0700 directory. Peak actor RSS was 982,384,640 bytes. These are one sequential shared-machine run, including process/file costs; they are not an isolated-host benchmark or a cryptographic security estimate.

[SOURCE] [README.md](README.md) documents the reusable `encode`, `window` and `query` commands. A `query` command uses the supplied key's already registered text-query coordinate; it has no arbitrary query-vector input. New query policies require a fresh registry/setup. The completed runtime and keys stay in ignored `.runtime/normal_001/`; public commands, receipts, profiles, closure and result are under `results/normal_001/`. No prior model or private key was reused.

## What remains outside the result

[SCOPE] A recipient can apply its projection key to every retained issued observation and permitted aggregate. A coalition gets its **entire per-input query span**, not only the final mean scores exposed by the benchmark interface. The full set of 16 keys is therefore substantially more capable than one final prediction. Class routing, counts, lineage, query vectors, original benchmark texts and timing are public. Expiry removes observations from active memory while old ciphertexts remain retained.

[SOURCE/OPEN] The conditional construction assumes honest recipient key generation and registration, the specified Ring-LWE hypothesis and sampling model. This execution does not measure hardness, certify PQ security or remove host administration, malicious registration, implementation side channels, filesystem access outside the declared profiles, or a public-dictionary inference risk. The invertible field basis does not prove ambiguity of the structured natural-language input domain. No proof-carrying journal or compiled relation is attached to these ring updates; the actual narrower credential construction is the new evidence here.
