# A continuing text learner with encrypted prototypes

[EXECUTED] This package implements a usable `teach`/`query` CLI and persistent class memory. A fixed local E5 encoder maps ordinary text into 576 projected integer features. Each class learns the mean of its eight most recent examples; a new label creates a new prototype immediately. The BFV backend encrypts issued features, adds the new contribution and subtracts the exact expired contribution, then evaluates public-query dot products against encrypted prototypes. It reuses the existing crypto binary unchanged; the multiclass Python wrapper is new.

[EXECUTED] On eight BANKING77 intents, 128 teaching observations caused 64 FIFO expiries. All 320 original test-split texts were kept out of updates. Four classes were taught first, four new classes followed, and teaching then continued across all eight. No test result selected the projection, window, model or readout.

| Teaching updates | Active intents | Correct / 320 | Original four / 160 | Added four / 160 |
|---:|---:|---:|---:|---:|
| 32 | 4 | 151 | 151 | 0 |
| 64 | 8 | 270 | 146 | 124 |
| 96 | 8 | 279 | 153 | 126 |
| 128 | 8 | 269 | 151 | 118 |

[EXECUTED] Final eight-intent accuracy is 84.0625%; the decrease from the intermediate checkpoint is retained. Prequential prediction before each teaching update was correct 96/128 times. The complete encrypted workload ran all 128 updates and all 320 test queries at revisions 32, 64 and 128: **6,400/6,400 exact integer scores and 960/960 multiclass predictions matched**. Public computation finished before any benchmark output decryption. Public work took 160.168 seconds; including the authorized comparisons, 284.605 seconds. These are shared-host timings, not an isolated performance comparison.

[EXECUTED] The same unchanged learner also ran on **all 77 BANKING77 intents**: 1,232 teaching updates and 616 expiries, with all 3,080 original test rows. The initial 38 classes received eight examples each, then 39 new classes arrived, then all classes received eight further examples. No model or hyperparameter search was introduced for this expansion.

| Teaching updates | Active intents | Correct / 3,080 | Original 38 / 1,520 | Added 39 / 1,560 |
|---:|---:|---:|---:|---:|
| 304 | 38 | 1,246 | 1,246 | 0 |
| 616 | 77 | 2,194 | 1,134 | 1,060 |
| 1,232 | 77 | 2,253 | 1,123 | 1,130 |

[EXECUTED] Final full-task accuracy is **73.1494%**. The old 38 prototype vectors stayed byte-for-byte equal while the 39 new classes were added, but old-class prediction accuracy decreased because the new prototypes compete at inference. Continued updates change the prototypes and can improve or regress individual intents. This is ordinary finite-memory online learning, without a guaranteed monotone utility claim.

[EXECUTED] The actual CLI then accepted two new authored `account_access` observations beyond the eight-intent benchmark. A login-help query changed from `card_payment_not_recognised` before teaching to `account_access` afterward. Both the plaintext and BFV CLIs produced identical integer scores for the before/after queries, and both models persisted revision 130 with nine classes. This is a concrete interaction, not another accuracy estimate. CLI queries use inline full-key receiving; the benchmark's deferred-decryption phase applies to the batch experiment only.

[EXECUTED] E5 performed 448 initial encodings in 28 batches, with 3.780 seconds of forward work; the full 77-class expansion added 3,864 encodings and reused the 448 feature cache entries, taking another 36.347 seconds of forward work. No tested coordinate clipped at the fixed scale 512. There was no encoder fine-tuning. Complete selected source rows, score/prediction tables, costs, model hashes and commands are retained in the adjacent JSON/log artifacts.

[EXECUTED] The complete 77-class BFV instantiation also finished: **1,232 updates, 616 expiries, 77 multiclass queries and 5,929/5,929 exact integer matches**. One fixed first-original-test row per class was queried against every prototype; all 77 predictions matched. The slice had 56/77 correct, but is reused-data integration evidence, not an additional accuracy estimate. This batch took 205.925 seconds for public work and 329.777 seconds including deferred comparison. Full 3,080-row utility is the separate plaintext measurement above.

[EXECUTED] A persistent JSONL session then taught a 78th class, `loan_application`, from two new mortgage-related texts. The query changed from `transfer_into_account` to `loan_application`; plaintext and BFV sessions matched all 155 before/after integer scores. Both sessions persisted revision 1,234. The encrypted model is immediately usable through `session.py models/full77_bfv` or the ordinary CLI. This interaction receives its query outputs inline after the completed benchmark.

[EXECUTED handoff; OPEN proof] `proof_join/event.json` and four public ciphertexts preserve the real Learn65 expiry (`acc + fresh - old`) for the proof worker. The source record binds the incoming and expired BANKING77 rows, encoder feature artifact and exact ciphertext bytes. No proof for this transition is claimed until the worker supplies its result.

[EXECUTED storage] The retained eight-intent and full77 encrypted research directories occupy 585,008 KiB and 735,324 KiB of allocated disk respectively, including operation history and outputs. Active class windows are bounded; the retained trace grows with further teaching and queries. These are not minimum-state size estimates.

[DERIVED boundaries] The issuer sees plaintext text/features; class routes, counts and queries are public. The recipient retains a full BFV secret key and can read more than the returned scalar. FIFO expiry removes an active contribution; it is not cryptographic deletion of retained ciphertext history. The public benchmark does not test confidential ingress. A proof of one ciphertext arithmetic relation would not prove E5 execution, the whole Python wrapper, history-bound release or operator privacy. The original test split is held out from online updates, but E5 pretraining may have included public benchmark data. No PQ or no-master-reader conclusion follows.

[SOURCE] BANKING77: [PolyAI original repository](https://github.com/PolyAI-LDN/task-specific-datasets), Casanueva et al., [Efficient Intent Detection with Dual Sentence Encoders](https://arxiv.org/abs/2003.04807). E5 interface: [official model card](https://huggingface.co/intfloat/e5-base-v2). CSV license/provenance and exact local model hashes are saved. Source search used one web query and two primary-page opens; zero Scry queries.
