[SOURCE] BANKING77 original author repository and train/test CSVs: https://github.com/PolyAI-LDN/task-specific-datasets . Read repository dataset statistics, split description and CC-BY-4.0 license. Local exact CSV hashes and selected row IDs are in data/selected.json. Citation: Casanueva et al., Efficient Intent Detection with Dual Sentence Encoders (2020), https://arxiv.org/abs/2003.04807 . No benchmark result from that paper is claimed here.

[SOURCE] E5 official model usage: https://huggingface.co/intfloat/e5-base-v2 . Read masked mean pooling, normalization and query prefix guidance; reuse cached revision f52bf8ec8c7124536f0efb74aca902b2995e5bcd read-only. Existing local metadata and model hashes come from ../utility/encoder_feasibility/candidates.json. E5's pretraining may have seen public benchmark data; no contamination-free generalization claim.

[SOURCE] Unchanged BFV primitive implementation: ../crypto/src/main.rs and ../crypto/target/release/resident-crypto. The new wrapper uses separate class accumulators beyond the former two-route protocol: no claim that the whole new wrapper was previously verified. Underlying fixed BFV parameter/arithmetic/canonical-byte entrypoints are reused.

[EXECUTED] Source discovery used one web search query and two primary-page opens; zero Scry queries. No prior learner fixture rerun.
