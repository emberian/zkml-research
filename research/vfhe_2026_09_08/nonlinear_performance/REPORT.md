[EXECUTED] **One complete corrected class kernel accepted.** The fresh consumer verified all 116 proofs against the approved saved model/query/evaluation-key/kernel ciphertext digests. It covers all 88 MAC, four extension, 18 tensor, and six rescale chunks. No keys, text encoder, encryption, or private reader ran. This is one class kernel on public saved data, not a new multiclass decision or a re-proof of the historical teaching chain.

[EXECUTED] [Authoritative acceptance](runtime/consumer001/RESULT.json), SHA256 `16f83668be8e459fb5f25b60e3927996a6558e63c4ea63122852f16eefd793f6`. The result's actual finished time is 2026-09-09T01:55:37.160660+00:00. Proof production occurred once; no proof was reused or regenerated.

| Recorded cost | Historical class000 | Corrected successor |
|---|---:|---:|
| Complete proof bytes | 145,623,212 | 133,690,186 |
| Complete proving | 382.996 s | 376.534 s |
| Complete proof phases, including emission/compression | 577.232 s | 556.312 s |
| Fresh complete consumer | 39.850 s | 35.749 s |
| Complete peak prover RSS | 8,975,597,568 B | 9,500,557,312 B |
| MAC proof bytes | 76,353,261 | 64,418,707 |
| MAC proving | 197.370 s | 164.104 s |
| MAC phase | 295.575 s | 239.973 s |
| MAC peak prover RSS | 1,219,149,824 B | 915,111,936 B |

[DERIVED from retained costs] Complete proof data fell **8.19%**. MAC proof bytes fell **15.63%**, MAC proving **16.85%**, MAC phase time **18.81%**, and MAC peak RSS **24.94%**. Whole proving improved only **1.69%** and proof-phase time **3.62%**; full peak RSS rose. Rescale proving took 128.38 s versus 93.82 s historically, including one 40.77 s chunk. This run establishes a bandwidth and MAC-cost improvement, not a broad latency or memory win. No cause is assigned to timing variation, and the historical run was not repeated.

[SOURCE/DERIVED] The compact source has 349 columns and explicit range9/range16 nodes. Range completion reconstructs omitted Boolean witnesses, applies the frozen paired-MAC theorem, and joins to the same full Infer source contract. The existing four-bit range backend expands it to 1,293 main columns. An isolated fixed-four grouping of consecutive same-bus LogUp interactions reduces 525 raw sends to 132 Ext4 permutation columns. The actual main+permutation size is 1,821 base-field equivalents versus 2,659 historically. Five formal source modules have 23 exact guarded declarations; the backend helper's two modules have 13. Exact native shape and patch are retained in `backend/`.

[SOURCE] **The semantics also changed to fix a soundness error.** Historical `gate` bodies were transition-only and skipped each chunk's last row. Every arithmetic assertion in all 116 successor proofs uses `window_gate/on_transition:false`. The compact emitter uses the shared Lean whole-row serializer. The 11 square templates were migrated with normalized arithmetic bodies, metadata, and lookups preserved. This is intentionally not a same-relation benchmark, and old acceptance is preserved as historical executed evidence.

[EXECUTED] Production made 116 proof objects and 116 normal self-checks. The first fresh native check accepted, but the wrapper then failed because it expected a `backend` diagnostic absent from native verification JSON. That attempt and its failure are unchanged at `runtime/run001/`. A separately frozen consumer uses the approved binary/template pins and checks optional diagnostics when present. It then accepted all 116 proofs. Total native verification calls were **233**: 116 self-checks, 116 final consumer checks, and one earlier native acceptance before the wrapper error. There was no cryptographic rejection, proof retry, or private read. Wall time including the source-repair interval was 840.080 s, so it is not presented as a clean end-to-end latency result.

The corrected callable entry point is:

```sh
python3 research/vfhe_2026_09_08/nonlinear_performance/runtime/api.py verify \
  /absolute/approved-request.json /absolute/produced-run /absolute/new-verification
```

`api.py prove NEW_RUN` produces and consumes the pinned saved public case. The same API exposes caller-selected `produce-infer`/`verify-infer` and `produce-update`/`verify-update`. The final dispatcher is source/CLI-checked and selects the exact metadata checker exercised by the completed consumer; no additional crypto was run merely to test dispatch. The measured production and consumer are retained separately. Commands require the approved workspace and public case files; they are not a standalone distributed verifier package.

[OPEN/explicit boundary] The successor is a **new three-instance profile**: degree six and eight ZK quotient chunks for the MAC, with unchanged FRI blowup3, queries38, query PoW16, Ext4, salts/random-codewords4, and witness hiding. The old query's numerical PCS/extraction theorem is not inherited. The grouping algebra requires nonzero denominators; this package does not supply a new end-to-end soundness probability. Lean range/source and whole-row results are separate from the Rust parser/lowering, byte-table/LogUp extraction, PCS/FRI implementation, seed expansion, encoding/NTT, and controller boundaries. Full-reader capability is unchanged and unused here.
