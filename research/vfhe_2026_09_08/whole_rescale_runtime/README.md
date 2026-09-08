# Whole captured nonlinear rescale

[EXECUTED] The public importer covers all 24,576 component/coefficient
positions of the frozen actual nonlinear 9-to-4 RNS rescale capture. Its
six 4,096-row chunks contain no padding. All 98,304 captured output residues
were compared with the raw output ciphertext through public decoding and
inverse NTT. See `results/import001.command.json` and
`results/case001/operation.json`.

[EXECUTED] All six proofs and fresh native verifications passed in 146.806
seconds: 34,632,537 proof bytes, 97.729 seconds summed proving, 1.507 seconds
fresh verification, and 9,497,837,568 bytes peak proof-process RSS. See
`REPORT.md` and `RESULT.json`. Earlier batch and cost artifacts remain unchanged.

The runtime consumes the unchanged smaller Lean-generated relation with
24,575 trace columns and 88 public columns. Rust only reads public artifacts,
binds table 11, and calls the frozen portable shared backend. It does not
implement rescale constraints or witness arithmetic. The native witness
executor consumes a Lean-generated plan and produces an untrusted trace.

The frozen `PIPELINE.json` selects the approved emitter. To run a new complete sequence:

```sh
python3 run.py results/case001 results/new-run
```

This executes one emission, proof and fresh-process verification per chunk,
sequentially with four Rayon threads. Failures stop without retries. Raw
witnesses are replaced by local compressed transport under ignored `work/`;
their exact hashes and lengths remain in each chunk result. Public proofs,
case data and execution records remain under `results/`.

An independent consumer can verify the entire six-proof bundle without
witnesses or private files:

```sh
python3 verify_all.py results/case001 results/run001 results/consumer001
```

The application must approve the local `PIPELINE.json` template/native pins.
`verify_all.py` calls the native verifier for each fixed global interval; it
does not rely on the producer's `verified` flag. The proof needs both the
public capture and all six proof files. Native direct commands are listed in
`src/main.rs`; the build is pinned in `BUILD.json`.

The proof scope is the complete **captured rescale**, not extension,
convolution or whole ciphertext multiplication. Public source capture,
Rust decoding/serialization, inverse NTT and ciphertext provenance remain
implementation assumptions. No decryption or new BFV operation is needed.
See `CONTRACT.md` for the execution and storage rules.
