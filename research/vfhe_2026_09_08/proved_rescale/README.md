# Small complete BFV rescale experiment

[EXECUTED] The actual ciphertext multiplication and complete rescale proof are
finished. See REPORT.md and RESULT.json for measurements and scope.

The runner uses the existing public Multiplicator API at degree 8, with the
fixed three base/six extended primes of the existing exact scaler certificate.
It saves actual ciphertexts and public product polynomials. Lean, in the sibling
arithmetic_rescale package, owns all arithmetic constraints and witness synthesis.
Rust invokes the frozen shared generic backend; it contains no rescale AIR or
quotient/carry witness implementation.

Build with `cargo build --release --offline -j2`. Existing fixtures and proof
are frozen; new output paths are required for additional invocations:

```
target/release/vfhe-proved-rescale generate NEW_CASE
target/release/vfhe-proved-rescale prove TEMPLATE CASE TRACE_LEU32 NEW_PROOF_DIR
target/release/vfhe-proved-rescale verify TEMPLATE CASE PROOF
target/release/vfhe-proved-rescale verify-changed-output TEMPLATE CASE PROOF
```

The completed case is results/case001/; proof is results/proof001/proof.bin.
Template and trace are ../arithmetic_rescale/artifacts/. The proof covers only
the complete rescale stage; degree 8 does not provide FHE security.
