[OPEN integration] Apply outer-mle-reuse.patch to the minidregg prover when selected by root; run the two focused release integration-test targets in README.md. This lane's implementation and one-workload validation are complete.

[EXECUTED follow-on] The concrete ring/vector contraction is now complete in ring_consumer/. Apply its ring-contraction.patch after new_constructions/implementation/fused-matvec.patch. The actual caller preserves original commitments and sumchecks and passed a PCS-enabled public workload. No additional benchmark grid is needed.

[OPEN next seam] A separately authorized cycle could remove padded MLE materialization from the ring prover while preserving its exact round polynomials. The present completed patches deliberately retain those tables and the existing verifier.
