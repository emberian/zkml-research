# Complete: actual small BFV multiplication/rescale proof

[EXECUTED] Actual degree-8 ciphertext multiplication, all eight plaintext
coefficient checks, and the complete 24-position/72-residue rescale proof pass.
Fresh native verification and changed-output rejection pass. The proof is
8,592,353 bytes; full prove command 2.028s with four workers.

The source/trace are Lean-generated in arithmetic_rescale. This proves the
complete small fixed-point rescale step; extension/convolution provenance and
secure-degree deployment are outside its scope. REPORT.md and RESULT.json
retain exact measurements, commands and artifacts.

This package's current source, binary, case and proof are now frozen for root
integration and the separately owned compiler_cost_successor comparison. No
additional verification cycles are needed here. The prior proved_operation
package remains unchanged.
