# Public-coin adapter evidence closeout

[EXECUTED seal, 2026-09-08] `python3 ../journal/seal_adapter.py` rehashes the
saved public exports, source/review pins and ciphertext inventory, and checks
actual public command counts/order. Retained output is
`../journal/reports/adapter_seal.json`; `FINAL_MANIFEST.json` pins this closeout
and every exported public report. No workload, group arithmetic or private
decode is rerun; no private file is opened or hashed. Frozen sources and prior
review notes remain unchanged.

[EXECUTED saved result; attribution] `reports/positive_001/report.json` records
33 Learn, four Infer, one expiry, 33 exact queue-byte checks and four matching
private integer comparisons. It records 174.625837167 seconds overall and
42.710028458 seconds setup. These are the original executed harness timings,
which included private-role processing outside the accepted-public-value
security transcript. The seal checks report provenance, not the private answers.

[DERIVED source/evidence agreement] The saved commands begin with independent
registration (16 recipient announcements), then public-build, verify-public,
full validate-context, and 16 recipient-finalize calls. No keygen, initializer
or recipient-register command appears. Reviewed setup/source bytes match the
execution pins; the source computes no scalar master or projection deliveries
on that path. Successful public algebra recomputation is attributed to its saved
command output. Source-level review remains in the unchanged
`../implementation_review/REVIEW.md`; this closeout supplies its missing seal
without impersonating an independent reviewer's final disposition.

[DERIVED limits] Honest direct tau/U sampling and honest independent recipient
registration remain premises. The recipient coalition retains its full fixed
per-input span, and the known fixture is reconstructible. Shared-account roles
provide no OS isolation or operator confidentiality. Classical DDH and Ed25519
remain separate assumptions; no PQ, malicious setup, selected-only release or
new utility claim follows. No metered or network query was used.
