# Reader-side verification of the complete admitted history

[EXECUTED, 2026-09-07] This successor passes an actual encrypted mixed history:
40 fresh private Learn operations, four Infer operations and eight exact-original
expiries, with 23 refusal controls, historical retry, reader SIGKILL recovery and
copied-authority rollback refusal. All four private output comparisons pass.
See [the frozen run and reproduction command](reports/README.md). This addresses
the baseline reader's reliance on a signature for arithmetic correctness.

[DERIVED design] The reader maintains its own durable encrypted state and
journal, beginning at the fixed genesis. Before installing any signed Learn or
Infer envelope, it checks the original issuer/query authorization and recomputes
the exact ciphertext transition. It checks every parent, output, expiry and
next-state field against that computation. Every later release must match an
already verified Infer record and an independently registered query ticket.
The authority's signature alone cannot authorize a substituted ciphertext on
this path.

[DERIVED trust] The reader still holds the full BFV secret and remains trusted.
Issuer feature/range/key provenance and the command policy remain trusted. The
reader's own persistence must resist host/authority rollback. The authority can
withhold progress; verification does not create availability. This is benchmark
R with a narrower authority trust requirement, not no-master-read cryptography.

[DERIVED protocol] Public blobs enter through content-addressed `put`; `sync`
admits one full finalized envelope in sequence. It never decrypts. Existing
`register` selects a signed query ticket; `receive` checks exact verified-history
membership before entering the trusted reader's scalar-decryption path. Exact
sync retry returns its stored revision even after later progress. Learn envelopes
never enter the release path. No caller path or scalar decryption argument is an
RPC field.

[EXECUTED validation] The fixed public wrong-output control is accepted by the
signature-only baseline and refused by this verifier before decryption. The
final driver freezes the repaired journal helpers, service, executable and
driver; private artifact omission and per-role costs are recorded. Independent
review also checks a scheduled concurrent status read against an actual commit:
the returned head and journal count share one SQLite snapshot.

[EXECUTED complete integration] The complete two-history utility workload now
passes through this verifier: 384 Learn, 96 Infer, 256 expiries and all 96 direct
integer comparisons. See [the full report](reports/UTILITY.md). The separate
private smoke test establishes arithmetic agreement for unknown synthetic inputs;
it does not itself measure useful adaptation. The fixed utility data are public.
