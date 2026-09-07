# Review scope before first normal completion

[REPORTED: read-only API compatibility review by the designated-crypto lane]
The backend author independently read the integration's `drain.py` and `model.py`
after the first ten normal updates. No API mismatch was found: the scalar path
is selected from signed `row_id`; the canonical signed query binds context, row
digest, token and recipient; the drain checks accepted verified Infer/ticket
membership and the decoder's key/context, ciphertext hash, row and recipient.
This is an API/source inspection of the adapter, not an independently executed
integration test and not a security proof. Exact source pins are in
`REVIEW_SOURCE_PINS.json`.

[REPORTED: nonblocking telemetry finding] `answer.get('metrics')` stores null in
the private cost log because the backend exposes its counters and BSGS details
as flat fields. The independently timed private `decode_elapsed_ns` is retained.
No arithmetic, identity binding or public-log omission depends on this null field.
The running source is deliberately preserved; future packaging can adapt private
telemetry without changing the crypto interface.

[SOURCE: local protocol review read] `../protocol_review/REVIEW.md` reviews the
host-view claim at the protocol level. Its key requirement is that all public
retries/status/failures/persistence, including later ones, remain independent of
private decode outcome. The public service in this copy has no private scalar
paths or private answer database reads. The drain reads its accepted journal and
writes a separate private database/log. The trusted benchmark coordinator's
comparison/report/scheduling is explicitly outside that host view, as directed
by the parent review. No runtime adverse suite was performed by that review.

[EXECUTED: source inventory] Seven original source files still match their
`SOURCE_FREEZE.json` hashes; all seven `source_original` copies match the originals.
The four copied designated-crypto runtime files match `CRYPTO_FREEZE.json`.
Compilation of the adapted Python modules succeeded before setup. The normal
run pins its actual loaded source set in genesis; no operational source edits
have been made during execution.
