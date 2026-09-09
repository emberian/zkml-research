# Status

[EXECUTED] Three real engine profiles passed isolated syntax/import and byte-pin
checks; the original live genesis policy and backend pins still match. The
APPLY-LATER patch passes `git apply --check`; current app sources remain unchanged.
See `checks.json` and `MANIFEST.json` for the exact inputs and patch hashes.

[DERIVED: implementation] Complete durable core integration is proposed for
squared/compact, linear/compact, and linear/matched. It includes fixed genesis
selection, separate update/query counts, fresh-input proof calls, current-parent
binding, FIFO8, phase recovery, signed linear receive and exact ranking.

[OPEN] No alternate-engine app operation was run in this lane. Root applies the
patch after the active quadratic lifecycle terminates and owns real evaluation.
