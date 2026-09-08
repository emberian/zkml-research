# Exact kernel construction; weak fixed utility

[EXECUTED] One feature map was specified before scores and evaluated once on
the exact six-observation, two-class, sixteen-query predecessor slice. No
original data, class order, query order, training order or expiry changed.

| checkpoint revision | live observations per class | quadratic map correct | predecessor correct |
|---:|---:|---:|---:|
|2|1|8/16|16/16|
|4|2|9/16|16/16|
|6|2|10/16|16/16|

[EXECUTED] `python3 -B prepare.py > prepare.log 2> prepare.stderr` completed
with PASS. Both source files are pinned and unchanged. All sixteen query rows
are independent modulo p; the identity completion supplies the remaining 561
basis rows. Six forward/inverse basis roundtrips and all 96 observation/query
kernel identities passed. The maximum observed individual kernel was 17,689
and maximum class score 33,314. Exact labels, inputs and predictions remain in
`registry.json` and `fixture.json`.

[DERIVED/EXECUTED] For every supported compact vector, the exact feature
identity yields a single-score bound 262,144, two-item bound 524,288 and signed
weight-32 bound 8,388,608. All are within the centered range of p=28,439,893.
The actual query registry also passes the unchanged general-int8 two-item
check, with maximum query L1=4,225 and bound 1,073,150. These latter generic
bounds are interface checks, not alternate kernel identities.

[EXECUTED] `python3 -B check_algebra.py > algebra.log 2> algebra.stderr`
completed with PASS: 6,561 exhaustive two-coordinate cross-term cases embedded
in 32 dimensions, tight dimension-32 bounds, zero/single-source-coordinate
normalization controls and one synthetic plaintext issuer CLI. It performed no
additional benchmark feasibility evaluation.

[DERIVED] [CONTRACT.md](CONTRACT.md) gives the continuing state transition:
sum lifted observations per class, then add each fresh ciphertext and subtract
the exact original being expired. A recipient with registered q obtains the
sum of `(x·q)²`, and ranks class means. Its capability also applies to retained
individual inputs. The exact transport privacy game pulls back through this
deterministic map with the same conditional bound; no ciphertext multiplication
or new FE assumption enters. The ambient B is invertible, while the quadratic
message image remains structured and is not asserted to hide natural language
from a coalition.

[EXECUTED decision] The parent accepted this as a scoped negative utility
result and directed **no fresh cryptographic run**. Consequently this packet
contains no setup, generated key, ciphertext, expiry run or actual recipient
output. It makes no successor execution-latency or storage measurement. The
underlying unmodified transport's earlier numbers remain predecessor evidence.
The concurrent durable-journal builder proceeds with the useful linear fixture.

[SCOPE] This is a failure of the single specified complete map on the known
slice. There was no ablation and no search; attributing the degradation only to
compression, normalization or squaring would exceed the experiment. Other
maps and fresh utility datasets are untested. The formal integer identity and
closed linear state interface survive this utility result.

[EXECUTED scope counts] One plaintext feasibility evaluation; zero new model
forwards; zero web queries; zero Scry queries; zero cryptographic runs; zero
estimator calls; zero original private-artifact reads; zero companion writes.
