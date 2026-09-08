# Addressable public ring-row expansion

[DERIVED implementation, 2026-09-08] The API is:

```python
from expansion import PublicExpander, ExpansionError

e = PublicExpander(seed, binding)
row = e.row(family, index, N, q)
rows = e.iter_rows(family, start, count, N, q)
```

[DERIVED] `seed` is exactly 32 or 64 public bytes; `binding` is exactly
32 public bytes. `family` is a nonempty byte string of at most 255 bytes,
or a string encoded literally as UTF-8 (no normalization). String/byte
spellings of the same encoded name identify the same family. Indices are
unsigned 64-bit integers, `N` is in `[1,2^64)`, and `q` is an integer at
least two. The parent owns parameter validation and chooses a noncircular
binding. This module reads/writes no files and obtains no OS random bytes.

## Canonical domain

[DERIVED] Let `LP(x)` be four-byte big-endian `len(x)` followed by `x`.
Let `U64(x)` be exactly eight big-endian bytes, and encode `q` as its
shortest unsigned nonempty big-endian byte string. A chunk address is

```
LP(b"ring-seed-transport/public-rows/v1")
|| LP(seed) || LP(binding) || LP(family_bytes)
|| U64(row_index) || U64(N) || LP(q_bytes) || U64(chunk_index).
```

[DERIVED] Field lengths and fixed-width integers make this serialization
unambiguous. It binds seed length, exact family bytes, row length and modulus
as well as the parent context. `row_domain(...)` exports the address prefix
before the final chunk index. Equal fields reproduce the same row;
different row lengths intentionally select different domains, rather than
sharing a coefficient prefix.

## Candidate extraction

[DERIVED] Set `bits=(q-1).bit_length()` and `word_bytes=ceil(bits/8)`.
For successive chunk indices, call SHAKE256 once on that chunk's complete
address and request exactly `1024*word_bytes` output bytes. Interpret each
word little-endian, mask to `bits` bits, and append it only if it is below
`q`. Stop after `N` accepted values. A cap of `ceil(4N/1024)+16` chunks
raises `ExpansionError` if insufficient candidates were accepted; it never
substitutes a fallback row. See `SECURITY.md` for the conditional ideal-XOF
uniformity/abort calculation and the unresolved seeded-construction theorem.

[DERIVED] Each chunk hashes a different address with one fixed-length
`digest` call. There is no repeated growth of `shake.digest(prefix_length)`
and no quadratic prefix re-expansion. `row` holds one output list and one
candidate chunk; `iter_rows` yields one such list at a time. `last_stats`
records the latest row's public counters; `totals` sums completed rows.
Repeated row calls recompute the row and do not retain a matrix cache.

## Executed evidence

[EXECUTED] `check_expansion.py` ran once. `CHECKS.json` and `RUN.log` retain
the exact command, output, source hashes and public test seed/context.
Eight changed-field domains are byte-distinct, two chunk indices give
different observed output, repeat/stream results match, and eight invalid
inputs are rejected. Forced candidate words distinguish rejection from
modulo reduction. A forced all-reject case exhausts 17,408 candidates and
raises without a row; a power-of-two modulus control accepts without rejection.
These are finite execution checks, not a pseudorandomness or collision proof.

[SOURCE: local parameter code] The one full public-row check uses the modulus
`q=4294967767*2^256+1` from
`../../ring_implementation_fast/run.py:16` and `N=16384`.

[EXECUTED] That public row required 32,793 candidates in 33 independently
addressed chunks, generated 1,250,304 XOF bytes and completed in 0.0100
seconds on the saved shared-machine environment. All values were in range.
The saved digest hashes its public residues encoded as 37-byte little-endian
words; no raw row file or private artifact was read or written. No search,
estimator, sampler change or old-package edit belongs to this lane.

[OPEN] The parent owns fresh setup, registry binding, compact file headers,
actual cross-process expansion and the seeded construction's security claim.
Single-row timing does not establish full transport throughput.
