# Canonical streaming packed unsigned payloads

[DERIVED implementation, 2026-09-08] `packed.py` implements the parent
transport's raw coefficient payload. It writes no headers, chooses no
cryptographic parameters, and reads no private artifacts by itself.
The encoding name is `fixed-width-unsigned-lsb0-v1`.

```python
from codec import pack_values, unpack_values, payload_bytes, CodecError

nbytes = pack_values(values, width, count, writer, upper_bound=q)
values = unpack_values(reader, width, count, q)
```

[DERIVED API] `pack_values(iterable,width,count,writer,*,upper_bound=None)`
returns the exact number of bytes written. It requires exactly `count`
integer values in `[0,upper_bound)`; the default bound is `2**width`.
Integer-like values implementing Python's index protocol are accepted;
booleans and nonintegers are rejected. Supply `q` explicitly for canonical
public residues. Negative values and values outside the declared bound
are rejected without reducing them modulo anything.

[DERIVED API] `unpack_values(reader,width,count,upper_bound,*,require_eof=False)`
returns an iterator of integers. It rejects truncated payloads, nonzero
high padding and decoded values outside `[0,upper_bound)`. By default it
consumes exactly one payload and leaves later sections unread. Setting
`require_eof=True` additionally rejects any trailing byte. Exhaust the
iterator to finish all validation. The parent must still validate its
container's declared payload length and overall trailing bytes.

[DERIVED API] `payload_bytes(width,count)` is exactly
`(width*count+7)//8`; `width` must be positive and `count` nonnegative.
The upper bound must lie in `[1,2**width]`. Short binary reads/writes are
supported. A nonprogressing writer raises `OSError`; malformed values,
parameters or input bytes raise `CodecError`, a `ValueError` subclass.

## Byte layout and canonicality

[DERIVED] Unsigned value `v_i` occupies bit positions
`i*width ... (i+1)*width-1`. Bit zero is the least significant bit of the
first byte. Thus the payload, viewed as a little-endian integer, is
`sum(v_i << (i*width))`. It occupies exactly `ceil(width*count/8)` bytes;
unused high bits of the final byte must be zero. Given width and count,
the accepted representation of each unsigned sequence is unique.

[DERIVED] Eight coefficients occupy exactly `width` bytes for every integer
width, including 289 and 29. The implementation combines/extracts eight
values at a time using Python big-integer shifts and little-endian
`to_bytes`/`from_bytes`; it has no Python loop over individual bytes.
It handles at most 8,192 coefficients per block. Nonfinal block boundaries
are byte aligned, so the final partial group alone can have padding.
Codec memory is bounded by this block size, independently of total count,
for a fixed width. The caller may independently retain its input/output.

[DERIVED limitation] Streaming validation is incremental. Packing can have
written earlier blocks before finding an invalid later value or wrong
total cardinality. Unpacking validates an entire block before yielding
that block, but later blocks may still be invalid. The parent must treat
a partially written/consumed container as incomplete until the operation
finishes successfully. No atomic publication or secure erasure is supplied.

[REPORTED: parent interface] The parent selected `RINGTRN1`, a four-byte
big-endian JSON-header length, a canonical JSON header, then this raw packed
payload. It owns kind/profile/parameter/context binding, payload counts,
signed 29-bit two's-complement mapping and the strict private magnitude
check. These header/process rules are outside this codec's verified scope.

## Executed evidence

[EXECUTED] `check_and_measure.py` ran once; `MEASUREMENTS.json` and `RUN.log`
retain the command, output, environment and unchanged source hashes.
Five small cases match the direct whole-integer byte encoding and roundtrip,
including widths 1, 9, 29 and 289, plus an empty payload. Fourteen malformed
cases are rejected. A short-read/write roundtrip passes, and a separate
case confirms the next container section remains unread by default.

[EXECUTED] One public deterministic benchmark streamed 1,048,576 values at
width 289, with a synthetic exclusive bound `(1<<288)+12345` (no primality
claim). Its 37,879,808-byte payload packed in 0.1807 seconds and unpacked
with per-value comparison in 0.2350 seconds: approximately 5.80 million
packed values/s and 4.46 million unpacked-and-compared values/s. Every value
matched. The codec used bounded blocks; the benchmark intentionally held
the public payload in `BytesIO`. No payload file or private artifact was
read or persisted, and no web search was made.

[OPEN] This is one memory-backed benchmark on a shared machine. Disk I/O,
container hashing, cross-process access enforcement, whole-transport
latency and cryptographic protocol correctness belong to the parent run.
No timing-side-channel or production serialization audit is claimed here.
