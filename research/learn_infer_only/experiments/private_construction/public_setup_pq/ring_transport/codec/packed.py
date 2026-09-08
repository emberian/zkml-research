"""[DERIVED] Canonical streaming fixed-width unsigned bit packing.

Values occupy consecutive little-endian bits; final unused high bits are zero.
This module encodes raw payloads. The container owns headers and signed mapping.
"""
from itertools import islice
import operator

ENCODING_NAME = "fixed-width-unsigned-lsb0-v1"
BLOCK_VALUES = 8192  # Multiple of eight, so nonfinal blocks need no padding.


class CodecError(ValueError):
    pass


def _integer(value, name):
    if isinstance(value, bool):
        raise CodecError(f"{name} must be an integer, not bool")
    if type(value) is int:
        return value
    try:
        return operator.index(value)
    except TypeError as exc:
        raise CodecError(f"{name} must be an integer") from exc


def _parameters(width, count, upper_bound=None):
    width = _integer(width, "width")
    count = _integer(count, "count")
    if width < 1 or count < 0:
        raise CodecError("width must be positive and count nonnegative")
    capacity = 1 << width
    bound = capacity if upper_bound is None else _integer(upper_bound, "upper_bound")
    if not 1 <= bound <= capacity:
        raise CodecError("upper_bound must be in [1, 2**width]")
    return width, count, bound


def payload_bytes(width, count):
    width, count, _ = _parameters(width, count)
    return (width * count + 7) // 8


def _write_all(writer, data):
    view = memoryview(data)
    position = 0
    while position < len(view):
        written = writer.write(view[position:])
        if not isinstance(written, int) or not 0 < written <= len(view) - position:
            raise OSError("writer did not make valid forward progress")
        position += written


def _read_exact(reader, size):
    data = reader.read(size)
    if not isinstance(data, (bytes, bytearray, memoryview)):
        raise CodecError("reader must return bytes")
    if len(data) == size:
        return data
    if len(data) > size:
        raise CodecError("reader returned more bytes than requested")
    result = bytearray(data)
    while len(result) < size:
        part = reader.read(size - len(result))
        if not isinstance(part, (bytes, bytearray, memoryview)):
            raise CodecError("reader must return bytes")
        if not part:
            raise CodecError("truncated packed payload")
        if len(part) > size - len(result):
            raise CodecError("reader returned more bytes than requested")
        result.extend(part)
    return result


def pack_values(iterable, width, count, writer, *, upper_bound=None):
    """Write exactly count unsigned values, returning the exact payload bytes.

    Reject nonintegers, out-of-range values, and too few/many input values.
    The optional upper_bound is exclusive (use q for canonical residues).
    Earlier blocks may already have been written if a later block is invalid.
    """
    width, count, bound = _parameters(width, count, upper_bound)
    source = iter(iterable)
    remaining = count
    total = 0
    w2, w3, w4, w5, w6, w7 = (width * j for j in range(2, 8))
    while remaining:
        n = min(BLOCK_VALUES, remaining)
        values = list(islice(source, n))
        if len(values) != n:
            raise CodecError("too few input values")
        for i, value in enumerate(values):
            if type(value) is not int:
                value = _integer(value, "coefficient")
                values[i] = value
            if not 0 <= value < bound:
                raise CodecError("coefficient outside canonical range")
        whole = n - n % 8
        chunks = [
            (values[i] | values[i + 1] << width | values[i + 2] << w2 |
             values[i + 3] << w3 | values[i + 4] << w4 | values[i + 5] << w5 |
             values[i + 6] << w6 | values[i + 7] << w7).to_bytes(width, "little")
            for i in range(0, whole, 8)
        ]
        if whole < n:
            tail = 0
            for j in range(whole, n):
                tail |= values[j] << ((j - whole) * width)
            chunks.append(tail.to_bytes(((n - whole) * width + 7) // 8, "little"))
        data = b"".join(chunks)
        _write_all(writer, data)
        total += len(data)
        remaining -= n
    sentinel = object()
    if next(source, sentinel) is not sentinel:
        raise CodecError("too many input values")
    assert total == (count * width + 7) // 8
    return total


def unpack_values(reader, width, count, upper_bound, *, require_eof=False):
    """Yield exactly count canonical unsigned values from one raw payload.

    Raises on truncation, nonzero final high padding or value >= upper_bound.
    Default consumes exactly payload_bytes(width,count), leaving later sections
    unread. require_eof additionally rejects trailing bytes in standalone input.
    Consume the iterator fully to complete all checks.
    """
    width, count, bound = _parameters(width, count, upper_bound)
    mask = (1 << width) - 1
    remaining = count
    w2, w3, w4, w5, w6, w7 = (width * j for j in range(2, 8))
    while remaining:
        n = min(BLOCK_VALUES, remaining)
        size = (n * width + 7) // 8
        data = _read_exact(reader, size)
        bits = n * width % 8
        if bits and data[-1] >> bits:
            raise CodecError("nonzero high padding bits")
        values = []
        whole = n - n % 8
        for offset in range(0, (whole // 8) * width, width):
            word = int.from_bytes(data[offset:offset + width], "little")
            values.extend((word & mask, word >> width & mask, word >> w2 & mask,
                           word >> w3 & mask, word >> w4 & mask, word >> w5 & mask,
                           word >> w6 & mask, word >> w7 & mask))
        if whole < n:
            tail = int.from_bytes(data[(whole // 8) * width:], "little")
            for _ in range(n - whole):
                values.append(tail & mask)
                tail >>= width
        if any(value >= bound for value in values):
            raise CodecError("noncanonical residue or coefficient")
        yield from values
        remaining -= n
    if require_eof:
        trailing = reader.read(1)
        if not isinstance(trailing, (bytes, bytearray, memoryview)):
            raise CodecError("reader must return bytes")
        if trailing:
            raise CodecError("trailing bytes after packed payload")
