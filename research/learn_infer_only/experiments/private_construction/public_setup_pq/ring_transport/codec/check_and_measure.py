"""[EXECUTED] Small malformed-input checks and one public-data codec benchmark."""
import hashlib
import io
from itertools import cycle, islice
import json
from pathlib import Path
import platform
import sys
import time

from packed import CodecError, pack_values, payload_bytes, unpack_values

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checks():
    refused = []

    def rejects(name, fn):
        try:
            fn()
        except CodecError:
            refused.append(name)
        else:
            raise AssertionError(name + " was accepted")

    cases = [(29, [0, 1, (1 << 28) - 1, 1 << 28, (1 << 29) - 1]),
             (289, [0, 1, (1 << 288) - 1, 1 << 288, (1 << 289) - 1] * 2),
             (1, [0, 1, 1, 0, 1]), (8, []), (9, [0, 511])]
    for width, values in cases:
        buf = io.BytesIO()
        wrote = pack_values(values, width, len(values), buf)
        expected = sum(value << (i * width) for i, value in enumerate(values))
        assert buf.getvalue() == expected.to_bytes(payload_bytes(width, len(values)), "little")
        assert wrote == len(buf.getvalue())
        assert list(unpack_values(io.BytesIO(buf.getvalue()), width, len(values), 1 << width, require_eof=True)) == values

    rejects("negative value", lambda: pack_values([-1], 29, 1, io.BytesIO()))
    rejects("too-wide value", lambda: pack_values([1 << 29], 29, 1, io.BytesIO()))
    rejects("bool value", lambda: pack_values([True], 29, 1, io.BytesIO()))
    rejects("float value", lambda: pack_values([1.0], 29, 1, io.BytesIO()))
    rejects("too few values", lambda: pack_values([1], 29, 2, io.BytesIO()))
    rejects("too many values", lambda: pack_values([1, 2], 29, 1, io.BytesIO()))
    rejects("noncanonical input residue", lambda: pack_values([17], 8, 1, io.BytesIO(), upper_bound=17))
    rejects("noncanonical decoded residue", lambda: list(unpack_values(io.BytesIO(bytes([17])), 8, 1, 17)))
    rejects("truncation", lambda: list(unpack_values(io.BytesIO(b"\x01"), 29, 1, 1 << 29)))
    rejects("high padding", lambda: list(unpack_values(io.BytesIO(b"\x00\x00\x00\x80"), 29, 1, 1 << 29)))
    rejects("standalone trailing byte", lambda: list(unpack_values(io.BytesIO(b"\x01\x00"), 8, 1, 256, require_eof=True)))
    rejects("zero width", lambda: payload_bytes(0, 1))
    rejects("negative count", lambda: payload_bytes(29, -1))
    rejects("invalid bound", lambda: list(unpack_values(io.BytesIO(), 29, 0, (1 << 29) + 1)))
    sections = io.BytesIO(b"\x07NEXT")
    assert list(unpack_values(sections, 8, 1, 256)) == [7]
    assert sections.read() == b"NEXT"

    class ShortIO(io.BytesIO):
        def write(self, data):
            return super().write(data[:5])

        def read(self, n=-1):
            return super().read(min(7, n))
    short = ShortIO()
    values = [0, 1, 2 ** 288, 2 ** 289 - 1] * 5
    assert pack_values(values, 289, len(values), short) == payload_bytes(289, len(values))
    short.seek(0)
    assert list(unpack_values(short, 289, len(values), 1 << 289, require_eof=True)) == values
    return {"all_passed": True, "small_roundtrips": len(cases), "refused": refused,
            "partial_read_write_roundtrip": True, "later_section_left_unread": True}


def main():
    names = ("packed.py", "__init__.py", "check_and_measure.py")
    before = {name: sha(HERE / name) for name in names}
    tests = checks()
    width, count = 289, 1_048_576
    bound = (1 << 288) + 12345  # Public synthetic range, no primality claim.
    pattern = [((i + 1) * (1 << 277) + i * i * 7919) % bound for i in range(1024)]
    buf = io.BytesIO()
    start = time.perf_counter()
    written = pack_values(islice(cycle(pattern), count), width, count, buf, upper_bound=bound)
    packed_seconds = time.perf_counter() - start
    assert written == 37_879_808
    buf.seek(0)
    start = time.perf_counter()
    seen = 0
    for index, value in enumerate(unpack_values(buf, width, count, bound, require_eof=True)):
        assert value == pattern[index & 1023]
        seen += 1
    unpacked_seconds = time.perf_counter() - start
    assert seen == count
    after = {name: sha(HERE / name) for name in names}
    assert before == after
    result = {"claim_label": "EXECUTED", "all_passed": True,
              "command": "python3 -B research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_transport/codec/check_and_measure.py",
              "completed_utc": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
              "source_sha256": after, "sources_unchanged": True,
              "python": sys.version, "platform": platform.platform(), "tests": tests,
              "benchmark": {"width": width, "count": count, "upper_bound": bound,
                            "payload_bytes": written, "pack_seconds": packed_seconds,
                            "unpack_and_compare_seconds": unpacked_seconds,
                            "pack_values_per_second": count / packed_seconds,
                            "unpack_and_compare_values_per_second": count / unpacked_seconds,
                            "io": "BytesIO; codec blocks bounded, benchmark payload resident in memory",
                            "input": "public 1024-value deterministic cyclic pattern", "all_values_equal": True},
              "private_artifact_reads": 0, "payload_files_persisted": 0, "search_queries": 0,
              "qualification": "One public-data benchmark; parent owns container headers, total-length validation, signed interpretation and full transport run."}
    (HERE / "MEASUREMENTS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    summary = json.dumps({"all_passed": True, "malformed_rejections": len(tests["refused"]),
                          "benchmark": result["benchmark"]}, sort_keys=True)
    (HERE / "RUN.log").write_text("[EXECUTED] " + result["command"] + "\n[EXECUTED] Exit code: 0\n" + summary + "\n")
    print(summary)


if __name__ == "__main__":
    main()
