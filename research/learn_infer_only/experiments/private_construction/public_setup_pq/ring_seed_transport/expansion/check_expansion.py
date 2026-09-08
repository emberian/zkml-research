"""[EXECUTED] Cheap public deterministic domain/rejection checks; one full row."""
import hashlib
import json
from pathlib import Path
import platform
import sys
import time
from unittest.mock import patch

from public_expander import CANDIDATES_PER_CHUNK, ExpansionError, PublicExpander

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    names = ("public_expander.py", "__init__.py", "check_expansion.py")
    before = {name: sha(HERE / name) for name in names}
    seed = bytes(range(32))
    binding = hashlib.sha256(b"public expander deterministic test context v1").digest()
    q = (4294967767 << 256) + 1
    e = PublicExpander(seed, binding)
    row = e.row("A", 7, 8, q)
    assert row == PublicExpander(seed, binding).row("A", 7, 8, q)
    assert row == e.row(b"A", 7, 8, q)  # UTF-8 str and its bytes name same family.
    domains = [e.row_domain("A", 7, 8, q), e.row_domain("AA", 7, 8, q),
               e.row_domain("A", 8, 8, q), e.row_domain("A", 7, 9, q),
               e.row_domain("A", 7, 8, q - 2),
               PublicExpander(bytes([1]) + seed[1:], binding).row_domain("A", 7, 8, q),
               PublicExpander(seed, bytes([binding[0] ^ 1]) + binding[1:]).row_domain("A", 7, 8, q),
               PublicExpander(seed + seed, binding).row_domain("A", 7, 8, q)]
    assert len(set(domains)) == len(domains)
    assert e._chunk(domains[0], 0, 37) != e._chunk(domains[0], 1, 37)
    assert list(e.iter_rows("A", 2, 2, 8, q)) == [e.row("A", i, 8, q) for i in (2, 3)]

    def rejection_words(domain, chunk, word_bytes):
        assert word_bytes == 1
        return bytes([7, 5, 4, 0, 1, 2, 3]) + bytes(CANDIDATES_PER_CHUNK - 7)
    with patch.object(PublicExpander, "_chunk", staticmethod(rejection_words)):
        assert e.row("forced", 0, 5, 5) == [4, 0, 1, 2, 3]
    assert e.last_stats["rejections"] == 2
    forced_rejection = dict(e.last_stats)
    with patch.object(PublicExpander, "_chunk", staticmethod(
            lambda domain, chunk, word_bytes: bytes([255]) * (CANDIDATES_PER_CHUNK * word_bytes))):
        try:
            e.row("forced", 0, 1, 5)
        except ExpansionError:
            pass
        else:
            raise AssertionError("exhaustion emitted a fallback")
        forced_exhaustion = dict(e.last_stats)
        assert e.row("forced", 0, 5, 8) == [7] * 5
        assert e.last_stats["rejections"] == 0
    assert forced_exhaustion["candidates_examined"] == 17 * 1024
    assert not forced_exhaustion["completed"]

    invalid = 0
    for fn in (lambda: PublicExpander(bytes(31), binding),
               lambda: PublicExpander(seed, bytes(31)),
               lambda: e.row("", 0, 1, q), lambda: e.row("A", -1, 1, q),
               lambda: e.row("A", 0, 0, q), lambda: e.row("A", 0, 1, 1),
               lambda: e.row("A", True, 1, q),
               lambda: list(e.iter_rows("A", (1 << 64) - 1, 2, 1, q))):
        try:
            fn()
        except ValueError:
            invalid += 1
        else:
            raise AssertionError("invalid context accepted")

    # One actual full-size deterministic public row, not an estimator/grid.
    full = PublicExpander(seed, binding)
    values = full.row("A", 0, 16384, q)
    assert len(values) == 16384 and all(0 <= x < q for x in values)
    public_digest = hashlib.sha256(b"".join(x.to_bytes(37, "little") for x in values)).hexdigest()
    after = {name: sha(HERE / name) for name in names}
    assert before == after
    result = {"claim_label": "EXECUTED", "all_passed": True,
              "command": "python3 -B research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_transport/expansion/check_expansion.py",
              "completed_utc": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
              "source_sha256": after, "sources_unchanged": True,
              "python": sys.version, "platform": platform.platform(),
              "public_test_seed_hex": seed.hex(), "public_test_binding_hex": binding.hex(),
              "distinct_canonical_domains": len(domains), "distinct_chunk_addresses": True,
              "repeat_and_stream_equality": True, "invalid_inputs_rejected": invalid,
              "forced_rejection": forced_rejection, "forced_exhaustion": forced_exhaustion,
              "power_of_two_modulus_control": True,
              "full_public_row": {"family": "A", "index": 0, "N": 16384, "q": q,
                                  "stats": full.last_stats, "sha256_of_37byte_le_values": public_digest},
              "raw_row_files_persisted": 0, "private_artifact_reads": 0, "search_queries": 0,
              "security_scope": "Deterministic public expansion; no hidden-seed PRG claim or seeded Ring-LWE/regularity proof."}
    (HERE / "CHECKS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    summary = json.dumps({"all_passed": True, "distinct_domains": len(domains),
                          "invalid_inputs_rejected": invalid,
                          "full_row_stats": full.last_stats}, sort_keys=True)
    (HERE / "RUN.log").write_text("[EXECUTED] " + result["command"] + "\n[EXECUTED] Exit code: 0\n" + summary + "\n")
    print(summary)


if __name__ == "__main__":
    main()
