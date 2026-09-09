"""[EXECUTED] Constructor/domain checks only; expansion is prohibited here."""
import hashlib
import json
from pathlib import Path
import sys
import time
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from expansion import PublicExpander
from expansion import public_expander as module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lp(value):
    return len(value).to_bytes(4, "big") + value


def main():
    old = HERE.parent.parent / "ring_seed_transport/expansion"
    source_before = {name: sha(HERE / name) for name in ("public_expander.py", "__init__.py", "check_version.py")}
    old_before = {name: sha(old / name) for name in ("public_expander.py", "__init__.py", "MANIFEST.json")}
    seed, binding = bytes(range(48)), bytes(range(32))
    q = (4294967767 << 256) + 1
    rejected = []
    forbidden = AssertionError("This check must never invoke expansion/SHAKE")
    with patch.object(module.hashlib, "shake_256", side_effect=forbidden) as shake, \
            patch.object(PublicExpander, "_chunk", side_effect=forbidden) as chunk:
        e = PublicExpander(seed, binding)
        assert len(e.seed) == 48 and len(e.binding) == 32
        assert module.PROTOCOL == b"ring-seed-semantic/public-rows/v2"
        domain = e.row_domain("A", 0, 16384, q)
        suffix = (lp(b"A") + bytes(8) + (16384).to_bytes(8, "big") +
                  lp(q.to_bytes(37, "big")))
        assert domain == lp(module.PROTOCOL) + lp(seed) + lp(binding) + suffix
        old_domain_with_same_bytes = lp(b"ring-seed-transport/public-rows/v1") + lp(seed) + lp(binding) + suffix
        assert domain != old_domain_with_same_bytes
        assert domain != e.row_domain("A", 1, 16384, q)
        assert domain != e.row_domain("missing", 0, 16384, q)
        for n in (32, 64, 47, 49):
            try:
                PublicExpander(bytes(n), binding)
            except ValueError:
                rejected.append(f"seed_bytes={n}")
            else:
                raise AssertionError("seed downgrade or wrong size accepted")
        for n in (31, 33):
            try:
                PublicExpander(seed, bytes(n))
            except ValueError:
                rejected.append(f"binding_bytes={n}")
            else:
                raise AssertionError("binding size accepted")
        assert e.totals == {"completed_rows": 0, "candidates_examined": 0,
                            "chunks_generated": 0, "xof_bytes_generated": 0}
        assert e.last_stats == {}
        assert shake.call_count == chunk.call_count == 0
    baseline = (old / "public_expander.py").read_text()
    replacement_pairs = [("See SECURITY.md", "See PROVENANCE.md"),
                         ("ring-seed-transport/public-rows/v1", "ring-seed-semantic/public-rows/v2"),
                         ("seed[32|64]", "seed[48]"),
                         ("len(seed) not in (32, 64)", "len(seed) != 48"),
                         ("exactly 32 or 64 bytes", "exactly 48 bytes")]
    for before, after in replacement_pairs:
        assert baseline.count(before) == 1
        baseline = baseline.replace(before, after)
    assert baseline == (HERE / "public_expander.py").read_text()
    assert (old / "__init__.py").read_bytes() == (HERE / "__init__.py").read_bytes()
    assert source_before == {name: sha(HERE / name) for name in source_before}
    assert old_before == {name: sha(old / name) for name in old_before}
    result = {"claim_label": "EXECUTED", "all_passed": True,
              "command": "python3 -B research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_semantic_successor/expansion/check_version.py",
              "completed_utc": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
              "source_sha256": source_before, "frozen_baseline_sha256": old_before,
              "exact_source_replacements": replacement_pairs,
              "protocol": module.PROTOCOL.decode(), "seed_bytes": 48, "binding_bytes": 32,
              "rejected": rejected, "canonical_domain_and_version_separation": True,
              "domain_bytes": len(domain), "public_test_domain_sha256": hashlib.sha256(domain).hexdigest(),
              "package_import_compatible": True, "initializer_byte_identical": True,
              "source_and_old_pins_unchanged": True,
              "expanded_rows": 0, "xof_calls": 0, "setup_runs": 0,
              "private_artifact_reads": 0, "search_queries": 0}
    (HERE / "CHECKS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    stdout = json.dumps({"all_passed": True, "protocol": result["protocol"],
                         "seed_bytes": 48, "rejected": rejected,
                         "expanded_rows": 0, "xof_calls": 0}, sort_keys=True)
    (HERE / "RUN.log").write_text("[EXECUTED] " + result["command"] + "\n[EXECUTED] Exit code: 0\n" + stdout + "\n")
    print(stdout)


if __name__ == "__main__":
    main()
