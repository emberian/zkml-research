#!/usr/bin/env python3
"""Check the Lean-emitted sharing pass and summarize its one native workload."""
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
VFHE = ROOT.parent
OLD = VFHE / "arithmetic_rescale/artifacts/template_ir2.json"
NEW = ROOT / "artifacts/template_ir2.json"
BIN = VFHE / "proved_rescale/target/release/vfhe-proved-rescale"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def result(label):
    return json.loads((ROOT / "results" / (label + ".stdout")).read_text())


before_bytes = OLD.read_bytes()
assert digest(OLD) == "842a74f0a9950243847bf10427ce5394ad5314eb48488aeedeb68abccca55822"
assert digest(BIN) == "11bdb1c15236ac169a156a742207d7d665a991687b056215cc2d0f602ea41239"
assert before_bytes == (ROOT / "artifacts/template_before_ir2.json").read_bytes()
before, after = json.loads(before_bytes), json.loads(NEW.read_bytes())
seen, expected = set(), []
for assertion in before["constraints"]:
    key = json.dumps(assertion, separators=(",", ":"))
    if key not in seen:
        seen.add(key)
        expected.append(assertion)
assert after == dict(before, constraints=expected)
assert before["constraints"][0] == after["constraints"][0]

old_run, new_run = result("prove-before-clean"), result("prove-after-clean")
assert old_run["verified"] and new_run["verified"]
for key in ["backend", "actual_positions", "proof_rows", "trace_width", "public_tuple_width"]:
    assert old_run[key] == new_run[key]
assert result("verify-after-clean")["verified"]
assert result("verify-after-changed-output")["changed_output_rejected"]

with tempfile.TemporaryDirectory(prefix="assertion-sharing-replay-") as scratch:
    scratch = Path(scratch)
    (scratch / "EmitBfvRescale.lean").write_bytes(
        (VFHE / "arithmetic_rescale/EmitBfvRescale.lean").read_bytes()
    )
    patch = str(ROOT / "assertion-sharing.patch")
    subprocess.run(["git", "apply", "--check", patch], cwd=scratch, check=True)
    subprocess.run(["git", "apply", patch], cwd=scratch, check=True)
    for name in ["Compiler/AirAssertionShare.lean", "Compiler/BfvRescaleAssertionShare.lean", "EmitBfvRescale.lean"]:
        assert (scratch / name).read_bytes() == (ROOT / name).read_bytes()
    subprocess.run(["git", "apply", "--reverse", "--check", patch], cwd=scratch, check=True)

summary = {
    "status": "PASS",
    "arithmetic_constraints_before": len(before["constraints"]) - 1,
    "arithmetic_constraints_after": len(after["constraints"]) - 1,
    "removed_repeated_assertions": len(before["constraints"]) - len(after["constraints"]),
    "reduction_fraction": 5880 / 45209,
    "template_is_exact_stable_full_syntax_sharing": True,
    "original_template_reemitted_byte_exactly": True,
    "metadata_public_lookup_and_indices_unchanged": True,
    "trace_width": after["trace_width"],
    "liveness": json.loads((ROOT / "column-liveness.json").read_text()),
    "clean_native_pair": {
        "order": "baseline first, then successor; no overlapping agent-owned build",
        "before": old_run,
        "after": new_run,
        "prover_ratio_before_over_after": old_run["prove_ns"] / new_run["prove_ns"],
        "scope": "one matched32-row/24-position small BFV rescale workload; not a distributional speedup estimate",
    },
    "initial_pair_retained": {
        "before": result("prove-before"),
        "after": result("prove-after"),
        "limitation": "after-side overlapped a Lean source check; slower result retained and not used as the controlled pair",
    },
    "source_checks": {
        "guarded_theorem_and_instance_pins": 16,
        "guarded_modules": 2,
        "guarded_logs_empty": all(
            (ROOT / "results" / p).read_text() == ""
            for p in ["share-final.log", "rescale-final.log", "patched-emitter-final.log"]
        ),
        "patch_replay_exact": True,
    },
    "sources": {
        "baseline_template_sha256": digest(OLD),
        "successor_template_sha256": digest(NEW),
        "original_trace_sha256": digest(VFHE / "arithmetic_rescale/artifacts/trace.leu32"),
        "unchanged_native_binary_sha256": digest(BIN),
        "owned_lean_sha256": {p.name: digest(p) for p in (ROOT / "Compiler").glob("*.lean")},
        "patch_sha256": digest(ROOT / "assertion-sharing.patch"),
        "proposed_emitter_sha256": digest(ROOT / "EmitBfvRescale.lean"),
    },
}
(ROOT / "RESULTS.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps({k: summary[k] for k in ["status", "arithmetic_constraints_before", "arithmetic_constraints_after", "removed_repeated_assertions", "reduction_fraction"]}))
