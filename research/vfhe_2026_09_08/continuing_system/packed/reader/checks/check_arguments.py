#!/usr/bin/env python3
"""Minimal native argument/binding refusals; no keygen, decryption, or proof run."""
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parents[1]
native = HERE / "native/target/release/vfhe-packed-class-reader"
records = []


def run(name, command, expected_error=None):
    result = subprocess.run([str(x) for x in command], capture_output=True, text=True)
    record = {"name": name, "command": [str(x) for x in command],
              "exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
    records.append(record)
    if expected_error is None:
        assert result.returncode == 0, record
    else:
        assert result.returncode != 0 and not result.stdout and expected_error in result.stderr, record
    return result


ast.parse((HERE / "caller.py").read_text())
config = json.loads(run("profile_pins", [sys.executable, HERE / "caller.py", "config"]).stdout)
assert config["pins_checked"] == 5
with tempfile.TemporaryDirectory(prefix="packed-reader-public-check-") as temporary:
    issuer = Path(temporary)
    public_bytes = b"Public placeholder for the pre-decryption hash refusal only.\n"
    (issuer / "evaluation.key").write_bytes(public_bytes)
    dot = issuer / "dot.ct"
    dot.write_bytes(public_bytes)
    zero = "0" * 64
    base = [native, "read", issuer, dot]
    run("count_above_capacity", [*base, zero, zero, "[9,0,0,0,0,0,0,0]"], "each class count must be in 0..8")
    run("evaluation_key_hash_mismatch", [*base, zero, zero, "[0,0,0,0,0,0,0,0]"], "evaluation-key SHA-256 mismatch")
    run("ciphertext_hash_mismatch", [*base, zero, hashlib.sha256(public_bytes).hexdigest(), "[0,0,0,0,0,0,0,0]"], "dot-ciphertext SHA-256 mismatch")
    assert not (issuer / ".private").exists()

linear_profile_path = HERE.parents[1] / "linear/PIPELINE.json"
linear_profile = json.loads(linear_profile_path.read_text())
linear_pins_unchanged = all(hashlib.sha256(Path(path).read_bytes()).hexdigest() == expected
                            for path, expected in linear_profile["pins"].items())
assert linear_pins_unchanged
report = {"claim_label": "EXECUTED", "caller_parses": True, "profile_pins": 5,
          "native_refusal_checks": 3, "commands": records,
          "linear_profile_pins_unchanged": len(linear_profile["pins"]),
          "private_reads": 0, "key_generations": 0, "proof_runs": 0,
          "complete_packed_flow": "Not launched by this check; owned by packed learner lifecycle."}
(HERE / "CHECKS.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: v for k, v in report.items() if k != "commands"}, indent=2))
