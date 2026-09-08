#!/usr/bin/env python3
"""Four public BFV ciphertexts -> native Lean-plan witness -> independently verified proof."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

PACKAGE = Path(__file__).resolve().parent
SWARM = PACKAGE.parent
ARITHMETIC = SWARM / "arithmetic_coverage"
APPROVED_TEMPLATE = "1afc2b3a120f59fdd79d273c6d32887373c5718225cb6e94b82a7231010c3aa7"
NAMES = ("acc.ct", "fresh.ct", "old.ct", "out.ct")


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", type=Path, help="directory containing acc/fresh/old/out.ct")
    parser.add_argument("output", type=Path, help="new job directory; must not already exist")
    parser.add_argument("--runtime", type=Path, default=SWARM / "proved_operation/target/release/vfhe-proved-operation")
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--step-timeout", type=int, default=600)
    args = parser.parse_args()
    if args.threads < 1 or args.step_timeout < 1:
        parser.error("threads and step-timeout must be positive")
    case, output, runtime = args.case.resolve(), args.output.resolve(), args.runtime.resolve()
    if output.exists():
        parser.error("output already exists; choose a new job directory")
    if not runtime.is_file():
        parser.error("build the proved_operation native runtime first, or set --runtime")
    emitter = PACKAGE / "emit.py"
    pins = json.loads((PACKAGE / "SOURCE_PINS.json").read_text())
    expected_runtime = pins["shared_files"][str(SWARM / "proved_operation/target/release/vfhe-proved-operation")]
    if sha256(runtime) != expected_runtime:
        parser.error("runtime differs from the approved update prover/verifier")
    for name in NAMES:
        if not (case / name).is_file():
            parser.error(f"missing public ciphertext: {case / name}")
    output.mkdir(parents=True)
    staged = output / "case"
    staged.mkdir()
    logs = output / "logs"
    logs.mkdir()
    report = {
        "claim": "EXECUTED public-only learner-update proof pipeline",
        "started_utc": now(), "status": "running", "steps": [],
        "operation": "acc + fresh - old",
        "approved_template_sha256": APPROVED_TEMPLATE,
        "runtime_sha256": sha256(runtime),
        "emitter_wrapper_sha256": sha256(emitter),
        "compiler_plan_source_sha256": sha256(PACKAGE / "Compiler/BfvExpiryWitnessPlan.lean"),
        "witness_plan_sha256": sha256(PACKAGE / "program/witness_plan.json"),
        "witness_generation": "Lean-emitted plan executed by unchanged native witness consumer",
        "inputs": {},
        "scope": "Selected exact ciphertext coefficient relation; no encoder, FIFO authorization, key membership or confidentiality claim.",
    }

    def save() -> None:
        (output / "result.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(label: str, command: list[str], env: dict[str, str] | None = None) -> None:
        entry = {"label": label, "command": command, "cwd": str(ARITHMETIC), "started_utc": now()}
        report["steps"].append(entry)
        save()
        started = time.perf_counter()
        with (logs / f"{label}.stdout").open("wb") as stdout, (logs / f"{label}.stderr").open("wb") as stderr:
            try:
                result = subprocess.run(command, cwd=ARITHMETIC, env=env, stdout=stdout, stderr=stderr,
                                        timeout=args.step_timeout, check=False)
                entry["returncode"] = result.returncode
            finally:
                entry["elapsed_seconds"] = time.perf_counter() - started
                save()
        print(f"{label}: exit {result.returncode}, {entry['elapsed_seconds']:.3f}s", flush=True)
        if result.returncode:
            raise RuntimeError(f"{label} failed; see {logs / (label + '.stderr')}")

    started = time.perf_counter()
    try:
        for name in NAMES:
            shutil.copyfile(case / name, staged / name)
            report["inputs"][name] = {"sha256": sha256(staged / name), "bytes": (staged / name).stat().st_size}
        if (case / "source_event.json").is_file():
            shutil.copyfile(case / "source_event.json", staged / "source_event.json")
            report["source_event_sha256"] = sha256(staged / "source_event.json")
            report["source_event_scope"] = "Carried application metadata; not authenticated or proved by this pipeline."
        save()
        run("export", [str(runtime), "export-update-ntt", str(staged)])
        env = os.environ.copy()
        emitted = output / "emitted"
        run("emit", [sys.executable, str(emitter), str(emitted),
                     str(staged / "public_ntt_rows.json")], env)
        template = emitted / "template_ir2.json"
        if sha256(template) != APPROVED_TEMPLATE:
            raise RuntimeError("emitted relation differs from the application's approved template")
        env = os.environ.copy()
        env["RAYON_NUM_THREADS"] = str(args.threads)
        proof_dir = output / "proof"
        run("prove", [str(runtime), "prove-update", str(template), str(staged),
                      str(emitted / "trace.leu32"), str(proof_dir)], env)
        run("verify", [str(runtime), "verify-update", str(template), str(staged), str(proof_dir / "proof.bin")], env)
        verification = json.loads((logs / "verify.stdout").read_text())
        if verification.get("verified") is not True:
            raise RuntimeError("fresh verifier did not report acceptance")
        proof = json.loads((proof_dir / "proof.json").read_text())
        report.update(status="verified", verified=True, verification=verification, proof=proof,
                      public_rows_sha256=sha256(staged / "public_ntt_rows.json"),
                      emission=json.loads((emitted / "emission.json").read_text()))
    except Exception as error:
        report.update(status="failed", verified=False, error=str(error))
        print(str(error), file=sys.stderr)
    finally:
        report["finished_utc"] = now()
        report["elapsed_seconds"] = time.perf_counter() - started
        save()
    print(json.dumps({"status": report["status"], "result": str(output / "result.json"),
                      "elapsed_seconds": report["elapsed_seconds"]}), flush=True)
    return 0 if report["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
