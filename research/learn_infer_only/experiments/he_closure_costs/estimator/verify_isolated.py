#!/usr/bin/env python3
"""Recheck reported minima / failing dual hybrids in fresh Sage processes.

This responds to an observed order-sensitive symbolic SignError in a
multi-attack invocation. It does not modify the pinned estimator.
Run this file through the activated Sage environment, like run_estimates.py.
"""
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
os.environ["DOT_SAGE"] = str(HERE / "runtime/sage_cache")
os.environ["MPLCONFIGDIR"] = str(HERE / "runtime/mpl")
names = []
for q in ["83", "109"]:
    for samples in ["4096", "infinity"]:
        for model, attack in [
            ("MATZOV_classical", "bdd"),
            ("ADPS16_classical", "usvp"),
            ("ADPS16_quantum_core_svp", "usvp"),
            ("MATZOV_quantum_depth_width", "bdd"),
            ("MATZOV_quantum_depth_width", "dual_hybrid"),
        ]:
            name = f"isolated_{q}_{samples}_{model}_{attack}"
            args = [sys.executable, str(HERE / "run_estimates.py"), "--qbits", q,
                    "--samples", samples, "--models", model, "--attacks", attack,
                    "--seconds", "60", "--output", name + ".jsonl"]
            with (HERE / (name + ".log")).open("w") as output, (HERE / (name + "_stderr.log")).open("w") as errors:
                completed = subprocess.run(args, stdout=output, stderr=errors, timeout=80)
            names.append({"name": name, "returncode": completed.returncode, "args": args})
            print(json.dumps(names[-1]), flush=True)
(HERE / "isolated_invocations.json").write_text(json.dumps(names, indent=2) + "\n")
