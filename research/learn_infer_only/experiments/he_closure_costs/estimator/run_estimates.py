#!/usr/bin/env python3
"""Run pinned generic-LWE attack estimates for the two executed BFV tuples.

This is a heuristic proxy for structured ring-LWE, not a BFV security proof.
Read AUDIT.md for sample exposure, distribution and model qualifications.
Each attack writes its result immediately. Failed/timed-out attacks remain
explicit; they are never silently removed from a security minimum.
"""
import argparse
import hashlib
import json
import os
import signal
import sys
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
PIN = "53da5982597709ba0fdf94ea37a84d822310fd84"
SOURCE = HERE / "runtime/pinned-estimator"
os.environ.setdefault("DOT_SAGE", str(HERE / "runtime/sage_cache"))
os.environ.setdefault("MPLCONFIGDIR", str(HERE / "runtime/mpl"))
sys.dont_write_bytecode = True
sys.path.insert(0, str(SOURCE))

from sage.all import ZZ, RR, oo, log  # noqa: E402
from sage.version import version as sage_version  # noqa: E402
from estimator import LWE, ND  # noqa: E402
from estimator.reduction import ADPS16, MATZOV  # noqa: E402

MODULI = {
    "83": 2199023190017 * 4398046486529,
    "109": 68719403009 * 68719230977 * 137438822401,
}
MODELS = {
    "MATZOV_classical": lambda: MATZOV(nn="list_decoding-classical"),
    "ADPS16_classical": lambda: ADPS16(mode="classical"),
    "ADPS16_quantum_core_svp": lambda: ADPS16(mode="quantum"),
    "MATZOV_quantum_depth_width": lambda: MATZOV(nn="list_decoding-dw"),
}


def expired(_sig, _frame):
    raise TimeoutError("per-attack wall-time budget exceeded")


def values_of(cost):
    out = {str(k): str(v) for k, v in cost.items() if k != "problem"}
    logs = {}
    for k in ["rop", "red", "guess", "mem", "svp", "N", "m"]:
        if k in cost:
            try:
                v = cost[k]
                logs[k] = float(log(v, 2)) if v > 0 and v != oo else str(v)
            except (TypeError, ValueError, OverflowError):
                logs[k] = None
    return out, logs


def one(attack, params, model):
    if attack == "usvp":
        return LWE.primal_usvp(params, red_cost_model=model, red_shape_model="gsa")
    if attack == "bdd":
        return LWE.primal_bdd(params, red_cost_model=model, red_shape_model="gsa")
    if attack == "bdd_hybrid":
        return LWE.primal_hybrid(params, red_cost_model=model, red_shape_model="gsa", mitm=False, babai=False)
    if attack == "bdd_mitm_hybrid":
        return LWE.primal_hybrid(params, red_cost_model=model, red_shape_model="gsa", mitm=True, babai=True)
    if attack == "dual":
        return LWE.dual(params, red_cost_model=model)
    if attack == "dual_hybrid":
        return LWE.dual_hybrid(params, red_cost_model=model)
    if attack == "bkw":
        return LWE.coded_bkw(params)
    if attack == "arora_gb":
        return LWE.arora_gb(params)
    raise ValueError(attack)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--qbits", nargs="+", choices=MODULI, default=["83", "109"])
    parser.add_argument("--samples", nargs="+", choices=["4096", "infinity"], default=["4096", "infinity"])
    parser.add_argument("--models", nargs="+", choices=MODELS, default=list(MODELS)[:3])
    parser.add_argument("--attacks", nargs="+", default=["usvp", "dual_hybrid"])
    parser.add_argument("--seconds", type=int, default=180)
    parser.add_argument("--output", default="results.jsonl")
    args = parser.parse_args()
    distribution = ND.CenteredBinomial(20)
    assert distribution.bounds == (-20, 20)
    assert abs(float(distribution.stddev)**2 - 10) < 1e-12
    manifest = {
        "estimator_commit": PIN, "sage_version": sage_version,
        "python_version": sys.version, "model_source_sha256": hashlib.sha256((SOURCE / "estimator/reduction.py").read_bytes()).hexdigest(),
        "distribution_class": type(distribution).__name__, "eta": 20,
        "variance_exact_by_definition": 10, "bounds": [-20, 20],
        "distribution_repr": repr(distribution), "is_Gaussian_like_flag": distribution.is_Gaussian_like,
        "generic_LWE_proxy_not_ring_reduction": True,
        "quantum_scope": "quantum lattice-reduction cost model substitution; does not quantize all guessing/FFT/attack costs",
        "shape_model": "gsa", "per_attack_seconds": args.seconds,
        "invocation": sys.argv,
    }
    destination = HERE / args.output
    (destination.with_suffix(".manifest.json")).write_text(json.dumps(manifest, indent=2) + "\n")
    signal.signal(signal.SIGALRM, expired)
    with destination.open("w") as output:
        for sample in args.samples:
            for qbits in args.qbits:
                q = ZZ(MODULI[qbits])
                params = LWE.Parameters(n=4096, q=q, Xs=ND.CenteredBinomial(20),
                                        Xe=ND.CenteredBinomial(20),
                                        m=4096 if sample == "4096" else oo,
                                        tag=f"BFV_proxy_Q{qbits}_CBD20_m{sample}")
                for model_name in args.models:
                    model = MODELS[model_name]()
                    for attack in args.attacks:
                        row = {"Q_bits_label": qbits, "Q_exact": str(q), "n": 4096,
                               "samples": sample, "Xs": "CenteredBinomial(20)",
                               "Xe": "CenteredBinomial(20)", "model": model_name,
                               "attack": attack, "parameters_repr": repr(params),
                               "status": "RUNNING"}
                        print("START", json.dumps(row), flush=True)
                        started = time.monotonic()
                        signal.alarm(args.seconds)
                        try:
                            cost = one(attack, params, model)
                            row["fields"], row["log2_fields"] = values_of(cost)
                            row["repr"] = repr(cost)
                            row["status"] = "EXECUTED"
                        except Exception as error:
                            row["status"] = "TIMEOUT" if isinstance(error, TimeoutError) else "ERROR"
                            row["exception"] = repr(error)
                            row["traceback"] = traceback.format_exc()
                        finally:
                            signal.alarm(0)
                        row["wall_seconds_estimator_runtime_not_attack_latency"] = time.monotonic() - started
                        output.write(json.dumps(row, allow_nan=False) + "\n")
                        output.flush()
                        print("RESULT", json.dumps(row, allow_nan=False), flush=True)


if __name__ == "__main__":
    main()
