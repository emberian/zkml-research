#!/usr/bin/env python3
"""Standalone caller-selected matched-field linear producer and consumer.

  caller.py pin-config LINEAR_PLAN NATIVE NEW_PIPELINE_JSON
  caller.py [--profile PIPELINE_JSON] config
  caller.py [--profile PIPELINE_JSON] produce-linear MODEL QUERY EVALUATION_KEY NEW_OUTPUT
  caller.py [--profile PIPELINE_JSON] verify-linear EXPECTED_JSON PRODUCED NEW_OUTPUT
  caller.py [--profile PIPELINE_JSON] produce-update ACC FRESH OLD NEW_OUTPUT
  caller.py [--profile PIPELINE_JSON] verify-update EXPECTED_JSON PRODUCED NEW_OUTPUT

EXPECTED_JSON pins model_ciphertext_sha256, query_sha256, and
evaluation_key_sha256; dot_ciphertext_sha256 is optional. Outputs must be new.
pin-config explicitly records the chosen plan, executable and caller byte hashes;
production and verification only check those pins and never regenerate them.
Update EXPECTED_JSON pins acc_sha256, fresh_sha256, and old_sha256;
out_sha256 is optional. The consumer reconstructs the complete public case and
verifies all 352 linear or 32 update proofs in a fresh native process.
Neither interface invokes a secret-key reader.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROFILE_SCHEMA = "matched-field-linear-profile-v1"
BUNDLE_SCHEMA = "matched-field-linear-bundle-v1"
STATEMENT_KIND = "packed-linear-dot"
INPUTS = {"model_ciphertext_sha256", "query_sha256", "evaluation_key_sha256"}
BINDING_FIELDS = INPUTS | {"linear_plan_sha256", "dot_ciphertext_sha256"}
UPDATE_INPUTS = {"acc_sha256", "fresh_sha256", "old_sha256"}
UPDATE_BINDING_FIELDS = UPDATE_INPUTS | {"out_sha256"}
PROFILE_FIELDS = {"schema", "linear_plan", "linear_plan_sha256", "native",
                  "native_sha256", "caller_sha256"}
CHUNKS = 352
UPDATE_CHUNKS = 32
ROWS_PER_CHUNK = 1024
PRIMES = [1125899906826241, 1125899906629633, 1125899905744897, 1125899905351681]
HEX = re.compile(r"[0-9a-f]{64}\Z")
MAX_JSON = 32 << 20


def require(condition, message):
    if not condition:
        raise ValueError(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def public_path(value):
    path = Path(value).resolve()
    require(".private" not in path.parts, "private paths are outside this public interface")
    return path


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON field: {key}")
        result[key] = value
    return result


def invalid_constant(value):
    raise ValueError(f"nonfinite JSON value: {value}")


def read(path):
    path = public_path(path)
    require(path.is_file(), f"missing regular JSON file: {path}")
    with path.open("rb") as stream:
        encoded = stream.read(MAX_JSON + 1)
    require(len(encoded) <= MAX_JSON, f"JSON exceeds size limit: {path}")
    return json.loads(encoded, object_pairs_hook=unique_object, parse_constant=invalid_constant)


def save_new(path, value):
    path = public_path(path)
    encoded = json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n"
    with path.open("x", encoding="utf-8") as stream:
        stream.write(encoded)


def sha(path):
    path = public_path(path)
    require(path.is_file(), f"missing regular input file: {path}")
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            result.update(block)
    return result.hexdigest()


def digest(value):
    require(isinstance(value, str) and HEX.fullmatch(value) is not None,
            "expected lowercase SHA-256 hex")
    return value


def binding(value, kind="linear"):
    fields = BINDING_FIELDS if kind == "linear" else UPDATE_BINDING_FIELDS
    require(isinstance(value, dict) and set(value) == fields,
            "binding must contain exactly the defined digests")
    return {key: digest(value[key]) for key in sorted(fields)}


def expected_values(value, kind="linear"):
    inputs = INPUTS if kind == "linear" else UPDATE_INPUTS
    output = "dot_ciphertext_sha256" if kind == "linear" else "out_sha256"
    require(isinstance(value, dict) and inputs <= set(value) <= inputs | {output},
            "expectation must pin all three inputs; only output is optional")
    return {key: digest(value[key]) for key in sorted(value)}


def pin_config(plan, native, out):
    plan, native, out = map(public_path, (plan, native, out))
    require(os.access(native, os.X_OK), "native executable is not executable")
    config = {"schema": PROFILE_SCHEMA, "linear_plan": str(plan),
              "linear_plan_sha256": sha(plan), "native": str(native),
              "native_sha256": sha(native), "caller_sha256": sha(__file__)}
    save_new(out, config)
    return config


def config(profile):
    value = read(profile)
    require(isinstance(value, dict) and set(value) == PROFILE_FIELDS,
            "unexpected profile fields")
    require(value["schema"] == PROFILE_SCHEMA, "wrong profile schema")
    for field in ("linear_plan", "native"):
        require(isinstance(value[field], str), "profile paths must be strings")
        path = public_path(value[field])
        require(path.is_absolute() and str(path) == value[field], "profile paths must be resolved absolute paths")
        require(sha(path) == digest(value[field + "_sha256"]), f"{field} byte pin mismatch")
    require(sha(__file__) == digest(value["caller_sha256"]), "caller byte pin mismatch")
    require(os.access(value["native"], os.X_OK), "native executable is not executable")
    return value


def approve(expected, actual, profile, kind="linear"):
    actual = binding(actual, kind)
    expected = expected_values(expected, kind)
    if kind == "linear":
        require(actual["linear_plan_sha256"] == profile["linear_plan_sha256"], "linear-plan binding mismatch")
    for key, value in expected.items():
        require(actual[key] == value, f"caller expectation mismatch: {key}")
    return actual


def input_binding(model, query, key, kind="linear"):
    names = (("model_ciphertext_sha256", "query_sha256", "evaluation_key_sha256") if kind == "linear"
             else ("acc_sha256", "fresh_sha256", "old_sha256"))
    return dict(zip(names,
                    (sha(path) for path in (model, query, key))))


def case_binding(case, profile, kind="linear"):
    if kind == "update":
        return binding({f"{name}_sha256": sha(case / f"{name}.ct")
                        for name in ("acc", "fresh", "old", "out")}, kind)
    actual = input_binding(case / "model.ct", case / "query.json", case / "evaluation.key")
    actual.update(linear_plan_sha256=profile["linear_plan_sha256"],
                  dot_ciphertext_sha256=sha(case / "expected_dot.ct"))
    require(sha(case / "steps/10.ct") == actual["dot_ciphertext_sha256"],
            "last step differs from dot ciphertext")
    return binding(actual)


def pins(paths):
    return {str(public_path(path)): sha(path) for path in paths}


def check_pins(frozen):
    for path, expected in frozen.items():
        require(sha(path) == expected, f"input changed during operation: {path}")


def case_files(case, kind="linear"):
    if kind == "update":
        return [case / f"{name}.ct" for name in ("acc", "fresh", "old", "out")]
    return ([case / name for name in ("model.ct", "query.json", "evaluation.key", "expected_dot.ct")]
            + [case / f"steps/{i:02}.ct" for i in range(11)])


def proof_files(proofs, kind="linear"):
    count = CHUNKS if kind == "linear" else UPDATE_CHUNKS
    return [proofs / "bundle.json"] + [proofs / f"chunk{i:03}.bin" for i in range(count)]


def run(out, label, argv):
    env = dict(os.environ)
    env["RAYON_NUM_THREADS"] = "1"
    env["CARGO_BUILD_JOBS"] = "1"
    started = time.monotonic()
    with (out / f"{label}.stdout").open("xb") as stdout, (out / f"{label}.stderr").open("xb") as stderr:
        process = subprocess.run([str(arg) for arg in argv], stdout=stdout, stderr=stderr,
                                 env=env, check=False)
    require(process.returncode == 0, f"native {label} failed ({process.returncode}); see {out / (label + '.stderr')}")
    return time.monotonic() - started


def native_report(path, actual, proofs, independent, kind="linear"):
    count = CHUNKS if kind == "linear" else UPDATE_CHUNKS
    report = read(path)
    require(isinstance(report, dict), "native report is not an object")
    require(report.get(f"complete_{kind}_verified") is True, "native report did not verify the complete relation")
    if independent:
        require(report.get("independent_consumer") is True and report.get("self_verification_only") is not True,
                "native report is not an independent consumer result")
    else:
        require(report.get("self_verification_only") is True,
                "native producer report lacks its self-verification scope")
    require(type(report.get("private_files_read")) is int and report["private_files_read"] == 0,
            "native operation exceeded the public-input scope")
    require(binding(report.get("binding"), kind) == actual, "native report binding mismatch")
    require(type(report.get("chunks")) is int and report["chunks"] == count, "native report has wrong chunk count")
    records = report.get("chunk_records")
    require(isinstance(records, list) and len(records) == count, "native report lacks complete chunk records")
    indexes = [record.get("index") if isinstance(record, dict) else None for record in records]
    require(all(type(index) is int for index in indexes) and indexes == list(range(count)),
            "native chunk records are missing, reordered, duplicated or out of range")
    require(type(report.get("proof_bytes")) is int and report["proof_bytes"] > 0,
            "native report lacks proof byte count")
    total = 0
    for index, record in enumerate(records):
        required = {"index": index, "stage": index // 32, "prime_index": (index // 8) % 4,
                    "modulus": PRIMES[(index // 8) % 4], "rows": ROWS_PER_CHUNK,
                    "first_coefficient": (index % 8) * ROWS_PER_CHUNK}
        for key, value in required.items():
            require(type(record.get(key)) is int and record[key] == value,
                    f"native chunk {index} has wrong {key}")
        filename = f"chunk{index:03}.bin"
        require(record.get("file") == filename, f"native chunk {index} has wrong filename")
        require(digest(record.get("proof_sha256")) == sha(proofs / filename),
                f"native chunk {index} proof digest mismatch")
        digest(record.get("public_rows_sha256"))
        digest(record.get("context_sha256"))
        timing = record.get("timing")
        require(isinstance(timing, dict) and type(timing.get("proof_bytes")) is int
                and timing["proof_bytes"] == (proofs / filename).stat().st_size,
                f"native chunk {index} has wrong proof byte count")
        total += timing["proof_bytes"]
    require(total == report["proof_bytes"], "native proof byte total mismatch")
    return report


def produce_operation(kind, profile_path, model, query, key, out):
    count = CHUNKS if kind == "linear" else UPDATE_CHUNKS
    profile = config(profile_path)
    frozen_profile = pins([profile_path])
    model, query, key, out = map(public_path, (model, query, key, out))
    expected = input_binding(model, query, key, kind)
    frozen_inputs = pins([model, query, key])
    out.mkdir()
    save_new(out / "started.json", {"expected": expected, "profile_sha256": sha(profile_path), "started_utc": now()})
    started = time.monotonic()
    prefix = ["import", profile["linear_plan"]] if kind == "linear" else ["import-update"]
    run(out, "import", [profile["native"], *prefix, model, query, key, out / "case"])
    actual = approve(expected, case_binding(out / "case", profile, kind), profile, kind)
    operation = read(out / "case/operation.json")
    require(binding(operation.get("binding"), kind) == actual, "import metadata binding mismatch")
    frozen_case = pins(case_files(out / "case", kind))
    prefix = ["prove-linear", profile["linear_plan"]] if kind == "linear" else ["prove-update"]
    run(out, "prove", [profile["native"], *prefix, out / "case", out / "proofs"])
    report = native_report(out / "proofs/result.json", actual, out / "proofs", independent=False, kind=kind)
    frozen_proofs = pins(proof_files(out / "proofs", kind))
    check_pins(frozen_inputs)
    check_pins(frozen_case)
    check_pins(frozen_profile)
    require(config(profile_path) == profile, "profile changed during production")
    result = {"schema": BUNDLE_SCHEMA if kind == "linear" else "matched-field-update-bundle-v1",
              "statement_kind": STATEMENT_KIND if kind == "linear" else "ciphertext-update",
              "case": str(out / "case"), "proofs": str(out / "proofs"), "binding": actual,
              "fresh_proofs": count, "proofs_generated": True, "fresh_consumer_verified": False,
              "proof_bytes": report["proof_bytes"], "native_producer_report": str(out / "proofs/result.json"),
              "case_and_proof_pins": {**frozen_case, **frozen_proofs},
              "profile_sha256": sha(profile_path), "private_files_read": 0,
              "elapsed_seconds": time.monotonic() - started, "finished_utc": now()}
    if kind == "linear":
        result["dot_ciphertext"] = str(out / "case/expected_dot.ct")
    else:
        result["output_ciphertext"] = str(out / "case/out.ct")
    save_new(out / "result.json", result)
    return result


def produce_linear(profile_path, model, query, key, out):
    return produce_operation("linear", profile_path, model, query, key, out)


def produce_update(profile_path, acc, fresh, old, out):
    return produce_operation("update", profile_path, acc, fresh, old, out)


def verify_operation(kind, profile_path, expected_path, produced, out):
    count = CHUNKS if kind == "linear" else UPDATE_CHUNKS
    profile = config(profile_path)
    frozen_profile = pins([profile_path])
    expected_path, produced, out = map(public_path, (expected_path, produced, out))
    expected = expected_values(read(expected_path), kind)
    supplied_path = produced / "result.json"
    frozen_metadata = pins([expected_path, supplied_path])
    supplied = read(supplied_path)
    schema = BUNDLE_SCHEMA if kind == "linear" else "matched-field-update-bundle-v1"
    statement = STATEMENT_KIND if kind == "linear" else "ciphertext-update"
    require(isinstance(supplied, dict) and supplied.get("schema") == schema
            and supplied.get("statement_kind") == statement, "wrong producer bundle")
    case, proofs = public_path(supplied["case"]), public_path(supplied["proofs"])
    actual = approve(expected, case_binding(case, profile, kind), profile, kind)
    require(binding(supplied.get("binding"), kind) == actual, "producer bundle binding mismatch")
    frozen_inputs = pins(case_files(case, kind) + proof_files(proofs, kind))
    # Stored producer pins are provenance checks only. The native consumer below
    # derives its statement from the public case and verifies all proof bytes.
    require(supplied.get("case_and_proof_pins") == frozen_inputs, "producer files changed since bundle creation")
    out.mkdir()
    save_new(out / "expected.json", expected)
    save_new(out / "started.json", {"expected": expected, "binding": actual,
                                    "input_pins": frozen_inputs, "profile_sha256": sha(profile_path), "started_utc": now()})
    started = time.monotonic()
    prefix = ["verify-linear", profile["linear_plan"]] if kind == "linear" else ["verify-update"]
    run(out, "verify", [profile["native"], *prefix,
                         out / "expected.json", case, proofs, out / "native-result.json"])
    report = native_report(out / "native-result.json", actual, proofs, independent=True, kind=kind)
    check_pins(frozen_inputs)
    check_pins(frozen_metadata)
    check_pins(frozen_profile)
    require(config(profile_path) == profile, "profile changed during verification")
    receipt = {"verified": True, f"complete_{kind}_verified": True, "binding": actual,
               "proofs_verified": count, "proofs_generated_this_call": 0,
               "native_report": str(out / "native-result.json"), "native_report_sha256": sha(out / "native-result.json"),
               "private_files_read": 0,
               "profile_sha256": sha(profile_path), "elapsed_seconds": time.monotonic() - started,
               "finished_utc": now()}
    if kind == "linear":
        receipt["dot_ciphertext"] = str(case / "expected_dot.ct")
    else:
        receipt["output_ciphertext"] = str(case / "out.ct")
    result = {**report, **receipt}
    save_new(out / "result.json", result)
    return result


def verify_linear(profile_path, expected_path, produced, out):
    return verify_operation("linear", profile_path, expected_path, produced, out)


def verify_update(profile_path, expected_path, produced, out):
    return verify_operation("update", profile_path, expected_path, produced, out)


def main(argv=None):
    args = list(sys.argv[1:] if argv is None else argv)
    if not args or args in (["--help"], ["-h"]):
        print(__doc__)
        return
    if args[0] == "pin-config":
        require(len(args) == 4, __doc__)
        pin_config(*args[1:])
        print(json.dumps({"profile": str(public_path(args[3])), "pins_recorded": True}))
        return
    profile = HERE / "PIPELINE.json"
    if args[0] == "--profile":
        require(len(args) >= 3, __doc__)
        profile, args = public_path(args[1]), args[2:]
    action, *args = args
    if action == "config" and not args:
        print(json.dumps(config(profile), indent=2))
        return
    if action == "produce-linear" and len(args) == 4:
        result = produce_linear(profile, *args)
    elif action == "verify-linear" and len(args) == 3:
        result = verify_linear(profile, *args)
    elif action == "produce-update" and len(args) == 4:
        result = produce_update(profile, *args)
    elif action == "verify-update" and len(args) == 3:
        result = verify_update(profile, *args)
    else:
        raise ValueError(__doc__)
    summary = {"action": action, "result": str(public_path(args[-1]) / "result.json")}
    for field in ("complete_linear_verified", "complete_update_verified", "fresh_proofs", "proofs_verified", "private_files_read"):
        if field in result:
            summary[field] = result[field]
    print(json.dumps(summary))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f"caller refused: {error}", file=sys.stderr)
        raise SystemExit(1)
