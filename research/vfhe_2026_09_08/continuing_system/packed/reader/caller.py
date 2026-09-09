#!/usr/bin/env python3
"""Invoke the separately pinned packed reader; the caller owns proof acceptance."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def config():
    profile = json.loads((HERE / "PROFILE.json").read_text())
    if profile["schema"] != "packed-class-reader-profile-v1":
        raise ValueError("unsupported packed reader profile")
    required = {str(HERE / filename) for filename in (
        "caller.py", "native/src/main.rs", "native/Cargo.toml", "native/Cargo.lock",
        "native/target/release/vfhe-packed-class-reader",
    )}
    if set(profile["pins"]) != required:
        raise ValueError("packed reader profile must pin its five operational files")
    if profile["native"] != str(HERE / "native/target/release/vfhe-packed-class-reader"):
        raise ValueError("unexpected packed reader executable")
    for filename, expected in profile["pins"].items():
        actual = hashlib.sha256(Path(filename).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"packed reader pin mismatch: {filename}")
    return profile


def main():
    profile = config()
    if sys.argv[1:] == ["config"]:
        print(json.dumps({"profile": profile, "pins_checked": len(profile["pins"])}))
        return
    if len(sys.argv) != 7 or sys.argv[1] != "read":
        raise ValueError("usage: config | read ISSUER DOT_CT DOT_SHA256 EVALKEY_SHA256 COUNTS_JSON")
    result = subprocess.run([profile["native"], *sys.argv[1:]], check=True, capture_output=True, text=True)
    decoded = json.loads(result.stdout)
    print(json.dumps(decoded, separators=(",", ":")))


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        sys.stderr.write(error.stderr)
        sys.exit(error.returncode)
    except (ValueError, OSError, KeyError) as error:
        sys.exit(str(error))
