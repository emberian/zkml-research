#!/usr/bin/env python3
"""Capture small immutable journal sources; never modify the original core."""
from pathlib import Path
import hashlib
import json
import shutil

HERE = Path(__file__).resolve().parent
CORE = HERE.parent / "journal"
DEST = HERE / "frozen_core"
DEST.mkdir(exist_ok=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
records = {}
for name in ("common.py", "model.py", "roles.py", "authority.py", "reader.py", "run.py", "client.py"):
    source, dest = CORE / name, DEST / name
    if dest.exists():
        assert dest.read_bytes() == source.read_bytes(), "Refuse snapshot drift: " + name
    else:
        shutil.copyfile(source, dest)
    records[name] = {"source": str(source), "sha256": sha(dest), "bytes": dest.stat().st_size}
crypto = HERE.parent / "crypto"
crypto_records = {name: sha(crypto / name) for name in ("src/main.rs", "Cargo.toml", "Cargo.lock", "params.json")}
pin = {"schema": "resident-host-runtime-source-pins-v1", "core": records,
       "crypto_source_sha256": crypto_records,
       "crypto_binary_source": str(crypto / "target/release/resident-crypto"),
       "crypto_binary_sha256": sha(crypto / "target/release/resident-crypto")}
path = HERE / "source_pins.json"
if path.exists():
    assert json.loads(path.read_text()) == pin, "Preserve frozen source pins"
else:
    path.write_text(json.dumps(pin, indent=2) + "\n")
print(json.dumps({"core_files": len(records), "crypto_binary_sha256": pin["crypto_binary_sha256"]}))

