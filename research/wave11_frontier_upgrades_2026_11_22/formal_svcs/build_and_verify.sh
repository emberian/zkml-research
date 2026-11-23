#!/usr/bin/env bash
# Compile the lane in a private overlay. Publish the Lean fixture only after all kernel checks.
set -euo pipefail
lane_dir="$(cd "$(dirname "$0")" && pwd)"
mini="/Users/ember/dev/minidregg"
toolchain="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin"
lean_only=0
for arg in "$@"; do
  case "$arg" in
    --lean-only) lean_only=1 ;;
    --rebuild-lean) ;; # The target is always rebuilt to exercise JSON emission.
    *) echo "Unknown argument $arg" >&2; exit 2 ;;
  esac
done
export PYTHONDONTWRITEBYTECODE=1
python3 - "$lane_dir" "$mini" "$toolchain" <<'PYTHON'
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

lane, mini, tools = map(Path, sys.argv[1:])
sys.path.insert(0, str(mini / "scripts"))
from lean_imports import header_imports

target = "Compiler.SvcsCredibleCompiler"
fixture = Path("prover/testdata/svcs_compiler_conformance.json")
source = (mini / "Compiler/SvcsCredibleCompiler.lean").read_text()
def strip_lean_comments_and_strings(src: str) -> str:
    out = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        if in_str:
            if src[i] == "\\" and i + 1 < n:
                i += 2
                continue
            if src[i] == '"':
                in_str = False
            i += 1
        elif depth > 0:
            if src[i:i+2] == "/-":
                depth += 1
                i += 2
            elif src[i:i+2] == "-/":
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        else:
            if src[i:i+2] == "/-":
                depth = 1
                i += 2
            elif src[i:i+2] == "--":
                while i < n and src[i] != "\n":
                    i += 1
            elif src[i] == '"':
                in_str = True
                out.append('""')
                i += 1
            else:
                out.append(src[i])
                i += 1
    return "".join(out)

lines = len(source.splitlines())
if lines >= 950:
    sys.exit(f"Lean file has {lines} lines (limit 949)")
allowed = set("Mathlib Lean Std Init Theory Effects Pred Kernel Selvage Assurance Compiler".split())
for dep in header_imports(source):
    if dep.removeprefix("Minidregg.").split(".")[0] not in allowed:
        sys.exit(f"Unauthorized import {dep}")
code = strip_lean_comments_and_strings(source)
if re.search(r"\b(sorry|sorryAx|axiom|native_decide)\b", code):
    sys.exit("Forbidden Lean declaration or proof token")
audits = re.findall(r"#guard_msgs[^\n]*\bin #print axioms (\w+)", code)
if len(audits) != len(re.findall(r"#print\s+axioms", code)) or not {
    "credible_cert_completeness", "credible_cert_knowledge_soundness", "credible_emit_accepts",
    "svcs_rbr_soundness_composed", "teeth_degree_inflating_fusion_rejected",
    "teeth_missing_pin_rejected", "teeth_unguarded_dce_rejected",
}.issubset(audits):
    sys.exit("Missing kernel axiom audit")
print(f"{lines} lines, {len(audits)} pinned axiom reports, target tier check passed", flush=True)
subprocess.run(["bash", mini / "scripts/check-import-boundary.sh"], cwd=mini, check=True)
version = subprocess.check_output([tools / "lean", "--version"], text=True).strip()
if not re.search(r"version 4\.35\.0\b", version):
    sys.exit(f"Wrong toolchain: {version}")
print(version, flush=True)
paths = subprocess.check_output([tools / "lake", "--dir", mini, "env", "printenv", "LEAN_PATH"],
                                text=True).strip().split(os.pathsep)
cache = mini / ".lake/build/lib/lean"
external = [p for p in paths if Path(p).resolve() != cache]
magic = b"olean\x02\x014.35.0"
dynlib = mini / ".lake/native/libmini_kernels_lean.so"
opts = [f"--load-dynlib={dynlib}"] if dynlib.exists() else []
opts += ["-DwarningAsError=true"]
with tempfile.TemporaryDirectory(prefix="w11-svcs-") as tmp:
    work = Path(tmp)
    env = {**os.environ, "LEAN_PATH": os.pathsep.join([str(work), *external])}
    built = {}

    def compile_module(mod):
        rel = Path(*mod.split("."))
        src = mini / rel.with_suffix(".lean")
        if not src.exists():
            return 0
        if mod in built:
            return built[mod]
        newest = max([src.stat().st_mtime_ns] + [
            compile_module(dep) for dep in header_imports(src.read_text())])
        out = work / rel.with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        for root in (lane / "build", cache):
            warm = root / rel.with_suffix(".olean")
            if mod == target or not warm.exists() or warm.stat().st_mtime_ns < newest:
                continue
            with warm.open("rb") as f:
                if f.read(len(magic)) != magic:
                    continue
            for sibling in warm.parent.glob(rel.name + ".*"):
                if sibling.is_file():
                    (out.parent / sibling.name).symlink_to(sibling.resolve())
            built[mod] = warm.stat().st_mtime_ns
            return built[mod]
        subprocess.run([tools / "lean", *opts, "-R", mini, "-o", out, src],
                       cwd=work, env=env, check=True)
        built[mod] = out.stat().st_mtime_ns
        return built[mod]

    compile_module(target)
    raw = (work / fixture).read_bytes()
    data = json.loads(raw)
    checks = data.get("lean_self_checks", {})
    expected = {"evm_ok", "einsum_ok", "dfa_ok", "degree_inflating_fusion_rejected",
                "missing_pin_rejected", "unguarded_dce_rejected"}
    if (data["schema"] != "minidregg.svcs_compiler_conformance.v1" or set(checks) != expected
        or not all(v is True for v in checks.values()) or len(data["bundles"]) != 3
        or not all(b["lean_check"] is True for b in data["bundles"])):
        sys.exit(f"Conformance checks failed: {checks}")
    dest = mini / fixture
    with tempfile.NamedTemporaryFile(dir=dest.parent, delete=False) as staged:
        staged.write(raw)
    os.chmod(staged.name, 0o644)
    os.replace(staged.name, dest)
    print(f"Kernel verified {target}; emitted {len(raw)} bytes and {len(checks)} passing checks.")
PYTHON

if [[ "$lean_only" == 1 ]]; then exit 0; fi
export CARGO_TARGET_DIR=/tmp/target-w11-svcs
export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }-Dwarnings"
cargo test --locked --release --manifest-path "$mini/prover/Cargo.toml" --lib svcs_smallval_engine
cargo test --locked --release --manifest-path "$mini/prover/Cargo.toml" --test svcs_credible_compiler \
  -- --include-ignored --nocapture --test-threads=1
