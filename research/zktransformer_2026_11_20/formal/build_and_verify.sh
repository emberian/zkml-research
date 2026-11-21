#!/usr/bin/env bash
# Build and kernel-verify Theory/ZkmlEinsum.lean and Assurance/ZkmlEinSumcheck.lean
# against /Users/ember/dev/minidregg (strictly read-only; all .olean artifacts go into ./build/).
set -euo pipefail

FORMAL_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
LAKE_BIN="$TOOLCHAIN_DIR/bin/lake"

python3 - "$FORMAL_DIR" "$MINIDREGG" "$LEAN_BIN" "$LAKE_BIN" <<'PY'
import os, re, subprocess, sys, time

formal, minidregg, lean_bin, lake_bin = sys.argv[1:5]
build = os.path.join(formal, "build")

pkg_path = subprocess.check_output(
    [lake_bin, "--dir", minidregg, "env", "printenv", "LEAN_PATH"],
    text=True
).strip()
parts = [p for p in pkg_path.split(":") if not p.startswith(minidregg)]
lean_path = build + ":" + ":".join(parts)
env = os.environ.copy()
env["LEAN_PATH"] = lean_path

def src_and_root(mod):
    local = os.path.join(formal, *mod.split(".")) + ".lean"
    if os.path.exists(local):
        return local, formal
    p = os.path.join(minidregg, *mod.split(".")) + ".lean"
    if os.path.exists(p):
        return p, minidregg
    return None, None

def get_imports(mod):
    p, _ = src_and_root(mod)
    if not p:
        return []
    sys.path.insert(0, os.path.join(minidregg, "scripts"))
    from lean_imports import header_imports
    with open(p, encoding="utf-8") as f:
        text = f.read()
    imps = []
    for imp in header_imports(text):
        if imp.split(".")[0] in {"Theory", "Selvage", "Assurance", "Compiler", "Kernel", "Pred", "Effects", "Loom"}:
            imps.append(imp)
    return imps

order, vis = [], set()
def dfs(mod):
    if mod in vis:
        return
    vis.add(mod)
    for imp in get_imports(mod):
        dfs(imp)
    order.append(mod)

dfs("Theory.ZkmlEinsum")
dfs("Assurance.ZkmlEinSumcheck")

t0 = time.time()
for mod in order:
    src, rdir = src_and_root(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    is_local = (rdir == formal)
    if not is_local and os.path.exists(out) and os.path.getmtime(out) >= os.path.getmtime(src):
        continue
    t1 = time.time()
    lean_opts = [
        "-Dbackward.privateInPublic=true",
        "-Dbackward.privateInPublic.warn=false",
        "-Dbackward.proofsInPublic=true",
        "-Dcompiler.relaxedMetaCheck=true",
    ]
    res = subprocess.run([lean_bin, *lean_opts, "-R", rdir, "-o", out, src], env=env, capture_output=True, text=True)
    dt = time.time() - t1
    tag = "LOCAL" if is_local else "CACHE"
    print(f"  [{tag} {dt:5.2f}s] {mod} -> rc={res.returncode}", flush=True)
    if res.stdout.strip():
        print(res.stdout.rstrip(), flush=True)
    if res.stderr.strip():
        print(res.stderr.rstrip(), flush=True)
    if res.returncode != 0:
        sys.exit(res.returncode)
print(f"Verified cleanly in {time.time() - t0:.2f}s")
PY
