#!/usr/bin/env bash
# Build and kernel-verify:
#   - Selvage/ContentCertificate.lean
#   - Assurance/CertificateComposition.lean
# against /Users/ember/dev/minidregg (all .olean/.ilean outputs isolated inside ./build/),
# plus verify ATLAS forbidden-token laws, 0 compiler warnings, #print axioms pins, and
# import-boundary rules (both on the new modules and across minidregg).
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
minidregg_lib = os.path.join(minidregg, ".lake", "build", "lib", "lean")
dynlib = os.path.join(minidregg, ".lake", "native", "libmini_kernels_lean.so")

target_mods = [
    ("Selvage", "Selvage/ContentCertificate.lean"),
    ("Assurance", "Assurance/CertificateComposition.lean"),
]

# 1. Verify forbidden-token hygiene (ATLAS laws)
for _, rel in target_mods:
    p = os.path.join(minidregg, rel)
    if not os.path.exists(p):
        print(f"FAIL: missing module {p}", file=sys.stderr)
        sys.exit(1)
    with open(p, encoding="utf-8") as f:
        text = f.read()
    stripped = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
    stripped = re.sub(r"--[^\n]*", "", stripped)
    for pat, label in [
        (r"\bsorry\b", "sorry"),
        (r"^\s*axiom\b", "custom axiom"),
        (r"\bnative_decide\b", "native_decide"),
        (r"#guard\b(?!_msgs)", "#guard unit test"),
    ]:
        if re.search(pat, stripped, flags=re.M):
            print(f"FAIL: forbidden `{label}` found in {rel}", file=sys.stderr)
            sys.exit(1)
    pin_count = len(re.findall(r"#guard_msgs[^\n]*#print\s+axioms", text))
    if pin_count == 0:
        print(f"FAIL: missing #guard_msgs-pinned #print axioms in {rel}", file=sys.stderr)
        sys.exit(1)
    print(f"OK: ATLAS syntax check for {rel} (0 sorry, 0 axiom, 0 native_decide, 0 #guard; {pin_count} #print axioms pins)")

# 2. Verify check-import-boundary.sh tier rules on our 2 new modules
sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports

ALLOWED = {
    "Theory":    {"Mathlib", "Lean", "Std", "Theory"},
    "Selvage":   {"Mathlib", "Theory", "Selvage"},
    "Effects":   {"Mathlib", "Lean", "Theory", "Effects"},
    "Pred":      {"Mathlib", "Theory", "Pred"},
    "Kernel":    {"Mathlib", "Lean", "Std", "Init", "Theory", "Effects", "Pred", "Compiler", "Kernel"},
    "Compiler":  {"Mathlib", "Lean", "Std", "Init", "Theory", "Effects", "Pred", "Kernel", "Selvage", "Assurance", "Compiler"},
    "Assurance": {"Mathlib", "Theory", "Pred", "Kernel", "Compiler", "Selvage", "Assurance"},
    "Host":      {"Mathlib", "Lean", "Std", "Theory", "Pred", "Kernel", "Compiler", "Host"},
}
bad_imports = []
for lib, rel in target_mods:
    p = os.path.join(minidregg, rel)
    with open(p, encoding="utf-8") as f:
        text = f.read()
    for imp in header_imports(text):
        parts = imp.split(".")
        tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
        if tgt not in ALLOWED[lib]:
            bad_imports.append(f"  {rel}: import {imp}   [illegal edge {lib} -> {tgt}]")
if bad_imports:
    print("FAIL: import-boundary violation:", file=sys.stderr)
    print("\n".join(bad_imports), file=sys.stderr)
    sys.exit(1)
print("OK: import-boundary check passed for Selvage/ContentCertificate.lean and Assurance/CertificateComposition.lean")

# 3. Overlay symlink prebuilt minidregg .olean/.ilean artifacts into ./build/
#    Filter out any stale .olean built under an older Lean toolchain by matching the 24-byte header
#    against a fresh v4.35.0 .olean (Selvage/Commitment.olean).
ref_olean = os.path.join(minidregg_lib, "Selvage", "Commitment.olean")
ref_hdr = open(ref_olean, "rb").read(24) if os.path.exists(ref_olean) else None

target_rel_stems = {rel[:-5] for _, rel in target_mods}
target_mod_names = {rel[:-5].replace("/", ".") for _, rel in target_mods}
os.makedirs(build, exist_ok=True)
if os.path.isdir(minidregg_lib):
    for root, _, files in os.walk(minidregg_lib):
        rel_dir = os.path.relpath(root, minidregg_lib)
        dst_dir = os.path.join(build, rel_dir) if rel_dir != "." else build
        os.makedirs(dst_dir, exist_ok=True)
        for fn in files:
            if not (".olean" in fn or fn.endswith(".ilean") or fn.endswith(".ir")):
                continue
            base_fn = fn.split(".")[0]
            stem = os.path.join(rel_dir, base_fn) if rel_dir != "." else base_fn
            if stem in target_rel_stems:
                continue
            olean_peer = os.path.join(root, base_fn + ".olean")
            if ref_hdr and os.path.exists(olean_peer):
                if open(olean_peer, "rb").read(24) != ref_hdr:
                    stale_dst = os.path.join(dst_dir, fn)
                    if os.path.islink(stale_dst):
                        os.unlink(stale_dst)
                    continue
            dst = os.path.join(dst_dir, fn)
            if not os.path.exists(dst):
                os.symlink(os.path.join(root, fn), dst)

pkg_path = subprocess.check_output(
    [lake_bin, "--dir", minidregg, "env", "printenv", "LEAN_PATH"],
    text=True
).strip()
parts = [p for p in pkg_path.split(":") if not p.startswith(minidregg)]
lean_path = build + ":" + ":".join(parts)
env = os.environ.copy()
env["LEAN_PATH"] = lean_path

def src_and_root(mod):
    p = os.path.join(minidregg, *mod.split(".")) + ".lean"
    if os.path.exists(p):
        return p, minidregg
    return None, None

def get_imports(mod):
    p, _ = src_and_root(mod)
    if not p:
        return []
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
    src, _ = src_and_root(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    if mod not in target_mod_names and os.path.exists(out) and os.path.getmtime(out) >= os.path.getmtime(src):
        return
    for imp in get_imports(mod):
        dfs(imp)
    order.append(mod)

for mod in ["Selvage.ContentCertificate", "Assurance.CertificateComposition"]:
    dfs(mod)

t0 = time.time()
lean_opts = []
if os.path.exists(dynlib):
    lean_opts.append(f"--load-dynlib={dynlib}")
lean_opts.extend([
    "-Dbackward.privateInPublic=true",
    "-Dbackward.privateInPublic.warn=false",
    "-Dbackward.proofsInPublic=true",
    "-Dcompiler.relaxedMetaCheck=true",
])
failed = False
for mod in order:
    src, rdir = src_and_root(mod)
    out = os.path.join(build, *mod.split(".")) + ".olean"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    is_target = mod in target_mod_names
    if not is_target and os.path.exists(out) and os.path.getmtime(out) >= os.path.getmtime(src):
        continue
    if is_target and os.path.islink(out):
        os.unlink(out)
    t1 = time.time()
    res = subprocess.run([lean_bin, *lean_opts, "-R", rdir, "-o", out, src], env=env, capture_output=True, text=True)
    dt = time.time() - t1
    tag = "TARGET" if is_target else "DEP"
    print(f"  [{tag:6s} {dt:5.2f}s] {mod} -> rc={res.returncode}", flush=True)
    if res.stdout.strip():
        print(res.stdout.rstrip(), flush=True)
    if res.stderr.strip():
        print(res.stderr.rstrip(), flush=True)
    if res.returncode != 0:
        failed = True
    if is_target and ("warning:" in res.stdout or "warning:" in res.stderr):
        print(f"FAIL: compiler warning emitted while building {mod}", file=sys.stderr)
        failed = True
if failed:
    sys.exit(1)
print(f"OK: Kernel-verified all target modules with 0 warnings in {time.time() - t0:.2f}s")
PY

bash /Users/ember/dev/minidregg/scripts/check-import-boundary.sh
