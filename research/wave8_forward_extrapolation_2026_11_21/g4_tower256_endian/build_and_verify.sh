#!/usr/bin/env bash
# Isolated Lean 4.35.0 overlay + Golden Vector + Obend Patch verifier for Gate G4:
#   - /Users/ember/dev/minidregg/Theory/Tower256EndianBridge.lean
#   - golden_vectors.json
#   - obend_binary_tower256_le_wire.patch (read-only `git apply --check` against /Users/ember/dev/obend)
#
# Never runs `lake build` in /Users/ember/dev/minidregg or /Users/ember/dev/obend.
# Temporary overlay build artifacts live in mktemp -d and are cleaned automatically on exit.
set -euo pipefail

G4_DIR="$(cd "$(dirname "$0")" && pwd)"
MINIDREGG="/Users/ember/dev/minidregg"
OBEND="/Users/ember/dev/obend"
TOOLCHAIN_DIR="/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0"
LEAN_BIN="$TOOLCHAIN_DIR/bin/lean"
LAKE_BIN="$TOOLCHAIN_DIR/bin/lake"

BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/g4_tower256_overlay.XXXXXX")"
trap 'rm -rf "$BUILD_DIR"' EXIT

python3 - "$G4_DIR" "$MINIDREGG" "$OBEND" "$LEAN_BIN" "$LAKE_BIN" "$BUILD_DIR" <<'PY'
import json, os, re, subprocess, sys, time

g4_dir, minidregg, obend, lean_bin, lake_bin, build = sys.argv[1:7]
dep_cwd = os.path.join(build, "_dep_workdir")
os.makedirs(dep_cwd, exist_ok=True)
minidregg_lib = os.path.join(minidregg, ".lake", "build", "lib", "lean")
dynlib = os.path.join(minidregg, ".lake", "native", "libmini_kernels_lean.so")

sys.path.insert(0, os.path.join(minidregg, "scripts"))
from lean_imports import header_imports

ALLOWED_THEORY = {"Mathlib", "Lean", "Std", "Theory"}
target_rel = "Theory/Tower256EndianBridge.lean"
target_mod = "Theory.Tower256EndianBridge"
target_path = os.path.join(minidregg, target_rel)

if not os.path.exists(target_path):
    print(f"FAIL: missing {target_path}", file=sys.stderr)
    sys.exit(1)

with open(target_path, encoding="utf-8") as f:
    text = f.read()

line_count = len(text.splitlines())
if line_count >= 900:
    print(f"FAIL: {target_rel} has {line_count} lines (>= 900 limit)", file=sys.stderr)
    sys.exit(1)

for imp in header_imports(text):
    parts = imp.split(".")
    tgt = parts[1] if parts[0] == "Minidregg" and len(parts) > 1 else parts[0]
    if tgt not in ALLOWED_THEORY:
        print(f"FAIL: import-boundary violation in {target_rel}: import {imp} (Theory -> {tgt})", file=sys.stderr)
        sys.exit(1)

stripped = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
stripped = re.sub(r"--[^\n]*", "", stripped)
for pat, label in [
    (r"\bsorry\b", "sorry"),
    (r"^\s*axiom\b", "custom axiom"),
    (r"\bnative_decide\b", "native_decide"),
    (r"#guard\b(?!_msgs)", "#guard unit test"),
]:
    if re.search(pat, stripped, flags=re.M):
        print(f"FAIL: forbidden `{label}` found in {target_rel}", file=sys.stderr)
        sys.exit(1)

pins = len(re.findall(r"#guard_msgs[^\n]*#print\s+axioms", text))
if pins < 10:
    print(f"FAIL: expected >= 10 #guard_msgs-pinned #print axioms, got {pins}", file=sys.stderr)
    sys.exit(1)

print(f"OK: ATLAS & tier-import hygiene for {target_rel} ({line_count} lines < 900, 0 sorry, 0 axiom, 0 native_decide, {pins} #print axioms pins)")

# 1. Run minidregg import-boundary script
ib = subprocess.run(["bash", os.path.join(minidregg, "scripts", "check-import-boundary.sh")],
                    cwd=minidregg, capture_output=True, text=True)
if ib.returncode != 0:
    print(f"FAIL: scripts/check-import-boundary.sh failed:\n{ib.stdout}\n{ib.stderr}", file=sys.stderr)
    sys.exit(1)
print("OK: minidregg/scripts/check-import-boundary.sh passed")

# 2. Populate isolated overlay with Lean 4.35.0 .olean/.ilean/.ir symlinks from minidregg/.lake/build/lib/lean
EXPECTED_MAGIC = b"olean\x02\x014.35.0"
def is_435_olean(path):
    try:
        with open(path, "rb") as f:
            return f.read(len(EXPECTED_MAGIC)) == EXPECTED_MAGIC
    except OSError:
        return False

for root, _, files in os.walk(minidregg_lib):
    rel_dir = os.path.relpath(root, minidregg_lib)
    dst_dir = os.path.join(build, rel_dir) if rel_dir != "." else build
    os.makedirs(dst_dir, exist_ok=True)
    valid_base_fns = {
        fn[:-6] for fn in files
        if fn.endswith(".olean") and is_435_olean(os.path.join(root, fn))
    }
    for fn in files:
        if not (".olean" in fn or fn.endswith(".ilean") or fn.endswith(".ir")):
            continue
        base_fn = fn.split(".")[0]
        if base_fn not in valid_base_fns:
            continue
        stem = os.path.join(rel_dir, base_fn) if rel_dir != "." else base_fn
        if stem == target_rel[:-5]:
            continue
        dst = os.path.join(dst_dir, fn)
        if not os.path.exists(dst):
            os.symlink(os.path.join(root, fn), dst)

pkg_path = subprocess.check_output(
    [lake_bin, "--dir", minidregg, "env", "printenv", "LEAN_PATH"],
    text=True
).strip()
parts = [p for p in pkg_path.split(":") if not p.startswith(minidregg)]
env = os.environ.copy()
env["LEAN_PATH"] = build + ":" + ":".join(parts)

lean_opts = []
if os.path.exists(dynlib):
    lean_opts.append(f"--load-dynlib={dynlib}")
lean_opts.extend([
    "-Dbackward.privateInPublic=true",
    "-Dbackward.privateInPublic.warn=false",
    "-Dbackward.proofsInPublic=true",
    "-Dcompiler.relaxedMetaCheck=true",
])

out_olean = os.path.join(build, "Theory", "Tower256EndianBridge.olean")
os.makedirs(os.path.dirname(out_olean), exist_ok=True)
t0 = time.time()
res = subprocess.run(
    [lean_bin, *lean_opts, "-R", minidregg, "-o", out_olean, target_path],
    cwd=minidregg, env=env, capture_output=True, text=True
)
dt = time.time() - t0
print(f"  [TARGET   {dt:5.2f}s] {target_mod} -> rc={res.returncode}")
if res.stdout.strip():
    print(res.stdout.rstrip())
if res.stderr.strip():
    print(res.stderr.rstrip())
if res.returncode != 0:
    sys.exit(1)
if "warning:" in res.stdout or "warning:" in res.stderr:
    print(f"FAIL: compiler warning emitted while building {target_mod}", file=sys.stderr)
    sys.exit(1)
print(f"OK: Lean 4.35.0 kernel-verified {target_mod} with 0 warnings in {dt:.2f}s")

# 3. Independently verify golden_vectors.json (including all buggy-transform falsifiers)
with open(os.path.join(g4_dir, "golden_vectors.json"), encoding="utf-8") as f:
    gv = json.load(f)

def mul_gen(k, v):
    if k == 0:
        return v & 1
    w = 1 << (k - 1)
    mask = (1 << w) - 1
    lo, hi = v & mask, (v >> w) & mask
    return hi | ((lo ^ mul_gen(k - 1, hi)) << w)

def mul_fp(k, a, b):
    if k == 0:
        return a & b & 1
    w = 1 << (k - 1)
    mask = (1 << w) - 1
    a0, a1 = a & mask, (a >> w) & mask
    b0, b1 = b & mask, (b >> w) & mask
    p0 = mul_fp(k - 1, a0, b0)
    p1 = mul_fp(k - 1, a1, b1)
    m = mul_fp(k - 1, a0 ^ a1, b0 ^ b1) ^ p0 ^ p1
    hi = m ^ (p1 if k - 1 == 0 else mul_gen(k - 1, p1))
    return (p0 ^ p1) | (hi << w)

def inv_fp(k, a):
    if k == 0:
        return a & 1
    w = 1 << (k - 1)
    mask = (1 << w) - 1
    a0, a1 = a & mask, (a >> w) & mask
    a0a1 = mul_fp(k - 1, a0, a1)
    xa0a1 = a0a1 if k - 1 == 0 else mul_gen(k - 1, a0a1)
    norm = mul_fp(k - 1, a0, a0) ^ xa0a1 ^ mul_fp(k - 1, a1, a1)
    ni = inv_fp(k - 1, norm)
    xa1 = a1 if k - 1 == 0 else mul_gen(k - 1, a1)
    return mul_fp(k - 1, a0 ^ xa1, ni) | (mul_fp(k - 1, a1, ni) << w)

by_name = {}
for el in gv["elements"]:
    limbs = [int(x, 16) for x in el["limbs_u64_le"]]
    val = limbs[0] | (limbs[1] << 64) | (limbs[2] << 128) | (limbs[3] << 192)
    le = val.to_bytes(32, "little")
    be = val.to_bytes(32, "big")
    assert le.hex() == el["le_bytes_hex"], f"LE mismatch on {el['name']}"
    assert be.hex() == el["be_bytes_hex"], f"BE mismatch on {el['name']}"
    assert be == le[::-1], f"BE != reverse(LE) on {el['name']}"
    if not el["palindromic"]:
        assert be != le, f"Expected non-palindromic on {el['name']}"
    if "square_be_hex" in el:
        assert mul_fp(8, val, val).to_bytes(32, "big").hex() == el["square_be_hex"]
    if "inv_be_hex" in el:
        iv = inv_fp(8, val)
        assert iv.to_bytes(32, "big").hex() == el["inv_be_hex"]
        assert mul_fp(8, val, iv) == 1
    if "pow256_be_hex" in el:
        p = val
        for _ in range(8):
            p = mul_fp(8, p, p)
        assert p.to_bytes(32, "big").hex() == el["pow256_be_hex"]
    by_name[el["name"]] = (val, le, be)

a_val, a_le, a_be = by_name["vec_rust_smoke_a"]
b_val, b_le, b_be = by_name["vec_rust_smoke_b"]
assert (a_val ^ b_val).to_bytes(32, "big").hex() == gv["binary_ops"]["a_plus_b_be_hex"]
assert (a_val ^ b_val).to_bytes(32, "little").hex() == gv["binary_ops"]["a_plus_b_le_hex"]
assert mul_fp(8, a_val, b_val).to_bytes(32, "big").hex() == gv["binary_ops"]["a_mul_b_be_hex"]
assert mul_fp(8, a_val, b_val).to_bytes(32, "little").hex() == gv["binary_ops"]["a_mul_b_le_hex"]

# Buggy-transform falsifiers on asymmetric vec_rust_smoke_a
assert a_be[24:32] + a_be[16:24] + a_be[8:16] + a_be[0:8] != a_le
assert a_be[0:8][::-1] + a_be[8:16][::-1] + a_be[16:24][::-1] + a_be[24:32][::-1] != a_le
assert a_be[16:32] + a_be[0:16] != a_le
assert a_be[0:16][::-1] + a_be[16:32][::-1] != a_le
bitrev = bytes(int(f"{b:08b}"[::-1], 2) for b in a_be[::-1])
assert bitrev != a_le
print(f"OK: verified {len(gv['elements'])} golden vectors + binary ops + 5 buggy-transform falsifiers")

# 4. Read-only patch check against /Users/ember/dev/obend
patch_path = os.path.join(g4_dir, "obend_binary_tower256_le_wire.patch")
pc = subprocess.run(
    ["git", "-C", obend, "apply", "--check", patch_path],
    capture_output=True, text=True
)
if pc.returncode != 0:
    print(f"FAIL: git apply --check failed on {patch_path}:\n{pc.stderr}", file=sys.stderr)
    sys.exit(1)
print("OK: obend_binary_tower256_le_wire.patch applies cleanly to /Users/ember/dev/obend (read-only check)")
PY
