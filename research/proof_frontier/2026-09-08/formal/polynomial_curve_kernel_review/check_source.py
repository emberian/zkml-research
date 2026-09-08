"""Read-only frozen-source/provenance audit; no Lean invocation or patch application."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / "polynomial_curve_kernel"
PREDECESSOR = HERE.parent / "polynomial_kernel/all_pins_successor/PolynomialMatrixKernel.lean"
ORIGINAL = HERE.parent / "polynomial_kernel/PolynomialMatrixKernel.lean"
SOURCE_PIN = "f510b6cc0c648a3583e3eefa49e283b2186add24d2e4df71f3afeb9b06a3fa91"
MANIFEST_PIN = "233f869cc51584f2be295dbe2c7076734a4bc10e3cdcee16a596ecc813f401e0"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(text):
    """Preserve offsets and newlines; this module has no noncomment string literals."""
    out = list(text)
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out[i:i + 2] = "  "
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out[i:i + 2] = "  "
            i += 2
        elif depth:
            if text[i] != "\n":
                out[i] = " "
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
        else:
            i += 1
    assert depth == 0
    return "".join(out)


def norm(text):
    return " ".join(text.split())


def declarations(raw):
    code = strip_comments(raw)
    assert '"' not in code, "Extend lexer before accepting string literals"
    commands = list(re.finditer(r"^(?:noncomputable )?(namespace|end|theorem|def|open|variable|import|#\w+)\b([^\n]*)", code, re.M))
    stack = []
    found = {}
    for index, command in enumerate(commands):
        kind = command[1]
        if kind == "namespace":
            stack.append(command[2].strip())
        elif kind == "end":
            assert stack.pop() == command[2].strip()
        elif kind in ("theorem", "def"):
            start = command.start()
            end = commands[index + 1].start() if index + 1 < len(commands) else len(code)
            chunk = code[start:end].strip()
            header, body = chunk.split(":=", 1)
            name = re.match(r"(?:noncomputable )?(?:theorem|def)\s+(\S+)", header)[1]
            qualified = ".".join(stack + [name])
            assert qualified not in found
            found[qualified] = {"kind": kind, "header": norm(header), "body": norm(body),
                                "line": raw.count("\n", 0, start) + 1}
    assert not stack
    return found, code


def guards(raw):
    pattern = r"/-- info: '([^']+)' depends on axioms: \[(.*?)\] -/\s*#guard_msgs in\s*#print axioms ([^\s]+)"
    found = {}
    for m in re.finditer(pattern, raw, re.S):
        assert m[1] == m[3]
        assert m[1] not in found
        axioms = [a.strip() for a in m[2].split(",")]
        assert axioms == ["propext", "Classical.choice", "Quot.sound"]
        found[m[1]] = m[0]
    assert len(found) == len(re.findall(r"^#guard_msgs\b", raw, re.M))
    assert len(found) == len(re.findall(r"^#print axioms\b", raw, re.M))
    return found


def git_read(cwd, *args, expected=0):
    command = ["git", "-C", str(cwd), *args]
    p = subprocess.run(command, text=True, capture_output=True)
    record = {"command": command, "exit_code": p.returncode, "stdout": p.stdout, "stderr": p.stderr}
    assert p.returncode == expected, record
    return record


assert sha(AUTHOR / "manifest.json") == MANIFEST_PIN
manifest = json.loads((AUTHOR / "manifest.json").read_text())
files = []
for item in manifest["files"]:
    path = AUTHOR / item["path"]
    assert path.resolve().is_relative_to(AUTHOR.resolve())
    actual = {"path": item["path"], "sha256": sha(path), "bytes": path.stat().st_size}
    assert actual == item, (actual, item)
    files.append(actual)
assert sha(AUTHOR / "PolynomialMatrixKernel.lean") == SOURCE_PIN
provenance = json.loads((AUTHOR / "provenance.json").read_text())
assert sha(PREDECESSOR) == provenance["predecessor_16_pin_source_sha256"]
assert sha(ORIGINAL) == provenance["original_8_pin_source_sha256"]
current = (AUTHOR / "PolynomialMatrixKernel.lean").read_text()
old = PREDECESSOR.read_text()
newdecl, code = declarations(current)
olddecl, oldcode = declarations(old)
newguards, oldguards = guards(current), guards(old)
theorems = {name for name, d in newdecl.items() if d["kind"] == "theorem"}
oldtheorems = {name for name, d in olddecl.items() if d["kind"] == "theorem"}
assert len(theorems) == len(newguards) == 26
assert len(oldtheorems) == len(oldguards) == 16
assert set(newguards) == theorems
assert set(oldguards) == oldtheorems
assert oldtheorems <= theorems
preserved = []
changed_bodies = []
for name, d in olddecl.items():
    assert d["header"] == newdecl[name]["header"], name
    if d["body"] != newdecl[name]["body"]:
        changed_bodies.append(name)
    if d["kind"] == "theorem":
        assert oldguards[name] == newguards[name], name
        preserved.append(name)
assert sorted(changed_bodies) == sorted([
    "PolynomialMatrixKernel.Source.RS_natDegree_det_le_of_entry_natDegree_le_one",
    "PolynomialMatrixKernel.Source.RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one",
]), changed_bodies
assert re.findall(r"^variable[^\n]*", code, re.M) == re.findall(r"^variable[^\n]*", oldcode, re.M)
forbidden = re.findall(r"\b(?:axiom|sorry|admit|unsafe|opaque|partial|macro|elab|syntax|implemented_by|extern|run_tac|run_elab|set_option)\b", code)
assert not forbidden, forbidden
imports = re.findall(r"^import\s+(\S+)", code, re.M)
assert len(imports) == 6 and all(i.startswith("Mathlib.") for i in imports)
assert imports == re.findall(r"^import\s+(\S+)", oldcode, re.M)

# Independently reconstruct only the complete new-file patch payloads in memory.
patch = (AUTHOR / "polynomial-curve-kernel.patch").read_text()
chunks = re.split(r"(?=^diff --git )", patch, flags=re.M)
payloads = {}
for chunk in chunks:
    if not chunk:
        continue
    lines = chunk.splitlines(keepends=True)
    target = re.fullmatch(r"diff --git a/(\S+) b/(\S+)\n", lines[0])
    assert target and target[1] == target[2]
    assert lines[1] == "new file mode 100644\n"
    assert lines[3] == "--- /dev/null\n" and lines[4] == f"+++ b/{target[1]}\n"
    hunk = re.fullmatch(r"@@ -0,0 \+1,(\d+) @@\n", lines[5])
    no_final_newline = lines[-1] == "\\ No newline at end of file\n"
    if no_final_newline:
        lines.pop()
    assert hunk and all(line.startswith("+") for line in lines[6:])
    assert len(lines[6:]) == int(hunk[1])
    payload = "".join(line[1:] for line in lines[6:]).encode()
    if no_final_newline:
        assert payload.endswith(b"\n")
        payload = payload[:-1]
    payloads[target[1]] = payload
assert set(payloads) == {"Theory/PolynomialMatrixKernel.lean", "LICENSES/ArkLib-Apache-2.0.txt"}
for target, data in payloads.items():
    assert data == (AUTHOR / Path(target).name).read_bytes()

compile_record = json.loads((AUTHOR / "lean_final.json").read_text())
isolate = Path(compile_record["cwd"])
assert compile_record["exit_code"] == 0
assert compile_record["stdout"] == compile_record["stderr"] == ""
assert compile_record["source_sha256"] == SOURCE_PIN and compile_record["source_unchanged"]
assert sha(isolate / "Theory/PolynomialMatrixKernel.lean") == SOURCE_PIN
olean = Path(compile_record["command"][4])
assert sha(olean) == compile_record["olean_sha256"]
assert (AUTHOR / "lean-final.log").read_bytes() == b""
assert manifest["modules"][0]["check"] == compile_record
assert (isolate / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.30.0"
git_records = [git_read(isolate, "rev-parse", "HEAD")]
assert git_records[-1]["stdout"].strip() == provenance["minidregg_base"]
git_records.append(git_read(isolate / ".lake/packages/mathlib", "rev-parse", "HEAD"))
assert git_records[-1]["stdout"].strip() == provenance["mathlib_commit"]
arklib_path = Path(provenance["arklib_source_path"])
assert sha(arklib_path) == provenance["arklib_source_sha256"]
for target in payloads:
    record = git_read(isolate, "ls-tree", "--name-only", provenance["minidregg_base"], "--", target)
    assert record["stdout"] == ""
    git_records.append(record)
retained_patch = json.loads((AUTHOR / "patch_and_import_checks.json").read_text())
assert all(r["exit_code"] == 0 for r in retained_patch["patch_checks"])
assert retained_patch["exact_applied_bytes_match"] and retained_patch["import_boundary_exit_code"] == 0
assert retained_patch["patch_sha256"] == sha(AUTHOR / "polynomial-curve-kernel.patch")
result = {
    "status": "PASS", "source_sha256": SOURCE_PIN, "author_manifest_sha256": MANIFEST_PIN,
    "author_files_checked": files, "independent_lean_invocations": 0,
    "declarations": [{"name": name, "line": d["line"], "kind": d["kind"], "header": d["header"]}
                     for name, d in newdecl.items()],
    "guarded_theorems": sorted(theorems), "old_theorems_preserved": sorted(preserved),
    "old_guard_bytes_equal": True, "old_definitions_and_binders_equal": True,
    "only_changed_old_proof_bodies": changed_bodies, "standard_guard_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "forbidden_tokens_in_comment_stripped_module": forbidden, "direct_imports": imports,
    "patch_payloads": [{"path": p, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
                       for p, data in payloads.items()],
    "retained_compile": compile_record,
    "current_isolate_source_and_olean_match_retained_record": True,
    "retained_patch_and_import_checks": retained_patch,
    "independent_read_only_git_commands": git_records,
    "source_queries": {"web": 0, "scry_sql": 0, "scry_schema": 0, "kagi": 0, "eprint_network": 0},
}
(HERE / "source_check.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"status": "PASS", "files": len(files), "theorems": len(theorems),
                  "old_heads_and_guards": len(preserved), "patch_targets": len(payloads), "lean_invocations": 0}))
