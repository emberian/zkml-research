#!/usr/bin/env python3
"""Package an owned proposed patch; inspect companion roots without changing them."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FORMAL = ROOT / "formal/he_closure_costs"
COMP = Path("/Users/ember/dev/minidregg")
OVERLAY = FORMAL / "build/package_overlay"
OVERLAY.mkdir(parents=True, exist_ok=True)
modules = ["Theory/IntegerWindowNoise", "Theory/CiphertextWindowNoise",
           "Assurance/ResidentBfvWindowNoise", "Assurance/ResidentBfvWindowPhase"]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
record = dict(modules=[], dependencies=[], checks=[], scope="proposed algebraic modules, not Rust refinement or companion umbrella build")
patch = []
for module in modules:
    source = FORMAL / (module + ".lean")
    assert not (COMP / (module + ".lean")).exists(), module
    text = source.read_text()
    assert not re.search(r"\b(sorry|axiom)\b", re.sub(r"/-[\s\S]*?-/|--[^\n]*", "", text)), source
    theorems = re.findall(r"^theorem (\w+)", text, re.M)
    pins = re.findall(r"#guard_msgs in\n#print axioms (\S+)", text)
    assert len(theorems) == len(pins), (source, theorems, pins)
    logs = sorted(HERE.glob(f"lean_{source.stem}_*.json"))
    latest = json.loads(logs[-1].read_text())
    assert latest["exit_code"] == 0 and latest["source_sha256"] == sha(source), source
    assert not latest["stdout"].strip() and not latest["stderr"].strip(), source
    record["modules"].append(dict(module=module, source_sha256=sha(source),
                                  successful_check=str(logs[-1].relative_to(ROOT)),
                                  theorem_count=len(theorems), pins=pins))
    patch.extend(difflib.unified_diff([], text.splitlines(keepends=True),
                                     fromfile="/dev/null", tofile="b/" + module + ".lean"))
    target = OVERLAY / (module + ".lean")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(text)
for umbrella, additions in [("Theory.lean", modules[:2]), ("Assurance.lean", modules[2:])]:
    original = (COMP / umbrella).read_text()
    amended = original + "\n" + "\n".join("import " + x.replace("/", ".") for x in additions) + "\n"
    patch.extend(difflib.unified_diff(original.splitlines(keepends=True), amended.splitlines(keepends=True),
                                     fromfile="a/" + umbrella, tofile="b/" + umbrella))
    (OVERLAY / umbrella).write_text(amended)
    record["dependencies"].append(dict(path=str(COMP / umbrella), sha256=sha(COMP / umbrella)))
patchfile = HERE / "proposed_minidregg.patch"
patchfile.write_text("".join(patch))
# Execute the exact companion import-boundary instrument in the isolated overlay.
script = COMP / "scripts/check-import-boundary.sh"
(OVERLAY / "scripts").mkdir(exist_ok=True)
shutil.copyfile(script, OVERLAY / "scripts/check-import-boundary.sh")
record["dependencies"].append(dict(path=str(script), sha256=sha(script)))
(OVERLAY / "Selvage.lean").write_text("-- No proposed Selvage changes.\n")
command = ["bash", str(OVERLAY / "scripts/check-import-boundary.sh")]
run = subprocess.run(command, cwd=OVERLAY, text=True, capture_output=True)
record["checks"].append(dict(command=command, exit_code=run.returncode, stdout=run.stdout, stderr=run.stderr))
assert run.returncode == 0, run.stdout + run.stderr
# Patch check against captured baseline roots, with no companion writes.
baseline = FORMAL / "build/patch_baseline"
baseline.mkdir(exist_ok=True)
for umbrella in ["Theory.lean", "Assurance.lean"]:
    shutil.copyfile(COMP / umbrella, baseline / umbrella)
command = ["git", "apply", "--check", str(patchfile)]
run = subprocess.run(command, cwd=baseline, text=True, capture_output=True)
record["checks"].append(dict(command=command, cwd=str(baseline), exit_code=run.returncode, stdout=run.stdout, stderr=run.stderr))
assert run.returncode == 0, run.stdout + run.stderr
for source in [ROOT / "formal/durable_integration/bfv_window/Theory/CiphertextWindow.lean",
               ROOT / "formal/durable_integration/bfv_window/Assurance/CiphertextWindowCell.lean",
               ROOT / "formal/durable_integration/Assurance/ResidentDurableIntegration.lean",
               COMP / "Theory/IndexedProgram.lean",
               COMP / "CLAUDE.md", COMP / "ATLAS.md", COMP / "lean-toolchain"]:
    if source.exists():
        record["dependencies"].append(dict(path=str(source), sha256=sha(source)))
record["patch_sha256"] = sha(patchfile)
(HERE / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
artifacts = [p for p in HERE.iterdir() if p.is_file() and p.name != "artifact_manifest.json"]
artifacts += [FORMAL / "README.md", FORMAL / ".gitignore"]
artifacts += [FORMAL / (module + ".lean") for module in modules]
manifest = {str(p.relative_to(ROOT)): dict(sha256=sha(p), bytes=p.stat().st_size)
            for p in sorted(artifacts)}
(HERE / "artifact_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(dict(modules=len(modules), theorems=sum(x["theorem_count"] for x in record["modules"]),
                      checks=[x["exit_code"] for x in record["checks"]], patch_sha256=record["patch_sha256"]), indent=2))
