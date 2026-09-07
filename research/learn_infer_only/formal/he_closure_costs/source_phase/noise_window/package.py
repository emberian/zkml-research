#!/usr/bin/env python3
"""Package only the two source/noise successors, without companion writes."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
FORMAL = HERE.parent
ROOT = FORMAL.parents[2]
COMP = Path("/Users/ember/dev/minidregg")
LOGS = ROOT / "experiments/he_closure_costs/source_phase"
OVERLAY = FORMAL / "build/noise_window_overlay"
BASELINE = FORMAL / "build/noise_window_baseline"
MODULES = ["Theory/BfvNoiseSource", "Assurance/ResidentBfvSourceWindow"]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
record = {"scope": "Two algebraic source/noise successor modules; no Rust refinement or combined umbrella build", "modules": [], "dependencies": [], "checks": []}
patch = []

for directory in (OVERLAY, BASELINE):
    directory.mkdir(parents=True, exist_ok=True)
for module in MODULES:
    source = FORMAL / (module + ".lean")
    assert not (COMP / (module + ".lean")).exists(), module
    text = source.read_text()
    assert not re.search(r"\b(sorry|axiom)\b", re.sub(r"/-[\s\S]*?-/|--[^\n]*", "", text))
    names = re.findall(r"^theorem (\w+)", text, re.M)
    pins = re.findall(r"#guard_msgs in\n#print axioms (\S+)", text)
    assert len(names) == len(pins)
    latest_path = sorted(LOGS.glob(f"lean_{source.stem}_*.json"))[-1]
    latest = json.loads(latest_path.read_text())
    assert latest["exit_code"] == 0 and latest["source_sha256"] == sha(source)
    assert not latest["stdout"].strip() and not latest["stderr"].strip()
    record["modules"].append({"module": module, "source_sha256": sha(source),
        "theorem_count": len(names), "pins": pins,
        "successful_check": str(latest_path.relative_to(ROOT)), "check_sha256": sha(latest_path)})
    patch.extend(difflib.unified_diff([], text.splitlines(keepends=True),
        fromfile="/dev/null", tofile="b/" + module + ".lean"))

for root, module in zip(("Theory.lean", "Assurance.lean"), MODULES):
    original = (COMP / root).read_text()
    amended = original + "\nimport " + module.replace("/", ".") + "\n"
    patch.extend(difflib.unified_diff(original.splitlines(keepends=True), amended.splitlines(keepends=True),
        fromfile="a/" + root, tofile="b/" + root))
    (BASELINE / root).write_text(original)
    record["dependencies"].append({"path": str(COMP / root), "sha256": sha(COMP / root), "role": "captured companion umbrella baseline"})

patchfile = HERE / "minidregg-bfv-source-window.patch"
patchfile.write_text("".join(patch))
# Apply into a fresh isolated copy, then scan actual new source plus all current
# companion Theory/Selvage and the frozen algebra dependency source files.
for root in ("Theory.lean", "Assurance.lean"):
    (OVERLAY / root).write_bytes((BASELINE / root).read_bytes())
for module in MODULES:
    target = OVERLAY / (module + ".lean")
    if target.exists():
        assert not target.is_symlink()
        target.unlink()
def run(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    record["checks"].append({"command": command, "cwd": str(cwd), "exit_code": result.returncode,
                             "stdout": result.stdout, "stderr": result.stderr})
    assert result.returncode == 0, result.stdout + result.stderr
run(["git", "apply", "--check", str(patchfile)], BASELINE)
run(["git", "apply", str(patchfile)], OVERLAY)

boundary_sources = []
for prefix in ("Theory", "Selvage"):
    for source in (COMP / prefix).rglob("*.lean"):
        target = OVERLAY / source.relative_to(COMP)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() and not target.is_symlink():
            target.symlink_to(source)
        boundary_sources.append({"path": str(source), "sha256": sha(source)})
for source, relative in [(FORMAL / "Theory/BfvPhaseAlgebra.lean", "Theory/BfvPhaseAlgebra.lean"),
                         (ROOT / "formal/he_closure_costs/Theory/IntegerWindowNoise.lean", "Theory/IntegerWindowNoise.lean")]:
    target = OVERLAY / relative
    if not target.exists() and not target.is_symlink():
        target.symlink_to(source)
    boundary_sources.append({"path": str(source), "sha256": sha(source)})
(OVERLAY / "Selvage.lean").write_bytes((COMP / "Selvage.lean").read_bytes())
(OVERLAY / "scripts").mkdir(exist_ok=True)
script = COMP / "scripts/check-import-boundary.sh"
shutil.copyfile(script, OVERLAY / "scripts/check-import-boundary.sh")
run(["bash", str(OVERLAY / "scripts/check-import-boundary.sh")], OVERLAY)
record["boundary_source_count"] = len(boundary_sources) + 4
(HERE / "boundary_sources.json").write_text(json.dumps(boundary_sources, indent=2) + "\n")

dependencies = [
    (FORMAL / "minidregg-bfv-source-phase.patch", "required frozen source phase 45-pin patch"),
    (ROOT / "experiments/he_closure_costs/window_formal/proposed_minidregg.patch", "required frozen window 62-pin patch; includes broader durable-dependent modules"),
    (ROOT / "formal/durable_integration/bfv_window/minidregg-ciphertext-window.patch", "prerequisite of full window patch; durable queue 44-pin patch"),
    (FORMAL / "Theory/BfvPhaseAlgebra.lean", "direct frozen source dependency"),
    (FORMAL / "Assurance/ResidentBfvSourcePhase.lean", "direct frozen source dependency"),
    (ROOT / "formal/he_closure_costs/Theory/IntegerWindowNoise.lean", "direct frozen source dependency"),
    (ROOT / "formal/he_closure_costs/Assurance/ResidentBfvWindowNoise.lean", "direct frozen source dependency"),
    (script, "import boundary instrument"),
    (COMP / "Selvage.lean", "boundary root"),
    (COMP / "lean-toolchain", "toolchain"),
    (LOGS / "check_lean.py", "module elaboration instrument"),
]
for source, role in dependencies:
    record["dependencies"].append({"path": str(source), "sha256": sha(source), "role": role})

source_register = json.loads((LOGS / "source_spans.json").read_text())
for entry in source_register:
    assert sha(Path(entry["path"])) == entry["sha256"]
anchor = Path("/Users/ember/dev/breadstuffs/metatheory/Bfv/Ring.lean")
source_register.append({"path": str(anchor), "sha256": sha(anchor),
    "role": "read-only mathematical negacyclic expansion anchor generalized from integers to ZMod", "lines": [110, 235]})
(HERE / "source_register.json").write_text(json.dumps(source_register, indent=2) + "\n")
record["patch_sha256"] = sha(patchfile)
record["total_pins"] = sum(module["theorem_count"] for module in record["modules"])
assert record["total_pins"] == 34
(HERE / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
artifacts = [p for p in HERE.iterdir() if p.is_file() and p.name != "artifact_manifest.json"]
artifacts += [FORMAL / (module + ".lean") for module in MODULES]
artifacts += [ROOT / module["successful_check"] for module in record["modules"]]
manifest = {str(p.relative_to(ROOT)): {"sha256": sha(p), "bytes": p.stat().st_size} for p in sorted(artifacts)}
(HERE / "artifact_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"pins": record["total_pins"], "checks": [c["exit_code"] for c in record["checks"]],
    "patch_sha256": record["patch_sha256"], "module_hashes": {m["module"]: m["source_sha256"] for m in record["modules"]}}, indent=2))
