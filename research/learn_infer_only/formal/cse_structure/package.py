#!/usr/bin/env python3
"""Apply-check the new structural theorem without touching frozen dependencies."""
from pathlib import Path
import difflib
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
COMPANION = Path('/Users/ember/dev/minidregg')
RESULTS = HERE / 'results'
SOURCE = HERE / 'Compiler/CseStructure.lean'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

spec = importlib.util.spec_from_file_location('formal_census',
    ROOT / 'research/learn_infer_only/experiments/integration/check_all_formal.py')
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
audited = census.census(SOURCE.read_text())
assert audited['pin_count'] == 18
last = json.loads((RESULTS / 'lean_005.json').read_text())
assert last['exit_code'] == 0 and last['source_unchanged']
assert last['source_sha256'] == sha(SOURCE) and not last['stdout'] and not last['stderr']
config = json.loads((RESULTS / 'environment.json').read_text())
initial = json.loads((RESULTS / 'baseline.json').read_text())
dependencies = [
    HERE.parent / 'private_address_ema/Theory/PrivateAddressEma.lean',
    HERE.parent / 'private_address_ema/emitted_schedule/Compiler/PrivateAddressEmaSchedule.lean',
    HERE.parent / 'emitted_schedule_execution/Compiler/EmittedScheduleExecution.lean',
]
for path, record in zip(dependencies, config['dependencies']):
    assert sha(path) == record['sha256'] and record['exit_code'] == 0
baseline = (COMPANION / 'Compiler.lean').read_text()
staged = baseline.rstrip('\n') + '\n\nimport Compiler.CseStructure\n'
patch = ''.join(difflib.unified_diff(baseline.splitlines(True), staged.splitlines(True),
    fromfile='a/Compiler.lean', tofile='b/Compiler.lean'))
patch += ''.join(difflib.unified_diff([], SOURCE.read_text().splitlines(True),
    fromfile='/dev/null', tofile='b/Compiler/CseStructure.lean'))
patch_path = HERE / 'minidregg-cse-structure.patch'
patch_path.write_text(patch)
scratch = Path(tempfile.mkdtemp(prefix='cse_structure_package_'))
records = []

def run(cmd, cwd, env=None):
    started = time.monotonic()
    p = subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True)
    record = dict(command=cmd, cwd=str(cwd), exit_code=p.returncode,
        seconds=time.monotonic()-started, stdout=p.stdout, stderr=p.stderr)
    records.append(record)
    assert p.returncode == 0, record
    return p

files = subprocess.check_output(['git', '-C', str(COMPANION), 'ls-files', '--cached',
    '--others', '--exclude-standard', '*.lean'], text=True).splitlines()
for rel in files + ['scripts/check-import-boundary.sh']:
    if rel in ['Theory.lean', 'Selvage.lean', 'Compiler.lean'] or rel.startswith(('Theory/', 'Selvage/', 'scripts/')):
        target = scratch / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(COMPANION / rel, target)
(scratch / 'Compiler').mkdir(exist_ok=True)
for path in dependencies:
    shutil.copy2(path, scratch / path.parent.name / path.name)
run(['git', 'init', '-q'], scratch)
run(['git', 'apply', '--check', str(patch_path)], scratch)
run(['git', 'apply', str(patch_path)], scratch)
assert sha(scratch / 'Compiler/CseStructure.lean') == sha(SOURCE)
assert (scratch / 'Compiler.lean').read_text() == staged
run(['bash', str(scratch / 'scripts/check-import-boundary.sh')], scratch)
run(['bash', str(COMPANION / 'scripts/check-import-boundary.sh')], COMPANION)
after_files = {path: sha(ROOT / path) for path in initial['frozen_files']}
assert after_files == initial['frozen_files']
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=COMPANION, text=True)
status = subprocess.check_output(['git', 'status', '--porcelain'], cwd=COMPANION, text=True)
assert head == initial['companion_head'] and status == initial['companion_status']
report = dict(all_package_checks_passed=True, source_sha256=sha(SOURCE), patch_sha256=sha(patch_path),
    census=audited, checks=records, lean_check='results/lean_005.json',
    frozen_files_unchanged=True, frozen_file_count=len(after_files),
    companion_head_unchanged=True, companion_status_unchanged=True,
    dependency_source_sha256={str(p):sha(p) for p in dependencies},
    reused_source_sha256={str(COMPANION / 'Compiler' / (n + '.lean')):
        sha(COMPANION / 'Compiler' / (n + '.lean')) for n in ['Emit', 'EmitShare', 'DescriptorEval']},
    scope='Kernel-checked generic CSE SSA/WellFormed preservation and unconditional existing '
        'Lean evaluator/source-output equality, including exact Learn/Infer. No initialized-reference '
        'theorem or Rust/TFHE language refinement. Fresh three proposal dependency oleans with '
        'cached external dependencies. Root owns full umbrella build.')
(RESULTS / 'verification.json').write_text(json.dumps(report, indent=2)+'\n')
entry = dict(name='cse_structure', root='formal/cse_structure',
    patch='formal/cse_structure/minidregg-cse-structure.patch', expected_pins=18,
    depends_on=['private_address_ema', 'private_address_ema_schedule', 'emitted_schedule_execution'])
(HERE / 'integration_entry.json').write_text(json.dumps(entry, indent=2)+'\n')
print(json.dumps({k: report[k] for k in ['all_package_checks_passed', 'source_sha256',
    'patch_sha256', 'frozen_files_unchanged', 'frozen_file_count', 'scope']}, indent=2))
