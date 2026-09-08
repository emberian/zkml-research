#!/usr/bin/env python3
"""Check this patch in isolation and reproduce old emissions in a fresh directory."""
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
SOURCE = HERE / 'Compiler/EmittedScheduleExecution.lean'
FROZEN = HERE.parent / 'private_address_ema'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

spec = importlib.util.spec_from_file_location('formal_census',
    ROOT / 'research/learn_infer_only/experiments/integration/check_all_formal.py')
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
audited = census.census(SOURCE.read_text())
assert audited['pin_count'] == 19
last = json.loads((RESULTS / 'lean_006.json').read_text())
assert last['exit_code'] == 0 and last['source_unchanged']
assert last['source_sha256'] == sha(SOURCE) and not last['stdout'] and not last['stderr']
config = json.loads((RESULTS / 'environment.json').read_text())
initial = json.loads((RESULTS / 'baseline.json').read_text())
dependencies = [
    FROZEN / 'Theory/PrivateAddressEma.lean',
    FROZEN / 'emitted_schedule/Compiler/PrivateAddressEmaSchedule.lean',
]
for path, record in zip(dependencies, config['dependencies']):
    assert sha(path) == record['sha256'] and record['exit_code'] == 0
baseline = (COMPANION / 'Compiler.lean').read_text()
staged = baseline.rstrip('\n') + '\n\nimport Compiler.EmittedScheduleExecution\n'
patch = ''.join(difflib.unified_diff(baseline.splitlines(True), staged.splitlines(True),
    fromfile='a/Compiler.lean', tofile='b/Compiler.lean'))
patch += ''.join(difflib.unified_diff([], SOURCE.read_text().splitlines(True),
    fromfile='/dev/null', tofile='b/Compiler/EmittedScheduleExecution.lean'))
patch_path = HERE / 'minidregg-emitted-schedule-execution.patch'
patch_path.write_text(patch)
scratch = Path(tempfile.mkdtemp(prefix='emitted_execution_package_'))
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
assert sha(scratch / 'Compiler/EmittedScheduleExecution.lean') == sha(SOURCE)
assert (scratch / 'Compiler.lean').read_text() == staged
run(['bash', str(scratch / 'scripts/check-import-boundary.sh')], scratch)
run(['bash', str(COMPANION / 'scripts/check-import-boundary.sh')], COMPANION)
env = dict(os.environ, LEAN_PATH=config['lean_path'])
repro = scratch / 'emission'
repro.mkdir()
run([config['lean'], '--run', str(FROZEN / 'emitted_schedule/EmitPrivateAddressEma.lean')], repro, env)
artifacts = {}
for name in ['learn.json', 'infer.json']:
    old = FROZEN / 'emitted_schedule/artifacts' / name
    emitted = repro / 'artifacts' / name
    assert old.read_bytes() == emitted.read_bytes()
    artifacts[name] = sha(old)
structure = run([config['lean'], '--run', str(HERE / 'CheckScheduleStructure.lean')], scratch, env)
structure_values = json.loads(structure.stdout)
assert len(structure_values) == 2 and all(r['structurallyValid'] for r in structure_values)
for row in structure_values:
    d = json.loads((repro / 'artifacts' / (row['operation'] + '.json')).read_text())
    assert (row['nInputs'], row['nWires'], row['gates'], row['outputs']) == (
        d['nInputs'], d['nWires'], len(d['gates']), len(d['outputs']))
after_files = {path: sha(ROOT / path) for path in initial['frozen_files']}
assert after_files == initial['frozen_files']
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=COMPANION, text=True)
status = subprocess.check_output(['git', 'status', '--porcelain'], cwd=COMPANION, text=True)
assert head == initial['companion_head'] and status == initial['companion_status']
report = dict(all_package_checks_passed=True, source_sha256=sha(SOURCE), patch_sha256=sha(patch_path),
    census=audited, checks=records, lean_check='results/lean_006.json',
    compiled_structural_checks=structure_values, frozen_json_sha256=artifacts,
    actual_validity_kernel_proved=False,
    kernel_probes={op: json.loads((RESULTS / f'kernel_{op}.json').read_text())
        for op in ['infer', 'learn', 'baseline', 'infer_3g', 'learn_3g']},
    frozen_files_unchanged=True, frozen_file_count=len(after_files),
    companion_head_unchanged=True, companion_status_unchanged=True,
    dependency_source_sha256={str(p):sha(p) for p in dependencies},
    reused_source_sha256={str(COMPANION / 'Compiler' / (n + '.lean')):
        sha(COMPANION / 'Compiler' / (n + '.lean')) for n in ['Emit', 'EmitShare', 'DescriptorEval']},
    scope='Kernel-checked universal conditional execution theorem; actual descriptor shape is '
        'compiled evidence only. Source patch/import checks; fresh proposal dependency oleans '
        'with cached external dependencies. Root owns the full umbrella build. No Rust/TFHE refinement.')
(RESULTS / 'verification.json').write_text(json.dumps(report, indent=2)+'\n')
entry = dict(name='emitted_schedule_execution', root='formal/emitted_schedule_execution',
    patch='formal/emitted_schedule_execution/minidregg-emitted-schedule-execution.patch', expected_pins=19,
    depends_on=['private_address_ema', 'private_address_ema_schedule'])
(HERE / 'integration_entry.json').write_text(json.dumps(entry, indent=2)+'\n')
print(json.dumps({k: report[k] for k in ['all_package_checks_passed', 'source_sha256',
    'patch_sha256', 'compiled_structural_checks', 'actual_validity_kernel_proved',
    'frozen_files_unchanged', 'scope']}, indent=2))
