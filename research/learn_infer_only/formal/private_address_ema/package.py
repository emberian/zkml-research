#!/usr/bin/env python3
"""Freeze and apply-check the 28-pin proposal in a fresh source-only directory."""
from pathlib import Path
import difflib
import hashlib
import importlib.util
import json
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
COMPANION = Path('/Users/ember/dev/minidregg')
RESULTS = HERE / 'results'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

spec = importlib.util.spec_from_file_location('formal_census',
    ROOT / 'research/learn_infer_only/experiments/integration/check_all_formal.py')
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
source = HERE / 'Theory/PrivateAddressEma.lean'
audited = census.census(source.read_text())
assert audited['pin_count'] == 28
last = json.loads((RESULTS / 'lean_010.json').read_text())
assert last['exit_code'] == 0 and last['source_sha256'] == sha(source)
assert not last['stdout'] and not last['stderr']
baseline = (COMPANION / 'Theory.lean').read_text()
patched = baseline.rstrip('\n') + '\n\nimport Theory.PrivateAddressEma\n'
patch = ''.join(difflib.unified_diff(baseline.splitlines(True), patched.splitlines(True),
    fromfile='a/Theory.lean', tofile='b/Theory.lean'))
patch += ''.join(difflib.unified_diff([], source.read_text().splitlines(True),
    fromfile='/dev/null', tofile='b/Theory/PrivateAddressEma.lean'))
patch_path = HERE / 'minidregg-private-address-ema.patch'
patch_path.write_text(patch)
scratch = Path(tempfile.mkdtemp(prefix='private_address_ema_'))
before = {k: subprocess.check_output(['git', '-C', str(COMPANION), *args], text=True)
    for k,args in [('head',['rev-parse','HEAD']),('status',['status','--porcelain'])]}
records = []
def run(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    records.append(dict(command=cmd, cwd=str(cwd), exit_code=p.returncode,
                        stdout=p.stdout, stderr=p.stderr))
    assert p.returncode == 0, records[-1]

files = subprocess.check_output(['git','-C',str(COMPANION),'ls-files','--cached',
    '--others','--exclude-standard','*.lean'],text=True).splitlines()
for rel in files + ['scripts/check-import-boundary.sh']:
    if rel == 'Theory.lean' or rel == 'Selvage.lean' or rel.startswith(('Theory/', 'Selvage/', 'scripts/')):
        p = scratch / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(COMPANION / rel, p)
run(['git','init','-q'],scratch)
run(['git','apply','--check',str(patch_path)],scratch)
run(['git','apply',str(patch_path)],scratch)
assert sha(scratch/'Theory/PrivateAddressEma.lean') == sha(source)
assert (scratch/'Theory.lean').read_text() == patched
run(['bash',str(scratch/'scripts/check-import-boundary.sh')],scratch)
run(['bash',str(COMPANION/'scripts/check-import-boundary.sh')],COMPANION)
after = {k: subprocess.check_output(['git', '-C', str(COMPANION), *args], text=True)
    for k,args in [('head',['rev-parse','HEAD']),('status',['status','--porcelain'])]}
assert before == after
frozen = json.loads((RESULTS/'environment.json').read_text())
assert before == {'head':frozen['companion_head'],'status':frozen['companion_status']}
inputs = [source, patch_path, HERE/'check.py', HERE/'package.py',
    ROOT/'research/learn_infer_only/formal/integration/minidregg-combined-resident-708.patch',
    ROOT/'research/learn_infer_only/experiments/end_to_end/private_ema/src/lib.rs',
    ROOT/'research/learn_infer_only/experiments/end_to_end/private_ema/review/IMPLEMENTATION_REVIEW.md']
report = dict(scope='Single Mathlib-only module; 28 exact pins; source-only patch and import checks. '
    'Cached dependency oleans reused; no full umbrella build or Rust/TFHE execution.',
    checks=records, census=audited, companion_before=before, companion_after=after,
    lean_check='results/lean_010.json', source_sha256=sha(source), patch_sha256=sha(patch_path),
    inputs={str(p.relative_to(ROOT)):sha(p) for p in inputs}, all_passed=True)
(RESULTS/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
entry = dict(name='private_address_ema', root='formal/private_address_ema',
    patch='formal/private_address_ema/minidregg-private-address-ema.patch', expected_pins=28)
(HERE/'integration_entry.json').write_text(json.dumps(entry,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['all_passed','source_sha256','patch_sha256','scope']},indent=2))
