#!/usr/bin/env python3
"""Apply-check the emitted-schedule proof and reproduce frozen Lean-authored JSON."""
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
ROOT = HERE.parents[4]
COMPANION = Path('/Users/ember/dev/minidregg')
RESULTS = HERE/'results'
SOURCE = HERE/'Compiler/PrivateAddressEmaSchedule.lean'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

spec = importlib.util.spec_from_file_location('formal_census',
    ROOT/'research/learn_infer_only/experiments/integration/check_all_formal.py')
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
audited = census.census(SOURCE.read_text())
assert audited['pin_count'] == 46
last = json.loads((RESULTS/'lean_009.json').read_text())
assert last['exit_code'] == 0 and last['source_unchanged']
assert last['source_sha256'] == sha(SOURCE) and not last['stdout'] and not last['stderr']
config = json.loads((RESULTS/'environment.json').read_text())
dependency = HERE.parent/'Theory/PrivateAddressEma.lean'
assert sha(dependency) == config['dependency_sha256']
assert sha(dependency) == '0b148bff8a53447bc9f30950948771a4b0f53edeb1110cc78f44e85a960d562d'
baseline = (COMPANION/'Compiler.lean').read_text()
staged = baseline.rstrip('\n')+'\n\nimport Compiler.PrivateAddressEmaSchedule\n'
patch = ''.join(difflib.unified_diff(baseline.splitlines(True),staged.splitlines(True),
    fromfile='a/Compiler.lean',tofile='b/Compiler.lean'))
patch += ''.join(difflib.unified_diff([],SOURCE.read_text().splitlines(True),
    fromfile='/dev/null',tofile='b/Compiler/PrivateAddressEmaSchedule.lean'))
patch_path = HERE/'minidregg-private-address-ema-schedule.patch'
patch_path.write_text(patch)
scratch = Path(tempfile.mkdtemp(prefix='ema_schedule_package_'))
before = {k:subprocess.check_output(['git','-C',str(COMPANION),*args],text=True)
    for k,args in [('head',['rev-parse','HEAD']),('status',['status','--porcelain'])]}
records = []
def run(cmd,cwd,env=None):
    start=time.monotonic()
    p=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True)
    records.append(dict(command=cmd,cwd=str(cwd),exit_code=p.returncode,
        elapsed_seconds=time.monotonic()-start,stdout=p.stdout,stderr=p.stderr))
    assert p.returncode == 0,records[-1]
    return p

files=subprocess.check_output(['git','-C',str(COMPANION),'ls-files','--cached',
    '--others','--exclude-standard','*.lean'],text=True).splitlines()
for rel in files+['scripts/check-import-boundary.sh']:
    if rel in ['Theory.lean','Selvage.lean','Compiler.lean'] or rel.startswith(('Theory/','Selvage/','scripts/')):
        target=scratch/rel
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(COMPANION/rel,target)
(scratch/'Compiler').mkdir(exist_ok=True)
shutil.copy2(dependency,scratch/'Theory/PrivateAddressEma.lean')
run(['git','init','-q'],scratch)
run(['git','apply','--check',str(patch_path)],scratch)
run(['git','apply',str(patch_path)],scratch)
assert sha(scratch/'Compiler/PrivateAddressEmaSchedule.lean') == sha(SOURCE)
assert (scratch/'Compiler.lean').read_text() == staged
run(['bash',str(scratch/'scripts/check-import-boundary.sh')],scratch)
run(['bash',str(COMPANION/'scripts/check-import-boundary.sh')],COMPANION)
repro=scratch/'emission'
repro.mkdir()
run([config['lean'],'--run',str(HERE/'EmitPrivateAddressEma.lean')],repro,
    dict(os.environ,LEAN_PATH=config['lean_path']))
frozen={
    'learn.json':'94e8369ffc8fcdf57b8351b278d5af90dc49a26d83600d40f0bd6a0da359dde8',
    'infer.json':'b742ed7710d2680119eceeff0c553d675e1ce187a503981fc500a6a4a683b80c'}
for name, expected in frozen.items():
    assert sha(HERE/'artifacts'/name) == expected
    assert (repro/'artifacts'/name).read_bytes() == (HERE/'artifacts'/name).read_bytes()
after = {k:subprocess.check_output(['git','-C',str(COMPANION),*args],text=True)
    for k,args in [('head',['rev-parse','HEAD']),('status',['status','--porcelain'])]}
assert before == after
old = json.loads((HERE.parent/'results/environment.json').read_text())
assert before == {'head':old['companion_head'],'status':old['companion_status']}
source_inputs=[SOURCE,HERE/'EmitPrivateAddressEma.lean',HERE/'check.py',HERE/'package.py',
    HERE/'SCHEMA.md',dependency,patch_path]
source_inputs += [COMPANION/f'Compiler/{name}.lean' for name in
    ['Signature','Air','AirFlatten','Emit','EmitShare','DescriptorEval']]
report=dict(all_passed=True,scope='46 exact-pin compiler proposal; single-file check and source-only '
    'patch/import checks; separate-cwd Lean emission byte reproduction. Cached dependency oleans; '
    'root owns full integration; Rust/TFHE execution belongs to independent runtime lane.',
    checks=records,census=audited,source_sha256=sha(SOURCE),patch_sha256=sha(patch_path),
    frozen_json=frozen,companion_before=before,companion_after=after,
    inputs={str(p):sha(p) for p in source_inputs},lean_check='results/lean_009.json')
(RESULTS/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
entry=dict(name='private_address_ema_schedule',root='formal/private_address_ema/emitted_schedule',
    patch='formal/private_address_ema/emitted_schedule/minidregg-private-address-ema-schedule.patch',expected_pins=46)
(HERE/'integration_entry.json').write_text(json.dumps(entry,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['all_passed','source_sha256','patch_sha256','frozen_json','scope']},indent=2))
