#!/usr/bin/env python3
"""Independent copy/apply/Lean verification, with read-only author and companion inputs."""
from pathlib import Path
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
RESIDENT = HERE.parents[2]
AUTHOR = RESIDENT/'formal/private_ema_dynamics'
DEPENDENCY = RESIDENT/'formal/private_address_ema'
COMPANION = Path('/Users/ember/dev/minidregg')
EXPECTED = {
    AUTHOR/'Theory/PrivateEmaDynamics.lean': '4cfad9f0326ba5ff7a13e871a6d56a82816d0746592248aa84cda40fcae56bfb',
    AUTHOR/'minidregg-private-ema-dynamics.patch': 'da4e1d75e0e7ff2843a598c008ba4126fcc3885ffa2529adb099eaf807ab8e1b',
    DEPENDENCY/'Theory/PrivateAddressEma.lean': '0b148bff8a53447bc9f30950948771a4b0f53edeb1110cc78f44e85a960d562d',
    DEPENDENCY/'minidregg-private-address-ema.patch': '9fabd5d64ab3280dde1bbb1affab9ced9d5835f248f984dd4bb9d0488622ebae',
}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def save(p,value):
    p.write_text(json.dumps(value,indent=2)+'\n')

index=1
while (HERE/f'run_{index:03d}').exists(): index+=1
OUT=HERE/f'run_{index:03d}'
OUT.mkdir()
scratch=Path(tempfile.mkdtemp(prefix='review_ema_dynamics_'))
for path,expected in EXPECTED.items(): assert sha(path)==expected, str(path)
manifest=json.loads((AUTHOR/'manifest.json').read_text())
author_inputs=[AUTHOR/'manifest.json']+[AUTHOR/e['path'] for e in manifest['entries']]
for e in manifest['entries']:
    p=AUTHOR/e['path']
    assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes'],e['path']
all_inputs=list(dict.fromkeys([*EXPECTED,*author_inputs,COMPANION/'Theory.lean',
    COMPANION/'scripts/check-import-boundary.sh']))
before_hashes={str(p):sha(p) for p in all_inputs}
save(OUT/'inputs_before.json',before_hashes)
before={k:subprocess.check_output(['git','-C',str(COMPANION),*args],text=True)
    for k,args in [('head',['rev-parse','HEAD']),('status',['status','--porcelain'])]}
records=[]
def run(cmd,cwd,env=None):
    start=time.monotonic()
    p=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True)
    record=dict(command=cmd,cwd=str(cwd),exit_code=p.returncode,
        elapsed_seconds=time.monotonic()-start,stdout=p.stdout,stderr=p.stderr)
    records.append(record)
    save(OUT/f'command_{len(records):02d}.json',record)
    assert p.returncode==0,record

files=subprocess.check_output(['git','-C',str(COMPANION),'ls-files','--cached',
    '--others','--exclude-standard','*.lean'],text=True).splitlines()
for rel in files+['scripts/check-import-boundary.sh']:
    if rel in ['Theory.lean','Selvage.lean'] or rel.startswith(('Theory/','Selvage/','scripts/')):
        dst=scratch/rel
        dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(COMPANION/rel,dst)
run(['git','init','-q'],scratch)
for patch in [DEPENDENCY/'minidregg-private-address-ema.patch',AUTHOR/'minidregg-private-ema-dynamics.patch']:
    run(['git','apply','--check',str(patch)],scratch)
    run(['git','apply',str(patch)],scratch)
for rel,original in [('Theory/PrivateAddressEma.lean',DEPENDENCY/'Theory/PrivateAddressEma.lean'),
    ('Theory/PrivateEmaDynamics.lean',AUTHOR/'Theory/PrivateEmaDynamics.lean')]:
    assert (scratch/rel).read_bytes()==original.read_bytes()
run(['bash',str(scratch/'scripts/check-import-boundary.sh')],scratch)

config=json.loads((DEPENDENCY/'results/environment.json').read_text())
overlay=scratch/'olean'
(overlay/'Theory').mkdir(parents=True)
env=dict(os.environ,LEAN_PATH=str(overlay)+':'+config['lean_path'])
for stem in ['PrivateAddressEma','PrivateEmaDynamics']:
    run([config['lean'],'-o',str(overlay/f'Theory/{stem}.olean'),str(scratch/f'Theory/{stem}.lean')],scratch,env)
    assert not records[-1]['stdout'] and not records[-1]['stderr']

spec=importlib.util.spec_from_file_location('census',RESIDENT/'experiments/integration/check_all_formal.py')
census=importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
audited=census.census((scratch/'Theory/PrivateEmaDynamics.lean').read_text())
assert audited['pin_count']==28 and audited['theorem_count']==28
save(OUT/'axiom_census.json',audited)
spec=importlib.util.spec_from_file_location('integer_controls',HERE/'integer_controls.py')
controls=importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)
control_report=controls.run()
save(OUT/'integer_controls.json',control_report)
after_hashes={str(p):sha(p) for p in all_inputs}
save(OUT/'inputs_after.json',after_hashes)
assert before_hashes==after_hashes
after={k:subprocess.check_output(['git','-C',str(COMPANION),*args],text=True)
    for k,args in [('head',['rev-parse','HEAD']),('status',['status','--porcelain'])]}
assert before==after
report=dict(all_passed=True,scope='Independent patch application, exact source/dependency checks, '
    'fresh Lean compilation of both proposed modules using cached external dependency oleans, '
    '28 exact dynamics pins, pure integer controls. No umbrella/clean dependency build or crypto.',
    expected_hashes={str(p):h for p,h in EXPECTED.items()},
    author_manifest_entries=len(manifest['entries']),inputs_unchanged=True,
    companion_before=before,companion_after=after,commands=len(records),
    integer_controls='integer_controls.json',axiom_census='axiom_census.json',
    audit_sha256=sha(Path(__file__)),integer_controls_sha256=sha(HERE/'integer_controls.py'))
save(OUT/'report.json',report)
print(json.dumps({k:report[k] for k in ['all_passed','scope','author_manifest_entries','commands']},indent=2))
