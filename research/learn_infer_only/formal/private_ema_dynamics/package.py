"""Patch, census and import-boundary checks for the isolated dynamics extension."""
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
COMPANION=Path('/Users/ember/dev/minidregg')
DEPENDENCY=HERE.parent/'private_address_ema'
RESULTS=HERE/'results'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
source=HERE/'Theory/PrivateEmaDynamics.lean'
latest=sorted(RESULTS.glob('lean_*.json'))[-1]
checked=json.loads(latest.read_text())
assert checked['exit_code']==0 and not checked['stdout'] and not checked['stderr']
assert checked['source_sha256']==sha(source)
spec=importlib.util.spec_from_file_location('census',REPO/'research/learn_infer_only/experiments/integration/check_all_formal.py')
census=importlib.util.module_from_spec(spec);spec.loader.exec_module(census)
audited=census.census(source.read_text());assert audited['pin_count']==28
assert not audited['forbidden_constructs'] and not audited['admit_identifier_tokens']
dependency_source=DEPENDENCY/'Theory/PrivateAddressEma.lean'
assert sha(dependency_source)=='0b148bff8a53447bc9f30950948771a4b0f53edeb1110cc78f44e85a960d562d'
assert sha(HERE/'.build/Theory/PrivateAddressEma.lean')==sha(dependency_source)
base=(COMPANION/'Theory.lean').read_text().rstrip('\n')+'\n\nimport Theory.PrivateAddressEma\n'
updated=base+'import Theory.PrivateEmaDynamics\n'
patch=''.join(difflib.unified_diff(base.splitlines(True),updated.splitlines(True),fromfile='a/Theory.lean',tofile='b/Theory.lean'))
patch+=''.join(difflib.unified_diff([],source.read_text().splitlines(True),fromfile='/dev/null',tofile='b/Theory/PrivateEmaDynamics.lean'))
patch_path=HERE/'minidregg-private-ema-dynamics.patch';patch_path.write_text(patch)
before={k:subprocess.check_output(['git','-C',str(COMPANION),*args],text=True)
        for k,args in [('head',['rev-parse','HEAD']),('status',['status','--porcelain'])]}
scratch=Path(tempfile.mkdtemp(prefix='private_ema_dynamics_'))
records=[]
def run(command,cwd):
    p=subprocess.run(command,cwd=cwd,text=True,capture_output=True)
    records.append({'command':command,'cwd':str(cwd),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    assert p.returncode==0,records[-1]
files=subprocess.check_output(['git','-C',str(COMPANION),'ls-files','--cached','--others','--exclude-standard','*.lean'],text=True).splitlines()
for rel in files+['scripts/check-import-boundary.sh']:
    if rel in ['Theory.lean','Selvage.lean'] or rel.startswith(('Theory/','Selvage/','scripts/')):
        dst=scratch/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(COMPANION/rel,dst)
run(['git','init','-q'],scratch)
dependency_patch=DEPENDENCY/'minidregg-private-address-ema.patch'
run(['git','apply','--check',str(dependency_patch)],scratch)
run(['git','apply',str(dependency_patch)],scratch)
assert (scratch/'Theory.lean').read_text()==base
run(['git','apply','--check',str(patch_path)],scratch)
run(['git','apply',str(patch_path)],scratch)
assert sha(scratch/'Theory/PrivateEmaDynamics.lean')==sha(source)
assert sha(scratch/'Theory/PrivateAddressEma.lean')==sha(dependency_source)
assert (scratch/'Theory.lean').read_text()==updated
run(['bash',str(scratch/'scripts/check-import-boundary.sh')],scratch)
run(['bash',str(COMPANION/'scripts/check-import-boundary.sh')],COMPANION)
after={k:subprocess.check_output(['git','-C',str(COMPANION),*args],text=True)
       for k,args in [('head',['rev-parse','HEAD']),('status',['status','--porcelain'])]}
assert before==after
environment=json.loads((RESULTS/'environment.json').read_text())
assert before=={'head':environment['companion_head'],'status':environment['companion_status']}
report={'all_passed':True,'scope':'28 new theorem pins, isolated single-file Lean check; existing 28-pin dependency reused, no full integration',
    'source_sha256':sha(source),'patch_sha256':sha(patch_path),'dependency_source_sha256':sha(dependency_source),
    'dependency_patch_sha256':sha(dependency_patch),'lean_check':str(latest.relative_to(HERE)),
    'census':audited,'patch_application_and_import_checks':records,
    'companion_before':before,'companion_after':after,'cached_dependency_oleans_reused':True,
    'rust_tfhe_refinement_or_crypto_claim':False,'new_model_or_crypto_operations':0}
save(RESULTS/'verification.json',report)
save(HERE/'integration_entry.json',{'name':'private_ema_dynamics','root':'formal/private_ema_dynamics',
    'patch':'formal/private_ema_dynamics/minidregg-private-ema-dynamics.patch','expected_pins':28,
    'requires':['private_address_ema']})
print({k:report[k] for k in ['all_passed','source_sha256','patch_sha256','scope']})
