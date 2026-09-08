from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-polynomial-gluing-20260908')
frozen=Path('/tmp/minidregg-full-ud-babybear-20260908')
module='Selvage/FullUDSamplingBudget.lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=(repo/module).read_text()
(root/'FullUDSamplingBudget.lean').write_text(s)
checkpoint=root/'FullUDSamplingBudget.checked-core.lean'
if checkpoint.exists():checkpoint.unlink()
run=json.loads((root/'logs/final-pinned.json').read_text())
assert run['exit_code']==0 and run['source_unchanged'] and run['source_sha256']==sha(repo/module)
# Strip comments before the declaration/pin census, including nested blocks.
def no_comments(s):
    out=[]; i=0; depth=0
    while i<len(s):
        if s[i:i+2]=='/-':depth+=1;i+=2
        elif depth and s[i:i+2]=='-/':depth-=1;i+=2
        elif depth:i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    return ''.join(out)
clean=no_comments(s)
names=re.findall(r'^theorem\s+(\w+)',clean,re.M)
pins=re.findall(r'^#print axioms\s+(\w+)',clean,re.M)
assert names==pins
assert len(re.findall(r'^#guard_msgs',clean,re.M))==len(names)
assert not re.search(r'\b(sorry|axiom|native_decide)\b',clean)
# Build a one-new-file patch. git diff exit1 means differences, as expected.
r=subprocess.run(['git','diff','--no-index','--','/dev/null',module],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
assert r.returncode==1 and not r.stderr
patch=root/'full-ud-sampling-budget.patch';patch.write_text(r.stdout)
checks=[]
for cmd in [['git','apply','--check','--cached',str(patch)],['git','apply','--reverse','--check',str(patch)],['bash','scripts/check-import-boundary.sh']]:
    q=subprocess.run(cmd,cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    checks.append({'command':cmd,'exit_code':q.returncode,'output':q.stdout})
assert all(x['exit_code']==0 for x in checks)
(root/'package-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
used={
'Selvage/FullUDFriConsumer.lean':['proximity_sound_rateHalf_twoFifths_fullUD'],
'Selvage/ProximityGapFullUD.lean':['foldDistancePreserving_fullUD'],
'Selvage/HalfThresholdFri.lean':['foldDistanceTransition_halfThreshold','FoldDistanceTransition.mono_bad'],
'Selvage/HalfThresholdFriCoherent.lean':['PowerTwoFriLevels','FriAdaptiveCoherentAccepts','friAdaptive_coherent_sampled_sound'],
'Selvage/HalfThresholdFriQuery.lean':['friAdaptive_earliestDeviation_cover'],
'Selvage/BabyBearFullUD.lean':['ext4_card'],
'Selvage/BabyBearExt4.lean':['Ext4'],
'Selvage/Proximity.lean':['FoldingTower']}
deps=[]
for path,nms in used.items():
    file=frozen/path
    text=file.read_text();lines=text.splitlines()
    deps.append({'path':str(file),'sha256':sha(file),'olean_sha256':sha(frozen/'.lake/build/lib/lean'/Path(path).with_suffix('.olean')),'declarations':[{'name':n,'line':next((i+1 for i,l in enumerate(lines) if re.search(r'\b(?:theorem|lemma|def|abbrev|structure)\s+'+re.escape(n)+r'\b',l)),None)} for n in nms]})
# Match the actually imported frozen files to the source packages, including all fullUD dependencies.
formal=root.parent
up=json.loads((formal/'full_ud/manifest.json').read_text())
for item in up['modules']:
    assert sha(frozen/item['path'])==item['sha256'],item['path']
assert sha(frozen/'Selvage/BabyBearFullUD.lean')=='03f80a278b95dfb767eaf6657ee63b26a643900df5d0cbfb4c1a579399314978'
(root/'dependency-pins.json').write_text(json.dumps({'direct_and_used_sources':deps,'full_ud_manifest':str(formal/'full_ud/manifest.json'),'full_ud_manifest_sha256':sha(formal/'full_ud/manifest.json'),'all_full_ud_sources_match_manifest':True,'babybear_frozen_source_sha256':sha(frozen/'Selvage/BabyBearFullUD.lean')},indent=2)+'\n')
manifest={'module':module,'source_sha256':sha(repo/module),'patch_sha256':sha(patch),'declarations':len(names),'pins':len(pins),'lines':len(s.splitlines()),'names':[{'name':n,'line':next(i+1 for i,l in enumerate(s.splitlines()) if l.startswith('theorem '+n+' ') or l.startswith('theorem '+n+'\n') or l=='theorem '+n or l.startswith('theorem '+n+' :'))} for n in names],'checked':run,'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'frozen':True}
(root/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(root/'integration_entry.json').write_text(json.dumps({'name':'full_ud_sampling_budget','root':'../proof_frontier/2026-09-08/formal/full_ud_sampling_budget','patch':'../proof_frontier/2026-09-08/formal/full_ud_sampling_budget/full-ud-sampling-budget.patch','expected_pins':len(pins),'source_files':{module:'../proof_frontier/2026-09-08/formal/full_ud_sampling_budget/FullUDSamplingBudget.lean'}},indent=2)+'\n')
print(json.dumps({k:manifest[k] for k in ['source_sha256','patch_sha256','declarations','pins','lines','base_commit']},indent=2))
