"""Package only the two owned index modules; replay the patch without building a closure."""
from pathlib import Path
import difflib, hashlib, json, re, subprocess, tempfile

HERE = Path(__file__).resolve().parent
WORK = Path('/tmp/minidregg-p3-folding-transport-20260908')
BASE = '6937394e1dc2c2aaff986c7d4b3a258aca5d16fd'
MODULES = ['Theory/BitReverseFriTransport.lean', 'Selvage/P3FriQueryTransport.lean']
patch_parts = []
source_hashes = {}
census = []
commands = []

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def run(argv,cwd):
    p=subprocess.run(argv,cwd=cwd,text=True,capture_output=True)
    record=dict(command=argv,cwd=str(cwd),exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr)
    commands.append(record)
    assert p.returncode==0,record
    return p.stdout

base_umbrellas={}
for umbrella,module in [('Theory.lean','Theory.BitReverseFriTransport'),
                        ('Selvage.lean','Selvage.P3FriQueryTransport')]:
    base=subprocess.check_output(['git','show',f'{BASE}:{umbrella}'],cwd=WORK,text=True)
    base_umbrellas[umbrella]=base
    new=base.rstrip('\n')+'\n\nimport '+module+'\n'
    (WORK/umbrella).write_text(new)
    patch_parts += difflib.unified_diff(base.splitlines(True),new.splitlines(True),
        fromfile='a/'+umbrella,tofile='b/'+umbrella)

for rel in MODULES:
    source=WORK/rel
    target=HERE/'src'/rel
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(source.read_bytes())
    source_hashes[rel]=sha(source)
    text=source.read_text()
    # These two reviewed sources contain non-nested block comments and no strings.
    code=re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S)
    assert not re.search(r'\b(sorry|sorryAx|axiom|admit|native_decide|unsafe)\b',code)
    declarations=re.findall(r'(?m)^theorem\s+(\w+)',code)
    pins=re.findall(r"/-- info: '([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms) -/\s*#guard_msgs \(whitespace := lax\) in #print axioms (\w+)",text)
    assert declarations==[n for _,_,n in pins]
    for qualified,message,name in pins:
        assert qualified.split('.')[-1]==name
        axioms=re.findall(r'propext|Classical\.choice|Quot\.sound',message)
        assert message=='depends on axioms: ['+', '.join(axioms)+']'
        line=next(i for i,s in enumerate(text.splitlines(),1) if s.startswith('theorem '+name+' '))
        census.append(dict(module=rel,name=qualified,line=line,axioms=axioms,exact_pin=True))
    imports=re.findall(r'(?m)^import (\S+)',code)
    assert imports==(['Mathlib.Data.Nat.Bitwise'] if rel.startswith('Theory/') else
                     ['Theory.BitReverseFriTransport','Selvage.HalfThresholdFriCoherent'])
    patch_parts += difflib.unified_diff([],text.splitlines(True),fromfile='/dev/null',tofile='b/'+rel)
assert len(census)==15

patch=HERE/'minidregg-p3-query-transport.patch'
patch.write_text(''.join(patch_parts))
with tempfile.TemporaryDirectory(prefix='p3_query_transport_patch_') as tmp:
    tmp=Path(tmp)
    for name,text in base_umbrellas.items(): (tmp/name).write_text(text)
    run(['git','init','-q'],tmp)
    run(['git','apply','--check',str(patch)],tmp)
    run(['git','apply',str(patch)],tmp)
    for rel in MODULES: assert sha(tmp/rel)==source_hashes[rel]
run(['bash','scripts/check-import-boundary.sh'],WORK)

checked_logs={}
for rel,prefix in zip(MODULES,['lean','selvage']):
    matching=[]
    for f in sorted((HERE/'logs').glob(prefix+'_*.json')):
        d=json.loads(f.read_text())
        if d['source_sha256']==source_hashes[rel] and d.get('source_sha256_after')==source_hashes[rel] and d['exit_code']==0 and not d['stdout'] and not d.get('stderr'):
            matching.append(str(f.relative_to(HERE)))
    assert matching,rel
    checked_logs[rel]=matching[-1]

result=dict(all_checks_passed=True,source_sha256=source_hashes,patch_sha256=sha(patch),
            theorem_count=15,census=census,clean_lean_checks=checked_logs,checks=commands,
            source_bytes_match_patch=True,import_boundary=True,full_closure_build=False,
            scope='Generic BitVec index transport and direct existing coherent-index wrapper; no folding arithmetic or probability theorem added.')
(HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
relative='../proof_frontier/2026-09-08/p3_folding_transport/formal'
entry=dict(name='p3_folding_transport',root=relative,patch=relative+'/'+patch.name,
           expected_pins=15,source_files={m:relative+'/src/'+m for m in MODULES})
(HERE/'integration_entry.json').write_text(json.dumps(entry,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['all_checks_passed','source_sha256','patch_sha256','theorem_count','clean_lean_checks']},indent=2))
