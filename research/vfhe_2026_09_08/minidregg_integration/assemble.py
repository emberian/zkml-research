#!/usr/bin/env python3
"""Assemble exact finished sources and their missing import closure; no builds."""
from pathlib import Path
import hashlib,json,re,subprocess,difflib
ROOT=Path(__file__).resolve().parent
LANES=ROOT.parent
REPO=LANES.parents[1]
MAIN=Path('/Users/ember/dev/minidregg')
BASE='6937394e1dc2c2aaff986c7d4b3a258aca5d16fd'
sha=lambda b:hashlib.sha256(b).hexdigest()
def read_json(p):return json.loads(p.read_text())
prerequisite_evidence=REPO/'research/learn_infer_only/formal/bfv_lift_refinement/target_projection/validation-summary.json'
prerequisite_pins=read_json(prerequisite_evidence)['sources_sha256']
files={}; records={}; candidates={}; evidence={}
def include(path,target=None,expected=None,group=None,override=False):
 path=Path(path).resolve();target=target or ('Compiler/'+path.name if path.parent.name=='Compiler' else path.name)
 if expected is None and group is None:expected=prerequisite_pins.get(str(path))
 data=path.read_bytes();digest=sha(data)
 if expected:assert digest==expected,(path,'source pin mismatch')
 if target in files and files[target]!=data:
  assert override,(target,'conflicting sources')
  previous=records[target]
 else:previous=None
 files[target]=data
 records[target]={'source':str(path),'sha256':digest,'group':group or 'required predecessor','expected_pin_checked':expected is not None}
 if previous:records[target]['replaces']=previous
 if target.startswith('Compiler/'):candidates[target]=path
def note_evidence(name,path):
 path=Path(path);evidence[name]={'path':str(path.resolve()),'sha256':sha(path.read_bytes())}
for name in ['arithmetic_coverage','arithmetic_rescale']:
 folder=LANES/name;pins=read_json(folder/'source_pins.json')
 note_evidence(name,folder/'results/checked_modules.json')
 for rel,digest in pins['proposal'].items():
  if rel.endswith('.lean'):include(folder/rel,rel,digest,name)
 for path in pins['reused_source']:
  p=Path(path)
  if p.suffix=='.lean':candidates['Compiler/'+p.name]=p
folder=LANES/'arithmetic_rescale_generic';pins=read_json(folder/'source_pins.json')
note_evidence('arithmetic_rescale_generic',folder/'results/checked_modules.json')
for item in pins['owned_sources']:
 p=Path(item['path'])
 if p.suffix=='.lean':include(p,expected=item['sha256'],group='arithmetic_rescale_generic')
for item in pins['reused_compiler_dependencies']:candidates[item['module'].replace('.','/')+'.lean']=Path(item['source']['path'])
folder=LANES/'compiler_cost_successor'
for rel,digest in {'Compiler/AirAssertionShare.lean':'e08fbc86e0829ba85bcf986f92f63b88e7cef4584ccd7eeaecfdf05ab7ce8cdf',
 'Compiler/BfvRescaleAssertionShare.lean':'a343673837610f4fb97a303fc4c07b4e49d743eece212ef1fca7f22e6353cc31'}.items():include(folder/rel,rel,digest,'compiler_cost_successor')
include(folder/'EmitBfvRescale.lean',expected=read_json(folder/'RESULTS.json')['sources']['proposed_emitter_sha256'],group='compiler_cost_successor',override=True)
note_evidence('compiler_cost_successor',folder/'RESULTS.json')
for name in ['bootstrap_successor','bootstrap_rotation_successor']:
 folder=LANES/name;manifest=read_json(folder/'MANIFEST.json')
 for item in manifest['files']:
  rel=item['path']
  if re.fullmatch(r'(Compiler/[^/]+|Emit[^/]+)\.lean',rel):include(folder/rel,rel,item['sha256'],name)
 note_evidence(name,folder/'MANIFEST.json')
folder=LANES/'query_arithmetic';pins=read_json(folder/'source_pins.json')
for rel,digest in pins['sources'].items():include(folder/rel,rel,digest,'query_arithmetic')
note_evidence('query_arithmetic',folder/'results/validation.json')

note_evidence('required_certificate_predecessors',prerequisite_evidence)
tracked=set(subprocess.check_output(['git','ls-tree','--name-only','-r',BASE],cwd=MAIN,text=True).splitlines())
# Index filenames only in the formal research subtree, for unresolved imports.
formal=REPO/'research/learn_infer_only/formal'
index={}
for text in subprocess.check_output(['rg','--files',str(formal)],text=True).splitlines():
 p=Path(text)
 if p.suffix=='.lean' and p.parent.name=='Compiler':index.setdefault('Compiler/'+p.name,[]).append(p)
imports=lambda data:re.findall(r'^import\s+(\S+)',data.decode(),flags=re.M)
processed=set();base_dependencies={}
while pending:=sorted(set(files)-processed):
 for target in pending:
  processed.add(target)
  for module in imports(files[target]):
   if not module.startswith('Compiler.'):continue
   rel=module.replace('.','/')+'.lean'
   if rel in files:continue
   if rel in tracked:
    base_dependencies[rel]={'source':str(MAIN/rel),'git_blob':subprocess.check_output(['git','rev-parse',f'{BASE}:{rel}'],cwd=MAIN,text=True).strip()}
    continue
   path=candidates.get(rel)
   if path is None:
    options=index.get(rel,[]);assert len(options)==1,(rel,[str(p) for p in options]);path=options[0]
   include(path,rel)

leaves=['Compiler.BfvOperationWitness','Compiler.BfvRescaleSound','Compiler.BfvRescaleWitness',
 'Compiler.BfvRescaleAssertionShare','Compiler.DirectedRnsExhibits','Compiler.DirectedRnsEmit',
 'Compiler.NonlinearRnsPublicSound','Compiler.TfheInitialRotation','Compiler.BfvQueryWitness','Compiler.BfvQueryTeeth']
umbrella='/-\nCompiler-derived FHE arithmetic entry points.\n\nThese imports expose source integer soundness, witness exhibits and the existing\nemitter refinements. They do not establish native library/JSON/proof-backend\nrefinement or complete encrypted-inference / programmable-bootstrapping security.\n-/\n'+''.join('import '+name+'\n' for name in leaves)
files['Compiler/FheArithmetic.lean']=umbrella.encode()
records['Compiler/FheArithmetic.lean']={'source':'new integration glue','sha256':sha(umbrella.encode()),'group':'integration'}
base_umbrella=subprocess.check_output(['git','show',f'{BASE}:Compiler.lean'],cwd=MAIN)
anchor=next(line for line in base_umbrella.decode().splitlines(keepends=True) if line.startswith('import Compiler.AirModularView '))
hook='import Compiler.FheArithmetic  -- BFV linear/query/directed-rescale and TFHE modulus-switch/initial-rotation arithmetic; native/cryptographic refinements remain explicit\n'
updated=base_umbrella.decode().replace(anchor,anchor+hook)
assert updated!=base_umbrella.decode()
files['Compiler.lean']=updated.encode()
records['Compiler.lean']={'source':f'git:{BASE}:Compiler.lean plus one import','base_sha256':sha(base_umbrella),'sha256':sha(updated.encode()),'group':'integration'}
# Dependency order also ensures every selected Compiler source is reachable.
graph={rel:[m.replace('.','/')+'.lean' for m in imports(data) if m.startswith('Compiler.') and m.replace('.','/')+'.lean' in files] for rel,data in files.items()}
order=[];active=set();done=set()
def visit(rel):
 if rel in done:return
 assert rel not in active,('cycle',rel);active.add(rel)
 for dep in graph[rel]:visit(dep)
 active.remove(rel);done.add(rel);order.append(rel)
visit('Compiler/FheArithmetic.lean')
assert all(rel in done for rel in files if rel.startswith('Compiler/')),sorted(set(files)-done)
module_order=order.copy()
for rel in sorted(files):visit(rel)
tree=ROOT/'proposal';tree.mkdir(exist_ok=False)
for rel,data in files.items():(tree/rel).parent.mkdir(parents=True,exist_ok=True);(tree/rel).write_bytes(data)
patch=[]
for rel in sorted(files):
 old=base_umbrella.decode() if rel=='Compiler.lean' else ''
 assert rel=='Compiler.lean' or rel not in tracked,(rel,'would replace existing base source')
 patch.append(f'diff --git a/{rel} b/{rel}\n')
 if rel!='Compiler.lean':patch.append('new file mode 100644\n')
 patch.extend(difflib.unified_diff(old.splitlines(keepends=True),files[rel].decode().splitlines(keepends=True),fromfile=f'a/{rel}' if rel=='Compiler.lean' else '/dev/null',tofile=f'b/{rel}',n=2))
(ROOT/'minidregg-fhe-arithmetic.patch').write_text(''.join(patch))
metadata={'base_commit':BASE,'files':records,'module_dependency_order':module_order,'all_file_order':order,
 'base_direct_dependencies':base_dependencies,'retained_completed_module_evidence':evidence,
 'exporter_resolution':'EmitBfvRescale.lean is the completed assertion-sharing replacement, not the earlier unspecialized exporter.',
 'excluded':['ongoing rescale_compiler_successor','proof_frontier work','runtime crates and generated traces/proofs','old Checks runners and experiment-only probes'],
 'new_glue':['Compiler/FheArithmetic.lean','Compiler.lean one import'],
 'patch_sha256':sha((ROOT/'minidregg-fhe-arithmetic.patch').read_bytes())}
(ROOT/'PROVENANCE.json').write_text(json.dumps(metadata,indent=2)+'\n')
(ROOT/'BUILD_ORDER.txt').write_text('\n'.join(rel.removesuffix('.lean').replace('/','.') for rel in module_order)+'\n')
print(json.dumps({'files':len(files),'compiler_modules':len(module_order),'required_predecessors':sum(r['group']=='required predecessor' for r in records.values()),'exporters':sum(rel.startswith('Emit') for rel in files),'patch_sha256':metadata['patch_sha256']},indent=2))
