from pathlib import Path
import subprocess,re,json,hashlib,tempfile,sys
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-full-ud-20260908')
owned=[
 'Theory/RSInterpolationMatrix.lean','Theory/RSInterpolationKernel.lean',
 'Selvage/FullUDStatement.lean','Selvage/FullUDTeeth.lean',
 'Selvage/FullUDInterpolation.lean','Selvage/FullUDBivariate.lean',
 'Selvage/FullUDCore.lean','Selvage/ProximityGapFullUD.lean',
 'Selvage/FullUDFriConsumer.lean','Selvage/FullUDWitnesses.lean']
dependencies=['Theory/PolynomialMatrixKernel.lean','Theory/PolynomialBivariate.lean',
 'Theory/PolynomialGluingStatement.lean','Theory/PolynomialGluing.lean']
def strip_comments(s):
 result=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2;continue
  if depth and s[i:i+2]=='-/':depth-=1;i+=2;continue
  if not depth and s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j;continue
  result.append(s[i] if not depth else ('\n' if s[i]=='\n' else ' '));i+=1
 return ''.join(result)
modules=[];parts=[]
for name in owned+dependencies:
 p=repo/name;s=p.read_text();code=strip_comments(s)
 declarations=re.findall(r'(?m)^(?:private\s+)?(?:theorem|lemma)\s+([^\s(:]+)',code)
 pins=re.findall(r'#print axioms\s+([^\s]+)',code)
 missing=[d for d in declarations if d.split('.')[-1] not in [x.split('.')[-1] for x in pins]]
 record={'path':name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(s.splitlines()),'declarations':declarations,'pins':pins,'missing_pins':missing,'owned':name in owned}
 modules.append(record)
 if missing:raise RuntimeError(record)
 if name in owned:
  dest=out/'src'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
  r=subprocess.run(['git','diff','--no-index','--','/dev/null',str(p)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  if r.returncode!=1:raise RuntimeError(r.stderr)
  patch=r.stdout.replace('a'+str(repo)+'/','a/').replace('b'+str(repo)+'/','b/')
  parts.append(patch)
patch=out/'full-ud.patch';patch.write_text(''.join(parts))
boundary=subprocess.run(['bash','scripts/check-import-boundary.sh'],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'logs/import-boundary.log').write_text(boundary.stdout)
if boundary.returncode:raise RuntimeError(boundary.stdout)
with tempfile.TemporaryDirectory(prefix='full-ud-patch-check-') as td:
 for command in [['git','init','-q'],['git','apply','--check',str(patch)],['git','apply',str(patch)]]:
  r=subprocess.run(command,cwd=td,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  if r.returncode:raise RuntimeError(r.stdout)
 for name in owned:
  assert (Path(td)/name).read_bytes()==(repo/name).read_bytes(),name
 (out/'logs/patch-apply.log').write_text('PASS: git apply --check; git apply; all ten source files byte-identical in a clean temporary tree.\n')
checks=[]
for i in range(1,15):
 f=out/'logs'/f'freeze-{i:02}.json'
 if f.exists():checks.append(json.loads(f.read_text()))
checks_complete=len(checks)==14 and all(x['exit_code']==0 and x['source_unchanged'] for x in checks)
if checks_complete:
 byname={x['command'][-1]:x['source_sha256'] for x in checks}
 checks_complete=all(byname[m['path']]==m['sha256'] for m in modules)
record={'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
 'checkout':str(repo),'owned_modules':len(owned),'owned_declarations':sum(len(m['declarations'])for m in modules if m['owned']),
 'owned_lines':sum(m['lines']for m in modules if m['owned']),
 'owned_pins':sum(len(m['pins'])for m in modules if m['owned']),
 'dependency_modules':len(dependencies),'modules':modules,
 'patch_sha256':hashlib.sha256(patch.read_bytes()).hexdigest(),
 'exact_byte_checks_complete':checks_complete,'checks':checks,
 'umbrella_imports_proposed':['Selvage.FullUDFriConsumer','Selvage.FullUDWitnesses'],
 'source_arklib_commit':'22dbd4e836c15a21f68889afa69b7130da04abbb',
 'all_pins_standard_only':'Each guard requires exactly propext, Classical.choice, Quot.sound; see final Lean checks.',
 'external_queries_added_during_formalization':0}
(out/'manifest.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items()if k not in ['modules','checks']},indent=2))
if '--require-complete' in sys.argv and not checks_complete:sys.exit(2)
