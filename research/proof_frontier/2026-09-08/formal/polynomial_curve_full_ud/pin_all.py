from pathlib import Path
import json,re,subprocess,importlib.util,sys
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-polynomial-curve-full-ud-20260908')
checker=Path('/Users/ember/dev/zkml-research/research/learn_infer_only/experiments/integration/check_all_formal.py')
spec=importlib.util.spec_from_file_location('root_census',checker);c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
mods=json.loads((out/'declaration-names.json').read_text())
for mod in mods:
 p=repo/Path(mod.replace('.','/')+'.lean')
 names=c.qualified_declarations(c.stripped_lean(p.read_text()))
 mods[mod]=[n['qualified_name']for n in names]
(out/'declaration-names.json').write_text(json.dumps(mods,indent=2)+'\n')
for i,(mod,names) in enumerate(mods.items(),1):
 p=repo/Path(mod.replace('.','/')+'.lean')
 s=p.read_text()
 if '#guard_msgs' in s:
  print('already guarded',mod,flush=True)
  continue
 if '#print axioms' in s:
  s=s[:s.index('\n#print axioms')]+'\n'
 p.write_text(s+'\n'+''.join('#print axioms '+n+'\n'for n in names))
 r=subprocess.run([sys.executable,str(out/'run_lean.py'),str(p.relative_to(repo)),f'axioms-{i:02d}'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print(mod,r.returncode,flush=True)
 if r.returncode:print(r.stdout,flush=True);sys.exit(1)
 log=(out/'checks'/f'axioms-{i:02d}.log').read_text()
 pattern=r"'([^']+)' (depends on axioms: \[([^]]*)\]|does not depend on any axioms)"
 found=list(re.finditer(pattern,log,re.S))
 assert len(found)==len(names),(mod,len(found),len(names),log)
 assert not re.sub(pattern,'',log,flags=re.S).strip(),log
 messages={}
 for n in names:
  matching=[m for m in found if m.group(1)==n or re.fullmatch(r'_private\.'+re.escape(mod)+r'\.\d+\.'+re.escape(n),m.group(1))]
  assert len(matching)==1,(mod,n,[m.group(1)for m in found])
  messages[n]=' '.join(matching[0].group(0).split())
 p.write_text(s+'\n'+''.join('/-- info: '+messages[n]+' -/\n#guard_msgs (whitespace := lax) in\n#print axioms '+n+'\n\n'for n in names))
 print('guarded',len(names),flush=True)
