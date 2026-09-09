from pathlib import Path
import importlib.util,json,re,subprocess,sys
root=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-ir2-packed-extraction-20260908')
spec=importlib.util.spec_from_file_location('c','/Users/ember/dev/zkml-research/research/learn_infer_only/experiments/integration/check_all_formal.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
mods=sys.argv[1:]
for mod in mods:
 p=repo/(mod.replace('.','/')+'.lean');s=p.read_text()
 if '#guard_msgs' in s:continue
 names=[n['qualified_name']for n in c.qualified_declarations(c.stripped_lean(s))]
 probe=repo/'Ir2AxiomProbe.lean';probe.write_text('import '+mod+'\n'+''.join('#print axioms '+n+'\n'for n in names))
 r=subprocess.run(['lake','env','lean',str(probe)],cwd=repo,text=True,capture_output=True)
 if r.returncode:print(r.stdout,r.stderr);sys.exit(r.returncode)
 pattern=r"'([^']+)' (depends on axioms: \[([^]]*)\]|does not depend on any axioms)"
 matches=list(re.finditer(pattern,r.stdout,re.S));assert len(matches)==len(names),(names,r.stdout)
 assert not re.sub(pattern,'',r.stdout,flags=re.S).strip(),r.stdout
 p.write_text(s+'\n'+''.join('/-- info: '+' '.join(m.group(0).split())+' -/\n#guard_msgs (whitespace := lax) in\n#print axioms '+m.group(1)+'\n\n'for m in matches))
 print(mod,len(names),flush=True)
probe.unlink(missing_ok=True)
