from pathlib import Path
import json, re, hashlib
root=Path('/Users/ember/src/ArkLib-2026-09')
start='ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding'
seen={}; external=set()
def visit(mod):
 if mod in seen:return
 path=root/(mod.replace('.','/')+'.lean')
 if not path.exists():external.add(mod);return
 text=path.read_text()
 imports=re.findall(r'^import\s+([\w.]+)',text,re.M)
 seen[mod]={'path':str(path),'lines':len(text.splitlines()),'sha256':hashlib.sha256(text.encode()).hexdigest(),'imports':imports}
 for imp in imports:
  if imp.startswith('ArkLib.'):visit(imp)
  else:external.add(imp)
visit(start)
result={'root':str(root),'start':start,'modules':seen,'external_imports':sorted(external)}
Path('research/proof_frontier/2026-09-08/evidence/source-closure.json').write_text(json.dumps(result,indent=2)+'\n')
print('ArkLib source import closure:',len(seen),'modules;',sum(x['lines'] for x in seen.values()),'lines')
print('external non-Mathlib imports:',[x for x in sorted(external) if not x.startswith('Mathlib.')])
for m,v in seen.items():
 if any(s in m for s in ('AffineLines','BerlekampWelch','Polishchuk','Polynomial.Bivariate')):
  print(v['lines'],m)
