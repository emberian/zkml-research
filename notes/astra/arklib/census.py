#!/usr/bin/env python3
"""Pinned-source lexical census; does not claim a fresh kernel axiom sweep.
Usage: python3 notes/astra/arklib/census.py /Users/ember/src/ArkLib-latest
The upstream scanner supplies its tested nested-comment/string masker. All files
are read from Git, so untracked files and installed dependencies are out of scope.
"""
import collections, csv, importlib.util, json, pathlib, re, subprocess, sys
root=pathlib.Path(sys.argv[1]).resolve()
out=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('arklib_trust_scanner',root/'scripts/source-trust-audit.py')
scanner=importlib.util.module_from_spec(spec);sys.modules[spec.name]=scanner;spec.loader.exec_module(scanner)
def git(*args): return subprocess.check_output(['git','-C',str(root),*args],text=True)
patterns={k:re.compile(r'(?<![`.\w\'])'+k+r'(?![\w\'])') for k in ['sorry','axiom','native_decide','opaque','implemented_by','unsafe']}
patterns['maxHeartbeats']=re.compile(r'\bset_option\s+maxHeartbeats\s+(\d+)')
paths=[p for p in git('ls-files','*.lean').splitlines()]
rows=[]; occurrences=[]; bydir={}
for path in paths:
 text=git('show','HEAD:'+path);clean=scanner.mask_noncode(text)
 row={'path':path,'lines':len(text.splitlines())}
 for kind,pattern in patterns.items():
  matches=list(pattern.finditer(clean)); row[kind]=len(matches)
  for m in matches:
   line=clean.count('\n',0,m.start())+1
   occurrences.append({'path':path,'line':line,'kind':kind,'source':text.splitlines()[line-1]})
 rows.append(row)
 directory=str(pathlib.PurePosixPath(path).parent)
 if directory not in bydir:bydir[directory]=collections.Counter()
 bydir[directory].update({k:v for k,v in row.items() if k!='path'});bydir[directory]['files']+=1
fields=['path','lines',*patterns]
with (out/'census-files.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(rows)
with (out/'census-directories.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=['directory','files','lines',*patterns]);w.writeheader()
 for directory,count in sorted(bydir.items()):w.writerow({'directory':directory,**count})
(out/'census-occurrences.json').write_text(json.dumps(occurrences,indent=2)+'\n')
scopes={}
for scope in ['ArkLib/','ArkLibTest/','scripts/','blueprint/']:
 selected=[r for r in rows if r['path'].startswith(scope)]
 scopes[scope]={'files':len(selected),**{k:sum(r[k] for r in selected) for k in ['lines',*patterns]}}
production=[o for o in occurrences if o['path'].startswith('ArkLib/')]
summary={'command':'python3 notes/astra/arklib/census.py '+str(root),'head':git('rev-parse','HEAD').strip(),'origin_main':git('rev-parse','origin/main').strip(),'scopes':scopes,'production_occurrences':production,'maxHeartbeats_values':dict(collections.Counter(o['source'].strip() for o in production if o['kind']=='maxHeartbeats'))}
(out/'census-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['production_occurrences','maxHeartbeats_values']},indent=2))
print('Production occurrences:')
for o in production: print(f"{o['path']}:{o['line']}: {o['kind']}: {o['source'].strip()}")
