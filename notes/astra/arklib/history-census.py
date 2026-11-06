#!/usr/bin/env python3
"""Compare like-for-like production source tokens at fixed historical commits."""
import collections, importlib.util, io, json, pathlib, re, subprocess, sys, tarfile
sys.dont_write_bytecode=True
root=pathlib.Path('/Users/ember/src/ArkLib-latest')
spec=importlib.util.spec_from_file_location('scanner',root/'scripts/source-trust-audit.py')
s=importlib.util.module_from_spec(spec);sys.modules[spec.name]=s;spec.loader.exec_module(s)
results=[]
for rev in ['9349870','22dbd4e','4d9d67be']:
 sha=subprocess.check_output(['git','-C',str(root),'rev-parse',rev],text=True).strip()
 data=subprocess.check_output(['git','-C',str(root),'archive',sha,'ArkLib'])
 counts=collections.Counter();files=0;lines=0
 with tarfile.open(fileobj=io.BytesIO(data)) as tar:
  for member in tar:
   if not member.isfile() or not member.name.endswith('.lean'):continue
   text=tar.extractfile(member).read().decode();code=s.mask_noncode(text);files+=1;lines+=len(text.splitlines())
   for tok in ['sorry','axiom','native_decide','opaque','implemented_by']:
    counts[tok]+=len(re.findall(r'(?<![`.\w\'])'+tok+r'(?![\w\'])',code))
   counts['maxHeartbeats']+=len(re.findall(r'\bset_option\s+maxHeartbeats\s+\d+',code))
 results.append({'sha':sha,'files':files,'lines':lines,**counts})
print(json.dumps(results,indent=2))
