#!/usr/bin/env python3
"""Seal retained public/source artifacts only; no proof or TFHE execution."""
import collections,difflib,hashlib,json,pathlib
r=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((r/'execution_pins.json').read_text())
for x in pins['owned']+pins['read_only_dependencies']:
 p=pathlib.Path(x['path']);assert p.stat().st_size==x['bytes'] and sha(p.read_bytes())==x['sha256'],p
for name in ['signed-final-002','combined-final-002','emit-004','capture-001','prove-001','verify-001','reject-001']:
 assert json.loads((r/'results'/f'{name}.json').read_text())['exit']==0,name
p=json.loads((r/'results/proof001/proof.json').read_text());v=json.loads((r/'results/verify.json').read_text());n=json.loads((r/'results/reject_changed.json').read_text())
assert p['verified'] and v['verified'] and n['changed_level2_digit_rejected'] and n['verifier_ran']
for report in [p,v,n]:
 assert report['prefix']['rotation_verified'] and report['prefix']['modulus_switch']['verified']
 assert report['prefix']['first_nonzero_mask_row']==[0,6878,25207,394]
assert sha((r/'results/proof001/proof.bin').read_bytes())==p['proof_sha256']
assert sha((r/'artifacts/template_ir2.json').read_bytes())==p['template_sha256']
patch=''
for f in ['Compiler/TfheSignedDecomposition.lean','Compiler/TfheCmuxDecomposition.lean','EmitTfheCmuxDecomposition.lean']:
 text=(r/f).read_text();assert 'sorry' not in text and '\naxiom ' not in text
 patch+=f'diff --git a/{f} b/{f}\nnew file mode 100644\n'+''.join(difflib.unified_diff([],text.splitlines(keepends=True),fromfile='/dev/null',tofile='b/'+f))
(r/'proposal.patch').write_text(patch)
rows=json.loads((r/'fixtures/normal_001/tables.json').read_text())['output_rows']
partials=[]
for f in sorted((r/'results').glob('*-partial-trace.leu32')):partials.append({'path':str(f.relative_to(r)),'bytes':f.stat().st_size,'sha256':sha(f.read_bytes()),'proved':False})
record={'claim':'EXECUTED public-only closure','new_proof_attempts':1,'fresh_positive_runs':1,'fresh_changed_digit_runs':1,'source_pins_recorded_after_run':True,'input_files_rehashed':len(pins['owned'])+len(pins['read_only_dependencies']),'all_inputs_unchanged':True,'retained_profile':{'path':'results/export-profile.txt','bytes':(r/'results/export-profile.txt').stat().st_size,'sha256':sha((r/'results/export-profile.txt').read_bytes())},'partial_exports':partials,'delta_counts':dict(collections.Counter(str(x[4]+65536*x[5]) for x in rows)),'digit_counts':dict(collections.Counter(str((x[8]-512,x[9]-512)) for x in rows)),'patch_sha256':sha(patch.encode())}
(r/'results/closure.json').write_text(json.dumps(record,indent=2)+'\n')
files=[]
for f in sorted(r.rglob('*')):
 rel=f.relative_to(r)
 if not f.is_file() or any(x in ['target','build','__pycache__'] for x in rel.parts) or str(rel)=='MANIFEST.json' or f.name.endswith('-partial-trace.leu32') or str(rel) in ['artifacts/trace.leu32','results/export-profile.txt']:continue
 files.append({'path':str(rel),'bytes':f.stat().st_size,'sha256':sha(f.read_bytes())})
manifest={'schema':'tfhe-cmux-decomposition-package-v1','files':files,'file_count':len(files),'bytes':sum(x['bytes'] for x in files),'ignored_execution_material':'Native binary, cached Lean overlay, complete witness trace and interrupted partial traces are pinned separately in execution_pins/closure; retained locally.','scope':'First CMUX integer input and exact signed decomposition only.'}
(r/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'manifest_sha256':sha((r/'MANIFEST.json').read_bytes()),'patch_sha256':record['patch_sha256'],'files':len(files),'bytes':manifest['bytes']}))
