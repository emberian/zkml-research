#!/usr/bin/env python3
"""Read-only local source hashes/extraction equivalence; no cryptography/network."""
import hashlib, json, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')

def sha(data):
    return hashlib.sha256(data).hexdigest()

out = {'scope':'local primary-source provenance only; no crypto execution',
       'source_rows':[], 'artifact_hashes':{}}
for ident in ['2013-727','2024-740','2021-1324','2025-045','2024-1477']:
    year, number = ident.split('-')
    pdf = MIRROR/year/(number+'.pdf')
    txt = ROOT/'extracts'/(ident+'.txt')
    saved = txt.read_bytes()
    attempts=[]
    matched=None
    for options in [['-layout'], []]:
        cmd=['pdftotext',*options,str(pdf),'-']
        p=subprocess.run(cmd,check=True,capture_output=True)
        ok=p.stdout==saved
        attempts.append({'command':cmd,'exit_code':p.returncode,
                         'stdout_sha256':sha(p.stdout),'matches_saved_text':ok,
                         'stderr':p.stderr.decode()})
        if ok:
            matched=cmd
            break
    assert matched is not None, ident+' saved extraction mismatch'
    out['source_rows'].append({'id':ident.replace('-','/'),
         'pdf_absolute_path':str(pdf),'pdf_sha256':sha(pdf.read_bytes()),
         'text_relative_path':str(txt.relative_to(ROOT)),
         'text_sha256':sha(saved),'extraction_attempts':attempts})
for p in sorted([*ROOT.glob('notes/*.md'),*ROOT.glob('searches/*.json'),Path(__file__) ]):
    out['artifact_hashes'][str(p.relative_to(ROOT))]=sha(p.read_bytes())
out['all_source_extractions_match']=True
(ROOT/'notes'/'SOURCE_MANIFEST.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
