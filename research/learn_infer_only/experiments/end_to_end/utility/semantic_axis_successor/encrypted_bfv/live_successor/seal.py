"""Seal retained public artifacts without private reads or any runtime execution."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 files={}
 for p in sorted(ROOT.rglob('*')):
  if not p.is_file():continue
  rel=p.relative_to(ROOT)
  if any(x in rel.parts for x in ['runtime','__pycache__']) or rel.as_posix()=='manifest.json':continue
  files[rel.as_posix()]={'bytes':p.stat().st_size,'sha256':sha(p)}
 out={'scope':'One fresh-text illustration, actual model/BFV; public and private phase claims are in reports, full key retained',
      'freeze_sha256':sha(ROOT/'freeze.json'),'files':files,'file_count':len(files)}
 (ROOT/'manifest.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 for p,r in files.items():assert sha(ROOT/p)==r['sha256']
 print(json.dumps({'files':len(files),'manifest_sha256':sha(ROOT/'manifest.json')}))
if __name__=='__main__':main()
