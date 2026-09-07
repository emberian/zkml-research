"""Retain a non-runtime artifact census; raw role files have their own census."""
import sys
sys.dont_write_bytecode=True
from common import *
def main():
 assert not (ROOT/'manifest.json').exists();verify();assert load(ROOT/'audit.json')['passed']
 emission=load(ROOT/'emit_runtime.stdout');assert emission['passed'] and emission['existing_files_byte_verified']==402
 files={}
 for p in sorted(ROOT.rglob('*')):
  if not p.is_file():continue
  relative=p.relative_to(ROOT)
  if relative.parts[0] in ['runtime','__pycache__'] or p.name=='manifest.json':continue
  files[str(relative)]={'sha256':sha(p),'bytes':p.stat().st_size}
 save(ROOT/'manifest.json',{'files':files,'retained_file_count':len(files),
  'derived_runtime_census_sha256':sha(ROOT/'runtime_hash_census.json'),'fixture_sha256':sha(ROOT/'fixture.json'),
  'scope':'PUBLIC deterministic consistency subset; no new utility estimate or crypto/model execution',
  'parent_entries_preserved':verify_parent()})
 print(json.dumps({'retained_files':len(files),'retained_bytes':sum(x['bytes'] for x in files.values()),
  'manifest_sha256':sha(ROOT/'manifest.json'),'readme_sha256':sha(ROOT/'README.md'),'fixture_sha256':sha(ROOT/'fixture.json')},indent=2))
if __name__=='__main__':main()
