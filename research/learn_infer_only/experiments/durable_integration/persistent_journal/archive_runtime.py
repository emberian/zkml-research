#!/usr/bin/env python3
"""Pin/compress owned SQLite evidence; leave raw runtime files in place and ignored."""
from pathlib import Path
import hashlib,json,tarfile
E=Path(__file__).resolve().parent
files=sorted(p for p in (E/'results').rglob('*') if p.is_file() and '.sqlite3' in p.name)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inventory=[dict(path=str(p.relative_to(E)),size_bytes=p.stat().st_size,sha256=sha(p)) for p in files]
archive=E/'sqlite_evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=9) as bundle:
 for p in files:bundle.add(p,arcname=str(p.relative_to(E)),recursive=False)
assert all(sha(E/x['path'])==x['sha256'] for x in inventory)
record=dict(raw_files=inventory,raw_count=len(files),raw_bytes=sum(x['size_bytes'] for x in inventory),archive_sha256=sha(archive),archive_bytes=archive.stat().st_size,raw_files_unchanged=True,scope='Owned SQLite/WAL/SHM evidence only; raw files retained and gitignored; logical JSON snapshots/logs remain ordinary artifacts')
(E/'sqlite_evidence_inventory.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='raw_files'},indent=2))
