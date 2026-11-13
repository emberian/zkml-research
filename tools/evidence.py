#!/usr/bin/env python3
"""Restore retained experiment evidence, checking its original Git blob identity."""
import argparse,hashlib,json,lzma,os,sys,tarfile,tempfile,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def target(name):
 p=Path(name)
 if p.is_absolute() or '..' in p.parts:raise ValueError('Unsafe member path: '+name)
 result=ROOT/p
 for parent in result.parents:
  if parent==ROOT:break
  if parent.is_symlink():raise ValueError('Symlink parent: '+str(parent))
 return result
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('action',choices=['restore','verify']);p.add_argument('--only',default='',help='Original path or directory prefix');args=p.parse_args()
 catalog=json.loads((ROOT/'.evidence/catalog.json').read_text());index=ROOT/'.evidence/index.json.xz'
 if hashlib.sha256(index.read_bytes()).hexdigest()!=catalog['index_sha256']:raise ValueError('Evidence index checksum mismatch')
 entries=json.loads(lzma.decompress(index.read_bytes()));selected={e['path']:e for e in entries if not args.only or e['path']==args.only or e['path'].startswith(args.only.rstrip('/')+'/')}
 if not selected:raise ValueError('No matching retained evidence paths')
 archive=None
 payload=catalog.get('payload_commit')
 if payload:
  present=subprocess.run(['git','-C',str(ROOT),'cat-file','-e',payload+'^{commit}'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
  if present.returncode:
   print('Fetching retained evidence from origin; this explicitly downloads the evidence corpus.',file=sys.stderr)
   subprocess.run(['git','-C',str(ROOT),'fetch','--no-tags','origin',catalog['payload_ref']],check=True)
   fetched=subprocess.check_output(['git','-C',str(ROOT),'rev-parse','FETCH_HEAD'],text=True).strip()
   if fetched!=payload:raise ValueError('Fetched evidence ref does not match its pinned commit')
   subprocess.run(['git','-C',str(ROOT),'update-ref',catalog['payload_ref'],payload],check=True)
 if catalog['format']=='tar.xz':
  archive=ROOT/'.evidence'/catalog['archive'];h=hashlib.file_digest(archive.open('rb'),'sha256').hexdigest()
  if h!=catalog['archive_sha256']:raise ValueError('Archive checksum mismatch')
 counts={'restored':0,'matching':0,'missing':0}
 def accept(e,data):
  if len(data)!=e['size'] or blob(data)!=e['oid']:raise ValueError('Stored bytes mismatch: '+e['path'])
  dest=target(e['path']);exists=dest.exists() or dest.is_symlink()
  if exists:
   old=os.readlink(dest).encode() if dest.is_symlink() else dest.read_bytes()
   if blob(old)!=e['oid'] or dest.is_symlink()!=(e['mode']=='120000'):raise ValueError('Refusing to overwrite different existing file: '+e['path'])
   counts['matching']+=1;return
  if args.action=='verify':counts['missing']+=1;return
  dest.parent.mkdir(parents=True,exist_ok=True)
  # Exclusive creation: a concurrently created file is never overwritten.
  if e['mode']=='120000':os.symlink(data.decode(),dest)
  else:
   with dest.open('xb') as f:f.write(data)
   dest.chmod(0o755 if e['mode']=='100755' else 0o644)
  counts['restored']+=1
 if archive:
  seen=set()
  with tarfile.open(archive,'r:xz') as tar:
   for m in tar:
    if m.name not in selected:continue
    if m.name in seen:raise ValueError('Duplicate archive member: '+m.name)
    seen.add(m.name);data=m.linkname.encode() if m.issym() else tar.extractfile(m).read();accept(selected[m.name],data)
  if seen!=set(selected):raise ValueError('Missing archive members')
 else:
  for e in selected.values():
   raw=subprocess.check_output(['git','-C',str(ROOT),'show',payload+':'+e['object']]) if payload else (ROOT/'.evidence'/e['object']).read_bytes();data=lzma.decompress(raw) if e['object'].endswith('.xz') else raw;accept(e,data)
 print(json.dumps({'paths':len(selected),**counts}))
 if counts['missing']:raise SystemExit(1)
if __name__=='__main__':main()
