"""Compact public evidence; never archive private keys, vectors, or reader DBs."""
import argparse,gzip,hashlib,json,tarfile
from common import *
HERE=Path(__file__).resolve().parent

def package(root):
 root=Path(root).resolve();out=root/'public_evidence';out.mkdir(exist_ok=True)
 inventory=[];compressed=[];omitted=[]
 for p in sorted(root.rglob('*')):
  if not p.is_file() or '.private' in p.relative_to(root).parts or 'public_evidence' in p.relative_to(root).parts:continue
  rel=str(p.relative_to(root))
  if 'work' in p.relative_to(root).parts or 'host_cas' in p.relative_to(root).parts:continue
  if 'cas' in p.relative_to(root).parts or '.sqlite3' in p.name:
   inventory.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())});continue
  if p.name in ['commands.jsonl','role_calls.jsonl','events.jsonl','replay.json','authority-server.jsonl','reader-server.jsonl','server_processes.jsonl']:
   target=out/(rel.replace('/','__')+'.gz');raw=p.read_bytes()
   with target.open('wb') as sink:
    with gzip.GzipFile(filename='',mode='wb',fileobj=sink,mtime=0) as zipped:zipped.write(raw)
   compressed.append({'source':rel,'source_bytes':len(raw),'source_sha256':sha(raw),'archive':target.name,'archive_bytes':target.stat().st_size,'archive_sha256':sha(target.read_bytes())})
 bundle=out/'complete_logs.tar.gz'
 with tarfile.open(bundle,'w:gz') as archive:
  for item in compressed:archive.add(out/item['archive'],arcname=item['archive'])
 # Complete signed packet is representative public output; scalar answers remain private.
 packets=[]
 for p in sorted(root.rglob('events.jsonl')):
  if '.private' in p.parts:continue
  for line in p.read_bytes().splitlines():
   row=json.loads(line);env=row.get('reply',{}).get('envelope')
   if env and env['payload']['request']['action']['kind']=='Infer':packets.append(env);break
  if len(packets)>=2:break
 write_json(out/'representative_finalized_infer.json',packets)
 write_json(out/'runtime_hash_inventory.json',inventory)
 result={'schema':'resident-public-evidence-v1','root':str(root),'compressed_complete_logs':compressed,'complete_logs_bundle':{'path':bundle.name,'bytes':bundle.stat().st_size,'sha256':sha(bundle.read_bytes())},'runtime_inventory_entries':len(inventory),'runtime_bytes':sum(x['bytes'] for x in inventory),
  'runtime_files_retained_ignored':True,'private_files_excluded':True,'scope':'No private keys/vectors/scalars or hashes of private files. Public CAS/database hashes retain exact local evidence identity; ignored bytes remain locally available. OS-random reruns reproduce behavior, not the same ciphertext bytes.'}
 write_json(out/'manifest.json',result);return {'root':str(root),'compressed_files':len(compressed),'public_runtime_hashes':len(inventory),'compressed_bytes':sum(x['archive_bytes'] for x in compressed)}
def main():
 p=argparse.ArgumentParser();p.add_argument('roots',nargs='+');a=p.parse_args()
 for root in a.roots:print(json.dumps(package(root)))
if __name__=='__main__':main()
