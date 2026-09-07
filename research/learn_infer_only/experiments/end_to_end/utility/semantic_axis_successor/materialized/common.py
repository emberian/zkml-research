"""Public fixture serialization and parent-byte preservation helpers."""
import hashlib,json,os,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent;PARENT=ROOT.parent
load=lambda p:json.loads(Path(p).read_text())
def save(path,value,compact=False):
 Path(path).write_text(json.dumps(value,sort_keys=True,separators=(',',':') if compact else None,indent=None if compact else 2)+'\n')
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def vector_bytes(v):return (json.dumps(v,separators=(',',':'))+'\n').encode()
def vector_sha(v):return hashlib.sha256(vector_bytes(v)).hexdigest()
def signed_bytes_sha(v):return hashlib.sha256(bytes(x%256 for x in v)).hexdigest()
def verify_parent():
 manifest=load(PARENT/'manifest.json')
 for name,row in manifest['files'].items():assert sha(PARENT/name)==row['sha256'],name
 return len(manifest['files'])
def verify():
 for path,digest in load(ROOT/'freeze.json')['source_sha256'].items():assert sha(path)==digest,path
 return verify_parent()
def onehot(route,a,b):
 assert route in [0,1] and a in [0,1] and b in [0,1]
 v=[0]*577;v[4*route+2*a+b]=127;return v
def role_json(path,value):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
 descriptor=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
 with os.fdopen(descriptor,'w') as f:json.dump(value,f,separators=(',',':'));f.write('\n')
 os.chmod(path,0o600)
