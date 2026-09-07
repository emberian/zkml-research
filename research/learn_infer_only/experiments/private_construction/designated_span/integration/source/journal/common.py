"""Public encodings, Ed25519 role credentials, strict immutable blobs and designated DDH CLI."""
from __future__ import annotations
import base64,hashlib,json,os,re,socket,subprocess,tempfile,time
from pathlib import Path
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey,Ed25519PublicKey

class Refusal(Exception):pass

def require(condition,reason):
 if not condition:raise Refusal(reason)
def canonical(obj):return json.dumps(obj,sort_keys=True,separators=(',',':'),ensure_ascii=True,allow_nan=False).encode()
def sha(data):return hashlib.sha256(data).hexdigest()
def digest(obj):return sha(canonical(obj))
def parse_json(raw):
 def pairs(items):
  out={}
  for key,value in items:
   require(key not in out,'duplicateJSONKey');out[key]=value
  return out
 def non_integer(value):raise Refusal('nonIntegerJSONNumber')
 return json.loads(raw,object_pairs_hook=pairs,parse_float=non_integer,parse_constant=non_integer)
def read_json(path):return parse_json(Path(path).read_bytes())
def exact_keys(obj,keys,reason='schemaFields'):
 require(isinstance(obj,dict) and set(obj)==set(keys),reason)
def integer(value):return isinstance(value,int) and not isinstance(value,bool)
def fsync_directory(path):
 fd=os.open(path,os.O_RDONLY)
 try:os.fsync(fd)
 finally:os.close(fd)
def atomic_write(path,data,private=False):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
 fd,temp=tempfile.mkstemp(prefix='.write-',dir=path.parent)
 try:
  os.fchmod(fd,0o600 if private else 0o644)
  with os.fdopen(fd,'wb') as out:out.write(data);out.flush();os.fsync(out.fileno())
  os.replace(temp,path);fsync_directory(path.parent)
 finally:
  if os.path.exists(temp):os.unlink(temp)
def write_json(path,obj,private=False):atomic_write(path,canonical(obj)+b'\n',private)
def create_signing_key(path):
 key=Ed25519PrivateKey.generate();atomic_write(path,key.private_bytes_raw(),True)
 return key.public_key().public_bytes_raw().hex()
def sign(payload,key_path,domain):
 key=Ed25519PrivateKey.from_private_bytes(Path(key_path).read_bytes())
 message=canonical({'domain':domain,'payload':payload})
 return {'domain':domain,'payload':payload,'signature':base64.b64encode(key.sign(message)).decode()}
def verify(signed,public_hex,domain):
 exact_keys(signed,['domain','payload','signature'],'signatureEnvelopeFields')
 require(signed['domain']==domain,'signatureDomain')
 try:
  key=Ed25519PublicKey.from_public_bytes(bytes.fromhex(public_hex))
  key.verify(base64.b64decode(signed['signature'],validate=True),canonical({'domain':domain,'payload':signed['payload']}))
 except Exception:raise Refusal('invalidSignature') from None
 return signed['payload']
def checked_genesis(genesis):
 require(genesis['schema']=='resident-genesis-v1','genesisSchema')
 return digest(genesis)
def load_genesis(config):
 genesis=read_json(config['genesis_path']);require(digest(genesis)==config['genesis_sha256'],'pinnedGenesis')
 for name,expected in genesis['journal_sources'].items():require(sha((Path(__file__).resolve().parent/name).read_bytes())==expected,'journalSourceChanged:'+name)
 return genesis
def identity_fields(genesis):
 return {'genesis':checked_genesis(genesis),'params_id':genesis['crypto']['params_id'],
  'program_id':genesis['crypto']['program_id'],'program_version':1,'key_id':genesis['key_id'],
  'public_key_sha256':genesis['public_key_sha256'],'context_id':genesis['context_id']}
def rpc(address,obj,timeout=300):
 with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
  s.settimeout(timeout);s.connect(str(address));s.sendall(canonical(obj)+b'\n')
  with s.makefile('rb') as inp:line=inp.readline(2_000_001)
  if not line:raise EOFError('peer exited before reply')
  require(len(line)<=2_000_000,'responseSize')
  return parse_json(line)

class Crypto:
 def __init__(self,config,role,log=None):
  self.config=config
  self.binary=Path(config['crypto_binary']);self.expected=config['crypto_binary_sha256'];self.role=role;self.log=Path(log) if log else None
 def run(self,command,private_output=False,**kwargs):
  require(sha(self.binary.read_bytes())==self.expected,'cryptoBinaryChanged')
  for name,expected in self.config.get('crypto_sources',{}).items():require(sha((self.binary.parent/name).read_bytes())==expected,'cryptoSourceChanged:'+name)
  native=self.config.get('native_dependency')
  if native:require(sha(Path(native['path']).read_bytes())==native['sha256'],'nativeDependencyChanged')
  argv=[str(self.binary),command]
  if command not in ['params','keygen']:
   context=Path(self.config['crypto_context']);require(sha(context.read_bytes())==self.config['crypto_context_sha256'],'contextChanged')
   argv.extend(['--context',str(context)])
   if command!='validate-context':argv.extend(['--validated-context-sha256',self.config['crypto_context_sha256']])
  for key,value in kwargs.items():
   if value is not None:argv.extend(['--'+key.replace('_','-'),str(value)])
  start=time.perf_counter_ns();out=subprocess.run(argv,capture_output=True,timeout=300)
  elapsed=time.perf_counter_ns()-start
  # Reader scalar output is never written to a public command log.
  record={'role':self.role,'command':argv,'elapsed_ns':None if private_output else elapsed,'exit_code':out.returncode,
   'stdout':None if private_output else out.stdout.decode(),'stderr':None if private_output else out.stderr.decode(),
   'private_output_omitted':private_output}
  if self.log:
   self.log.parent.mkdir(parents=True,exist_ok=True)
   with self.log.open('ab') as sink:sink.write(canonical(record)+b'\n')
  require(out.returncode==0,'cryptoRejected:'+command)
  try:return json.loads(out.stdout)
  except Exception:raise Refusal('cryptoOutputSchema') from None

class CAS:
 def __init__(self,root,genesis,crypto):
  self.root=Path(root);self.root.mkdir(parents=True,exist_ok=True);self.genesis=genesis;self.crypto=crypto;self.inspected={}
 def path(self,hexdigest):
  require(isinstance(hexdigest,str) and re.fullmatch('[0-9a-f]{64}',hexdigest),'blobDigestSyntax')
  return self.root/hexdigest
 def get(self,hexdigest,kind='ct'):
  path=self.path(hexdigest);require(path.is_file(),'missingBlob')
  data=path.read_bytes();require(sha(data)==hexdigest,'blobDigestMismatch')
  if kind=='ct':
   if hexdigest not in self.inspected:
    meta=self.crypto.run('inspect',ct=path)
    require(meta['sha256']==hexdigest and meta['canonical'] is True,'ciphertextCanonicalIdentity')
    require(meta['params_id']==self.genesis['crypto']['params_id'] and meta['key_id']==self.genesis['key_id'],'ciphertextParamsOrKey')
    self.inspected[hexdigest]=meta
  elif kind=='query':
   query=parse_json(data)
   exact_keys(query,['schema','params_id','context_id','row_id','row_sha256','recipient_id','token_sha256','coefficients'],'queryFields')
   require(query['schema']=='resident-designated-query-v1' and query['params_id']==self.genesis['crypto']['params_id'] and query['context_id']==self.genesis['context_id'],'queryParams')
   binding=self.genesis['query_bindings'].get(hexdigest)
   require(binding is not None and all(query[k]==v for k,v in binding.items()),'designatedQueryBinding')
   q=query['coefficients'];require(isinstance(q,list) and len(q)==577 and all(integer(x) and -127<=x<=127 for x in q),'queryRange')
   require(canonical(query)==data,'queryCanonicalEncoding')
  else:raise Refusal('blobKind')
  return path
 def put(self,data,kind='ct',expected=None):
  hexdigest=sha(data);require(expected is None or expected==hexdigest,'uploadDigestMismatch')
  path=self.path(hexdigest)
  if path.exists():require(path.read_bytes()==data,'existingBlobCorrupt')
  else:atomic_write(path,data)
  self.get(hexdigest,kind)
  return hexdigest
 def import_file(self,path,kind='ct'):return self.put(Path(path).read_bytes(),kind)
 def fresh_output(self):
  # Crypto CLI intentionally refuses to overwrite different bytes.
  return self.root/('.result-'+os.urandom(12).hex())
 def finish_output(self,path):
  path=Path(path)
  try:return self.import_file(path)
  finally:
   if path.exists():path.unlink()

def initial_state(genesis):
 return {'schema':'resident-window-state-v1','params_id':genesis['crypto']['params_id'],
  'key_id':genesis['key_id'],'genesis':digest(genesis),
  'routes':{str(route):{'queue':[],'acc_ct':genesis['zero_ct_sha256'],'admissions':0} for route in genesis['routes']}}
def validate_state(state,genesis,cas):
 exact_keys(state,['schema','params_id','key_id','genesis','routes'],'stateFields')
 require(state['schema']=='resident-window-state-v1' and state['params_id']==genesis['crypto']['params_id'] and state['key_id']==genesis['key_id'] and state['genesis']==digest(genesis),'stateIdentity')
 require(set(state['routes'])=={str(x) for x in genesis['routes']},'stateRoutes')
 records=[]
 for route in state['routes'].values():
  exact_keys(route,['queue','acc_ct','admissions'],'routeStateFields')
  require(isinstance(route['queue'],list) and len(route['queue'])<=genesis['capacity'],'windowCapacity')
  require(integer(route['admissions']) and route['admissions']>=len(route['queue']),'admissionCounter')
  cas.get(route['acc_ct'])
  for entry in route['queue']:
   exact_keys(entry,['record_id','ct_sha256'],'queueEntryFields');records.append(entry['record_id']);cas.get(entry['ct_sha256'])
 require(len(records)==len(set(records)),'duplicateCurrentInput')
 return digest(state)
