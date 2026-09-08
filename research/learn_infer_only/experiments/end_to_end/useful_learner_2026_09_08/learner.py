#!/usr/bin/env python3
"""Continuing class prototype learner with plaintext and BFV backends."""
import argparse,contextlib,hashlib,json,os,subprocess,time,uuid
from fractions import Fraction
from pathlib import Path
HERE=Path(__file__).resolve().parent
CFG=json.loads((HERE/'config.json').read_text())
BINARY=HERE.parent/'crypto/target/release/resident-crypto'
BINARY_SHA='9c79c02e7d919ecdc24851c6f77e50ed6990397bd669f571a886f8e2b85058c2'
def save(path,value):
 path=Path(path);tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2)+'\n');os.replace(tmp,path)
def rank(scores,counts):
 eligible=[label for label in scores if counts[label]]
 ordered=sorted(eligible,key=lambda label:(-Fraction(int(scores[label]),int(counts[label])),label))
 return {'label':ordered[0] if ordered else None,'ranking':[{'label':label,'mean_dot':float(Fraction(int(scores[label]),int(counts[label]))),'sum_dot':int(scores[label]),'observations':counts[label]} for label in ordered]}
def valid(vector):
 vector=[int(x) for x in vector]
 if len(vector)!=577 or any(abs(x)>127 for x in vector):raise ValueError('Expected 577 signed coordinates in [-127,127]')
 return vector
class Learner:
 def __init__(self,directory):
  self.root=Path(directory).resolve();self.path=self.root/'learner.json';self.state=json.loads(self.path.read_text())
  if self.state['config_sha256']!=hashlib.sha256((HERE/'config.json').read_bytes()).hexdigest():raise ValueError('Feature configuration changed')
  if self.state['backend']=='bfv' and hashlib.sha256(BINARY.read_bytes()).hexdigest()!=BINARY_SHA:raise ValueError('BFV binary changed')
 @classmethod
 def create(cls,directory,backend='plain',capacity=8):
  root=Path(directory).resolve()
  if root.exists():raise ValueError('Choose a new model directory')
  if not 1<=capacity<=32:raise ValueError('Capacity must be in [1,32]')
  root.mkdir(parents=True)
  state={'version':1,'backend':backend,'capacity':capacity,'revision':0,'classes':{},'config_sha256':hashlib.sha256((HERE/'config.json').read_bytes()).hexdigest()}
  save(root/'learner.json',state);obj=cls(root)
  if backend=='bfv':
   (root/'ciphertexts').mkdir();(root/'queries').mkdir();(root/'answers').mkdir();(root/'.private').mkdir(mode=0o700)
   obj.crypto('keygen',pk=root/'public.key',sk=root/'.private/reader.key',zero=root/'zero.ct')
  return obj
 def crypto(self,command,**kwargs):
  argv=[str(BINARY),command]
  for key,val in kwargs.items():argv.extend(['--'+key.replace('_','-'),str(val)])
  t=time.perf_counter();p=subprocess.run(argv,capture_output=True,text=True,timeout=60)
  row={'command':command,'arguments':{k:str(v) for k,v in kwargs.items()},'elapsed_seconds':time.perf_counter()-t,'returncode':p.returncode}
  if p.returncode:row['stderr']=p.stderr
  else:
   result=json.loads(p.stdout)
   if command!='reader-decrypt':row['result']=result
  with (self.root/'operations.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  if p.returncode:raise RuntimeError(p.stderr)
  return result
 def teach_vector(self,label,vector):
  if not isinstance(label,str) or not label.strip():raise ValueError('Label must be nonempty')
  vector=valid(vector);state=self.state;classes=state['classes'];fresh_class=label not in classes
  entry=classes.setdefault(label,{'queue':[],'sum':[0]*577} if state['backend']=='plain' else {'queue':[],'acc':str(self.root/'zero.ct')})
  expiry=len(entry['queue'])==state['capacity'];old=entry['queue'][0] if expiry else None
  if state['backend']=='plain':
   updated=[a+b-(old[i] if old else 0) for i,(a,b) in enumerate(zip(entry['sum'],vector))]
   fresh=vector;entry['sum']=updated
  else:
   token=f'{state["revision"]+1:06d}-{uuid.uuid4().hex[:8]}'
   path=self.root/'.private'/f'input-{token}.json';path.write_text(json.dumps(vector));os.chmod(path,0o600)
   fresh=self.root/'ciphertexts'/f'input-{token}.ct';out=self.root/'ciphertexts'/f'state-{token}.ct'
   self.crypto('issuer-encrypt',pk=self.root/'public.key',vector=path,out=fresh)
   kwargs={'acc':entry['acc'],'fresh':fresh,'out':out}
   if old:kwargs['old']=old
   self.crypto('host-learn',**kwargs)
   path.unlink();fresh=str(fresh);entry['acc']=str(out)
  if expiry:entry['queue'].pop(0)
  entry['queue'].append(fresh);state['revision']+=1;save(self.path,state)
  return {'revision':state['revision'],'label':label,'new_class':fresh_class,'observations':len(entry['queue']),'expired':expiry}
 def public_query(self,vector,query_id=None):
  if self.state['backend']!='bfv':raise ValueError('Public encrypted query requires BFV backend')
  vector=valid(vector);token=query_id or uuid.uuid4().hex
  if '/' in token or token in ['.','..']:raise ValueError('Invalid query id')
  vec=self.root/'queries'/f'{token}.vector.json';query=self.root/'queries'/f'{token}.query.json'
  vec.write_text(json.dumps(vector));self.crypto('encode-query',vector=vec,out=query)
  outputs={}
  for i,(label,entry) in enumerate(sorted(self.state['classes'].items())):
   out=self.root/'answers'/f'{token}-{i:03}.ct'
   self.crypto('host-infer',acc=entry['acc'],query=query,out=out);outputs[label]=str(out)
  ticket={'revision':self.state['revision'],'outputs':outputs,'counts':{l:len(e['queue']) for l,e in self.state['classes'].items()}}
  save(self.root/'answers'/f'{token}.json',ticket);return ticket
 def receive(self,ticket):
  scores={l:self.crypto('reader-decrypt',sk=self.root/'.private/reader.key',ct=p)['signed_score'] for l,p in ticket['outputs'].items()}
  return dict(rank(scores,ticket['counts']),revision=ticket['revision'])
 def query_vector(self,vector):
  vector=valid(vector)
  if self.state['backend']=='bfv':return self.receive(self.public_query(vector))
  scores={l:sum(a*b for a,b in zip(e['sum'],vector)) for l,e in self.state['classes'].items()}
  return dict(rank(scores,{l:len(e['queue']) for l,e in self.state['classes'].items()}),revision=self.state['revision'])
 def status(self):return {'backend':self.state['backend'],'revision':self.state['revision'],'capacity':self.state['capacity'],'classes':{l:len(e['queue']) for l,e in self.state['classes'].items()}}
def main():
 p=argparse.ArgumentParser(description='Teach a label and ask which learned class a text resembles.')
 sub=p.add_subparsers(dest='command',required=True)
 init=sub.add_parser('init');init.add_argument('directory');init.add_argument('--backend',choices=['plain','bfv'],default='plain');init.add_argument('--capacity',type=int,default=8)
 for cmd in ['teach','query','status']:
  s=sub.add_parser(cmd);s.add_argument('directory')
  if cmd!='status':s.add_argument('--text',required=True)
  if cmd=='teach':s.add_argument('--label',required=True)
 a=p.parse_args()
 if a.command=='init':answer=Learner.create(a.directory,a.backend,a.capacity).status()
 else:
  learner=Learner(a.directory)
  if a.command=='status':answer=learner.status()
  else:
   from encoder import Encoder
   with contextlib.redirect_stdout(__import__('sys').stderr):vector=Encoder().encode([a.text])[0]
   answer=learner.teach_vector(a.label,vector) if a.command=='teach' else learner.query_vector(vector)
 print(json.dumps(answer,indent=2))
if __name__=='__main__':main()
