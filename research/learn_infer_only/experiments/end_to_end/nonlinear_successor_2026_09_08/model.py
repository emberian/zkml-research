#!/usr/bin/env python3
"""Continuing nonlinear text-kernel classifier with an actual BFV backend."""
import argparse,contextlib,hashlib,json,os,subprocess,sys,time,uuid
from fractions import Fraction
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent;OLD=HERE.parent/'useful_learner_2026_09_08';BINARY=HERE/'crypto/target/release/kernel-crypto'
CFG=json.loads((HERE/'config.json').read_text())
sys.path.insert(0,str(OLD))
from encoder import Encoder

def save(path,value):
 path=Path(path);tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2)+'\n');os.replace(tmp,path)
def transform(v):
 a=np.rint(np.asarray(v,dtype=np.float64)[...,:576]/4).astype(np.int64)
 assert np.max(abs(a))<=32 and np.all(np.sum(a*a,axis=-1)<=20000)
 return a
def encode(text):
 encoder=Encoder(cache=HERE/'feature_cache');old=OLD/'feature_cache'/(encoder.key(text)+'.json')
 if old.exists():return transform(json.loads(old.read_text())['vector'])
 with contextlib.redirect_stdout(sys.stderr):return transform(encoder.encode([text])[0])
def rank(scores,counts):
 order=sorted(scores,key=lambda label:(-Fraction(int(scores[label]),int(counts[label])),label))
 return {'label':order[0] if order else None,'ranking':[{'label':l,'sum_kernel':int(scores[l]),'observations':counts[l],'mean_kernel':float(Fraction(int(scores[l]),int(counts[l])))} for l in order]}
class Model:
 def __init__(self,directory):
  self.root=Path(directory).resolve();self.state=json.loads((self.root/'model.json').read_text())
  if self.state['config_sha256']!=hashlib.sha256((HERE/'config.json').read_bytes()).hexdigest():raise ValueError('Configuration changed')
 @classmethod
 def create(cls,directory,backend):
  root=Path(directory).resolve();root.mkdir(parents=True)
  if (root/'model.json').exists():raise ValueError('Model exists')
  save(root/'model.json',{'backend':backend,'revision':0,'classes':{},'config_sha256':hashlib.sha256((HERE/'config.json').read_bytes()).hexdigest()})
  m=cls(root)
  if backend=='bfv':
   for name in ['ciphertexts','queries','answers','trace']:(root/name).mkdir()
   m.crypto('keygen',dir=root)
  return m
 def crypto(self,command,**kwargs):
  argv=[str(BINARY),command]
  for k,v in kwargs.items():argv.extend(['--'+k,str(v)])
  start=time.perf_counter();p=subprocess.run(argv,capture_output=True,text=True,timeout=120)
  row={'command':command,'arguments':{k:str(v) for k,v in kwargs.items()},'returncode':p.returncode,'elapsed_seconds':time.perf_counter()-start}
  if p.returncode:row['stderr']=p.stderr
  else:
   result=json.loads(p.stdout)
   if command!='read':row['result']=result
  with (self.root/'operations.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  if p.returncode:raise RuntimeError(p.stderr)
  return result
 def teach_vector(self,label,vector):
  vector=np.asarray(vector,dtype=np.int64);assert vector.shape==(576,) and np.max(abs(vector))<=32 and int(vector@vector)<=20000
  if not isinstance(label,str) or not label.strip():raise ValueError('A nonempty label is required')
  entry=self.state['classes'].setdefault(label,{'slots':[None]*8,'next_lane':0,'count':0,'acc':str(self.root/'zero.ct')})
  lane=entry['next_lane'];old=entry['slots'][lane];expired=old is not None
  if self.state['backend']=='plain':fresh=vector.tolist()
  else:
   token=f'{self.state["revision"]+1:06d}-{uuid.uuid4().hex[:8]}';path=self.root/'.private'/f'{token}.json';path.write_text(json.dumps(vector.tolist()));os.chmod(path,0o600)
   fresh=self.root/'ciphertexts'/f'input-{token}.ct';out=self.root/'ciphertexts'/f'state-{token}.ct'
   self.crypto('issue',dir=self.root,vector=path,lane=lane,out=fresh)
   kwargs={'acc':entry['acc'],'fresh':fresh,'out':out}
   if old is not None:kwargs['old']=old
   self.crypto('learn',**kwargs);path.unlink();entry['acc']=str(out);fresh=str(fresh)
  entry['slots'][lane]=fresh;entry['next_lane']=(lane+1)%8;entry['count']=min(8,entry['count']+1);self.state['revision']+=1;save(self.root/'model.json',self.state)
  return {'revision':self.state['revision'],'label':label,'active_examples':entry['count'],'replaced_lane':lane,'expired':expired}
 def public_query(self,vector,query_id=None,trace=False):
  token=query_id or uuid.uuid4().hex;query=self.root/'queries'/f'{token}.json';save(query,np.asarray(vector).tolist());outputs={}
  for i,(label,entry) in enumerate(sorted(self.state['classes'].items())):
   out=self.root/'answers'/f'{token}-{i:03}.ct';kwargs={'dir':self.root,'acc':entry['acc'],'query':query,'out':out}
   if trace and i==0:kwargs['trace']=self.root/'trace'/token
   self.crypto('infer',**kwargs);outputs[label]=str(out)
  return {'revision':self.state['revision'],'outputs':outputs,'counts':{l:e['count'] for l,e in self.state['classes'].items()}}
 def receive(self,ticket):
  scores={l:self.crypto('read',dir=self.root,ct=p)['sum_kernel'] for l,p in ticket['outputs'].items()}
  return dict(rank(scores,ticket['counts']),revision=ticket['revision'])
 def query_vector(self,vector):
  if self.state['backend']=='bfv':return self.receive(self.public_query(vector))
  scores={l:sum(int(np.asarray(v,dtype=np.int64)@vector)**2 for v in e['slots'] if v is not None) for l,e in self.state['classes'].items()}
  return dict(rank(scores,{l:e['count'] for l,e in self.state['classes'].items()}),revision=self.state['revision'])
 def status(self):return {'backend':self.state['backend'],'revision':self.state['revision'],'classes':{l:e['count'] for l,e in self.state['classes'].items()}}
def main():
 p=argparse.ArgumentParser(description='Teach and query a nonlinear degree2 text-kernel classifier.');sub=p.add_subparsers(dest='command',required=True)
 for cmd in ['init','teach','query','status']:
  s=sub.add_parser(cmd);s.add_argument('directory')
  if cmd=='init':s.add_argument('--backend',choices=['plain','bfv'],default='plain')
  if cmd in ['teach','query']:s.add_argument('--text',required=True)
  if cmd=='teach':s.add_argument('--label',required=True)
 a=p.parse_args()
 if a.command=='init':result=Model.create(a.directory,a.backend).status()
 else:
  m=Model(a.directory)
  if a.command=='status':result=m.status()
  elif a.command=='teach':result=m.teach_vector(a.label,encode(a.text))
  else:result=m.query_vector(encode(a.text))
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
