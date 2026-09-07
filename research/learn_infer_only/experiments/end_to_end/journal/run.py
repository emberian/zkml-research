"""Separate-process E2E coordinator. Plain inputs/oracles stay in trusted roles."""
import argparse,copy,sqlite3,sys
from model import *
HERE=Path(__file__).resolve().parent
CRYPTO=HERE.parent/'crypto'/'target'/'release'/'resident-crypto'
UTILITY=HERE.parent/'utility'

class Run:
 def __init__(self,root,queries,binary=CRYPTO):
  self.root=Path(root).resolve();self.processes=[];self.events=[];self.calls=[];self.started=time.perf_counter_ns()
  setup=subprocess.run([sys.executable,str(HERE/'roles.py'),'setup','--root',str(self.root),'--binary',str(binary),'--queries',str(queries)],capture_output=True)
  require(setup.returncode==0,'setup:'+setup.stderr.decode()+setup.stdout.decode())
  self.g=read_json(self.root/'genesis.json');self.acfg=read_json(self.root/'.private/authority/config.json');self.rcfg=read_json(self.root/'.private/reader/config.json')
  self.hcfg=read_json(self.root/'host_config.json');self.host_cas=CAS(self.root/'host_cas',self.g,Crypto(self.hcfg,'public_transport',self.root/'commands.jsonl'))
  self.work=self.root/'work';self.work.mkdir();self.host_cas.import_file(self.root/'zero.ct')
  self.reader=self.start('reader',self.root/'.private/reader/config.json');self.authority=self.start('authority',self.root/'.private/authority/config.json')
  self.upload(self.root/'zero.ct')
  for q in sorted((self.root/'queries').glob('*.json')):self.host_cas.import_file(q,'query');self.upload(q,'query')
 def role(self,command,**kwargs):
  argv=[sys.executable,str(HERE/'roles.py'),command]
  for k,v in kwargs.items():argv.extend(['--'+k.replace('_','-'),str(v)])
  start=time.perf_counter_ns();out=subprocess.run(argv,capture_output=True,timeout=180)
  record={'role_process':command,'argv':argv,'elapsed_ns':time.perf_counter_ns()-start,'exit_code':out.returncode,'stdout':out.stdout.decode(),'stderr':out.stderr.decode()};self.calls.append(record)
  with (self.root/'role_calls.jsonl').open('ab') as f:f.write(canonical(record)+b'\n')
  require(out.returncode==0,'roleRejected:'+command+':'+out.stdout.decode()+out.stderr.decode());return json.loads(out.stdout)
 def start(self,role,config,**options):
  cfg=read_json(config);argv=[sys.executable,str(HERE/(role+'.py')),'--config',str(config)]
  for k,v in options.items():argv.extend(['--'+k.replace('_','-'),str(v)])
  address=options.get('socket',cfg['socket']);Path(address).unlink(missing_ok=True)
  with (self.root/'server_processes.jsonl').open('ab') as log:log.write(canonical({'argv':argv,'role':role})+b'\n')
  err=open(self.root/(role+'-server.jsonl'),'ab');proc=subprocess.Popen(argv,stdout=err,stderr=err);self.processes.append(proc)
  start=time.monotonic()
  while not Path(address).exists():
   require(proc.poll() is None,'serverExited:'+role);require(time.monotonic()-start<30,'serverStartup');time.sleep(.02)
  return proc
 def stop(self,proc):
  if proc.poll() is None:proc.terminate();proc.wait(timeout=10)
 def close(self):
  for p in self.processes:self.stop(p)
  for cfg in [self.acfg,self.rcfg]:Path(cfg['socket']).unlink(missing_ok=True)
 def upload(self,path,kind='ct',address=None):
  raw=Path(path).read_bytes();reply=rpc(address or self.acfg['socket'],{'op':'put','kind':kind,'sha256':sha(raw),'data':base64.b64encode(raw).decode()});require(reply.get('ok'),'upload:'+str(reply));return sha(raw)
 def head(self):
  reply=rpc(self.acfg['socket'],{'op':'head'});require(reply.get('ok'),'head:'+str(reply));return {k:reply[k] for k in ['revision','state_digest','state']}
 def prepare(self,kind,route,event_id,vector=None,query_index=None,head=None):
  head=head or self.head();folder=self.work/event_id;folder.mkdir();write_json(folder/'head.json',head)
  if kind=='Learn':
   self.role('issue',config=self.root/'.private/issuer/config.json',head=folder/'head.json',route=route,request_id=event_id,nonce='nonce-'+event_id,record_id='record-'+event_id,vector=vector,out=folder/'issued')
   auth_path=folder/'issued/authorization.json';ct=folder/'issued/fresh.ct';self.host_cas.import_file(ct);self.upload(ct)
  else:
   query=self.root/'queries'/f'q{query_index:02d}.json';auth_path=folder/'authorization.json'
   self.role('authorize',config=self.root/'.private/command/config.json',head=folder/'head.json',route=route,request_id=event_id,nonce='nonce-'+event_id,query=query,out=auth_path)
   reply=rpc(self.rcfg['socket'],{'op':'register','authorization':read_json(auth_path),'query':base64.b64encode(query.read_bytes()).decode()});require(reply.get('ok'),'register:'+str(reply))
  self.role('propose',config=self.root/'host_config.json',head=folder/'head.json',authorization=auth_path,cas=self.root/'host_cas',out=folder/'request.json')
  req=read_json(folder/'request.json');self.upload(self.host_cas.get(req['proposal']['result_ct']))
  return req
 def submit(self,req,address=None):
  start=time.perf_counter_ns();reply=rpc(address or self.acfg['socket'],{'op':'submit','request':req});elapsed=time.perf_counter_ns()-start
  record={'request_sha256':digest(req),'request_id':req['action']['request_id'],'reply':reply,'elapsed_ns':elapsed}
  with (self.root/'events.jsonl').open('ab') as f:f.write(canonical(record)+b'\n')
  self.events.append(record);return reply
 def accepted(self,req):
  reply=self.submit(req);require(reply.get('ok'),'submit:'+str(reply))
  if req['action']['kind']=='Infer':require(reply['delivery']['status']=='acknowledged','delivery:'+str(reply))
  return reply
 def answers(self):
  # Trusted test-oracle direct read. Not exposed on host, authority, or reader RPC.
  with sqlite3.connect(self.rcfg['db']) as db:return {row[0]:json.loads(row[1])['signed_score'] for row in db.execute('SELECT request_id,answer FROM received')}
 def replay(self,recompute=False):
  exported=rpc(self.acfg['socket'],{'op':'export'});require(exported.get('ok'),'export')
  state=initial_state(self.g);revision=0;ids=set();nonces=set();records=set();acas=CAS(self.acfg['cas'],self.g,Crypto(self.acfg,'independent_public_replay',self.root/'commands.jsonl'))
  for row in exported['journal']:
   p=verify(row['envelope'],self.g['authority_vk'],'resident-authority-finalization-v1');req=p['request'];a=req['action'];check_request(req,self.g,acas)
   require(p['request_sha256']==digest(req) and p['revision']==revision+1 and a['parent_revision']==revision,'replayRevision')
   require(p['parent_state']==a['parent_state']==digest(state),'replayParent')
   require(a['request_id'] not in ids and a['nonce'] not in nonces,'replayUniqueness');ids.add(a['request_id']);nonces.add(a['nonce'])
   if a['kind']=='Learn':require(a['record_id'] not in records,'replayInputUnique');records.add(a['record_id'])
   if recompute:
    computed,delta,proposal=transition(state,a,self.g,acas);require(delta==p['delta'] and proposal==req['proposal'],'replayArithmetic')
   state=apply_delta(state,p['delta'],self.g);revision+=1
   require(validate_state(state,self.g,acas)==p['next_state']==req['proposal']['next_state'],'replayNext')
  require(revision==exported['head']['revision'] and state==exported['head']['state'],'replayInstalledHead')
  public={'schema':'resident-public-replay-v1','genesis':digest(self.g),'revision':revision,'state_digest':digest(state),'admissions':{k:v['admissions'] for k,v in state['routes'].items()},'queue_lengths':{k:len(v['queue']) for k,v in state['routes'].items()},'journal_rows':exported['journal'],'head':exported['head'],'public_recomputation':recompute}
  write_json(self.root/'replay.json',public);return {'ok':True,'revision':revision,'state_digest':digest(state),'admissions':public['admissions'],'queue_lengths':public['queue_lengths'],'public_recomputation':recompute}

def smoke(args):
 queries=Path(args.root).parent/'smoke_queries.json';vector=Path(args.root).parent/'smoke_vector.json';rawquery=Path(args.root).parent/'smoke_query_vector.json'
 write_json(vector,[1,-2,3]+[0]*574);write_json(rawquery,[2,1,0]+[0]*574);write_json(queries,[{'route':0,'path':str(rawquery.resolve())}])
 run=Run(args.root,queries)
 try:
  first=run.prepare('Learn',0,'learn-1',vector=vector);r1=run.accepted(first)
  infer=run.prepare('Infer',0,'infer-1',query_index=0);ri=run.accepted(infer)
  second=run.prepare('Learn',0,'learn-2',vector=vector);r2=run.accepted(second)
  infer2=run.prepare('Infer',0,'infer-2',query_index=0);ri2=run.accepted(infer2)
  retry=run.accepted(first);require(retry['status']=='replayed' and retry['envelope']==r1['envelope'],'historicalExactRetry')
  answers=run.answers();require(answers=={'infer-1':0,'infer-2':0},'privateOracle')
  report={'ok':True,'mixed_events':4,'learns':2,'infers':2,'distinct_fresh_ciphertexts':first['action']['fresh_ct']!=second['action']['fresh_ct'],'historical_retry':True,'oracle_comparisons':2,'oracle_all_match':True,'replay':run.replay(True),'elapsed_ns':time.perf_counter_ns()-run.started}
  write_json(run.root/'report.json',report);print(json.dumps(report))
 finally:run.close()
def main():
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['smoke']);p.add_argument('--root',required=True);a=p.parse_args();smoke(a)
if __name__=='__main__':main()
