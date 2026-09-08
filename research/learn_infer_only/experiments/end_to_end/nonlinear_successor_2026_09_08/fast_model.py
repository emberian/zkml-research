"""Cache the public BFV evaluation key across Learn/Infer requests."""
import json,os,subprocess,time
from model import Model,HERE
HOST=HERE/'crypto/target/release/kernel-crypto-cached'
class FastModel(Model):
 def __init__(self,directory):super().__init__(directory);self.host=None;self.host_stderr=None
 def _start(self):
  if self.host is not None:return
  self.host_stderr=(self.root/'cached_host.stderr').open('a')
  self.host=subprocess.Popen([str(HOST),'serve','--dir',str(self.root)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=self.host_stderr,text=True,bufsize=1,env=dict(os.environ,RAYON_NUM_THREADS='1'))
  line=self.host.stdout.readline()
  if not line or not json.loads(line).get('ready'):raise RuntimeError('Public host did not become ready')
 def crypto(self,command,**kwargs):
  if command not in ['learn','infer']:return super().crypto(command,**kwargs)
  start=time.perf_counter();self._start();request={'command':command,'arguments':{k:str(v) for k,v in kwargs.items()}}
  self.host.stdin.write(json.dumps(request)+'\n');self.host.stdin.flush();line=self.host.stdout.readline()
  if not line:raise RuntimeError('Public host closed')
  response=json.loads(line);row={'command':command,'arguments':request['arguments'],'cached_public_host':True,'elapsed_seconds':time.perf_counter()-start,'returncode':0 if response['ok'] else 2}
  if response['ok']:row['result']=response['result']
  else:row['error']=response['error']
  with (self.root/'operations.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  if not response['ok']:raise RuntimeError(response['error'])
  return response['result']
 def close(self):
  if self.host is not None:
   try:self.host.stdin.close()
   except BrokenPipeError:pass
   try:self.host.wait(timeout=10)
   except subprocess.TimeoutExpired:
    self.host.terminate()
    try:self.host.wait(timeout=5)
    except subprocess.TimeoutExpired:self.host.kill();self.host.wait()
   self.host.stdout.close();self.host_stderr.close();self.host=None
