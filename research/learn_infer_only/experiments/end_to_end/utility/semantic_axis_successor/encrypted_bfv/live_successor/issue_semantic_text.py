"""Private new text -> fixed semantic scorer -> signed encrypted contribution."""
import argparse,hashlib,json,os,shutil,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def private_json(p,x):
 fd=os.open(p,os.O_CREAT|os.O_TRUNC|os.O_WRONLY,0o600)
 with os.fdopen(fd,'w') as f:json.dump(x,f,sort_keys=True,indent=2);f.write('\n')
 os.chmod(p,0o600)
def main():
 parser=argparse.ArgumentParser()
 for name in ['input','issuer-config','head','private-workdir','out','request-id','nonce','record-id']:parser.add_argument('--'+name,required=True)
 args=parser.parse_args();data=load(args.input);freeze=load(ROOT/'freeze.json')
 assert set(data)=={'text','route','label'} and isinstance(data['text'],str)
 assert type(data['route']) is int and data['route']==0
 assert type(data['label']) is int and data['label']==1
 for p,h in freeze['public_source_dependencies'].items():assert sha(p)==h,p
 prepared=ROOT/'runtime/.private/prepared';pf=load(prepared/'freeze.json')
 assert sha(args.input)==pf['private_input_sha256'],'Use the one predeclared private text'
 work=Path(args.private_workdir).resolve();work.mkdir(parents=True,mode=0o700,exist_ok=False);os.chmod(work,0o700)
 for name in ['freeze.json','issuer_inputs.json']:
  shutil.copyfile(prepared/name,work/name);os.chmod(work/name,0o600)
 private_json(work/'input.json',data)
 env=dict(os.environ,SEMANTIC_LIVE_WORKDIR=str(work),HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
 encoder=[freeze['encoder_python'],'-B',str(ROOT/'encoder/score.py')]
 begin=time.perf_counter_ns();result=subprocess.run(encoder,env=env,capture_output=True,text=True,timeout=300)
 encoder_ns=time.perf_counter_ns()-begin
 processes=[{'stage':'actual_semantic_encoder','command':encoder,'returncode':result.returncode,'wall_ns':encoder_ns,'stdout':result.stdout,'stderr':result.stderr}]
 private_json(work/'processes.json',processes)
 if result.returncode:
  print(json.dumps({'ok':False,'stage':'semantic_encoder','private_diagnostics_retained':True}));raise SystemExit(result.returncode)
 rows=load(work/'raw_scores.json');cost=load(work/'score_results.json')
 assert len(rows)==2 and [r['axis'] for r in rows]==['a','b']
 assert cost['actual_model_forward_calls']==1 and cost['actual_forward_examples']==2
 bits=[r['predicted_bit'] for r in rows];vector=[0]*577
 vector[4*data['route']+2*bits[0]+bits[1]]=127*data['label']
 private_json(work/'vector.json',vector)
 # The supplied teaching label is used only after model scoring above.
 issued=[sys.executable,'-B',str(ROOT/'runtime/e2e/journal/roles.py'),'issue',
  '--config',args.issuer_config,'--head',args.head,'--route','0','--request-id',args.request_id,
  '--nonce',args.nonce,'--record-id',args.record_id,'--vector',str(work/'vector.json'),'--out',args.out]
 begin=time.perf_counter_ns();result=subprocess.run(issued,capture_output=True,text=True,timeout=120)
 issuer_ns=time.perf_counter_ns()-begin
 processes.append({'stage':'encrypted_signed_issuer','command':issued,'returncode':result.returncode,'wall_ns':issuer_ns,'stdout':result.stdout,'stderr':result.stderr})
 private_json(work/'processes.json',processes)
 if result.returncode:
  print(json.dumps({'ok':False,'stage':'encrypted_signed_issuer','private_diagnostics_retained':True}));raise SystemExit(result.returncode)
 inner={'cached_quantized_comparison':False,'load_seconds':cost['cpu_load_wall_seconds']+cost['transfer_to_mps_wall_seconds'],
  'feature_seconds':cost['forward_wall_seconds'],'actual_forward_calls':1,'actual_axis_examples':2}
 private_json(work/'report.json',{'ok':True,'live_encoder_result':inner,'encoder_cost':cost,'predicted_bits':bits,
  'input_sha256':sha(work/'input.json'),'vector_sha256':sha(work/'vector.json'),'issuer_result':json.loads(result.stdout)})
 print(json.dumps({'ok':True,'dimension':577,'encoder_wall_ns':encoder_ns,'issuer_wall_ns':issuer_ns,
  'issuer_result':json.loads(result.stdout),'scope':'Actual fixed semantic forward then signed encrypted Learn; no private feature or input hash published'}))
if __name__=='__main__':main()
