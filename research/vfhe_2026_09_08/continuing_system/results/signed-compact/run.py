from pathlib import Path
import importlib.util, json, hashlib, sys, time
from datetime import datetime, timezone
HERE=Path(__file__).resolve().parent
APP=HERE.parent.parent
ROOT=HERE.parent/'signed-compact'
spec=importlib.util.spec_from_file_location('signed_compact_core',APP/'core.py')
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
def read(p):return json.loads(Path(p).read_text())
def write(p,v):core.backend.save(p,v)
def sha(p):return core.backend.sha(p)
def now():return datetime.now(timezone.utc).isoformat()
def phase(name,arguments):
 write(HERE/'progress.json',{'phase':name,'utc':now()})
 record=core.backend.run(HERE,name,[sys.executable,APP/'core.py',*arguments],1800)
 value=read(HERE/(name+'.stdout'))
 print(json.dumps({'phase':name,'complete':True,'elapsed_seconds':record['elapsed_seconds']}),flush=True)
 return value,record
start=time.monotonic()
try:
 assert not ROOT.exists(),'Fresh signed-compact instance required'
 prepared=APP/'prepared'
 frozen={str(p):sha(p) for p in [prepared/'vectors.json',prepared/'frozen_workload.json',prepared/'reference.json',APP/'workload.json']}
 vectors=read(prepared/'vectors.json');workload=read(prepared/'frozen_workload.json')
 training=next(r for r in workload['training'] if r['id']=='pi01');query=workload['held_out'][0]
 assert query['id']=='hpi01'
 tv=vectors['pi01'];qv=[-x for x in vectors[query['id']]]
 dot=sum(a*b for a,b in zip(tv,qv));assert dot<0
 expected=[dot]+[0]*7
 text='Analytic signed-vector stress query: coordinatewise negation of fixed public held-out hpi01 embedding; not a natural-language utility example.'
 write(HERE/'teach-vector.json',tv);write(HERE/'negative-query-vector.json',qv)
 provenance={'scope':'Public corpus and analytic signed-vector stress; not natural-language utility.',
  'training':training,'original_heldout':query,'transform':'q[i] = -prepared.vectors[hpi01][i]',
  'query_text_metadata':text,'expected_dot_values':expected,'expected_sum_dot':dot,
  'expected_ranking':[training['label']],'source_pins':frozen,
  'teach_vector_sha256':sha(HERE/'teach-vector.json'),'query_vector_sha256':sha(HERE/'negative-query-vector.json'),
  'application_source_pins':{str(APP/n):sha(APP/n) for n in ['core.py','backend.py','engines.py']},'started_utc':now()}
 write(HERE/'PROVENANCE.json',provenance)
 init,ic=phase('initialize',['init',ROOT,'--class',training['label'],'--score','linear','--proof-backend','compact'])
 taught,tc=phase('teach',['teach',ROOT,'--label',training['label'],'--text',training['text'],'--request-id','teach-pi01','--vector-json',HERE/'teach-vector.json'])
 assert taught['committed'] and taught['head']['revision']==1
 assert taught['metrics']['proofs_generated']==taught['metrics']['proofs_verified']==8
 args=['query',ROOT,'--text',text,'--request-id','negative-hpi01','--vector-json',HERE/'negative-query-vector.json']
 answer,qc=phase('query',args)
 actual=answer['classes'][training['label']]
 assert actual['dot_values']==expected and actual['sum_dot']==dot
 assert actual['all8192_slots_repeat8'] is True and actual['full_reader_key'] is True
 assert answer['ranking']==[training['label']] and answer['counts']=={training['label']:1}
 assert answer['class_scores'][0]['mean_numerator']==dot and answer['class_scores'][0]['mean_denominator']==1
 assert answer['metrics']['proofs_generated']==answer['metrics']['proofs_verified']==88
 assert answer['private_reads']==1 and answer['public_accepted'] is True
 assert not list((ROOT/'queries').rglob('*capture*'))
 before={str(p):sha(p) for pattern in ['proof.bin','read.stdout'] for p in ROOT.rglob(pattern)}
 reopened,rc=phase('reopen-same-query',args)
 assert reopened==answer
 after={str(p):sha(p) for pattern in ['proof.bin','read.stdout'] for p in ROOT.rglob(pattern)}
 assert after==before
 for p,digest in frozen.items():assert sha(p)==digest
 queries=ROOT/'queries/negative-hpi01'
 acceptance=read(queries/'public_acceptance.json');receive=read(queries/'receive_started.json')
 assert acceptance['private_reads']==0 and acceptance['all_active_classes_verified'] is True
 assert acceptance['public_phase_complete_utc']<=receive['utc']
 proofs=[]
 for phase_file in ROOT.rglob('*.command.json'):
  record=read(phase_file)
  if phase_file.name.endswith('-prove.command.json') and '/chunk' in str(phase_file): proofs.append(record)
 result={'complete':True,'instance':str(ROOT),'scope':provenance['scope'],
  'expected_dot_values':expected,'actual_dot_values':actual['dot_values'],'sum_dot':dot,'ranking':answer['ranking'],
  'fresh_setup':True,'fresh_update_proofs':8,'fresh_linear_proofs':88,'independent_consumer_checks':96,
  'reader_decryptions':1,'retained_response_identical_after_fresh_process':True,'reopen_new_proofs':0,'reopen_new_reads':0,
  'all8192_slots_repeat8':True,'no_quadratic_capture':True,'public_acceptance_before_private_read':True,
  'teach_metrics':taught['metrics'],'query_metrics':answer['metrics'],
  'wall_seconds':{'initialize':ic['elapsed_seconds'],'teach':tc['elapsed_seconds'],'query':qc['elapsed_seconds'],'reopen_same_query':rc['elapsed_seconds'],'total':time.monotonic()-start},
  'native_prove_command_seconds':sum(p['elapsed_seconds'] for p in proofs),
  'native_prove_peak_rss_bytes':max((p.get('max_rss_bytes',0) for p in proofs),default=0),
  'proof_bytes':taught['metrics']['proof_bytes']+answer['metrics']['proof_bytes'],
  'genesis':init['genesis'],'answer_sha256':sha(queries/'answer.json'),'provenance_sha256':sha(HERE/'PROVENANCE.json'),
  'profile_sha256':sha(APP/'linear/PIPELINE.json'),'finished_utc':now()}
 write(HERE/'RESULT.json',result);write(HERE/'progress.json',{'phase':'complete','utc':now()})
 print(json.dumps(result,indent=2),flush=True)
except BaseException as e:
 write(HERE/'FAILED.json',{'error':repr(e),'elapsed_seconds':time.monotonic()-start,'utc':now()});raise
