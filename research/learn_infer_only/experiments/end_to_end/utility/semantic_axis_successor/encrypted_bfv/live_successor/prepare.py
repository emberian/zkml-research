"""Freeze one private text/prompt and public normal-flow code before inference."""
import ast,difflib,hashlib,json,os,shutil,sys,tarfile,time
from pathlib import Path
sys.dont_write_bytecode=True
for key in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[key]='1'
os.environ['TOKENIZERS_PARALLELISM']='false'
ROOT=Path(__file__).resolve().parent;BFV=ROOT.parent;SEM=ROOT.parents[1];UTILITY=ROOT.parents[2];E2E=ROOT.parents[3]
BASE=E2E.parent/'adaptation_utility';SELECT=UTILITY/'semantic_axis_selection'
RUNTIME=ROOT/'runtime';SNAP=RUNTIME/'e2e';REPORTS=ROOT/'reports/run001'
load=lambda p:json.loads(Path(p).read_bytes())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while raw:=f.read(1024*1024):h.update(raw)
 return h.hexdigest()
def dump(p,x,private=False):
 Path(p).write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
 if private:os.chmod(p,0o600)
def verify(directory):
 m=load(directory/'manifest.json')
 for n,r in m['files'].items():assert sha(directory/n)==r['sha256'],(directory,n)
 return len(m['files'])
def main():
 start=time.perf_counter();assert not (ROOT/'freeze.json').exists() and not SNAP.exists()
 parents=[BFV,SEM,SEM/'materialized',SELECT];preserved={str(p):verify(p) for p in parents}
 inputpath=RUNTIME/'.private/input.json';data=load(inputpath)
 assert set(data)=={'text','route','label'} and type(data['text']) is str and data['route']==0 and data['label']==1
 corpusfiles=[BASE/'text_transfer_records.json',BASE/'representation_records.json',UTILITY/'attribute_calibration/records.json',
  UTILITY/'e5_successor/records.json',SEM/'records.json'];corpus=[];texts=set()
 for p in corpusfiles:
  rows=load(p);old=[r['text'] for r in rows];assert data['text'] not in old
  texts.update(old);corpus.append({'path':str(p),'sha256':sha(p),'records':len(old),'full_text_disjoint':True})
 REPORTS.mkdir(parents=True)
 dump(REPORTS/'freshness.json',{'instrument':'Exact Python string equality against all text fields in the five named synthetic corpora',
  'corpora':corpus,'unique_prior_texts':len(texts),'fresh_texts':1,'full_text_disjoint':True,'private_text_and_hash_omitted':True,
  'scope':'Full-text disjointness only; semantic task, meanings and ordinary words overlap; no training-corpus absence claim.'})
 oldfreeze=load(SEM/'freeze.json');modelpath=Path(oldfreeze['model_path'])
 for n,r in oldfreeze['model_files'].items():assert sha(modelpath/n)==r['sha256'],n
 expected=(SEM/'score.py').read_text()
 for a,b in [("'new_test_texts':128","'new_test_texts':1"),("'semantic_bits_per_framing':256","'semantic_bits_per_framing':2"),
  ("'pairs_per_framing':128","'pairs_per_framing':1"),("'heldout_inputs':128","'heldout_inputs':1")]:expected=expected.replace(a,b)
 assert (ROOT/'encoder/score.py').read_text()==expected,'Only fixed output-count metadata changes in scorer'
 from transformers import AutoTokenizer
 tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
 prompts=load(SELECT/'prompts.json');framing=prompts['framings']['A'];ids=[15,16];inputs=[]
 assert [tok(s,add_special_tokens=False)['input_ids'] for s in ['0','1']]==[[15],[16]]
 for axis in ['a','b']:
  definition=prompts['axes']['plant'][axis]
  messages=[{'role':'system','content':framing['system']},{'role':'user','content':framing['user_template'].format(task='plant',text=data['text'],**definition)}]
  rendered=tok.apply_chat_template(messages,tokenize=False,add_generation_prompt=True,enable_thinking=False)
  tokens=tok(rendered,add_special_tokens=False)['input_ids']
  for alternative,tid in zip(['0','1'],ids):assert tok(rendered+alternative,add_special_tokens=False)['input_ids']==tokens+[tid]
  inputs.append({'example_index':len(inputs),'record_id':0,'task':'plant','axis':axis,'framing':'A',
   'text':data['text'],'messages':messages,'rendered_prompt':rendered,'token_ids':tokens,'token_count':len(tokens),
   'alternatives_in_bit_order':['0','1'],'alternative_token_ids_in_bit_order':ids})
 prepared=RUNTIME/'.private/prepared';prepared.mkdir(mode=0o700)
 dump(prepared/'issuer_inputs.json',inputs,True)
 pins={};deps={}
 parentpins=load(BFV/'reports/run001/source_pins.json');parentsnap=BFV/'runtime/e2e'
 for name,h in parentpins.items():
  if name in ['verified_reader/utility_driver.py','verified_reader/fast_utility_driver.py']:continue
  source=parentsnap/name;assert sha(source)==h,name
  target=SNAP/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
  if name=='resident-crypto':os.chmod(target,0o755)
  pins[name]=h;deps[str(source)]=h
 originalpath=E2E/'verified_reader/live_driver.py';original=originalpath.read_text()
 assert sha(originalpath)=='b0d450fda66aa126bb647d98a041d66447afbef9ab2c6805a24a3df0ef103d65'
 adapted=(ROOT/'driver.py').read_text()
 def live_class(source):return ast.get_source_segment(source,next(n for n in ast.walk(ast.parse(source)) if isinstance(n,ast.ClassDef) and n.name=='LiveRun'))
 assert live_class(original)==live_class(adapted),'LiveRun persistent transport class remains byte-identical'
 dest=SNAP/'verified_reader/live_driver.py';dest.write_text(adapted);pins['verified_reader/live_driver.py']=sha(dest)
 (ROOT/'live_driver_adapter.diff').write_text('\n'.join(difflib.unified_diff(original.splitlines(),adapted.splitlines(),fromfile='frozen_original_live_driver.py',tofile='deferred_semantic_live_driver.py'))+'\n')
 deps[str(originalpath)]=sha(originalpath)
 qdir=RUNTIME/'public_query_inputs';qdir.mkdir();querypins={};policy=[]
 for i in range(16):
  p=SEM/'materialized/runtime/public_queries'/f'q{i:02d}.json';target=qdir/p.name
  expected=load(SEM/'materialized/runtime_hash_census.json')['files'][str(p.relative_to(SEM/'materialized'))]['sha256']
  assert sha(p)==expected;shutil.copyfile(p,target);querypins[p.name]=expected
  policy.append({'route':0 if i<8 else 1,'path':str(target)})
 dump(RUNTIME/'query_policy.json',policy);dump(REPORTS/'public_query_pins.json',querypins)
 assert load(qdir/'q01.json')==[127]+[0]*576
 dump(ROOT/'encoder_inventory.json',{'model':oldfreeze['model'],'revision':oldfreeze['revision'],'model_path':str(modelpath),
  'model_files':oldfreeze['model_files'],'fixed_framing':'A','token_alternatives':[15,16],'actual_scored_axes_planned':2,
  'expected_forward_calls':1,'maximum_batch_size':8,'actual_partial_batch_size':2,'private_text_prompt_and_token_hashes_omitted':True})
 for p in [ROOT/n for n in ['CONTRACT.md','.gitignore','prepare.py','run.py','public_verify.py','drain.py','validate.py','driver.py','issue_semantic_text.py','encoder/common.py','encoder/score.py','encoder_inventory.json']]:deps[str(p)]=sha(p)
 for p in [SEM/'score.py',SEM/'freeze.json',SELECT/'prompts.json']+corpusfiles+[p/'manifest.json' for p in parents]:deps[str(p)]=sha(p)
 for p in sorted((BFV/'live').rglob('*')):
  if p.is_file() and 'runtime' not in p.relative_to(BFV/'live').parts:deps[str(p)]=sha(p)
 for p,h in oldfreeze['source_sha256'].items():
  if p.endswith('modeling_smollm3.py'):assert sha(p)==h;deps[p]=h
 freeze={'public_source_dependencies':deps,'snapshot_source_pins':pins,'query_vector_pins':querypins,
  'encoder_python':str(BASE/'.venv/bin/python'),'model_path':str(modelpath),'model_files':oldfreeze['model_files'],
  'revision':oldfreeze['revision'],'route':0,'query_index':1,'same_query_before_after':True,
  'public_phase_before_decryption':True,'offline_private_drain_after_public_verification':True,'source_model_forwards_before_freeze':0,'crypto_calls_before_freeze':0,'private_input_prompt_freeze_stored':True,
  'private_input_and_prompt_hashes_omitted':True,'tensor_forward_loop_identical':True,'LiveRun_class_identical':True,
  'parent_entries_preserved':preserved,'prepare_wall_seconds':time.perf_counter()-start,
  'runtime':str(RUNTIME),'reports':str(REPORTS)}
 dump(ROOT/'freeze.json',freeze)
 privatefreeze={'source_sha256':dict(deps,**{str(prepared/'issuer_inputs.json'):sha(prepared/'issuer_inputs.json')}),
  'private_input_sha256':sha(inputpath),'model_path':str(modelpath),'model_files':oldfreeze['model_files'],
  'pad_token_id':tok.pad_token_id,'parent_manifests':[str(p) for p in parents],
  'framing':'A','one_text':True,'label_not_in_model_inputs':True}
 dump(prepared/'freeze.json',privatefreeze,True)
 dump(REPORTS/'source_pins.json',pins);dump(REPORTS/'frontend_dependencies.json',deps)
 dump(REPORTS/'frontend_metadata.json',{'frontend_path':str(ROOT/'issue_semantic_text.py'),
  'encoder_inventory':str(ROOT/'encoder_inventory.json'),'input_path_and_input_hash_omitted':True})
 dump(REPORTS/'model_pins.json',{'model_path':str(modelpath),'revision':oldfreeze['revision'],'files':oldfreeze['model_files']})
 with tarfile.open(REPORTS/'source_snapshot.tar.gz','w:gz') as archive:
  for name in sorted(pins):
   if name!='resident-crypto':archive.add(SNAP/name,arcname=name)
  for name in ['issue_semantic_text.py','encoder/common.py','encoder/score.py','encoder_inventory.json','CONTRACT.md']:
   archive.add(ROOT/name,arcname='semantic_frontend/'+name)
  archive.add(SELECT/'prompts.json',arcname='semantic_frontend/public_framing_definitions.json')
 for p in parents:assert verify(p)==preserved[str(p)]
 print(json.dumps({'prepared':True,'freeze_sha256':sha(ROOT/'freeze.json'),'public_query_index':1,
  'fresh_texts':1,'model_forwards':0,'crypto_calls':0,'private_contents_and_hashes_omitted':True,'prepare_seconds':freeze['prepare_wall_seconds']}))
if __name__=='__main__':main()
