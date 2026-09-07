"""Freeze two prompts and all teacher tokens before any forward score."""
import sys,time
sys.dont_write_bytecode=True
from common import *
START=time.perf_counter()
from transformers import AutoTokenizer
from transformers.models.smollm3 import modeling_smollm3
def main():
 assert not (ROOT/'freeze.json').exists(),'Preserve preregistration bytes'
 old_counts=verify_priors();old=load(PRIOR/'freeze.json');modelpath=Path(old['model_path'])
 for name,row in old['model_files'].items():assert sha(modelpath/name)==row['sha256'],name
 tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
 config=load(ROOT/'prompts.json');records=load(BASE/'representation_records.json')
 teachers=[r for r in records if r['pool']=='teach']
 assert [r['id'] for r in teachers]==list(range(128))
 inputs=[];oracle=[]
 for record in teachers:
  oracle.append({'record_id':record['id'],'task':['plant','letter'][record['skill']],
   'a':record['a'],'b':record['b'],'previously_inspected':record['id'] in INSPECTED})
 for framing in ['A','B']:
  setting=config['framings'][framing]
  alternatives=setting['alternatives_in_bit_order']
  ids=[tok(t,add_special_tokens=False)['input_ids'] for t in alternatives]
  assert all(len(t)==1 for t in ids),(alternatives,ids)
  for record in teachers:
   task=['plant','letter'][record['skill']]
   for axis in ['a','b']:
    definition=config['axes'][task][axis]
    user=setting['user_template'].format(task=task,text=record['text'],**definition)
    messages=[{'role':'system','content':setting['system']},{'role':'user','content':user}]
    prompt=tok.apply_chat_template(messages,tokenize=False,add_generation_prompt=True,enable_thinking=False)
    token_ids=tok(prompt,add_special_tokens=False)['input_ids']
    for alternative,alternative_ids in zip(alternatives,ids):
     assert tok(prompt+alternative,add_special_tokens=False)['input_ids']==token_ids+alternative_ids
    # IDs below are output bookkeeping only; score.py forwards only token_ids.
    inputs.append({'example_index':len(inputs),'record_id':record['id'],'task':task,'axis':axis,
     'framing':framing,'text':record['text'],'messages':messages,'rendered_prompt':prompt,
     'rendered_prompt_sha256':hashlib.sha256(prompt.encode()).hexdigest(),
     'token_ids':token_ids,'token_count':len(token_ids),'alternatives_in_bit_order':alternatives,
     'alternative_token_ids_in_bit_order':[x[0] for x in ids]})
 assert len(inputs)==512
 save(ROOT/'issuer_inputs.json',inputs);save(ROOT/'teacher_oracle.json',oracle)
 sources=[ROOT/n for n in ['CONTRACT.md','prompts.json','common.py','prepare.py','score.py','evaluate.py','audit.py','launch.py','issuer_inputs.json','teacher_oracle.json']]
 sources += [BASE/'representation_records.json',PRIOR/'freeze.json',PRIOR/'manifest.json',PRIOR/'corrected_run/manifest.json',Path(modeling_smollm3.__file__)]
 freeze={'model':old['model'],'revision':old['revision'],'model_path':old['model_path'],
  'model_files':old['model_files'],'source_sha256':{str(p):sha(p) for p in sources},
  'teacher_ids':list(range(128)),'previously_inspected_teacher_ids':INSPECTED,
  'prompt_framings':['A','B'],'actual_forward_examples':512,'score_batches':64,'batch_size':8,
  'one_token_suffix_checks':1024,'alternatives':{f:next(r['alternative_token_ids_in_bit_order'] for r in inputs if r['framing']==f) for f in ['A','B']},
  'pad_token_id':tok.pad_token_id,'runtime':runtime(),'prior_files_verified':old_counts,
  'weights_loaded_in_prepare':False,'heldout_inputs':0,'utility_history_runs':0,
  'prepare_wall_seconds_including_imports':time.perf_counter()-START,
  'nonpadding_tokens':sum(r['token_count'] for r in inputs),
  'padded_tokens':sum(8*max(r['token_count'] for r in inputs[start:start+8]) for start in range(0,512,8))}
 save(ROOT/'freeze.json',freeze)
 print(json.dumps({k:v for k,v in freeze.items() if k not in ['model_files','source_sha256','teacher_ids']},indent=2))
 print('freeze_sha256',sha(ROOT/'freeze.json'))
if __name__=='__main__':main()
