"""Freeze fresh surfaces, histories, actual teacher predictions and A tokens."""
import sys,time,importlib.util,subprocess
sys.dont_write_bytecode=True
from common import *
from surfaces import make_records
sys.path.insert(0,str(BASE))
import text_transfer_data as olddata
import representation_data as repdata
from transformers import AutoTokenizer
def imported(path,name):
 spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def main():
 assert not (ROOT/'freeze.json').exists(),'Preserve first freeze'
 t=time.perf_counter();verify_priors();selection=load(SELECTED/'results.json')
 assert selection['selected_framing']=='A' and selection['teacher_gate_passed']
 cmd=['rg','-n',r'"seed"[[:space:]]*:[[:space:]]*670([0-5][0-9]|6[0-3])([^0-9]|$)',str(ROOT.parents[3]),'-g','*.json']
 check=subprocess.run(cmd,capture_output=True,text=True)
 assert check.returncode==1 and check.stdout=='',check.stdout
 save(ROOT/'seed_inventory.json',{'command':cmd,'returncode':check.returncode,'stdout':check.stdout,'stderr':check.stderr,
  'scope':'all JSON numeric seed fields in research/learn_infer_only before this fixture is written'})
 prior_modules=[imported(UTILITY/'attribute_calibration/data.py','old_attribute_data'),imported(UTILITY/'e5_successor/surfaces.py','old_e5_surfaces')]
 records=make_records(load(BASE/'representation_records.json'),[olddata,repdata],prior_modules)
 for previous in [BASE/'text_transfer_records.json',BASE/'representation_records.json',UTILITY/'attribute_calibration/records.json',UTILITY/'e5_successor/records.json']:
  if previous.exists():assert set(r['text'] for r in records[256:]).isdisjoint(r['text'] for r in load(previous)),previous
 save(ROOT/'records.json',records)
 histories=[olddata.history(seed,records) for seed in range(67000,67064)]
 save(ROOT/'histories.json',{'seeds':list(range(67000,67064)),'histories':histories})
 teachers={i:{'record_id':i,'task':['plant','letter'][records[i]['skill']]} for i in range(128)}
 oldrows=load(SELECTED/'raw_scores.json')
 for row in oldrows:
  if row['framing']=='A':teachers[row['record_id']][row['axis']]=row['predicted_bit']
 assert all(set(r)=={'record_id','task','a','b'} for r in teachers.values())
 save(ROOT/'teacher_predictions.json',list(teachers.values()))
 oldfreeze=load(SELECTED/'freeze.json');modelpath=Path(oldfreeze['model_path'])
 expected_score=(SELECTED/'score.py').read_text().replace("'teacher_texts'","'new_test_texts'").replace("'framings':2","'framings':1").replace("'heldout_inputs':0","'heldout_inputs':128").replace("'oracle_opened_by_scoring_process'","'oracle_parsed_by_scoring_process'")
 assert (ROOT/'score.py').read_text()==expected_score,'Only score result metadata may differ from selected implementation'
 for n,row in oldfreeze['model_files'].items():assert sha(modelpath/n)==row['sha256'],n
 tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
 prompts=load(SELECTED/'prompts.json');setting=prompts['framings']['A'];ids=[15,16]
 assert [tok(x,add_special_tokens=False)['input_ids'] for x in ['0','1']]==[[15],[16]]
 inputs=[];oracle=[]
 for record in records[256:]:
  task=['plant','letter'][record['skill']];oracle.append({'record_id':record['id'],'task':task,'a':record['a'],'b':record['b']})
  for axis in ['a','b']:
   definition=prompts['axes'][task][axis]
   user=setting['user_template'].format(task=task,text=record['text'],**definition)
   messages=[{'role':'system','content':setting['system']},{'role':'user','content':user}]
   prompt=tok.apply_chat_template(messages,tokenize=False,add_generation_prompt=True,enable_thinking=False)
   tokens=tok(prompt,add_special_tokens=False)['input_ids']
   for alt,tid in zip(['0','1'],ids):assert tok(prompt+alt,add_special_tokens=False)['input_ids']==tokens+[tid]
   inputs.append({'example_index':len(inputs),'record_id':record['id'],'task':task,'axis':axis,'framing':'A','text':record['text'],
    'messages':messages,'rendered_prompt':prompt,'rendered_prompt_sha256':hashlib.sha256(prompt.encode()).hexdigest(),
    'token_ids':tokens,'token_count':len(tokens),'alternatives_in_bit_order':['0','1'],'alternative_token_ids_in_bit_order':ids})
 save(ROOT/'issuer_inputs.json',inputs);save(ROOT/'test_oracle.json',oracle)
 source=[ROOT/n for n in ['CONTRACT.md','common.py','surfaces.py','prepare.py','score.py','extract_smol.py','protocol.py','evaluate.py','audit.py','launch.py',
  'records.json','histories.json','seed_inventory.json','teacher_predictions.json','issuer_inputs.json','test_oracle.json']]
 source += [SELECTED/n for n in ['manifest.json','freeze.json','prompts.json','raw_scores.json','results.json','score.py']]
 source += [BASE/n for n in ['text_transfer_data.py','representation_data.py','representation_records.json','representation_features.npz']]
 source += [UTILITY/n for n in ['encoder_policy.json','encoder_feasibility.json','e5_successor/features.npz','e5_successor/surfaces.py','attribute_calibration/data.py']]
 source += [Path(p) for p in oldfreeze['source_sha256'] if p.endswith('modeling_smollm3.py')]
 save(ROOT/'freeze.json',{'source_sha256':{str(p):sha(p) for p in source},'model':oldfreeze['model'],'model_path':str(modelpath),
  'revision':oldfreeze['revision'],'model_files':oldfreeze['model_files'],'pad_token_id':tok.pad_token_id,
  'selected_teacher_manifest_sha256':sha(SELECTED/'manifest.json'),'fixed_framing':'A','new_texts':128,'new_histories':64,
  'new_forward_examples':256,'teacher_reencoding_examples':0,'one_token_suffix_checks':512,
  'source_model_forwards_before_freeze':0,'settings_selected_after_teacher_stage':0,
  'runtime':runtime(),'prepare_wall_seconds':time.perf_counter()-t,
  'nonpadding_tokens':sum(r['token_count'] for r in inputs),'padded_tokens':sum(8*max(r['token_count'] for r in inputs[i:i+8]) for i in range(0,256,8))})
 print(json.dumps({'prepared':True,'freeze_sha256':sha(ROOT/'freeze.json'),'teacher_predictions_sha256':sha(ROOT/'teacher_predictions.json'),
  'test_texts':128,'source_examples':256,'new_histories':64,'nonpadding_tokens':sum(r['token_count'] for r in inputs)},indent=2))
if __name__=='__main__':main()
