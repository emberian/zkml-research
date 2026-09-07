"""No-model audit of actual greedy configs, unchanged inputs and all outputs."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent;PRIOR=ROOT.parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 r=load(ROOT/'results.json');raw=load(ROOT/'raw_outputs.json');configs=load(ROOT/'effective_configurations.json')
 inputs=load(PRIOR/'issuer_inputs.json');gold=load(PRIOR/'teacher_oracle.json');manifest=load(PRIOR/'manifest.json')
 for name,row in manifest['files'].items():assert sha(PRIOR/name)==row['sha256'],name
 for p,h in load(ROOT/'freeze.json')['source_sha256'].items():assert sha(p)==h,p
 assert r['raw_outputs_sha256']==sha(ROOT/'raw_outputs.json') and r['effective_configurations_sha256']==sha(ROOT/'effective_configurations.json')
 assert r['prior_issuer_inputs_sha256']==sha(PRIOR/'issuer_inputs.json')
 assert len(raw)==len(configs)==len(inputs)==len(gold)==8
 # Literal transcription of visible payloads for diagnosis only. It neither
 # repairs responses nor supplies accepted vectors to any encoder or learner.
 visible=[{'a':0,'b':0},{'a':0,'b':1},{'a':1,'b':0},{'a':1,'b':0},
          {'a':0,'b':None},{'a':0,'b':1},{'a':None,'b':1},{'a':None,'b':1}]
 correct=0;nulls=0;wrong=0;paircorrect=0;generated=0
 for i,(row,config,item,want,payload) in enumerate(zip(raw,configs,inputs,gold,visible)):
  assert row['record_id']==item['record_id']==want['record_id']
  assert row['effective_config_call_index']==config['call_index']==i
  assert config['explicit_use_model_defaults'] is False and config['explicit_do_sample_kwarg'] is False
  actual=config['effective_configuration'];assert config['effective_generation_mode']=='greedy_search'
  assert actual['do_sample'] is False and actual['num_beams']==1 and actual['max_new_tokens']==32 and actual['use_cache'] is True
  assert actual['temperature']==actual['top_p']==1.0
  assert row['input_tokens']==len(item['token_ids']) and row['parsed'] is None
  try:json.loads(row['raw_output'].strip())
  except ValueError:pass
  else:raise AssertionError('Expected frozen strict parser refusal')
  assert row['raw_output']=='```json\n'+json.dumps(payload,indent=2)+'\n```'
  for k in ['a','b']:
   nulls+=int(payload[k] is None);correct+=int(payload[k]==want[k]);wrong+=int(payload[k] is not None and payload[k]!=want[k])
  paircorrect+=int(all(payload[k]==want[k] for k in ['a','b']))
  assert len(row['generated_token_ids'])==row['generated_tokens']<32 and row['generated_token_ids'][-1]==128012
  generated+=row['generated_tokens']
 assert (r['valid_json_count'],r['correct_attribute_count'],r['correct_pair_count'])==(0,0,0)
 assert (correct,nulls,wrong,paircorrect)==(11,3,2,4)
 assert 'default values have been modified' not in (ROOT/'run.stderr').read_text()
 result={'audit_passed':True,'actual_merge_configs_verified':8,'effective_mode_all_greedy_search':True,
  'teacher_inputs_this_corrected_run':8,'strict_parser_valid':0,'strict_accepted_correct_pairs':0,'strict_correct_attribute_denominator':16,
  'visible_payload_diagnostic_only':{'correct_printed_bits':11,'null_printed_bits':3,'wrong_printed_bits':2,
   'printed_pairs_matching_oracle':4,'pair_denominator':8,'attribute_denominator':16,
   'none_accepted_as_encoder_output':True,'literal_transcription_checked_against_full_raw_strings':True},
  'input_tokens':sum(i['token_count'] for i in inputs),'generated_tokens':generated,'all_outputs_eos_before_cap':True,
  'original_files_verified_unchanged':len(manifest['files']),'model_calls_in_audit':0,'heldout_inputs':0,'utility_history_runs':0,
  'results_sha256':sha(ROOT/'results.json'),'source_sha256':sha(__file__)}
 (ROOT/'audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
