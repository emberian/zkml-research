"""Audit the preserved first attempt without model loading or inference."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def parse(text):
 def pairs(values):
  out={}
  for k,v in values:
   if k in out:raise ValueError('duplicate key')
   out[k]=v
  return out
 try:
  obj=json.loads(text.strip(),object_pairs_hook=pairs)
  assert type(obj) is dict and set(obj)=={'a','b'}
  assert all(v is None or type(v) is int and v in [0,1] for v in obj.values())
  return obj
 except (AssertionError,ValueError,TypeError):return None
def main():
 f=load(ROOT/'freeze.json');r=load(ROOT/'results.json');inputs=load(ROOT/'issuer_inputs.json');raw=load(ROOT/'raw_outputs.json');oracle=load(ROOT/'teacher_oracle.json')
 for p,h in f['source_sha256'].items():assert sha(p)==h,p
 assert r['freeze_sha256']==sha(ROOT/'freeze.json') and r['raw_outputs_sha256']==sha(ROOT/'raw_outputs.json')
 ids=[0,16,32,48,64,80,96,112]
 assert [x['record_id'] for x in inputs]==[x['record_id'] for x in raw]==[x['record_id'] for x in oracle]==ids
 valid=0;bits=0;pairs=0
 for item,row,gold in zip(inputs,raw,oracle):
  assert not {'a','b','label','oracle'}.intersection(item)
  assert item['token_count']==len(item['token_ids'])
  assert hashlib.sha256(item['rendered_prompt'].encode()).hexdigest()==item['rendered_prompt_sha256']
  parsed=parse(row['raw_output']);assert parsed==row['parsed'];valid+=int(parsed is not None)
  correct=[parsed is not None and parsed[k]==gold[k] for k in ['a','b']];bits+=sum(correct);pairs+=int(all(correct))
  assert row['generated_tokens']==len(row['generated_token_ids'])<32 and row['generated_token_ids'][-1]==128012
 assert (valid,bits,pairs)==(r['valid_json_count'],r['correct_attribute_count'],r['correct_pair_count'])==(1,2,1)
 diag=load(ROOT/'config_diagnostic.json');assert diag['original_default_merge']['do_sample'] is True
 assert r['settings']['do_sample'] is False # Recorded intent, explicitly contradicted by effective merge.
 assert 'do_sample' in (ROOT/'run.stderr').read_text() and 'True' in (ROOT/'run.stderr').read_text()
 out={'audit_passed':True,'model_runtime_completed':True,'greedy_contract_fulfilled':False,
  'deviation':'Recorded do_sample=False intent was merged to effective sampling by installed Transformers.',
  'teacher_inputs':8,'attributes':16,'valid_strict_json':valid,'correct_attributes_under_strict_parser':bits,'correct_pairs':pairs,
  'all_outputs_ended_with_eos_before_cap':True,'all_prompt_hashes_and_inputs_match':True,
  'oracle_fields_absent_from_input_records':True,'new_model_calls_in_audit':0,'heldout_inputs':0,
  'results_sha256':sha(ROOT/'results.json'),'source_sha256':sha(__file__)}
 (ROOT/'audit.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
