"""Independent scalar arithmetic, complete denominator and source audit; no model."""
import sys,math
sys.dont_write_bytecode=True
from common import *
def main():
 freeze=load(ROOT/'freeze.json')
 for p,h in freeze['source_sha256'].items():assert sha(p)==h,p
 counts=verify_priors();inputs=load(ROOT/'issuer_inputs.json');raw=load(ROOT/'raw_scores.json')
 oracle={r['record_id']:r for r in load(ROOT/'teacher_oracle.json')};out=load(ROOT/'results.json')
 assert len(inputs)==len(raw)==512
 assert {(r['framing'],r['record_id'],r['axis']) for r in raw}=={(f,i,a) for f in ['A','B'] for i in range(128) for a in ['a','b']}
 correct={f:[] for f in ['A','B']};worst_log_error=0;worst_prob_error=0
 for source,r in zip(inputs,raw):
  for key in ['example_index','record_id','framing','axis','task']:assert source[key]==r[key]
  assert hashlib.sha256(source['rendered_prompt'].encode()).hexdigest()==source['rendered_prompt_sha256']
  assert source['token_count']==len(source['token_ids'])
  x,y=r['logits_in_bit_order'];pred=int(x<y)
  assert pred==r['predicted_bit'];assert (x==y)==r['exact_tie']
  probs=[1/(1+math.exp(y-x)),1/(1+math.exp(x-y))]
  for index in [0,1]:
   error=abs(r['log_likelihoods_in_bit_order'][index]-(r['logits_in_bit_order'][index]-r['full_vocabulary_logsumexp']))
   worst_log_error=max(worst_log_error,error);assert error<1e-5
   error=abs(probs[index]-r['conditional_probabilities_in_bit_order'][index]);worst_prob_error=max(worst_prob_error,error);assert error<1e-6
  good=pred==oracle[r['record_id']][r['axis']]
  correct[r['framing']].append((r['record_id'],r['task'],r['axis'],good))
 scores={}
 for f,rows in correct.items():
  got=sum(r[3] for r in rows);scores[f]=got/256
  assert got==out['framings'][f]['overall']['correct_bits']
  pairs=sum(all(r[3] for r in rows if r[0]==rid) for rid in range(128))
  assert pairs==out['framings'][f]['overall']['correct_pairs']
  for task in ['plant','letter']:
   subset=[r for r in rows if r[1]==task];assert len(subset)==128
   assert sum(r[3] for r in subset)==out['framings'][f]['tasks'][task]['correct_bits']
 selected='A' if scores['A']>=scores['B'] else 'B';assert selected==out['selected_framing']
 gate=scores[selected]>=.9 and all(sum(r[3] for r in correct[selected] if r[1]==task)/128>=.85 for task in ['plant','letter'])
 assert gate==out['teacher_gate_passed']
 audit={'passed':True,'audited_scored_bits':512,'audited_teacher_pairs':256,
  'complete_framing_record_axis_coverage':True,'selected_framing':selected,'gate_passed':gate,
  'max_float32_loglik_scalar_error':worst_log_error,'max_float32_conditional_probability_error':worst_prob_error,
  'prior_file_counts_preserved':counts,'model_forwards_in_audit':0,'heldout_inputs':0,
  'results_sha256':sha(ROOT/'results.json'),'freeze_sha256':sha(ROOT/'freeze.json')}
 save(ROOT/'audit.json',audit);print(json.dumps(audit,indent=2))
if __name__=='__main__':main()
