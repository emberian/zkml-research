"""Teacher-only selection, no model and no modification of frozen scores."""
import sys,statistics
sys.dont_write_bytecode=True
from common import *
def cell(rows):
 pairs={}
 for r in rows:pairs.setdefault(r['record_id'],[]).append(r)
 complete=[v for v in pairs.values() if {r['axis'] for r in v}=={'a','b'}]
 return {'correct_bits':sum(r['correct'] for r in rows),'bits':len(rows),
  'bit_accuracy':sum(r['correct'] for r in rows)/len(rows),
  'correct_pairs':sum(all(r['correct'] for r in p) for p in complete),'pairs':len(complete),
  'exact_ties':sum(r['exact_tie'] for r in rows),
  'mean_chosen_conditional_probability':statistics.mean(max(r['conditional_probabilities_in_bit_order']) for r in rows),
  'mean_alternative_probability_mass':statistics.mean(r['alternative_probability_mass'] for r in rows),
  'minimum_alternative_probability_mass':min(r['alternative_probability_mass'] for r in rows),
  'top1_is_alternative_count':sum(r['unconstrained_top1_is_alternative'] for r in rows)}
def main():
 assert not (ROOT/'results.json').exists(),'Preserve first selection'
 result=load(ROOT/'score_results.json');assert result['execution_completed']
 oracle={r['record_id']:r for r in load(ROOT/'teacher_oracle.json')};rows=load(ROOT/'raw_scores.json')
 assert len(rows)==512 and len(oracle)==128
 for r in rows:
  gold=oracle[r['record_id']];r['oracle_bit']=gold[r['axis']];r['correct']=r['predicted_bit']==r['oracle_bit']
  r['previously_inspected']=gold['previously_inspected']
 framings={}
 for f in ['A','B']:
  subset=[r for r in rows if r['framing']==f]
  out={'overall':cell(subset),'tasks':{},'axes':{},'inspected_status':{},'gold_pairs':{}}
  for task in ['plant','letter']:
   out['tasks'][task]=cell([r for r in subset if r['task']==task])
   for axis in ['a','b']:out['axes'][f'{task}.{axis}']=cell([r for r in subset if r['task']==task and r['axis']==axis])
  for flag in [False,True]:out['inspected_status'][str(flag)]=cell([r for r in subset if r['previously_inspected']==flag])
  for task in ['plant','letter']:
   for a in [0,1]:
    for b in [0,1]:out['gold_pairs'][f'{task}.{a}{b}']=cell([r for r in subset if r['task']==task and oracle[r['record_id']]['a']==a and oracle[r['record_id']]['b']==b])
  out['route_balanced_bit_accuracy']=statistics.mean(c['bit_accuracy'] for c in out['tasks'].values())
  framings[f]=out
 selected=max(['A','B'],key=lambda f:framings[f]['route_balanced_bit_accuracy'])
 chosen=framings[selected]
 gate=chosen['overall']['bit_accuracy']>=.9 and all(c['bit_accuracy']>=.85 for c in chosen['tasks'].values())
 save(ROOT/'scored_teacher_rows.json',rows)
 out={'scope':'Teacher-selected forced-choice factual axes; no held-out/utility evidence',
  'framings':framings,'selected_framing':selected,'teacher_gate_passed':gate,
  'recommend_fresh_preregistered_evaluation_only':gate,'teacher_inputs':128,'teacher_bit_denominator_per_framing':256,
  'teacher_pair_denominator_per_framing':128,'prior_inspected_texts':8,'heldout_inputs':0,'utility_history_runs':0,
  'source_results_sha256':sha(ROOT/'score_results.json'),'raw_scores_sha256':sha(ROOT/'raw_scores.json'),
  'scored_teacher_rows_sha256':sha(ROOT/'scored_teacher_rows.json'),'freeze_sha256':sha(ROOT/'freeze.json')}
 save(ROOT/'results.json',out);print(json.dumps(out,indent=2))
if __name__=='__main__':main()
