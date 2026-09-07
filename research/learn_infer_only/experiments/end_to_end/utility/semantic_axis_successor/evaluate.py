"""One fixed fresh factual and paired W32 utility evaluation, no model calls."""
import sys,time
sys.dont_write_bytecode=True
from protocol import *
def main():
 t=time.perf_counter();cpu=time.process_time();verify()
 assert not (ROOT/'results.json').exists(),'No reevaluation or tuning'
 assert load(ROOT/'score_results.json')['execution_completed'] and load(ROOT/'smol_test.extraction.json')['executed']
 records=load(ROOT/'records.json');routes=np.array([r['skill'] for r in records]);raw=load(ROOT/'raw_scores.json')
 assert len(raw)==256 and {r['framing'] for r in raw}=={'A'}
 oracle={r['record_id']:r for r in load(ROOT/'test_oracle.json')}
 bits={i:{'record_id':i} for i in range(256,384)}
 for row in raw:
  assert row['predicted_bit']==int(row['logits_in_bit_order'][0]<row['logits_in_bit_order'][1])
  bits[row['record_id']][row['axis']]=row['predicted_bit']
  row['oracle_bit']=oracle[row['record_id']][row['axis']];row['correct']=row['predicted_bit']==row['oracle_bit']
 assert all(set(r)=={'record_id','a','b'} for r in bits.values())
 save(ROOT/'scored_test_rows.json',raw);save(ROOT/'test_predictions.json',list(bits.values()))
 factual={'overall':factual_cell(raw),'tasks':{},'axes':{},'joint_attributes':{},'errors':[]}
 for task in ['plant','letter']:
  factual['tasks'][task]=factual_cell([r for r in raw if r['task']==task])
  for axis in ['a','b']:factual['axes'][f'{task}.{axis}']=factual_cell([r for r in raw if r['task']==task and r['axis']==axis])
  for a in [0,1]:
   for b in [0,1]:factual['joint_attributes'][f'{task}.{a}{b}']=factual_cell([r for r in raw if r['task']==task and oracle[r['record_id']]['a']==a and oracle[r['record_id']]['b']==b])
 for row in raw:
  if not row['correct']:
   rec=records[row['record_id']];factual['errors'].append({'record_id':row['record_id'],'task':row['task'],'axis':row['axis'],
    'text':rec['text'],'entity':rec['entity'],'template':rec['template'],'true_pair':[rec['a'],rec['b']],
    'oracle_bit':row['oracle_bit'],'predicted_bit':row['predicted_bit'],'exact_tie':row['exact_tie'],
    'logits_in_bit_order':row['logits_in_bit_order']})
 enc_start=time.perf_counter();teacher=load(ROOT/'teacher_predictions.json')
 primary=one_hot(teacher+list(bits.values()),routes)
 gold=one_hot([{'record_id':r['id'],'a':r['a'],'b':r['b']} for r in records],routes)
 semantic_cost=time.perf_counter()-enc_start;enc_start=time.perf_counter()
 hidden=np.concatenate([np.load(BASE/'representation_features.npz')['mean_10'][:256],np.load(ROOT/'smol_test.npz')['features']]).astype(np.float64)
 original=original_features(hidden,routes);baseline_cost=time.perf_counter()-enc_start
 assert np.array_equal(original[:256],np.load(UTILITY/'e5_successor/features.npz')['original577'][:256])
 Q={'semantic577':primary,'original577':original,'attribute8':gold};np.savez_compressed(ROOT/'features.npz',**Q)
 histories=load(ROOT/'histories.json')['histories'];results={};state_arrays={}
 for name,q in Q.items():
  rows=[];states=[]
  for H in histories:
   row,state=run_history(H,records,q);rows.append(row);states.append(state)
  state_arrays[name]=np.array(states);keys=rows[0]['metrics'];strata={};byrule={};joint={}
  for typ in ['linear/linear','linear/nonlinear','nonlinear/linear','nonlinear/nonlinear']:
   subset=[r for r in rows if r['joint_stratum']==typ]
   strata[typ]={'histories':len(subset),'final_queries':128*len(subset),
    'metrics':{k:summary([r['metrics'][k] for r in subset]) for k in keys} if subset else None,
    'correct_final':sum(sum(p==y for p,y in zip(r['predictions'][2],r['targets'][2])) for r in subset)}
  for typ in ['linear','nonlinear']:
   values=[r['metrics'][['plant_changed','letter_retained'][s]] for r in rows for s in [0,1] if r['rule_types'][s]==typ]
   byrule[typ]={'skill_instances':len(values),'final_queries':64*len(values),'accuracy':float(np.mean(values)),
    'correct_final':round(sum(values)*64)}
  for s in [0,1]:
   for a in [0,1]:
    for b in [0,1]:
     inds=[i-256 for i in range(256,384) if records[i]['skill']==s and records[i]['a']==a and records[i]['b']==b]
     right=sum(r['predictions'][2][i]==r['targets'][2][i] for r in rows for i in inds);total=len(inds)*64
     joint[f'{["plant","letter"][s]}.{a}{b}']={'correct_final':right,'final_queries':total,'accuracy':right/total}
  results[name]={'dimension':577,'metrics':{k:summary([r['metrics'][k] for r in rows]) for k in keys},
   'joint_rule_strata':strata,'by_rule_type':byrule,'joint_attribute_strata':joint,'per_history':rows,
   'correct_final':sum(sum(p==y for p,y in zip(r['predictions'][2],r['targets'][2])) for r in rows),'final_queries':8192}
 np.savez_compressed(ROOT/'checkpoint_states.npz',**state_arrays)
 paired={ref:summary([a['metrics']['final_mean']-b['metrics']['final_mean'] for a,b in zip(results['semantic577']['per_history'],results[ref]['per_history'])]) for ref in ['original577','attribute8']}
 p=results['semantic577'];b=results['original577'];gain=paired['original577']
 ng=p['by_rule_type']['nonlinear']['accuracy']-b['by_rule_type']['nonlinear']['accuracy']
 lg=p['by_rule_type']['linear']['accuracy']-b['by_rule_type']['linear']['accuracy']
 gates={'fresh_factual_bits_at_least_90pct':factual['overall']['bit_accuracy']>=.9,
  'fresh_factual_each_task_at_least_85pct':all(c['bit_accuracy']>=.85 for c in factual['tasks'].values()),
  'final_accuracy_at_least_75pct':p['metrics']['final_mean']['mean']>=.75,
  'each_task_final_accuracy_at_least_75pct':all(p['metrics'][k]['mean']>=.75 for k in ['plant_changed','letter_retained']),
  'paired_gain_over_original_at_least_10pp':gain['mean']>=.1,
  'descriptive_paired_lower_endpoint_positive':gain['mean']-gain['normal95_half_width']>0,
  'nonlinear_gain_over_original_at_least_10pp':ng>=.1,'simple_regression_no_worse_than_5pp':lg>=-.05,
  'untouched_route_state_and_output_retention_exact':True,
  'every_populated_joint_rule_stratum_at_least_65pct':all(c['metrics']['final_mean']['mean']>=.65 for c in p['joint_rule_strata'].values() if c['histories']),
  'every_task_attribute_stratum_at_least_65pct':all(c['accuracy']>=.65 for c in p['joint_attribute_strata'].values())}
 image={}
 for s in [0,1]:
  image[str(s)]={}
  for pool,ids in [('teacher',list(range(128))),('test',list(range(256,384)))]:
   active=sorted({int(np.flatnonzero(primary[i])[0]) for i in ids if routes[i]==s})
   assert all(4*s<=j<4*s+4 for j in active)
   image[str(s)][pool]={'observed_active_coordinates':active,'observed_one_hot_image_count':len(active),'exact_rank':len(active)}
 rank={'effective_feature_span_rank_per_route':4,'two_route_direct_sum_rank':8,'ambient_dimensions_per_route':577,
  'basis_scale':127,'exact_score_basis_diagonal':127**2,'exact_score_basis_determinant_per_route':(127**2)**4,
  'observed_images':image,'aggregate_image':'C=127*z, z integer4; L1(z)<=32, full-window sum parity even (necessary conditions)',
  'scope':'Four exact basis-score functionals determine the current route aggregate. Sign-only results do not give magnitudes; queue order is a separate object.',
  'encryption_or_key_instantiation':False,'security_attack_executed':False,'features_sha256':sha(ROOT/'features.npz')}
 save(ROOT/'image_rank_scope.json',rank)
 out={'execution_passed':True,'useful_restricted_successor':all(gates.values()),'acceptance':gates,'factual':factual,
  'results':results,'paired_primary_minus':paired,'nonlinear_gain':ng,'simple_gain':lg,
  'denominators':{'unique_new_texts':128,'new_histories':64,'methods':3,'checkpoints':3,'scores':73728,
   'final_queries_per_method':8192,'new_factual_bits':256,'teacher_factual_bits_reused':256,'reset_accuracy':.5},
  'primary_feature_encoding_wall_seconds':semantic_cost,'original_feature_encoding_wall_seconds':baseline_cost,
  'baseline_teacher_cache_exact':True,'freeze_sha256':sha(ROOT/'freeze.json'),'features_sha256':sha(ROOT/'features.npz'),
  'checkpoint_states_sha256':sha(ROOT/'checkpoint_states.npz'),'raw_scores_sha256':sha(ROOT/'raw_scores.json'),
  'rank_scope_sha256':sha(ROOT/'image_rank_scope.json'),'evaluation_wall_seconds':time.perf_counter()-t,
  'evaluation_cpu_seconds':time.process_time()-cpu,'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
  'cryptographic_success_claim':False,'new_prompt_or_feature_choices':0}
 save(ROOT/'results.json',out)
 print(json.dumps({k:v for k,v in out.items() if k not in ['results','factual']},indent=2))
 print(json.dumps({'factual':{k:v for k,v in factual.items() if k!='errors'},'final_correct':{name:m['correct_final'] for name,m in results.items()}},indent=2))
if __name__=='__main__':main()
