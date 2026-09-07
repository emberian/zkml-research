"""Human-readable full denominator/error tables, cost rows and hash census."""
import sys,csv
sys.dont_write_bytecode=True
from common import *
def main():
 assert not (ROOT/'manifest.json').exists(),'Preserve final census'
 verify();assert load(ROOT/'audit.json')['passed']
 r=load(ROOT/'results.json');big=load(ROOT/'score_results.json');small=load(ROOT/'smol_test.extraction.json')
 records=load(ROOT/'records.json');pred={x['record_id']:x for x in load(ROOT/'test_predictions.json')}
 with (ROOT/'test_decisions.csv').open('w',newline='') as f:
  w=csv.writer(f,lineterminator='\n');w.writerow(['record_id','task','template','entity','gold_a','gold_b','predicted_a','predicted_b','both_correct','text'])
  for rec in records[256:]:
   p=pred[rec['id']];w.writerow([rec['id'],['plant','letter'][rec['skill']],rec['template'],rec['entity'],rec['a'],rec['b'],
    p['a'],p['b'],int(p['a']==rec['a'] and p['b']==rec['b']),rec['text']])
 errors=['# All fresh factual errors','',
  '[EXECUTED] Every error among 256 axis decisions on 128 new texts. No errors are omitted. The full 128-text denominator is in `test_decisions.csv`; raw likelihoods remain in `raw_scores.json`. All rows below are plant soil errors: true wet (0), predicted dry (1). No exact tie occurred.','',
  '| Record | True pair | Wet logit | Dry logit | Full source text |','|---|---|---:|---:|---|']
 for e in r['factual']['errors']:
  x,y=e['logits_in_bit_order'];errors.append(f"| {e['record_id']} | {e['true_pair']} | {x} | {y} | {e['text']} |")
 errors += ['', '[DERIVED] These are retained failures, not examples used to alter the prompt, parser, ontology, decoder, feature map or gates. The common first-template phrase is visible in every row; this is a descriptive association, not an identified causal mechanism.', '']
 (ROOT/'ERRORS.md').write_text('\n'.join(errors))
 rows=[]
 def add(metric,value,unit,source):rows.append([metric,value,unit,source])
 for prefix,obj in [('smollm3',big),('smollm2',small)]:
  add(prefix+'_parameters',obj.get('model_parameter_count',obj.get('parameter_count')),'parameters','Actual loaded model census')
  add(prefix+'_process_wall',obj['total_wall_seconds_including_imports'],'seconds','Actual child process interval including imports; shared local load')
  add(prefix+'_forward_wall',obj['forward_wall_seconds'],'seconds','Measured batch forward intervals')
  add(prefix+'_real_input_tokens',obj.get('nonpadding_tokens',obj.get('unpadded_tokens')),'tokens','Actual tokenizer counts')
  add(prefix+'_padded_input_tokens',obj['padded_tokens'],'tokens','Actual padded batches')
  add(prefix+'_cpu_seconds',obj.get('total_process_cpu_seconds_including_imports',obj.get('total_cpu_seconds_including_imports')),'seconds','Actual process CPU; not accelerator duration')
 add('smollm3_actual_batch_forwards',big['actual_model_forward_calls'],'calls','32 batches /256 axis examples /128 new texts')
 add('smollm2_actual_batch_forwards',len(small['batches']),'calls','8 batches /128 new texts')
 add('teacher_model_reencodings',0,'examples','Frozen selected A bits and original mean10 teacher cache reused')
 add('smollm3_peak_process_rss',big['memory_at_end']['process_high_water_rss_bytes_macos'],'bytes','macOS high-water RSS; unified memory figures not additive')
 add('smollm3_final_mps_current',big['memory_at_end']['mps_current_allocated_bytes'],'bytes','Actual MPS counter')
 add('smollm3_final_mps_driver',big['memory_at_end']['mps_driver_allocated_bytes'],'bytes','Actual MPS counter; includes allocator/cache; not additive with RSS')
 add('smollm2_peak_process_rss',small['process_high_water_rss_bytes_macos'],'bytes','Actual macOS high-water RSS')
 add('semantic_and_gold_feature_conversion',r['primary_feature_encoding_wall_seconds'],'seconds','Measured conversion of 256 inferred and384 diagnostic pairs; no model inside interval')
 add('original_feature_conversion',r['original_feature_encoding_wall_seconds'],'seconds','Measured cached/new hidden concatenation and public center/scale quantization')
 add('utility_evaluation',r['evaluation_wall_seconds'],'seconds','Three methods /64 histories /3 checkpoints /128 queries')
 add('utility_prediction_records',73728,'scores','Exact full paired denominator')
 add('effective_aggregate_rank_per_route',4,'coordinates','One-hot basis; exact image/rank scope')
 add('ambient_coordinates_per_route',577,'coordinates','Padding kept for arithmetic format; no privacy claim')
 add('one_route_aggregate_coordinate_bound',4064,'absolute integer value','32*127')
 add('one_hot_absolute_score_bound',516128,'absolute integer value','32*127^2')
 for n in ['features.npz','checkpoint_states.npz','issuer_inputs.json','teacher_predictions.json','test_predictions.json','raw_scores.json','results.json']:
  add(n,(ROOT/n).stat().st_size,'bytes','Actual retained artifact; public synthetic fixture/evidence')
 with (ROOT/'costs.csv').open('w',newline='') as f:
  w=csv.writer(f,lineterminator='\n');w.writerow(['metric','value','unit','provenance']);w.writerows(rows)
 for name,columns in [('costs.csv',4),('test_decisions.csv',10)]:
  with (ROOT/name).open(newline='') as f:assert all(len(row)==columns for row in csv.reader(f))
  assert b'\r' not in (ROOT/name).read_bytes()
 files={str(p.relative_to(ROOT)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(ROOT.rglob('*')) if p.is_file() and p.name!='manifest.json'}
 save(ROOT/'manifest.json',{'files':files,'files_count':len(files),'freeze_sha256':sha(ROOT/'freeze.json'),
  'scope':'Fresh restricted plaintext semantic issuer utility; four effective aggregate coordinates per route; no cryptographic success'})
 print(json.dumps({'files':len(files),'manifest_sha256':sha(ROOT/'manifest.json'),'report_sha256':sha(ROOT/'REPORT.md'),'total_file_bytes':sum(x['bytes'] for x in files.values())}))
if __name__=='__main__':main()
