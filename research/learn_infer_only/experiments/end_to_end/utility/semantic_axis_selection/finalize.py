"""Emit cost rows and a complete local artifact census; no inference."""
import sys,csv
sys.dont_write_bytecode=True
from common import *
def main():
 assert not (ROOT/'manifest.json').exists(),'Preserve final artifact census'
 assert load(ROOT/'audit.json')['passed'];verify_priors()
 result=load(ROOT/'score_results.json');freeze=load(ROOT/'freeze.json')
 batches=load(ROOT/'batch_costs.json');rows=[]
 def add(metric,value,unit,provenance):rows.append([metric,value,unit,provenance])
 add('model_parameters',result['model_parameter_count'],'parameters','Actual loaded model parameter census')
 add('cached_weight_shards',sum(r['bytes'] for n,r in freeze['model_files'].items() if n.endswith('.safetensors')),'bytes','Frozen source snapshot; stored BF16')
 for name in ['total_wall_seconds_including_imports','total_process_cpu_seconds_including_imports',
  'cpu_load_wall_seconds','cpu_load_process_cpu_seconds','transfer_to_mps_wall_seconds',
  'forward_wall_seconds','forward_process_cpu_seconds','likelihood_and_transfer_wall_seconds']:
  add(name,result[name],'seconds','score_results.json; shared local load; intervals overlap where named')
 for name in ['actual_forward_examples','actual_model_forward_calls','nonpadding_tokens','padded_tokens','generated_tokens','weight_updates','heldout_inputs','utility_history_runs']:
  add(name,result[name],'count','score_results.json; one run only')
 for name,value in result['memory_at_end'].items():add(name,value,'bytes','Actual MPS/RSS counters; unified memory figures are not additive')
 for f,subset in [('A',batches[:32]),('B',batches[32:])]:
  wall=sum(r['forward_wall_seconds'] for r in subset)
  add(f'framing_{f}_forward_wall_seconds',wall,'seconds','32 batches; 256 axis examples; includes any shape warmup in that frame')
  add(f'framing_{f}_amortized_forward_seconds_per_two_axis_text',wall/128,'seconds','Batch-8 throughput accounting; not measured singleton latency')
 for n in ['issuer_inputs.json','teacher_oracle.json','raw_scores.json','scored_teacher_rows.json']:
  add(n,(ROOT/n).stat().st_size,'bytes','Actual retained public synthetic teacher artifact')
 with (ROOT/'costs.csv').open('w',newline='') as f:
  writer=csv.writer(f,lineterminator='\n');writer.writerow(['metric','value','unit','provenance']);writer.writerows(rows)
 with (ROOT/'costs.csv').open(newline='') as f:assert all(len(r)==4 for r in csv.reader(f))
 assert b'\r' not in (ROOT/'costs.csv').read_bytes()
 files={str(p.relative_to(ROOT)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(ROOT.rglob('*')) if p.is_file() and p.name!='manifest.json'}
 save(ROOT/'manifest.json',{'files':files,'freeze_sha256':sha(ROOT/'freeze.json'),
  'claim_scope':'Teacher-only forced-choice semantic selection; no held-out or encrypted utility test',
  'prior_preflight_bytes_preserved':True,'files_count':len(files)})
 print(json.dumps({'files':len(files),'manifest_sha256':sha(ROOT/'manifest.json'),'report_sha256':sha(ROOT/'REPORT.md'),'cost_rows':len(rows)}))
if __name__=='__main__':main()
