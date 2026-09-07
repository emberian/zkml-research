"""Attribute diagnostic and architecture-only cost estimates; no inference."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 source=ROOT.parent/'attribute_calibration';selection=load(source/'selection.json');r=load(source/'results.json');audit=load(source/'audit.json')
 save(ROOT/'failure_diagnostic.json',{'source_sha256':{str(source/n):sha(source/n) for n in ['selection.json','results.json','audit.json']},
  'chosen_lambda':selection['chosen_lambda'],'teacher_and_selection':selection['grid'][str(selection['chosen_lambda'])],
  'test':r['test_attribute_report'],'all_route_template_cells':audit['attribute_accuracy_by_all_route_template_cells'],
  'new_model_evaluation':False,'new_hyperparameters_or_ontology':False})
 candidates=load(ROOT/'candidates.json');estimates={}
 for name,row in candidates.items():
  cfg=row['config'];h=cfg['hidden_size'];I=cfg['intermediate_size'];n=cfg['num_hidden_layers'];L=40
  if cfg['model_type']=='bert':
   linear_per_token=4*h*h+2*h*I;qwidth=h
  else:
   head=cfg.get('head_dim',h//cfg['num_attention_heads']);qwidth=head*cfg['num_attention_heads'];kvwidth=head*cfg.get('num_key_value_heads',cfg['num_attention_heads'])
   linear_per_token=2*h*qwidth+2*h*kvwidth+3*h*I
  mac=n*(L*linear_per_token+2*L*L*qwidth)
  estimates[name]={'sequence_length_assumed':L,'dense_linear_and_attention_MACs_per_text':mac,
    'two_FLOPs_per_MAC':2*mac,'float32_parameter_storage_lower_bound_bytes':4*row['floating_tensor_scalars'],
    'on_disk_weight_bytes':row['weight_file_bytes'],'source_config':str(Path(row['path'])/'config.json')}
 save(ROOT/'cost_estimates.json',{'label':'DERIVED, not executed model timings','candidates':estimates,
  'formula':'BERT n*(L*(4h²+2hI)+2L²h); gated decoder n*(L*(2hQ+2hKV+3hI)+2L²Q)',
  'excluded':['embedding lookup','biases','normalization','activation functions','softmax','pooling/pooler','padding variation','framework and memory traffic'],
  'not_a_latency_or_peak_memory_estimate':True,
  'proposed_fixed_projection_768_to_576':{'public_scalar_products':768*576,'reduction_adds':576*767,
    'float32_matrix_bytes':768*576*4,'float64_matrix_bytes':768*576*8,'seeded_Rademacher_generation_possible':True},
  'raw769_control_not_577_interface':True})
 print(json.dumps({'diagnostic_written':True,'costs_written':True,'model_forwards':0}))
if __name__=='__main__':main()
