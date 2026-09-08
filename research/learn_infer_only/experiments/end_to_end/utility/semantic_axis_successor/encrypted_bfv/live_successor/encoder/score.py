"""One model load and one frozen forward-scoring pass; no oracle read."""
import sys,time
sys.dont_write_bytecode=True
START=time.perf_counter();CPUSTART=time.process_time()
from common import *
import torch
from transformers import AutoModelForCausalLM
def main():
 assert not (ROOT/'score_started.json').exists(),'No scoring retries'
 freeze=load(ROOT/'freeze.json')
 for p,h in freeze['source_sha256'].items():assert sha(p)==h,p
 verify_priors();modelpath=Path(freeze['model_path'])
 for name,row in freeze['model_files'].items():assert sha(modelpath/name)==row['sha256'],name
 assert torch.backends.mps.is_available(),'No backend fallback'
 torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
 save(ROOT/'score_started.json',{'freeze_sha256':sha(ROOT/'freeze.json'),'attempt':1,'pid':os.getpid()})
 before=memory();t=time.perf_counter();c=time.process_time()
 model=AutoModelForCausalLM.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False,
  dtype=torch.float16,attn_implementation='eager').eval().requires_grad_(False)
 cpu_loaded=time.perf_counter();cpu_loadcpu=time.process_time()-c
 model.to('mps');torch.mps.synchronize();loaded=time.perf_counter();after_load=memory()
 assert model.config._attn_implementation=='eager'
 assert next(model.parameters()).dtype==torch.float16
 inputs=load(ROOT/'issuer_inputs.json');rows=[];batches=[]
 with torch.inference_mode():
  for start in range(0,len(inputs),8):
   batch=inputs[start:start+8];width=max(r['token_count'] for r in batch)
   padded=[];masks=[]
   for r in batch:
    n=width-r['token_count'];padded.append([freeze['pad_token_id']]*n+r['token_ids'])
    masks.append([0]*n+[1]*r['token_count'])
   tokens=torch.tensor(padded,dtype=torch.long,device='mps')
   mask=torch.tensor(masks,dtype=torch.long,device='mps')
   positions=mask.cumsum(-1)-1;positions.masked_fill_(mask==0,0)
   assert bool(torch.all(mask[:,-1]==1).item())
   torch.mps.synchronize();t0=time.perf_counter();c0=time.process_time()
   result=model(input_ids=tokens,attention_mask=mask,position_ids=positions,
    use_cache=False,logits_to_keep=1,return_dict=True)
   torch.mps.synchronize();t1=time.perf_counter();c1=time.process_time()
   assert result.logits.shape[0]==len(batch) and result.logits.shape[1]==1
   assert result.past_key_values is None
   # Pin likelihood arithmetic to float32 CPU after the actual MPS float16 forward.
   logits=result.logits[:,0,:].float().cpu()
   assert bool(torch.isfinite(logits).all())
   denom=torch.logsumexp(logits,dim=-1)
   for k,r in enumerate(batch):
    aid=r['alternative_token_ids_in_bit_order'];two=logits[k,aid]
    loglik=two-denom[k];conditional=torch.softmax(two,dim=-1)
    row={key:r[key] for key in ['example_index','record_id','task','axis','framing','token_count','alternative_token_ids_in_bit_order']}
    row.update({'batch_index':len(batches),'logits_in_bit_order':two.tolist(),
     'full_vocabulary_logsumexp':denom[k].item(),'log_likelihoods_in_bit_order':loglik.tolist(),
     'conditional_probabilities_in_bit_order':conditional.tolist(),
     'alternative_probability_mass':torch.exp(loglik).sum().item(),
     'unconstrained_top1_token_id':logits[k].argmax().item(),
     'unconstrained_top1_is_alternative':logits[k].argmax().item() in aid,
     'exact_tie':bool((two[0]==two[1]).item()),'predicted_bit':0 if two[0]>=two[1] else 1})
    rows.append(row)
   t2=time.perf_counter();c2=time.process_time()
   telemetry={'batch_index':len(batches),'first_example_index':start,'examples':len(batch),
    'nonpadding_tokens':sum(r['token_count'] for r in batch),'padded_tokens':len(batch)*width,
    'forward_wall_seconds':t1-t0,'forward_process_cpu_seconds':c1-c0,
    'likelihood_and_transfer_wall_seconds':t2-t1,'likelihood_and_transfer_process_cpu_seconds':c2-c1,
    'memory_after_batch':memory()}
   batches.append(telemetry);save(ROOT/'raw_scores.json',rows);save(ROOT/'batch_costs.json',batches)
   print(json.dumps(telemetry),flush=True)
   del result,logits,tokens,mask,positions
 verify_priors()
 out={'execution_completed':True,'score_attempts':1,'actual_forward_examples':len(rows),'actual_model_forward_calls':len(batches),
  'new_test_texts':1,'framings':1,'semantic_bits_per_framing':2,'pairs_per_framing':1,
  'heldout_inputs':1,'utility_history_runs':0,'generated_tokens':0,'weight_updates':0,
  'model_parameter_count':sum(p.numel() for p in model.parameters()),'runtime':runtime(),
  'settings':{'device':'mps','dtype':'float16','source_weight_dtype':'bfloat16','attention':'eager',
   'enable_thinking':False,'use_cache':False,'logits_to_keep':1,'model_eval':True,'inference_mode':True,
   'generation_invoked':False,'likelihood_dtype':'float32 CPU','batch_size':8,'left_padding':True,
   'position_ids':'attention_mask.cumsum(-1)-1; pad positions zero','tie_rule':'bit0',
   'threads':2,'interop_threads':1,'seed':7901},
  'nonpadding_tokens':sum(x['nonpadding_tokens'] for x in batches),
  'padded_tokens':sum(x['padded_tokens'] for x in batches),
  'cpu_load_wall_seconds':cpu_loaded-t,'cpu_load_process_cpu_seconds':cpu_loadcpu,
  'transfer_to_mps_wall_seconds':loaded-cpu_loaded,
  'forward_wall_seconds':sum(x['forward_wall_seconds'] for x in batches),
  'forward_process_cpu_seconds':sum(x['forward_process_cpu_seconds'] for x in batches),
  'likelihood_and_transfer_wall_seconds':sum(x['likelihood_and_transfer_wall_seconds'] for x in batches),
  'total_wall_seconds_including_imports':time.perf_counter()-START,
  'total_process_cpu_seconds_including_imports':time.process_time()-CPUSTART,
  'memory_before_load':before,'memory_after_load':after_load,'memory_at_end':memory(),
  'freeze_sha256':sha(ROOT/'freeze.json'),'raw_scores_sha256':sha(ROOT/'raw_scores.json'),
  'prior_bytes_preserved':True,'oracle_parsed_by_scoring_process':False}
 save(ROOT/'score_results.json',out);print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':main()
