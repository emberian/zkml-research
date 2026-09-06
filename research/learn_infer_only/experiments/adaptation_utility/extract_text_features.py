"""Actual frozen-model execution on synthetic text only; no labels in model inputs."""
import os
os.environ['HF_HUB_OFFLINE']='1';os.environ['TRANSFORMERS_OFFLINE']='1';os.environ['TOKENIZERS_PARALLELISM']='false'
import json,time
from pathlib import Path
import numpy as np
import torch
from transformers import AutoTokenizer,AutoModelForCausalLM
from extract_features import MODEL,REV,sha
from text_transfer_data import make_records
ROOT=Path(__file__).resolve().parent

def main():
    torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
    records=make_records();prompts=[r['text'] for r in records]
    (ROOT/'text_transfer_records.json').write_text(json.dumps(records,indent=2)+'\n')
    t=time.perf_counter()
    tok=AutoTokenizer.from_pretrained(MODEL,local_files_only=True,trust_remote_code=False)
    tok.pad_token=tok.eos_token;tok.padding_side='right'
    model=AutoModelForCausalLM.from_pretrained(MODEL,local_files_only=True,trust_remote_code=False,
        dtype=torch.float32,attn_implementation='eager').eval().requires_grad_(False)
    load_seconds=time.perf_counter()-t;hs=[];lengths=[];times=[];padded=[]
    with torch.inference_mode():
        for start in range(0,len(prompts),16):
            b=tok(prompts[start:start+16],padding=True,return_tensors='pt');n=b['attention_mask'].sum(1)
            t=time.perf_counter();o=model.model(**b,use_cache=False,return_dict=True)
            h=o.last_hidden_state[torch.arange(len(n)),n-1];times.append(time.perf_counter()-t)
            hs.append(h.numpy());lengths.extend(n.tolist());padded.append(int(b['input_ids'].shape[1]))
            print(json.dumps({'batch_start':start,'seconds':times[-1],'padded_tokens':padded[-1]}),flush=True)
    np.savez(ROOT/'text_transfer_features.npz',hidden=np.concatenate(hs),lengths=np.array(lengths))
    m={'revision':REV,'model':'HuggingFaceTB/SmolLM2-135M','device':'cpu','dtype':'float32','no_gradients':True,
      'use_cache':False,'remote_code':False,'records':len(records),'load_seconds':load_seconds,
      'feature_seconds':sum(times),'batch_seconds':times,'batch_padded_tokens':padded,
      'actual_token_length_counts':{str(n):lengths.count(n) for n in set(lengths)},
      'script_sha256':sha(__file__),'data_script_sha256':sha(ROOT/'text_transfer_data.py'),
      'protocol_sha256':sha(ROOT/'TEXT_TRANSFER_PROTOCOL.md'),'features_sha256':sha(ROOT/'text_transfer_features.npz'),
      'base_model_manifest_sha256':sha(ROOT/'model_manifest.json')}
    (ROOT/'text_transfer_model_manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'complete':True,'feature_seconds':sum(times),'shape':list(np.concatenate(hs).shape)}),flush=True)

if __name__=='__main__':main()
