"""Execute real pinned SmolLM2 weights; extract only synthetic public-domain features."""
import os
os.environ['HF_HUB_OFFLINE'] = '1'
os.environ['TRANSFORMERS_OFFLINE'] = '1'
os.environ['TOKENIZERS_PARALLELISM'] = 'false'
import hashlib, json, platform, sys, time
from pathlib import Path
import numpy as np
import torch
from transformers import AutoTokenizer, AutoModelForCausalLM

ROOT = Path(__file__).resolve().parent
REV = '93efa2f097d58c2a74874c7e644dbc9b0cee75a2'
MODEL = Path.home()/'.cache/huggingface/hub/models--HuggingFaceTB--SmolLM2-135M/snapshots'/REV

def sha(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        while b:=f.read(1024*1024): h.update(b)
    return h.hexdigest()

def main():
    torch.set_num_threads(2)
    torch.set_num_interop_threads(1)
    torch.manual_seed(7901)
    t=time.perf_counter()
    tok=AutoTokenizer.from_pretrained(MODEL,local_files_only=True,trust_remote_code=False)
    tok.pad_token=tok.eos_token
    tok.padding_side='right'
    model=AutoModelForCausalLM.from_pretrained(MODEL,local_files_only=True,
        trust_remote_code=False,torch_dtype=torch.float32,attn_implementation='eager')
    model.eval()
    model.requires_grad_(False)
    load_seconds=time.perf_counter()-t
    xy=np.array([(x,y) for x in range(-8,9) for y in range(-8,9)],dtype=np.int64)
    prompts=[f'Sensor reading: x={x}, y={y}. Response class:' for x,y in xy]
    a=tok.encode(' A',add_special_tokens=False); b=tok.encode(' B',add_special_tokens=False)
    assert len(a)==len(b)==1,(a,b)
    hs=[]; logits=[]; lengths=[]; batch_times=[]
    with torch.inference_mode():
        for start in range(0,len(prompts),16):
            batch=tok(prompts[start:start+16],padding=True,return_tensors='pt')
            n=batch['attention_mask'].sum(1)
            tb=time.perf_counter()
            out=model.model(**batch,use_cache=False,return_dict=True)
            h=out.last_hidden_state[torch.arange(len(n)),n-1]
            # Exactly the two selected tied LM-head rows; avoids irrelevant full logits.
            selected=h @ model.lm_head.weight[[a[0],b[0]]].T
            batch_times.append(time.perf_counter()-tb)
            hs.append(h.numpy());logits.append(selected.numpy());lengths.extend(n.tolist())
            print(json.dumps({'batch_start':start,'batch_seconds':batch_times[-1],
                              'max_tokens':int(n.max())}),flush=True)
    hidden=np.concatenate(hs); selected_logits=np.concatenate(logits)
    np.savez(ROOT/'features.npz',xy=xy,hidden=hidden,selected_logits=selected_logits,
             token_lengths=np.array(lengths))
    (ROOT/'prompts.json').write_text(json.dumps(prompts,indent=2)+'\n')
    meta={'model':'HuggingFaceTB/SmolLM2-135M','revision':REV,'device':'cpu','dtype':'float32',
      'python':sys.version,'platform':platform.platform(),'torch':torch.__version__,
      'transformers':__import__('transformers').__version__,'numpy':np.__version__,
      'model_parameter_count':sum(p.numel() for p in model.parameters()),
      'trainable_backbone_parameters':sum(p.numel() for p in model.parameters() if p.requires_grad),
      'config':model.config.to_dict(),'selected_token_ids':{'A':a[0],'B':b[0]},
      'num_prompts':len(prompts),'prompt_token_length_counts':{str(n):lengths.count(n) for n in set(lengths)},
      'load_seconds':load_seconds,'batch_seconds':batch_times,'feature_seconds':sum(batch_times),
      'features_shape':list(hidden.shape),'thread_count':torch.get_num_threads(),
      'model_files':{p.name:{'sha256':sha(p),'bytes':p.stat().st_size} for p in MODEL.iterdir() if p.is_file()},
      'extract_script_sha256':sha(__file__),'protocol_sha256':sha(ROOT/'PROTOCOL.md'),
      'features_sha256':sha(ROOT/'features.npz')}
    (ROOT/'model_manifest.json').write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'complete':True,'load_seconds':load_seconds,'feature_seconds':sum(batch_times),
                      'hidden_shape':list(hidden.shape),'parameter_count':meta['model_parameter_count']}),flush=True)

if __name__=='__main__': main()
