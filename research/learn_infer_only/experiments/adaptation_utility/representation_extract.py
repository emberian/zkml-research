"""One actual full-model pass collects four fixed representations of new text."""
import os
os.environ['HF_HUB_OFFLINE']='1';os.environ['TRANSFORMERS_OFFLINE']='1';os.environ['TOKENIZERS_PARALLELISM']='false'
import json,time
from pathlib import Path
import numpy as np
import torch
from transformers import AutoTokenizer,AutoModelForCausalLM
from extract_features import MODEL,REV,sha
from representation_data import make_records
ROOT=Path(__file__).resolve().parent

def main():
    torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
    rec=make_records();prompts=[r['text'] for r in rec]
    (ROOT/'representation_records.json').write_text(json.dumps(rec,indent=2)+'\n')
    t=time.perf_counter()
    tok=AutoTokenizer.from_pretrained(MODEL,local_files_only=True,trust_remote_code=False)
    tok.pad_token=tok.eos_token;tok.padding_side='right'
    model=AutoModelForCausalLM.from_pretrained(MODEL,local_files_only=True,trust_remote_code=False,
        dtype=torch.float32,attn_implementation='eager').eval().requires_grad_(False)
    load_seconds=time.perf_counter()-t
    captured={}
    def hook(index):
        def save(module,args,output):captured[index]=output
        return save
    handles=[model.model.layers[i].register_forward_hook(hook(i)) for i in [9,19]]
    gathered={k:[] for k in ['last_30','mean_10','mean_20','mean_30']};times=[];lengths=[];padding=[]
    with torch.inference_mode():
        for start in range(0,len(prompts),16):
            b=tok(prompts[start:start+16],padding=True,return_tensors='pt');n=b['attention_mask'].sum(1)
            captured.clear();t=time.perf_counter();o=model.model(**b,use_cache=False,return_dict=True)
            assert set(captured)=={9,19}
            mask=b['attention_mask'][:,:,None]
            for name,h in [('mean_10',captured[9]),('mean_20',captured[19]),('mean_30',o.last_hidden_state)]:
                pooled=(h*mask).sum(1)/n[:,None]
                assert pooled.shape==(len(n),576)
                gathered[name].append(pooled.numpy())
            gathered['last_30'].append(o.last_hidden_state[torch.arange(len(n)),n-1].numpy())
            times.append(time.perf_counter()-t);lengths.extend(n.tolist());padding.append(int(b['input_ids'].shape[1]))
            print(json.dumps({'batch_start':start,'seconds':times[-1],'padded_tokens':padding[-1]}),flush=True)
    for handle in handles:handle.remove()
    arrays={k:np.concatenate(v) for k,v in gathered.items()};arrays['lengths']=np.array(lengths)
    np.savez(ROOT/'representation_features.npz',**arrays)
    m={'model':'HuggingFaceTB/SmolLM2-135M','revision':REV,'device':'cpu','dtype':'float32','records':len(rec),
      'use_cache':False,'remote_code':False,'trainable_parameters':sum(p.numel() for p in model.parameters() if p.requires_grad),
      'representations':{'last_30':'final RMS-normalized final real token',
        'mean_10':'masked mean of direct block9 output (10 decoder blocks)',
        'mean_20':'masked mean of direct block19 output (20 decoder blocks)',
        'mean_30':'masked mean of final RMS-normalized hidden states'},
      'load_seconds':load_seconds,'feature_seconds':sum(times),'batch_seconds':times,'batch_padded_tokens':padding,
      'actual_token_length_counts':{str(n):lengths.count(n) for n in set(lengths)},
      'script_sha256':sha(__file__),'data_script_sha256':sha(ROOT/'representation_data.py'),
      'protocol_sha256':sha(ROOT/'representation_PROTOCOL.md'),'features_sha256':sha(ROOT/'representation_features.npz'),
      'original_model_manifest_sha256':sha(ROOT/'model_manifest.json'),'requirements_sha256':sha(ROOT/'requirements-lock.txt')}
    (ROOT/'representation_model_manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'complete':True,'feature_seconds':sum(times),'representations':list(gathered)}),flush=True)

if __name__=='__main__':main()
