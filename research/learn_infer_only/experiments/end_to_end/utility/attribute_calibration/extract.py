"""One pinned local CPU model extraction after attribute selection is frozen."""
import hashlib,json,os,resource,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
for k in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[k]='1'
os.environ['TOKENIZERS_PARALLELISM']='false'
started=time.perf_counter();cpu_started=time.process_time()
import numpy as np
import torch
import transformers
from transformers import AutoTokenizer,AutoModelForCausalLM
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    assert not (ROOT/'extraction.json').exists(),'Preserve completed extraction'
    for path,digest in load(ROOT/'freeze.json')['source_sha256'].items():assert sha(path)==digest
    selection_sha=sha(ROOT/'selection.json');records=load(ROOT/'records.json')[256:]
    assert [r['id'] for r in records]==list(range(256,384))
    inv=load(ROOT.parent/'encoder_feasibility.json');modelpath=Path(inv['model_path'])
    for name,row in inv['model_files'].items():assert sha(modelpath/name)==row['sha256']
    torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
    t=time.perf_counter();tcpu=time.process_time()
    tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
    tok.pad_token=tok.eos_token;tok.padding_side='right'
    model=AutoModelForCausalLM.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False,
      dtype=torch.float32,attn_implementation='eager').eval().requires_grad_(False)
    load_wall=time.perf_counter()-t;load_cpu=time.process_time()-tcpu;captured={}
    def hook(module,inputs,output):captured['block9']=output
    handle=model.model.layers[9].register_forward_hook(hook);arrays=[];batches=[];lengths=[]
    with torch.inference_mode():
        for i in range(0,128,16):
            batch=tok([r['text'] for r in records[i:i+16]],padding=True,return_tensors='pt')
            t=time.perf_counter();tcpu=time.process_time();model.model(**batch,use_cache=False,return_dict=True)
            n=batch['attention_mask'].sum(1);mask=batch['attention_mask'][:,:,None]
            h=(captured['block9']*mask).sum(1)/n[:,None];assert h.shape==(16,576)
            arrays.append(h.numpy());lengths.extend(n.tolist())
            row={'first_record_id':256+i,'records':16,'padded_tokens':batch['input_ids'].shape[1],
              'wall_seconds':time.perf_counter()-t,'cpu_seconds':time.process_time()-tcpu}
            batches.append(row);print(json.dumps(row),flush=True)
    handle.remove();np.savez(ROOT/'new_features.npz',mean_10=np.concatenate(arrays),token_lengths=np.array(lengths))
    out={'executed':True,'new_texts':128,'backbone_training_steps':0,'parameter_count':sum(p.numel() for p in model.parameters()),
      'trainable_parameter_count':sum(p.numel() for p in model.parameters() if p.requires_grad),
      'model':'HuggingFaceTB/SmolLM2-135M','revision':inv['revision'],'model_path':str(modelpath),'model_files':inv['model_files'],
      'python':sys.version,'executable':sys.executable,'numpy':np.__version__,'torch':torch.__version__,'transformers':transformers.__version__,
      'settings':{'device':'cpu','dtype':'float32','attention':'eager','threads':2,'interop_threads':1,'seed':7901,
        'batch_size':16,'padding_side':'right','use_cache':False,'gradients':False,'blocks_actually_executed':30,
        'representation':'masked mean direct block9 output; padding excluded','local_files_only':True,'trust_remote_code':False},
      'selection_sha256':selection_sha,'script_sha256':sha(__file__),'records_sha256':sha(ROOT/'records.json'),
      'freeze_sha256':sha(ROOT/'freeze.json'),'features_sha256':sha(ROOT/'new_features.npz'),
      'load_wall_seconds':load_wall,'load_cpu_seconds':load_cpu,'batches':batches,
      'forward_wall_seconds':sum(r['wall_seconds'] for r in batches),'forward_cpu_seconds':sum(r['cpu_seconds'] for r in batches),
      'unpadded_tokens':sum(lengths),'padded_tokens':sum(r['records']*r['padded_tokens'] for r in batches),
      'token_length_histogram':{str(n):lengths.count(n) for n in sorted(set(lengths))},
      'total_wall_seconds_including_imports':time.perf_counter()-started,'total_cpu_seconds_including_imports':time.process_time()-cpu_started,
      'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    assert sha(ROOT/'selection.json')==selection_sha
    (ROOT/'extraction.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['model_files','batches']},indent=2),flush=True)
if __name__=='__main__':main()
