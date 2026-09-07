"""PREPARED, not yet executed: one private text -> signed int8 issuer vector.

Uses only pinned local assets and public teacher calibration. Actual execution
and single-prompt/batched quantization agreement must be recorded before claiming
this encoder has been integrated. This command neither encrypts nor signs.
"""
import argparse,json,os,sys,time
from pathlib import Path
sys.dont_write_bytecode=True

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',required=True,help='Issuer-only JSON: text, route, label (+1/-1)')
    parser.add_argument('--output',required=True,help='Issuer-only vector JSON; mode0600')
    parser.add_argument('--expect-record-id',type=int,help='Optional exact quantized cached-vector comparison')
    args=parser.parse_args()
    for k in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[k]='1'
    os.environ['TOKENIZERS_PARALLELISM']='false'
    import numpy as np
    import torch
    from transformers import AutoTokenizer,AutoModelForCausalLM
    from build_mapping import ROOT,BASE,load,sha
    data=load(args.input);assert set(data)=={'text','route','label'}
    assert isinstance(data['text'],str) and data['route'] in [0,1] and data['label'] in [-1,1]
    policy=load(ROOT/'encoder_policy.json');cal=policy['policies_by_public_route'][str(data['route'])]
    inventory=load(ROOT/'encoder_feasibility.json');modelpath=Path(inventory['model_path'])
    assert inventory['revision']==policy['revision']
    assert all(sha(modelpath/name)==row['sha256'] for name,row in inventory['model_files'].items())
    torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
    started=time.perf_counter()
    tokenizer=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
    tokenizer.pad_token=tokenizer.eos_token;tokenizer.padding_side='right'
    model=AutoModelForCausalLM.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False,
        dtype=torch.float32,attn_implementation='eager').eval().requires_grad_(False)
    loaded=time.perf_counter();captured={}
    def hook(module,inputs,output):captured['mean10_source']=output
    handle=model.model.layers[9].register_forward_hook(hook)
    with torch.inference_mode():
        batch=tokenizer([data['text']],padding=True,return_tensors='pt')
        model.model(**batch,use_cache=False,return_dict=True)
        mask=batch['attention_mask'][:,:,None];n=batch['attention_mask'].sum(1)
        hidden=((captured['mean10_source']*mask).sum(1)/n[:,None])[0].numpy().astype(np.float64)
    handle.remove();finished=time.perf_counter()
    feature=np.r_[hidden-np.array(cal['center'],dtype=np.float64),1.0]/cal['scale']
    vector=data['label']*np.clip(np.rint(feature*127),-127,127).astype(np.int64)
    assert vector.shape==(577,)
    if args.expect_record_id is not None:
        record=load(BASE/'representation_records.json')[args.expect_record_id]
        assert record['text']==data['text'] and record['skill']==data['route']
        cache=np.load(BASE/'representation_features.npz')['mean_10'][args.expect_record_id].astype(np.float64)
        expected=np.r_[cache-np.array(cal['center']),1.0]/cal['scale']
        expected=data['label']*np.clip(np.rint(expected*127),-127,127).astype(np.int64)
        differences=int(np.count_nonzero(vector!=expected))
        assert differences==0,f'Quantized batch/single-prompt mismatch in {differences} coordinates; no vector emitted'
    output=Path(args.output);output.parent.mkdir(parents=True,exist_ok=True)
    fd=os.open(output,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)
    with os.fdopen(fd,'w') as stream:json.dump(vector.tolist(),stream,separators=(',',':'));stream.write('\n')
    os.chmod(output,0o600)
    print(json.dumps({'encoded_vectors':1,'dimension':577,'load_seconds':loaded-started,
        'feature_seconds':finished-loaded,'cached_quantized_comparison':args.expect_record_id is not None,
        'scope':'Issuer plaintext processing; output must enter issuer encryption before host admission'}))

if __name__=='__main__':main()
