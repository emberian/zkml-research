"""Independent cache/metadata audit. Uses NumPy; does not execute the model."""
from pathlib import Path
import hashlib,json,os,sys
sys.dont_write_bytecode=True
import numpy as np
from build_mapping import ROOT,BASE,ENC,load,sha,vdigest,save

def main():
    records=load(BASE/'representation_records.json');hidden=np.load(BASE/'representation_features.npz')['mean_10'].astype(np.float64)
    model=np.column_stack([hidden,np.ones(len(hidden))]);policies={}
    for route in [0,1]:
        ids=[r['id'] for r in records if r['pool']=='teach' and r['skill']==route]
        allids=[r['id'] for r in records if r['skill']==route]
        center=hidden[ids].mean(0);model[allids,:-1]-=center
        scale=float(np.linalg.norm(model[ids],axis=1).max());model[allids]/=scale
        policies[str(route)]={'teacher_record_ids':ids,'center':center.tolist(),'scale':scale}
    quantized=np.clip(np.rint(model*127),-127,127).astype(np.int8)
    mapping=load(ROOT/'issuer_oracle/mapping.json');lines=(ENC/'fixture.txt').read_text().splitlines()
    inputs={x['event_id']:x for x in load(ROOT/'issuer_oracle/input_index.json')['events']}
    count=0
    for e in mapping['events']:
        vector=list(map(int,lines[e['source_fixture_line']-1].split()[6:]))
        raw=quantized[e['record_id']].astype(np.int64)
        expected=(e['observed_label']*raw if e['kind']=='Learn' else raw).tolist()
        assert vector==expected
        record=records[e['record_id']];assert e['source_record']==record
        idx=inputs[e['event_id']];path=Path(idx['issuer_vector_path'] if e['kind']=='Learn' else idx['public_query_vector_path'])
        assert load(path)==expected
        if e['kind']=='Learn':assert path.stat().st_mode&0o777==0o600
        count+=1
    public=load(ROOT/'public_event_index.json')['events']
    allowed={'event_id','history_index','event_ordinal','kind','route'}
    assert len(public)==480 and all(set(e)==allowed for e in public)
    assert public==[{k:e[k] for k in allowed} for e in mapping['events']]
    manifest=load(ROOT/'mapping_manifest.json')
    for p,h in manifest['sources_sha256'].items():assert sha(p)==h
    for p,h in manifest['outputs_sha256'].items():assert sha(p)==h
    source_model=load(BASE/'representation_model_manifest.json')
    assert sha(BASE/'representation_features.npz')==source_model['features_sha256']
    assert sha(BASE/'representation_PROTOCOL.md')==source_model['protocol_sha256']
    assert sha(BASE/'representation_selection.json')==load(BASE/'representation_results.json')['selection_sha256']
    save(ROOT/'encoder_policy.json',{'schema':'SMOLLM2_MEAN10_ISSUER_POLICY_V1',
      'exposure':'Public calibration from unlabelled public synthetic teacher text; no history-dependent state or labels',
      'model':'HuggingFaceTB/SmolLM2-135M','revision':'93efa2f097d58c2a74874c7e644dbc9b0cee75a2',
      'representation':'masked mean of direct block9 output; eager attention, CPU float32, no padding tokens',
      'source_feature_sha256':sha(BASE/'representation_features.npz'),'quantization':'clip(rint(127*normalized),-127,127); NumPy ties-to-even',
      'dimension':577,'bias_before_scale':1,'policies_by_public_route':policies})
    result={'passed':True,'all_event_vectors_reconstructed_from_cached_model_features':count,
      'model_executed':False,'teaching_vectors':384,'public_query_events':96,'public_index_exact_field_allowlist':True,
      'source_and_output_hashes_checked':True,'script_sha256':sha(__file__),
      'encoder_policy_sha256':sha(ROOT/'encoder_policy.json')}
    save(ROOT/'audit_mapping.json',result);print(json.dumps(result,indent=2))

if __name__=='__main__':main()
