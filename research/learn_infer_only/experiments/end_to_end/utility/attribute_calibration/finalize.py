"""Freeze final evidence census and structured cost provenance; no experiments."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
    e=load(ROOT/'extraction.json');s=load(ROOT/'selection.json');r=load(ROOT/'results.json');a=load(ROOT/'audit.json')
    save(ROOT/'costs.json',{'executed':{'source':'extraction.json, selection.json, results.json, audit.json and command records',
      'model_extraction':{k:e[k] for k in ['new_texts','unpadded_tokens','padded_tokens','load_wall_seconds','load_cpu_seconds',
        'forward_wall_seconds','forward_cpu_seconds','total_wall_seconds_including_imports','total_cpu_seconds_including_imports',
        'process_high_water_rss_bytes_macos']},
      'extraction_process_wall_seconds':load(ROOT/'extract.command.json')['wall_seconds'],
      'five_lambda_fit_and_selection_including_hash_cache_checks':s['cost'],
      'encode_384_cached_hidden_vectors':r['encoding_cost'],'utility_evaluation':r['evaluation_cost'],
      'independent_audit_wall_seconds':a['wall_seconds']},
      'derived':{'added_public_policy_float64_count':2308,'added_public_policy_raw_bytes':2308*8,
        'two_heads_scalar_products_per_text_after_normalization':1152,'head_reduction_adds':1150,'intercept_adds':2,
        'clip_calls':2,'conjunction_products':4,'active_quantizations':4,
        'representation_dimensions':577,'nonzero_slots_per_route_at_most':4,'signed_int8_contribution_raw_bytes':577,
        'window_per_route':32,'generic_absolute_score_bound':577*32*127**2,
        'head_operations_are_plaintext':True,'new_encrypted_execution':False},
      'limits':['Process high-water RSS values are not additive.',
        'Calibration encode includes soft and hard arrays; shared normalization is timed with original577.',
        'Batched model time per text is not single-query latency.',
        'Fitted parameter count does not measure total private computation.']})
    # The initial prepare stage was executed directly and its tool output retained here.
    save(ROOT/'prepare.command.json',{'command':['research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python',
      'research/learn_infer_only/experiments/end_to_end/utility/attribute_calibration/run.py','prepare'],
      'cwd':'/Users/ember/dev/zkml-research','returncode':0,'provenance':'Recorded from exec tool result; not a rerun',
      'tool_reported_wall_seconds':.298225208,'stdout':{'stage':'prepare','freeze_sha256':sha(ROOT/'freeze.json'),'test_texts':128}})
    files={p.name:{'bytes':p.stat().st_size,'sha256':sha(p),'ignored_regeneratable':p.suffix=='.npz'}
      for p in sorted(ROOT.iterdir()) if p.is_file() and p.name!='manifest.json'}
    save(ROOT/'manifest.json',{'completed':True,'useful_successor':False,'contract_and_selection_preserved':True,
      'executed_new_model_extractions':1,'new_texts':128,'added_teacher_attribute_bits':256,'added_selection_attribute_bits':256,
      'command_exit_codes':{stage:load(ROOT/f'{stage}.command.json')['returncode'] for stage in ['prepare','select','extract','evaluate','audit']},
      'files':files})
    print(json.dumps({'completed':True,'useful_successor':False,'files':len(files),'manifest_sha256':sha(ROOT/'manifest.json')}))
if __name__=='__main__':main()
