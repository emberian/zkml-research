"""Read-only model/runtime feasibility inventory; no model construction or forward."""
from pathlib import Path
import hashlib,json,sys,time
sys.dont_write_bytecode=True
import numpy,torch,transformers
from build_mapping import ROOT,BASE,load,sha,save

def main():
    before=time.perf_counter();original=load(BASE/'model_manifest.json')
    revision=original['revision']
    model=Path.home()/'.cache/huggingface/hub/models--HuggingFaceTB--SmolLM2-135M/snapshots'/revision
    files={}
    for name,record in original['model_files'].items():
        path=model/name
        assert path.is_file() and sha(path)==record['sha256'] and path.stat().st_size==record['bytes']
        files[name]=record
    result={'passed':True,'scope':'Read-only cached source/runtime inventory; no model loaded or run',
      'python_executable':sys.executable,'python':sys.version,'torch':torch.__version__,
      'transformers':transformers.__version__,'numpy':numpy.__version__,
      'model_path':str(model),'revision':revision,'model_files':files,
      'recorded_original_parameter_count':original['model_parameter_count'],
      'recorded_original_full_feature_pass_seconds':load(BASE/'representation_model_manifest.json')['feature_seconds'],
      'requirements_sha256':sha(BASE/'requirements-lock.txt'),'script_sha256':sha(__file__),
      'new_dependencies':[],'model_executed':False,'read_inventory_seconds':time.perf_counter()-before}
    save(ROOT/'encoder_feasibility.json',result)
    print(json.dumps({k:v for k,v in result.items() if k not in ['model_files','python']},indent=2))

if __name__=='__main__':main()
