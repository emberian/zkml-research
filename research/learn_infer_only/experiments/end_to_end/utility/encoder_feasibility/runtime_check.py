"""Local config/tokenizer/model-class check, without weight loading or forward."""
import hashlib,importlib.util,json,os,resource,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
for k in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[k]='1'
os.environ['TOKENIZERS_PARALLELISM']='false'
t=time.perf_counter()
import torch,transformers
from transformers import AutoConfig,AutoTokenizer,AutoModel,AutoModelForCausalLM
ROOT=Path(__file__).resolve().parent
def main():
 rows={}
 for name,row in json.loads((ROOT/'candidates.json').read_text()).items():
  p=row['path'];config=AutoConfig.from_pretrained(p,local_files_only=True,trust_remote_code=False)
  tokenizer=AutoTokenizer.from_pretrained(p,local_files_only=True,trust_remote_code=False)
  auto=AutoModel if name in ['intfloat/e5-base-v2','microsoft/harrier-oss-v1-0.6b'] else AutoModelForCausalLM
  cls=auto._model_mapping[type(config)]
  rows[name]={'config_class':type(config).__name__,'tokenizer_class':type(tokenizer).__name__,
    'model_class_available':cls.__name__,'tokenizer_vocab_size':len(tokenizer),
    'weights_loaded':False,'forward_calls':0}
 result={'passed':True,'models':rows,'python':sys.version,'executable':sys.executable,
   'torch':torch.__version__,'transformers':transformers.__version__,
   'sentence_transformers_installed':importlib.util.find_spec('sentence_transformers') is not None,
   'extra_package_required_for_AutoModel_usage':False,'wall_seconds_including_imports':time.perf_counter()-t,
   'metadata_only_process_high_water_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
   'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 (ROOT/'runtime.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
