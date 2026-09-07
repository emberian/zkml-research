"""Reproduce config merging without a model or any inference."""
import hashlib,json,sys
from pathlib import Path
from types import SimpleNamespace
sys.dont_write_bytecode=True
from transformers import GenerationConfig
from transformers.generation.utils import GenerationMixin
import transformers.generation.utils as utils
ROOT=Path(__file__).resolve().parent
freeze=json.loads((ROOT/'freeze.json').read_text())
fake=SimpleNamespace(generation_config=GenerationConfig.from_pretrained(freeze['model_path'],local_files_only=True))
def check(flag,**kwargs):
 proposed=GenerationConfig(max_new_tokens=32,do_sample=False,num_beams=1,use_cache=True,bos_token_id=128000,eos_token_id=128012,pad_token_id=128004)
 effective,_=GenerationMixin._prepare_generation_config(fake,proposed,use_model_defaults=flag,**kwargs)
 return {'do_sample':effective.do_sample,'temperature':effective.temperature,'top_p':effective.top_p,'generation_mode':effective.get_generation_mode().value}
result={'no_model_loaded':True,'actual_generation_calls':0,
 'original_default_merge':check(None),'disable_model_defaults':check(False),
 'disable_and_explicit_kwargs':check(False,do_sample=False,temperature=1.,top_p=1.),
 'installed_source_path':utils.__file__,'installed_source_sha256':hashlib.sha256(Path(utils.__file__).read_bytes()).hexdigest(),
 'source_locations':'GenerationMixin._prepare_generation_config lines1704-1801; generate lines2378-2381',
 'diagnostic_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
assert result['original_default_merge']['do_sample'] is True
assert result['disable_and_explicit_kwargs']['do_sample'] is False
(ROOT/'config_diagnostic.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))
