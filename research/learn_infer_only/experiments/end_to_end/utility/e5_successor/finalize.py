"""Final evidence and cost census; does not execute models or utility."""
import ast,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 r=load(ROOT/'results.json');a=load(ROOT/'audit.json');sel=load(ROOT/'selection.json');stages=['prepare','e5_train','fit_select','e5_test','smol_test','evaluate','audit']
 assert a['passed'] and not r['useful_successor'] and all(load(ROOT/f'{s}.command.json')['returncode']==0 for s in stages)
 extract={}
 for name in ['e5_train','e5_test','smol_test']:
  x=load(ROOT/f'{name}.extraction.json');extract[name]={k:x[k] for k in ['model','revision','records','parameter_count','unpadded_tokens','padded_tokens','load_wall_seconds','load_cpu_seconds',
   'forward_wall_seconds','forward_cpu_seconds','total_wall_seconds_including_imports','total_cpu_seconds_including_imports','process_high_water_rss_bytes_macos']}
  extract[name]['full_process_wall_seconds']=load(ROOT/f'{name}.command.json')['wall_seconds']
 save(ROOT/'costs.json',{'label':'EXECUTED unless nested under derived','extraction':extract,
  'teacher_fit_and_encode_both_e5':sel['teacher_fit_encoding_cost'],'encode_384_vectors':r['encoding_cost'],
  'utility_evaluation':r['cost'],'independent_audit_wall_seconds':a['wall_seconds'],
  'derived':{'projection_scalar_products_per_text':768*576,'projection_reduction_adds_per_text':576*767,
   'projection_float64_bytes':768*576*8,'generic_577_score_bound':577*32*127**2,'generic_raw769_score_bound':769*32*127**2,
   'primary_added_attribute_labels':0,'raw769_is_offline_only':True},
  'limitations':['Shared machine; timings are observed executions, not a controlled speed comparison.',
   'Forward and load timings are nested in full process wall time.',
   'RSS high-water values are not additive.',
   'Projection and full source encoding are plaintext issuer/public-query work, not HE costs.']})
 files={}
 for p in sorted(ROOT.iterdir()):
  if p.is_file() and p.name!='manifest.json':
   if p.suffix=='.py':ast.parse(p.read_text())
   if p.suffix in ['.py','.md','.json']:assert b'\r\n' not in p.read_bytes()
   files[p.name]={'bytes':p.stat().st_size,'sha256':sha(p),'ignored_regeneratable':p.suffix=='.npz'}
 save(ROOT/'manifest.json',{'completed':True,'useful_successor':False,'contract_selection_preserved':True,
  'actual_e5_text_encodings':384,'actual_smol_test_text_encodings':128,'total_scores':147456,
  'command_exit_codes':{s:load(ROOT/f'{s}.command.json')['returncode'] for s in stages},'files':files})
 print(json.dumps({'completed':True,'useful_successor':False,'files':len(files),'manifest_sha256':sha(ROOT/'manifest.json')}))
if __name__=='__main__':main()
