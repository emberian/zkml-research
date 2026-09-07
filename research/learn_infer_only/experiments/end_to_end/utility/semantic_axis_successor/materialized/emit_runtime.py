"""Regenerate or byte-verify ignored PUBLIC fixture role files; no crypto/model."""
import sys,argparse
sys.dont_write_bytecode=True
from common import *
def main():
 p=argparse.ArgumentParser();p.add_argument('--output-dir',default=str(ROOT/'runtime'));args=p.parse_args()
 output=Path(args.output_dir).resolve();assert ROOT in output.parents,'Output must stay in owned child directory'
 verify();assert sha(ROOT/'fixture.json')==load(ROOT/'build_results.json')['fixture_sha256']
 f=load(ROOT/'fixture.json');raw=load(ROOT/'integer_oracle.json')['queries'];files={};written=0;verified=0
 def emit(path,value):
  nonlocal written,verified
  payload=(json.dumps(value,separators=(',',':'))+'\n').encode()
  if path.exists():assert path.read_bytes()==payload,path;verified+=1
  else:role_json(path,value);written+=1
  assert path.stat().st_mode&0o777==0o600
  files[str(path)]={'sha256':sha(path),'bytes':path.stat().st_size}
 for q in f['query_records']:emit(output/'public_queries'/f"{q['query_id']}.json",q['vector'])
 entries=[];oracle={}
 oracle_keys=['expected_scalar','sign','target_label','correct','public_structural_zero','nonempty_zero_score',
  'record_id','phase','history_id','source_factual_error']
 for event in f['events']:
  entry={k:event[k] for k in ['event_id','kind','route']}
  if event['kind']=='Learn':
   row=f['learn_vectors'][event['learn_vector_index']];path=output/'issuer/vectors'/f"{event['event_id']}.json"
   emit(path,row['vector']);entry['issuer_vector_path']=str(path)
  else:
   entry['public_query_vector_path']=str(output/'public_queries'/f"{event['public_query_id']}.json")
   source=raw[event['event_id']];value={k:source[k] for k in oracle_keys}
   value['original_full_survey_selected_records']={name:{k:source['original_full_survey_selected_records'][name][k]
    for k in ['score','prediction','target','correct']} for name in sorted(source['original_full_survey_selected_records'])}
   oracle[event['event_id']]=value
  entries.append(entry)
 emit(output/'issuer/input_index.json',{'schema':'E2E_ISSUER_INPUT_INDEX_V1',
  'exposure':'PUBLIC research fixture, issuer/coordinator role input only','events':entries})
 emit(output/'oracle/expected_scalars.json',{'schema':'E2E_TEST_ORACLE_SCALARS_V1',
  'exposure':'PUBLIC test oracle, not host input','queries':oracle})
 assert len(files)==402
 if output==ROOT/'runtime':
  original=load(ROOT/'runtime_hash_census.json')['files']
  for path,row in files.items():assert row==original[str(Path(path).relative_to(ROOT))]
 print(json.dumps({'passed':True,'files_written':written,'existing_files_byte_verified':verified,'total_files':len(files),
  'input_index':str(output/'issuer/input_index.json'),'fixture_sha256':sha(ROOT/'fixture.json'),
  'parent_entries_unchanged':verify_parent(),'command':[sys.executable,*sys.argv]},indent=2))
if __name__=='__main__':main()
