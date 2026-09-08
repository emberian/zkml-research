"""Post-drain source/omission audit; reads authorized private fixture/key bytes only here."""
import base64,gzip,hashlib,json,sqlite3,subprocess,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 freeze=load(ROOT/'freeze.json');runtime=Path(freeze['runtime']);reports=Path(freeze['reports']);run=runtime/'run'
 report=load(reports/'report.json');assert report['ok'] and report['all_oracle_matches']
 assert report['public_phase_decryptions']==report['baseline_decryptions']==0
 assert report['verified_decryptions_after_public_verification']==2
 assert report['public_verification_sha256']==sha(reports/'public_verification.json')
 for p,h in freeze['public_source_dependencies'].items():assert sha(p)==h,p
 for p,h in freeze['snapshot_source_pins'].items():assert sha(runtime/'e2e'/p)==h,p
 for p,h in freeze['query_vector_pins'].items():assert sha(runtime/'public_query_inputs'/p)==h,p
 # Key and private-input omission is checked without printing their values/hashes.
 public=[]
 for p in reports.rglob('*'):
  if not p.is_file():continue
  if p.name.endswith('.tar.gz'):
   with tarfile.open(p) as tar:public.extend(tar.extractfile(x).read() for x in tar.getmembers() if x.isfile())
  elif p.suffix=='.gz':public.append(gzip.decompress(p.read_bytes()))
  else:public.append(p.read_bytes())
 all_public=b'\n'.join(public)
 secrets=list((run/'.private').glob('*/signing.key'))+[run/'.private/reader/bfv_secret.bin'];assert len(secrets)==4
 for p in secrets:
  raw=p.read_bytes()
  for value in ([raw,raw[81:]] if p.name=='bfv_secret.bin' else [raw]):
   assert value not in all_public and value.hex().encode() not in all_public and base64.b64encode(value) not in all_public
 private_files=[runtime/'.private/input.json',runtime/'.private/prepared/issuer_inputs.json',
                run/'.private/issuer/live_encoder/vector.json',run/'.private/issuer/live_encoder/raw_scores.json',
                runtime/'.private/integer_audit.json']
 for p in private_files:
  # Every possible feature row is already a public policy query. Its bare
  # hash is therefore public dictionary data, not a selected-feature binding.
  if p.name!='vector.json':assert p.read_bytes() not in all_public and sha(p).encode() not in all_public
 assert not ({'predicted_bits','vector','vector_sha256','signed_score','answers','expected'} & set(report))
 for row in load(runtime/'.private/prepared/issuer_inputs.json'):
  for key in ['text','rendered_prompt']:
   value=row[key];assert value.encode() not in all_public and json.dumps(value).encode() not in all_public
  assert json.dumps(row['token_ids']).encode() not in all_public
 with sqlite3.connect(run/'authority/journal.sqlite3') as db:
  assert db.execute("SELECT count(*) FROM journal WHERE published=0 AND json_extract(request,'$.action.kind')='Infer'").fetchone()[0]==2
 ignored=subprocess.run(['git','check-ignore',str(private_files[0]),str(secrets[-1]),str(run/'verified_state.sqlite3')],capture_output=True,text=True)
 assert ignored.returncode==0 and len(ignored.stdout.splitlines())==3
 parent_counts={}
 for p,count in freeze['parent_entries_preserved'].items():
  directory=Path(p);entries=load(directory/'manifest.json')['files']
  for n,row in entries.items():assert sha(directory/n)==row['sha256'],(directory,n)
  assert len(entries)==count;parent_counts[p]=count
 result={'ok':True,'source_model_query_and_parent_pins_match':True,'parent_entries_preserved':parent_counts,
         'secret_files_scanned_raw_hex_base64':4,'private_text_prompt_and_raw_score_artifacts_omitted':True,
         'selected_feature_binding_fields_omitted':True,'public_query_dictionary_contains_possible_feature_rows':True,
         'runtime_gitignored':True,'authority_pending_infers':2,'selected_score_secrecy_claim':False,
         'scope':'Normal authorized result/omission audit; output-change boolean deliberately reveals selected after-score.'}
 (reports/'validation.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
