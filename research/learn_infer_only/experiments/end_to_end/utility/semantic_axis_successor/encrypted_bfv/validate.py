"""Direct mathematical queue replay; normal completed-run evidence only."""
import base64,collections,gzip,hashlib,json,platform,sqlite3,subprocess,sys,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_bytes())
def dump(p,x):Path(p).write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
def main():
 freeze=load(ROOT/'freeze.json');runtime=Path(freeze['runtime']);reports=Path(freeze['reports']);snap=runtime/'e2e'
 for p,h in freeze['source_dependencies'].items():assert sha(p)==h,p
 for p,h in freeze['snapshot_source_pins'].items():assert sha(snap/p)==h,p
 assert load(reports/'dependency_pins_after.json')==freeze['source_dependencies']
 assert load(reports/'snapshot_pins_after.json')==freeze['snapshot_source_pins']
 report=load(reports/'report.json');assert report['ok'] and report['oracle_comparisons']==96
 assert report['verified_decrypt_calls']==96 and report['baseline_decrypt_calls']==0
 fp=load(reports/'fixture_pins.json');assert sha(reports/'fixture_pins.json')==freeze['fixture_pins_sha256']
 for p,h in fp['frozen_vector_files'].items():assert sha(snap/p)==h,p
 inputs=snap/'utility/issuer_oracle'
 assert sha(inputs/'input_index.json')==fp['copied_index_sha256']
 assert sha(inputs/'expected_scalars.json')==fp['oracle_sha256']
 events=load(inputs/'input_index.json')['events'];oracle=load(inputs/'expected_scalars.json')['queries']
 fixture=load(ROOT.parent/'materialized/fixture.json');canonical={e['event_id']:e for e in fixture['events']}
 assert len(canonical)==len(events)==480
 history_results=[];actual_secret_files=[]
 for history in [0,1]:
  root=runtime/f'history_{history}';cfg=load(root/'.private/verified_reader/config.json')
  with sqlite3.connect(cfg['db']) as db:
   answers={rid:json.loads(raw)['signed_score'] for rid,raw in db.execute('SELECT request_id,answer FROM received')}
   journal=[json.loads(r[0]) for r in db.execute('SELECT envelope FROM verified_journal ORDER BY revision')]
   head=db.execute('SELECT revision,state_digest FROM verified_head').fetchone()
  authority_cfg=load(root/'.private/authority/config.json')
  envelopes=load(reports/f'history_{history}/accepted_envelopes.json')
  assert journal==envelopes and len(journal)==head[0]==240
  envelope_by_id={e['payload']['request']['action']['request_id']:e for e in envelopes}
  queues={0:collections.deque(),1:collections.deque()};fresh={};query_ids=set()
  learned=expired=count=correct=empty=0;strata=collections.defaultdict(lambda:{'queries':0,'correct':0,'empty':0})
  for event in events:
   rid=event['event_id']
   if not rid.startswith(f'h{history}-'):continue
   declared=canonical[rid];envelope=envelope_by_id[rid];payload=envelope['payload'];request=payload['request']
   action=request['action'];route=event['route'];queue=queues[route]
   assert declared['route']==action['route']==route and declared['kind']==action['kind']==event['kind']
   assert payload['revision']==declared['event_ordinal']
   if event['kind']=='Learn':
    vector=load(event['issuer_vector_path'])
    assert len(vector)==577 and all(type(v) is int and -127<=v<=127 for v in vector)
    assert vector==fixture['learn_vectors'][declared['learn_vector_index']]['vector']
    fresh[rid]=action['fresh_ct'];queue.append((rid,vector));removed=None
    if len(queue)>32:removed=queue.popleft()[0];expired+=1
    assert removed==declared['expired_event_id']
    expected_expired=None if removed is None else fresh[removed]
    assert request['proposal']['expired_ct']==expected_expired
    if removed is None:assert payload['delta']['expired'] is None
    else:
     assert payload['delta']['expired']['ct_sha256']==expected_expired
     assert payload['delta']['expired']['record_id']=='record-'+removed
    learned+=1
   else:
    query=load(event['public_query_vector_path']);assert len(query)==577 and all(type(q) is int and -127<=q<=127 for q in query)
    assert query==fixture['query_records'][declared['query_index']]['vector']
    # Independent definition: sum every unexpired original contribution's
    # dot product, without using the accumulator or BFV implementation.
    expected=sum(sum(v*q for v,q in zip(vector,query)) for _,vector in queue)
    assert answers[rid]==oracle[rid]['expected_scalar']==expected
    prediction=1 if expected>=0 else -1;assert oracle[rid]['sign']==prediction
    is_correct=prediction==oracle[rid]['target_label'];assert is_correct==oracle[rid]['correct']
    is_empty=not queue;assert is_empty==oracle[rid]['public_structural_zero']==declared['public_empty_route']
    tally=strata[f"phase_{declared['phase']}_route_{route}"];tally['queries']+=1;tally['correct']+=is_correct;tally['empty']+=is_empty
    correct+=is_correct;empty+=is_empty;count+=1;query_ids.add(rid)
  assert set(answers)==query_ids and count==48 and learned==192 and expired==128 and empty==8
  assert len(set(fresh.values()))==192
  commands=[json.loads(line) for line in (root/'verified_commands.jsonl').read_bytes().splitlines()]
  decrypts=[row for row in commands if row['command'][1]=='reader-decrypt']
  assert len(decrypts)==48 and all(row['stdout'] is None and row['stderr'] is None and row['private_output_omitted'] for row in decrypts)
  sizes={}
  for role,path in [('verified_reader',Path(cfg['db'])),('authority',Path(authority_cfg['db']))]:
   sizes[role]={suffix or 'database':Path(str(path)+suffix).stat().st_size for suffix in ['', '-wal', '-shm'] if Path(str(path)+suffix).exists()}
  actual_secret_files.extend((root/'.private').glob('*/signing.key'))
  actual_secret_files.append(Path(cfg['bfv_secret_key']))
  history_results.append({'history_id':67000+history,'events':240,'direct_integer_queries':count,
   'learns':learned,'same_original_ciphertext_expiries':expired,'all_scores_and_expiry_identities_match':True,
   'verified_records':len(journal),'verified_received_answers':len(answers),'empty_route_scores':empty,
   'frozen_fixture_label_correct':correct,'phase_route_fixture_label_counts':dict(strata),
   'label_count_scope':'Full predeclared integration subset only; not a new accuracy estimate.',
   'database_bytes_after_services_closed':sizes})
 # Omission audit over retained outputs, including decompressed logs/sources.
 public=[]
 for path in reports.rglob('*'):
  if not path.is_file():continue
  if path.name.endswith('.tar.gz'):
   with tarfile.open(path) as archive:public.extend(archive.extractfile(item).read() for item in archive.getmembers() if item.isfile())
  elif path.name.endswith('.gz'):public.append(gzip.decompress(path.read_bytes()))
  else:public.append(path.read_bytes())
 all_public=b'\n'.join(public);assert len(actual_secret_files)==8
 for path in actual_secret_files:
  raw=path.read_bytes()
  for key in ([raw,raw[81:]] if path.name=='bfv_secret.bin' else [raw]):
   assert key not in all_public and key.hex().encode() not in all_public and base64.b64encode(key) not in all_public
 ignored=subprocess.run(['git','check-ignore',str(actual_secret_files[0]),str(actual_secret_files[-1]),str(inputs/'input_index.json')],capture_output=True,text=True)
 assert ignored.returncode==0 and len(ignored.stdout.splitlines())==3
 preserved={}
 for name,path in [('parent',ROOT.parent),('materialized',ROOT.parent/'materialized')]:
  records=load(path/'manifest.json')['files']
  for f,r in records.items():assert sha(path/f)==r['sha256'],f
  preserved[name]=len(records)
 result={'ok':True,'independent_direct_integer_comparisons':96,'same_original_ciphertext_expiries':256,
  'all_match':True,'histories':history_results,'all_original_and_snapshot_source_pins_unchanged':True,
  'parent_manifest_entries_preserved':preserved,'secret_files_scanned_raw_hex_base64':8,
  'bfv_inner_secret_payloads_scanned':True,'reader_plaintext_stdout_omitted':True,'runtime_gitignored':True,
  'python':platform.python_version(),'platform':platform.platform(),'validator_sha256':sha(__file__),
  'command':[sys.executable,'-B',str(Path(__file__).resolve())],
  'scope':'Normal public semantic fixture integer and artifact audit. Full decryption keys retained. No OS isolation, exactly-once physical delivery, no-master-read, or recipient-coalition state privacy claim.'}
 dump(reports/'validation.json',result)
 print(json.dumps({'ok':True,'independent_scores':96,'expiry_identities':256,'parent_entries_preserved':preserved}))
if __name__=='__main__':main()
