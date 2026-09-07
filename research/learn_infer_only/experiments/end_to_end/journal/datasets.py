"""Frozen public utility and fresh private ingress through the same journal path."""
import argparse,collections
from run import *

def sources():
 return {p.name:sha(p.read_bytes()) for p in sorted(HERE.glob('*.py'))}
def storage(run):
 head=run.head();live={run.g['zero_ct_sha256']}
 for route in head['state']['routes'].values():live.add(route['acc_ct']);live.update(x['ct_sha256'] for x in route['queue'])
 cas=Path(run.acfg['cas']);blobs=[p for p in cas.iterdir() if p.is_file() and len(p.name)==64]
 return {'current_state_manifest_bytes':len(canonical(head['state'])),'current_ciphertext_reference_count':len(live),'current_ciphertext_bytes':sum((cas/x).stat().st_size for x in live),
  'retained_authority_cas_blob_count':len(blobs),'retained_authority_cas_bytes':sum(p.stat().st_size for p in blobs),'authority_database_file_bytes':Path(run.acfg['db']).stat().st_size,'authority_database_wal_shm_bytes':sum(Path(run.acfg['db']+suffix).stat().st_size for suffix in ['','-wal','-shm'] if Path(run.acfg['db']+suffix).exists()),
  'journal_delta_replay_bytes':(run.root/'replay.json').stat().st_size,'scope':'current window O(W); immutable historical fresh/accumulator/output blobs O(T); delta metadata O(T), no full queue poststate per entry'}
def report_calls(run):
 records=[json.loads(line) for line in (run.root/'commands.jsonl').read_bytes().splitlines()]
 roles={}
 for record in records:
  r=roles.setdefault(record['role'],{'calls':0,'elapsed_ns':0,'failed':0});r['calls']+=1;r['elapsed_ns']+=record['elapsed_ns'];r['failed']+=int(record['exit_code']!=0)
 # Dataflow check is argv-level evidence, not OS isolation or a general noninterference theorem.
 for record in records:
  if record['role'] in ['host','authority','independent_public_replay']:
   require(record['command'][1] in ['inspect','host-learn','host-infer'],'keylessCommandBoundary')
   require('--sk' not in record['command'] and '--vector' not in record['command'],'keylessArgumentBoundary')
  if record['role']=='reader':
   require(record['command'][1] in ['inspect','reader-decrypt'],'readerCommandBoundary')
   if record['command'][1]=='reader-decrypt':require(record['stdout'] is None and record['private_output_omitted'],'privateReaderLog')
 return {'roles':roles,'keyless_command_audit':True,'reader_plaintext_stdout_omitted':True}
def utility(args):
 root=Path(args.root).resolve();root.mkdir(parents=True,exist_ok=False)
 queries=root/'query_policy_inputs.json';write_json(queries,[{'route':0 if i<8 else 1,'path':str((UTILITY/'public_queries'/f'q{i:02d}.json').resolve())} for i in range(16)])
 events=read_json(UTILITY/'issuer_oracle/input_index.json')['events'];oracle=read_json(UTILITY/'issuer_oracle/expected_scalars.json')['queries'];reports=[]
 for h in [0,1]:
  run=Run(root/f'history_{h}',queries)
  try:
   selected=[e for e in events if e['event_id'].startswith(f'h{h}-')];first=None;first_reply=None;infer_ids=[];fresh=[];expiry=0
   for n,event in enumerate(selected,1):
    kwargs={'vector':event['issuer_vector_path']} if event['kind']=='Learn' else {'query_index':int(Path(event['public_query_vector_path']).stem[1:])}
    req=run.prepare(event['kind'],event['route'],event['event_id'],**kwargs);reply=run.accepted(req)
    if first is None:first,first_reply=req,reply
    if event['kind']=='Learn':fresh.append(req['action']['fresh_ct']);expiry+=req['proposal']['expired_ct'] is not None
    else:infer_ids.append(event['event_id'])
    if n%40==0:print(json.dumps({'history':h,'events_completed':n}),flush=True)
   retry=run.accepted(first);require(retry['status']=='replayed' and retry['envelope']==first_reply['envelope'],'historicalRetry')
   answers=run.answers();require(set(answers)==set(infer_ids),'oracleEventSet');require(all(answers[k]==oracle[k]['expected_scalar'] for k in answers),'utilityOracleMismatch')
   replay=run.replay(True);knownzero=sum(oracle[k]['public_structural_zero'] for k in answers)
   report={'ok':True,'kind':'public_fixed_utility_history','history':h,'events':len(selected),'learns':len(fresh),'infers':len(answers),'expiries':expiry,'fresh_ciphertexts_distinct':len(fresh)==len(set(fresh)),
    'oracle_comparisons':len(answers),'oracle_all_match':True,'known_empty_route_outputs':knownzero,'nonempty_encrypted_outputs':len(answers)-knownzero,'historical_exact_retry':True,
    'replay':replay,'storage':storage(run),'commands':report_calls(run),'elapsed_ns':time.perf_counter_ns()-run.started,'source_sha256':sources()}
   write_json(run.root/'report.json',report);reports.append(report)
  finally:run.close()
 report={'ok':True,'schema':'resident-journal-utility-v1','histories':reports,'events':sum(x['events'] for x in reports),'oracle_comparisons':sum(x['oracle_comparisons'] for x in reports),'all_oracle_matches':True}
 write_json(root/'report.json',report);print(json.dumps({'ok':True,'events':report['events'],'oracle_comparisons':report['oracle_comparisons']}))
def private(args):
 root=Path(args.root).resolve();root.parent.mkdir(parents=True,exist_ok=True)
 # Public fixed test queries disclose selected coordinates/linear combinations by policy.
 inputs=root.parent/(root.name+'_query_inputs');inputs.mkdir();vectors=[[1]+[0]*576,[0,1,-1]+[0]*574]
 for i,q in enumerate(vectors):write_json(inputs/f'q{i}.json',q)
 queries=inputs/'policy.json';write_json(queries,[{'route':0,'path':str(inputs/f'q{i}.json')} for i in range(2)])
 run=Run(root,queries)
 try:
  priv=root/'.private/issuer/observations';priv.mkdir(mode=0o700);oracle=[];queue=collections.deque();expiry=0;fresh=[]
  for step in range(1,41):
   path=priv/f'o{step:03d}.json';Crypto(read_json(root/'.private/issuer/config.json'),'issuer_private_generator',root/'commands.jsonl').run('issuer-private-vector',out=path)
   values=read_json(path);queue.append(values)
   if len(queue)>32:queue.popleft()
   req=run.prepare('Learn',0,f'private-learn-{step:03d}',vector=path);run.accepted(req);fresh.append(req['action']['fresh_ct']);expiry+=req['proposal']['expired_ct'] is not None
   if step in [1,16,33,40]:
    qi=step%2;event_id=f'private-infer-{step:03d}';query=vectors[qi];expected=sum(sum(x*y for x,y in zip(v,query)) for v in queue)
    req=run.prepare('Infer',0,event_id,query_index=qi);run.accepted(req);oracle.append((event_id,expected))
  answers=run.answers();require(all(answers[k]==v for k,v in oracle),'privateOracleMismatch');require(len(set(fresh))==40,'privateDistinctCiphertexts')
  # No scalar, vector, state value, or plaintext hash is emitted to the retained report.
  report={'ok':True,'schema':'resident-journal-private-ingress-v1','learns':40,'infers':len(oracle),'expiries':expiry,'oracle_comparisons':len(oracle),'oracle_all_match':True,'distinct_fresh_ciphertexts':True,
   'private_input_mode_0600':all((p.stat().st_mode&0o777)==0o600 for p in priv.iterdir()),'replay':run.replay(True),'storage':storage(run),'commands':report_calls(run),
   'elapsed_ns':time.perf_counter_ns()-run.started,'source_sha256':sources(),'scope':'OS-random synthetic issuer-only observations; selected public queries; trusted full-key reader and honest authority; no utility or OS isolation claim'}
  write_json(root/'report.json',report);print(json.dumps({'ok':True,'learns':40,'infers':len(oracle),'oracle_all_match':True}))
 finally:run.close()
def main():
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['utility','private']);p.add_argument('--root',required=True);a=p.parse_args();globals()[a.mode](a)
if __name__=='__main__':main()
