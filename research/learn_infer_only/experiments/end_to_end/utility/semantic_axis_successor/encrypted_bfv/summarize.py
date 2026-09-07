"""Summarize completed normal-run costs without another crypto/model call."""
import collections,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
def main():
 freeze=load(ROOT/'freeze.json');reports=Path(freeze['reports']);runtime=Path(freeze['runtime'])
 full=load(reports/'report.json');fast=load(reports/'fast_report.json');launch=load(ROOT/'run.command.json')
 validation=load(reports/'validation.json');assert validation['ok']
 rolecosts=collections.defaultdict(lambda:{'calls':0,'sum_ns':0})
 transition=collections.defaultdict(lambda:{'events':0,'sum_ns':0})
 for h in full['histories']:
  for k,v in h['crypto_process_costs'].items():rolecosts[k]['calls']+=v['count'];rolecosts[k]['sum_ns']+=v['sum_ns']
  for k,v in h['transition_wall_costs'].items():transition[k]['events']+=v['count'];transition[k]['sum_ns']+=v['sum_ns']
  for row in transition.values():row['mean_ns']=row['sum_ns']/row['events']
 histories=[]
 for n,h in enumerate(full['histories']):
  root=runtime/f'history_{n}';cfg=load(root/'.private/verified_reader/config.json')
  issuer=load(root/'.private/issuer/config.json')
  # Public/secret key sizes are reported, never key material or reader scores.
  keys={}
  for label,path in [('bfv_reader_secret',cfg['bfv_secret_key']),('bfv_public',issuer['public_key'])]:keys[label]=Path(path).stat().st_size
  histories.append({'history_id':67000+n,'bytes':h['bytes'],'key_bytes':keys,
   'database_bytes_after_services_closed':validation['histories'][n]['database_bytes_after_services_closed'],
   'persistent_host':fast['workers'][n]})
 summary={'scope':'One fresh BFV setup per frozen semantic history; retained full-key verifying reader; no model execution or new utility estimate.',
  'histories':[67000,67001],'events':480,'learns':384,'infers':96,'expiries':256,
  'integer_matches':96,'known_empty_outputs':16,'nonempty_outputs':80,
  'prepare_seconds':freeze['prepare_wall_seconds'],'launcher_wall_ns':launch['launcher_wall_ns'],
  'pipeline_elapsed_ns':full['elapsed_ns'],'persistent_worker_wrapper_elapsed_ns':fast['worker_elapsed_ns'],
  'children_user_cpu_seconds':launch['children_user_cpu_seconds'],
  'children_system_cpu_seconds':launch['children_system_cpu_seconds'],
  'max_child_rss_bytes_macos':launch['max_child_rss_bytes_macos'],
  'rss_scope':'Launcher getrusage(RUSAGE_CHILDREN): maximum child high-water RSS, not concurrent resident memory or model RSS.',
  'interval_scope':'Wall/worker/transition/crypto intervals overlap; do not sum them into end-to-end latency. Shared machine load; one measured execution.',
  'crypto_process_costs':dict(sorted(rolecosts.items())),'transition_wall_costs':dict(transition),
  'per_history':histories,'summarizer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 (reports/'costs.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'launcher_seconds':summary['launcher_wall_ns']/1e9,'pipeline_seconds':summary['pipeline_elapsed_ns']/1e9,
  'crypto_calls':sum(v['calls'] for v in rolecosts.values()),'source_model_forwards':0}))
if __name__=='__main__':main()
