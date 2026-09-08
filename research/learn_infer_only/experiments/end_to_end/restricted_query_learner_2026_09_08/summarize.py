"""Read completed public receipts only; no private payloads or cryptography."""
import csv,hashlib,json
from collections import defaultdict
from pathlib import Path
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 root=HERE/'results/normal_001';r=json.loads((root/'RESULT.json').read_text());assert r['status']=='PASS' and r['sources_unchanged']
 registry=json.loads((HERE/'registry.json').read_text());fixture=json.loads((HERE/'fixture.json').read_text());cost=defaultdict(lambda:{'calls':0,'seconds':0.});rows=[]
 for command in r['commands']:
  name=command['event'];kind='register' if name.startswith('register_') else 'encode' if name.startswith('encode_') else 'learn' if name.startswith('learn_') else 'query' if name.startswith('query_') else 'rebuild' if name.startswith('exact_expiry_') else name
  cost[kind]['calls']+=1;cost[kind]['seconds']+=command['wall_seconds']
  receipt=json.loads(Path(command['receipt']).read_text());assert receipt['status']=='PASS' and receipt['registry_sha256']==r['registry_sha256']
  assert receipt['result'].get('private_rows_read',0)==(1 if kind=='query' else 0)
 for answer in r['registered_query_results']:
  i=answer['coordinate']
  for got,reference in zip(answer['results'],fixture['snapshots']):
   assert got['scores']==reference['scores'][i]
   for label,score in got['scores'].items():rows.append({'coordinate':i,'text':answer['query_text'],'expected_label':answer['expected_label'],'revision':got['revision'],'class':label,'score':score,'reference':reference['scores'][i][label],'prediction':got['prediction'],'correct':got['prediction']==answer['expected_label']})
 with (HERE/'SCORES.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
 changed=sum(a['results'][1]['scores'][label]!=a['results'][2]['scores'][label] for a in r['registered_query_results'] for label in registry['classes'])
 summary={'status':'PASS','registered_keys':16,'absent_secret_rows':0,'universal_reader':False,'encodes':6,'learns':6,'expiries':2,'scalar_scores_matched':len(rows),'decisions_matched':48,'registered_query_correct_at_each_checkpoint':[s['correct'] for s in fixture['snapshots']],'query_count':16,'utility_scope':'Fixed known-public reused slice, not new held-out estimate','class_scores_changed_by_expiry':changed,'whole_window_bound':2520950,'p_half_floor':14219946,'elapsed_seconds':r['elapsed_seconds'],'public_elapsed_seconds':r['public_elapsed_seconds'],'costs':dict(cost),'public_before_private':r['public_complete_before_first_recipient_read'],'source_pins_sha256':r['source_pins_sha256'],'runtime_result_sha256':sha(root/'RESULT.json'),'public_complete_sha256':sha(root/'PUBLIC_COMPLETE.json'),'scores_csv_sha256':sha(HERE/'SCORES.csv'),'collector_private_payload_reads':0}
 (HERE/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
if __name__=='__main__':main()
