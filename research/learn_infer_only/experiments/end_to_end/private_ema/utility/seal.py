"""Verify summary cells, price a bounded next run, and seal this utility artifact."""
import csv
import statistics
from common import ROOT, load, save, sha, verify_freeze, cell

pins=verify_freeze()
result=load(ROOT/'results.json');rows=load(ROOT/'query_scores.json')
final=[r for r in rows if r['phase']==3]
checks=0
for field, groups in result['strata'].items():
    for key, methods in groups.items():
        if field=='task_attribute':
            route=int(key[5]);pair=list(map(int,key.split('.')[1]))
            selected=[r for r in final if r['route']==route and r['gold_pair']==pair]
        else:selected=[r for r in final if r[field]==key]
        for method,value in methods.items():
            assert value==cell(selected,method+'_prediction');checks+=1
assert result['paired_label_changes_vs_window']=={
    'all_checkpoints':sum(r['ema_prediction']!=r['window_prediction'] for r in rows),
    'final':sum(r['ema_prediction']!=r['window_prediction'] for r in final),
    'final_improved':sum(r['ema_prediction']==r['target'] and r['window_prediction']!=r['target'] for r in final),
    'final_regressed':sum(r['ema_prediction']!=r['target'] and r['window_prediction']==r['target'] for r in final)}
prior=list(csv.DictReader((ROOT.parent/'costs.csv').open()))
projections=[]
for prefix,count in [('host_learn_',384),('replay_learn_',384),('host_infer_',96),('replay_infer_',96),
                     ('issuer_learn_',384),('issuer_query',16),('issuer_init',4),('setup',1),
                     ('reader_state_',16),('reader_output_',96)]:
    matching=[r for r in prior if r['operation'].startswith(prefix)]
    seconds=statistics.mean(float(r['wall_seconds']) for r in matching)
    projections.append({'claim':'DERIVED projection','operation':prefix,'count':count,
                        'prior_sample_count':len(matching),'prior_mean_wall_seconds':seconds,
                        'projected_wall_seconds':count*seconds,
                        'source':'../costs.csv; matched operation prefix; process wall including startup'})
save(ROOT/'encrypted_cost_proposal.json',{'scope':'unexecuted 384 Learn / 96 Infer and one full replay each',
     'assumptions':'same backend and machine; serialized operations; no contention; no new compilation',
     'excluded':'additional read-time hashing, wrapper overhead, audit/sealing and contention',
     'public_query_encryption_policy':'16 fixed source query IDs once, reused unchanged at six checkpoints',
     'rows':projections,'projected_wall_seconds':sum(r['projected_wall_seconds'] for r in projections),
     'prior_costs_sha256':sha(ROOT.parent/'costs.csv')})
with (ROOT/'costs.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['claim','operation','count','wall_seconds','scope','source'])
    for stage in ['freeze','evaluate','audit']:
        c=load(ROOT/(stage+'.command.json'))
        w.writerow(['EXECUTED',stage,1,c['wall_seconds'],'whole subprocess wall',stage+'.command.json'])
    w.writerow(['EXECUTED','evaluation_interval',1,result['evaluation_wall_seconds'],'internal interval','results.json'])
    w.writerow(['EXECUTED','audit_interval',1,load(ROOT/'audit.json')['audit_wall_seconds'],'internal interval','audit.json'])
    for p in projections:w.writerow([p['claim'],p['operation'],p['count'],p['projected_wall_seconds'],'projected total from prior mean',p['source']])
save(ROOT/'summary_checks.json',{'passed':True,'stratum_method_cells_recomputed':checks,
    'label_change_counts_recomputed':4,'frozen_files_preserved':pins,'cryptography_executed':False})
files=[p for p in sorted(ROOT.iterdir()) if p.is_file() and p.name not in ['manifest.json','seal.stdout']]
save(ROOT/'manifest.json',{'scope':'completed plaintext fixed-law utility tranche; no encrypted execution',
    'files':{p.name:{'sha256':sha(p),'bytes':p.stat().st_size} for p in files},
    'file_count':len(files),'freeze_sha256':sha(ROOT/'freeze.json')})
print({'sealed_files':len(files),'stratum_cells_checked':checks,
       'projected_crypto_wall_seconds':sum(p['projected_wall_seconds'] for p in projections),
       'manifest_sha256':sha(ROOT/'manifest.json')})
