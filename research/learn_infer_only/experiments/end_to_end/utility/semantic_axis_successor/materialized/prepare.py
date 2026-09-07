"""Pin identifier-only subset before any fixture vector materialization."""
import sys
sys.dont_write_bytecode=True
from common import *
def main():
 assert not (ROOT/'freeze.json').exists() and not (ROOT/'fixture.json').exists()
 count=verify_parent();records=load(PARENT/'records.json');allhist=load(PARENT/'histories.json')['histories']
 seeds=sorted(h['seed'] for h in allhist)[:2];assert seeds==[67000,67001]
 query=sorted(i for s in [0,1] for a in [0,1] for b in [0,1]
  for i in sorted(r['id'] for r in records if r['pool']=='test' and (r['skill'],r['a'],r['b'])==(s,a,b))[:2])
 assert len(query)==16 and len(set(query))==16
 selection={'history_ids':seeds,'query_ids':query,'rule':'First two ascending history IDs; lowest two IDs per task/gold-attribute stratum, globally sorted',
  'prepared_before_vector_materialization':True,'query_selection_uses_outcomes':False,
  'gold_metadata_use':'Balanced identifier selection and test oracle only; never semantic feature values',
  'integration_correctness_subset_not_new_utility_estimate':True}
 save(ROOT/'selection.json',selection)
 source=[ROOT/n for n in ['CONTRACT.md','.gitignore','common.py','prepare.py','build.py','audit.py','launch.py','selection.json']]
 source += [PARENT/n for n in ['manifest.json','records.json','histories.json','teacher_predictions.json','test_predictions.json',
  'features.npz','checkpoint_states.npz','results.json','raw_scores.json','image_rank_scope.json','ERRORS.md']]
 save(ROOT/'freeze.json',{'source_sha256':{str(p):sha(p) for p in source},'parent_manifest_sha256':sha(PARENT/'manifest.json'),
  'frozen_parent_entries_verified':count,'selection_sha256':sha(ROOT/'selection.json'),
  'expected_counts':{'learn':384,'queries':96,'events':480,'expiries':256,'empty_route_queries':16,'public_query_records':16},
  'crypto_or_encoder_executions_authorized':0})
 print(json.dumps({'prepared':True,'freeze_sha256':sha(ROOT/'freeze.json'),'selection':selection},indent=2))
if __name__=='__main__':main()
