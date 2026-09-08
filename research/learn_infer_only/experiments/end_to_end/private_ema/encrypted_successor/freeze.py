import datetime
from common import ROOT,PRIOR,UTILITY,BIN,load,save,meta,sha

assert not (ROOT/'freeze.json').exists()
assert not (ROOT/'runtime/run001').exists()
previous=load(PRIOR/'source_manifest.json')
for name,h in previous['binary_hashes'].items():assert sha(BIN/name)==h,name
for name,row in load(UTILITY/'manifest.json')['files'].items():assert sha(UTILITY/name)==row['sha256'],name
paths=[p for p in ROOT.iterdir() if p.is_file() and p.suffix in ['.py','.md']]
paths += [PRIOR/'Cargo.toml',PRIOR/'Cargo.lock',PRIOR/'source_manifest.json',UTILITY/'manifest.json',
          UTILITY/'materialized_fixture.json',UTILITY/'results.json',UTILITY/'REPORT.md',UTILITY/'encrypted_cost_proposal.json']
paths += list((PRIOR/'src').rglob('*.rs')) + [BIN/name for name in ['setup','issuer','host','reader']]
save(ROOT/'freeze.json',{'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
                       'files':{str(p):meta(p) for p in sorted(paths)},
                       'binary_hashes_match_reviewed_prior':True,
                       'fixture_counts':{'Learn':384,'Infer':96,'replay_pairs':480},
                       'launch_mode':'sequential subprocesses, one host at a time',
                       'client_key_retained':True,'public_routes':True,'fresh_utility_estimate':False})
print({'freeze_sha256':sha(ROOT/'freeze.json'),'files':len(paths)})
