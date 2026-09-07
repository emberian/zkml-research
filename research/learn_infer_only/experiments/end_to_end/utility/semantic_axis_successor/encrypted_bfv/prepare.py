"""Freeze only normal-flow worker adapters, immutable BFV/core and semantic data."""
import ast,difflib,hashlib,json,os,shutil,sys,tarfile,time
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent;E2E=ROOT.parents[2];PARENT=ROOT.parent;MAT=PARENT/'materialized'
RUNTIME=ROOT/'runtime';SNAP=RUNTIME/'e2e';REPORTS=ROOT/'reports/run001'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_bytes())
def dump(p,x):Path(p).write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
def preserved(directory):
 m=load(directory/'manifest.json')
 for n,r in m['files'].items():assert sha(directory/n)==r['sha256'],(directory,n)
 return len(m['files'])
def function(source,name):
 node=next(n for n in ast.parse(source).body if isinstance(n,ast.FunctionDef) and n.name==name)
 return ast.get_source_segment(source,node)
MAIN='''\ndef main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--runtime', required=True)
    parser.add_argument('--reports', required=True)
    parser.add_argument('--binary', required=True)
    args=parser.parse_args()
    assert args.worker, 'Only the frozen normal worker entry point is staged'
    worker(args)
if __name__=='__main__':main()
'''
def main():
 started=time.perf_counter();assert not (ROOT/'freeze.json').exists() and not RUNTIME.exists()
 counts={'parent':preserved(PARENT),'materialized':preserved(MAT)}
 assert sha(MAT/'fixture.json')=='bcdda47d227853e546427e9fb42de489b7c227ace65b10a9099cec81f4481b11'
 RUNTIME.mkdir(mode=0o700);REPORTS.mkdir(parents=True)
 pins={};dependencies={}
 def copy(source,name,expected=None):
  source=Path(source);raw=source.read_bytes();digest=hashlib.sha256(raw).hexdigest()
  if expected is not None:assert digest==expected,(source,digest,expected)
  path=SNAP/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
  pins[name]=digest;dependencies[str(source)]=digest;return path
 host=E2E/'host_runtime';hp=load(host/'source_pins.json')
 for name,row in hp['core'].items():
  copy(host/'frozen_core'/name,'journal/'+name,row['sha256'])
  copy(host/'frozen_core'/name,'host_runtime/frozen_core/'+name,row['sha256'])
 copy(host/'host.py','host_runtime/host.py','5f4426feebc68cdeea16cd69a20157e080e47aad7459c3741cfde291a64070a9')
 copy(host/'source_pins.json','host_runtime/source_pins.json')
 copy(E2E/'verified_reader/service.py','verified_reader/service.py','f0e79c2a33baa32e2867d467735dafd29b26c480deb1f688289e7468bd2de01b')
 binary=copy(E2E/'crypto/target/release/resident-crypto','resident-crypto',hp['crypto_binary_sha256']);os.chmod(binary,0o755)
 assert pins['resident-crypto']=='9c79c02e7d919ecdc24851c6f77e50ed6990397bd669f571a886f8e2b85058c2'
 for name,digest in hp['crypto_source_sha256'].items():copy(E2E/'crypto'/name,'crypto_sources/'+name,digest)
 original=(E2E/'verified_reader/utility_driver.py').read_text();dependencies[str(E2E/'verified_reader/utility_driver.py')]=hashlib.sha256(original.encode()).hexdigest()
 assert dependencies[str(E2E/'verified_reader/utility_driver.py')]=='f623dbf5d903c6a6ced87cfb5735dd1bda47f861665f8d88670184f6dc463847'
 utility_worker=function(original,'worker')
 old="    require(correct == 52 and nonempty_correct == 44, 'sameFrozenUtilityDenominator')\n    require(report['utility_counts']['final_checkpoint_correct'] == 18, 'sameFrozenFinalSubset')"
 replacement="    expected = read_json(utility / 'fixture_expectations.json')\n    require(correct == expected['all_correct'] and nonempty_correct == expected['nonempty_correct'], 'sameSemanticFixtureLabels')\n    require(report['utility_counts']['final_checkpoint_correct'] == expected['final_correct'], 'sameSemanticFinalSubset')"
 assert old in utility_worker;utility_worker=utility_worker.replace(old,replacement).replace("'utility_counts'","'fixture_label_checks'")
 utility_worker=utility_worker.replace("'Both complete predeclared public fixture histories; no new model runs/training/downloads or utility reselection.'",
  "'Both complete semantic integration-fixture histories; this subset is not a new accuracy sample and no model ran.'")
 utility_worker=utility_worker.replace("'Public fixture is known-state utility evidence, not private-ingress confidentiality evidence.'",
  "'Public semantic fixture is known-state consistency evidence. Effective rank4 per route/rank8 total; spanning exact-score recipients determine each aggregate.'")
 adapted=original[:original.index('def stage(args):')]+utility_worker+'\n'+MAIN
 path=SNAP/'verified_reader/utility_driver.py';path.write_text(adapted);pins['verified_reader/utility_driver.py']=sha(path)
 (ROOT/'utility_worker_adapter.diff').write_text('\n'.join(difflib.unified_diff(original.splitlines(),adapted.splitlines(),fromfile='frozen_original_utility_driver.py',tofile='semantic_utility_driver.py'))+'\n')
 original_fast=(E2E/'verified_reader/fast_utility_driver.py').read_text();dependencies[str(E2E/'verified_reader/fast_utility_driver.py')]=hashlib.sha256(original_fast.encode()).hexdigest()
 assert dependencies[str(E2E/'verified_reader/fast_utility_driver.py')]=='6581d30f17d7e330f1e17cb5517f144232bc720019617299aae114aff594492d'
 fast_worker=function(original_fast,'worker');cut=fast_worker.index("    baseline = load(reports / 'baseline_utility_report.json')")
 fast_worker=fast_worker[:cut]+'''    workers=[load(reports/f'history_{h}/host_worker_report.json') for h in [0,1]]
    summary={'ok':True,'schema':'semantic-complete-bfv-persistent-host-v1',
             'events':full['events'],'learns':full['learns'],'infers':full['infers'],
             'expiries':full['expiries'],'all_oracle_matches':full['all_oracle_matches'],
             'worker_processes':2,'workers':workers,'worker_elapsed_ns':time.perf_counter_ns()-started,
             'pipeline_elapsed_ns':full['elapsed_ns'],
             'scope':'One actual semantic consistency fixture. No cross-fixture speedup or new utility estimate; full BFV receiver key retained.'}
    dump(reports/'fast_report.json',summary)
    print(json.dumps({'ok':True,'events':full['events'],'verified_outputs':96,'fast_report':str(reports/'fast_report.json')}),flush=True)
'''
 fast_prefix=original_fast[:original_fast.index('def outer(args):')]
 fast_prefix=fast_prefix.replace("UTILITY_SHA = 'f623dbf5d903c6a6ced87cfb5735dd1bda47f861665f8d88670184f6dc463847'",f"UTILITY_SHA = '{pins['verified_reader/utility_driver.py']}'")
 adapted_fast=fast_prefix+fast_worker+'\n'+MAIN
 path=SNAP/'verified_reader/fast_utility_driver.py';path.write_text(adapted_fast);pins['verified_reader/fast_utility_driver.py']=sha(path)
 def persistent_body(source):
  node=next(n for n in ast.walk(ast.parse(source)) if isinstance(n,ast.ClassDef) and n.name=='PersistentRun')
  return ast.get_source_segment(source,node)
 assert persistent_body(original_fast)==persistent_body(adapted_fast),'PersistentRun body must remain byte-identical'
 (ROOT/'persistent_worker_adapter.diff').write_text('\n'.join(difflib.unified_diff(original_fast.splitlines(),adapted_fast.splitlines(),fromfile='frozen_fast_driver.py',tofile='semantic_fast_driver.py'))+'\n')
 fixture=load(MAT/'fixture.json');index=load(MAT/'runtime/issuer/input_index.json');oraclepath=MAT/'runtime/oracle/expected_scalars.json'
 census=load(MAT/'runtime_hash_census.json')['files'];frozen={}
 for event in index['events']:
  field='issuer_vector_path' if event['kind']=='Learn' else 'public_query_vector_path';source=Path(event[field]);raw=source.read_bytes()
  expected=census[str(source.relative_to(MAT))]['sha256'];assert hashlib.sha256(raw).hexdigest()==expected
  dest=SNAP/'utility'/('issuer_oracle' if event['kind']=='Learn' else 'public_queries')/source.name
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);os.chmod(dest,0o600 if event['kind']=='Learn' else 0o644)
  event[field]=str(dest);frozen[str(dest.relative_to(SNAP))]=expected
 issuer=SNAP/'utility/issuer_oracle';os.chmod(issuer,0o700)
 dump(issuer/'input_index.json',index);os.chmod(issuer/'input_index.json',0o600)
 shutil.copyfile(oraclepath,issuer/'expected_scalars.json');os.chmod(issuer/'expected_scalars.json',0o600)
 oracle=load(oraclepath)['queries'];expect={'all_correct':sum(x['correct'] for x in oracle.values()),
  'nonempty_correct':sum(x['correct'] for x in oracle.values() if not x['public_structural_zero']),
  'final_correct':sum(x['correct'] for x in oracle.values() if x['phase']==3),'scope':'Frozen fixture label checks, not new accuracy estimate'}
 dump(SNAP/'utility/fixture_expectations.json',expect)
 public=load(MAT/'public_query_records.json')['queries'];assert len(public)==16 and [q['route'] for q in public]==[0]*8+[1]*8
 assert len({tuple(q['vector']) for q in public})==8
 provenance={'semantic_fixture_sha256':sha(MAT/'fixture.json'),'semantic_materialization_manifest_sha256':sha(MAT/'manifest.json'),
  'original_index_sha256':sha(MAT/'runtime/issuer/input_index.json'),'copied_index_sha256':sha(issuer/'input_index.json'),
  'oracle_sha256':sha(issuer/'expected_scalars.json'),'expectations_sha256':sha(SNAP/'utility/fixture_expectations.json'),
  'frozen_vector_files':frozen,'issuer_vectors':384,'public_query_records':16,'distinct_query_rows':8,'expected_outputs':96,
  'history_ids':[67000,67001],'source_utility_results_sha256':sha(PARENT/'results.json'),
  'scope':'Teacher-derived PUBLIC semantic fixture; source/oracle not passed to keyless roles; no new model or accuracy sample'}
 dump(REPORTS/'source_pins.json',pins);dump(REPORTS/'fixture_pins.json',provenance)
 shutil.copyfile(MAT/'full_survey_reference.json',REPORTS/'full_survey_reference.json')
 shutil.copyfile(MAT/'build_results.json',REPORTS/'semantic_image_scope.json')
 with tarfile.open(REPORTS/'source_snapshot.tar.gz','w:gz') as archive:
  for name in sorted(pins):
   if name!='resident-crypto':archive.add(SNAP/name,arcname=name)
 for p in [ROOT/'CONTRACT.md',ROOT/'.gitignore',ROOT/'prepare.py',ROOT/'run.py',ROOT/'validate.py',PARENT/'manifest.json',MAT/'manifest.json',MAT/'fixture.json']:
  dependencies[str(p)]=sha(p)
 freeze={'source_dependencies':dependencies,'snapshot_source_pins':pins,'fixture_pins_sha256':sha(REPORTS/'fixture_pins.json'),
  'parent_entries_preserved':counts,'persistent_run_class_identical':True,'runtime':str(RUNTIME),'reports':str(REPORTS),
  'prepared_before_crypto_execution':True,'crypto_executions_so_far':0,'prepare_wall_seconds':time.perf_counter()-started}
 dump(ROOT/'freeze.json',freeze);dump(REPORTS/'dependency_pins_before.json',dependencies)
 assert preserved(PARENT)==counts['parent'] and preserved(MAT)==counts['materialized']
 print(json.dumps({'prepared':True,'freeze_sha256':sha(ROOT/'freeze.json'),'source_pins':pins,
  'fixture_pins_sha256':sha(REPORTS/'fixture_pins.json'),'expected_counts':fixture['counts'],'retained_parent_counts':counts},indent=2))
if __name__=='__main__':main()
