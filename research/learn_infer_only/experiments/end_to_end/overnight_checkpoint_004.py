#!/usr/bin/env python3
"""Collect named frozen public evidence only; never execute its producers.

Only this script and overnight_checkpoint_004.json are written. Public source
bytes are hashed; saved theorem/runtime assertions remain attributed evidence.
No private, model, key, ciphertext, stopped-task or active runtime file is read.
"""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import sys
import traceback
from collect_interrupted_run import HERE, REPO, SEEN

R = REPO/'research'
L = R/'learn_infer_only'
E = L/'experiments'
F = R/'proof_frontier/2026-09-08'
V = E/'adversarial_review'
PQ = E/'private_construction/public_setup_pq'
RUN = E/'integration/results/run_018'
LONG = HERE/'private_ema/emitted_long_run'
SEED = E/'private_construction/designated_span/public_coin_setup/public_seed/adapter'
COUNTS, FACTS, COMMANDS, OMITTED = {}, {}, [], []

# Exact anchors supplied by root or the owning lane before this collection.
ANCHORS = {
 HERE/'overnight_2026-09-08_baseline.json':'c3900b2f77cd701412c40622ecf790746722c9cbf96e92fdf53be1e1d5802e9a',
 RUN/'report.json':'75c1d3921998fdf7fd5377af07be6887304ebe004369eab09c28effc75ec5b39',
 RUN/'check_all_formal.py':'563b52272d913d00eb5751588befbbe7f7b226d83016d1c53f917dececff57ff',
 RUN/'SUMMARY.md':'905591728b9b87a97b7048c5d955eff379ae2fa40766c58b7f58e46432f6c3bd',
 L/'formal/integration/minidregg-combined-resident-952.patch':'82e1ac3f54aa0b82e74c464358724a05be206e358bb634b4f49016a196b3dd18',
 F/'formal/babybear_folding_tower/manifest.json':'ae965e4e43fdded42b7992ee8ee9a1a265085c9ab861e2c481fef75ca1e14dc2',
 V/'babybear_folding_tower/review_manifest.json':'fee6b2e836d0655e6f0309e9ef9e4bfc34bc5b2a930580b3969691f9cca5660a',
 L/'formal/cse_initialized_references/manifest.json':'1c8d73ab40a06bde6dbed4b045d78d67d7fced01c5013141047ac40dc305c5c5',
 V/'cse_initialized_references/manifest.json':'d5c28ec39637be38e485ebbb9d412e587a4b20deac84c53311543146025dcc81',
 F/'p3_folding_transport/manifest.json':'17b4f5a087248c521eb25e7ca8d44ee859f67f2a22dac7a54dfaca43602327f5',
 F/'p3_folding_transport_review/MANIFEST.json':'32cae024984e677fd2331e1c4bfd36ed7649c24d4a650300579c62b2bc36d26e',
 F/'formal/polynomial_curve_kernel/manifest.json':'233f869cc51584f2be295dbe2c7076734a4bc10e3cdcee16a596ecc813f401e0',
 F/'formal/polynomial_curve_kernel_review/manifest.json':'ebc3125c67caa4891141bd115846a44a94fee495333d0bf599dd6f9936bbfa7e',
 F/'formal/polynomial_curve_full_ud/manifest.json':'fed8141f3d1606cd7ffa25bdd85918acbbdcb1ac8037307359adf1ff05994729',
 F/'polynomial_curve_full_ud_review/MANIFEST.json':'b07d6fe4f59c6f08a6a925dc6223c15ab80604a63d476158f904e60dc8996ccb',
 F/'polynomial_curve_full_ud_review/REPORT.md':'8729bb47fa550c8c0a37e16f90c8876c77fc8295a3cf70d6e618486047e8a090',
 F/'efficient_root_binding/MANIFEST.json':'036da50e4a76d36581ea7d867096292008db6691661f0721471b3c71c63aa118',
 F/'efficient_root_binding_review/MANIFEST.json':'b2a166db6eb5daf1b24902bb9ff0f49b7b45559dfd743fdc7d97a130ffb7189a',
 SEED/'FINAL_MANIFEST.json':'e59b5c1734dd229fd9eaf38084f0efce977f9f49319c7057c067855deeaefff8',
 V/'public_seed_adapter/manifest.json':'e3cdb34f400ea9d67574d91e32f5249cdfc4f40039f6ec2a8d5f1e0016283709',
 V/'public_seed_adapter/execution/manifest.json':'c5e05ce99c7e88ad048f552d3130bb3403213ce0f1c9849ecb0c45ea8fa44976',
 LONG/'PACKAGE.json':'0a9a15b6ca0784b3f6de03df83b77873469ef26f59164a5663882fe2065b6ba4',
 LONG/'collection.json':'e536a7027fd89bf849d86edda20fd72cd8396e1dc69cdc737cea17f455a3e16f',
 LONG/'REPORT.md':'0bfcfc46d5d469d4b113c1179f0147664207a0e3c5b511c4c87e98344d8e934a',
 PQ/'ring_candidate/MANIFEST.json':'703e824295a40357f44d3a8cfa073ae2f6c1411b24783a83ca1c6e4f7992fbdb',
 PQ/'ring_candidate/hardness/MANIFEST.json':'2f90bee88437465514066d879eddbc3918ab1af6d0c8d6592e63b0750adeef53',
 PQ/'finite_sampler/MANIFEST.json':'23226a36d44899189716a63bd97378bdf114b8791fa0f80a39ed3f212b1adf4e',
 V/'ring_fixed_coordinate/manifest.json':'04faaf80518c2893943d0f67399eb1ba8351ff5edf6f0dcb1a49028521be880b',
 V/'ring_hardness/review_manifest.json':'66286b9e9535e0951cc39c9aab0e8afa62ac0a5e9add0330c96927f131f41121',
 V/'finite_sampler/manifest.json':'ec58c8a262a4821028d715a28c30a7de76cd38140a11e2b01fe7fc7c7a236921',
}


def excluded(path):
    p = Path(path).resolve()
    if any(x in p.parts for x in ('.private','.private_fixture','private','runtime','models')):
        return 'private/model/runtime subtree excluded'
    if any(x in str(p) for x in ('signer_route','verified_route','efficient_root_opening','seed_journal')):
        return 'stopped or unsealed task excluded'
    if p.suffix in ('.bin','.safetensors','.pt','.pth','.olean'):
        return 'binary runtime/model/key/output bytes excluded; saved inventory only'
    if p in (E/'integration/check_all_formal.py', E/'integration/results/latest.json',
             L/'formal/integration/minidregg-combined-resident.patch', L/'STATUS.md', L/'NEXT.md',
             REPO/'docs/VERDICTS.md'):
        return 'mutable shared alias or central ledger excluded'
    return None


def pin(path, expected=None, expected_bytes=None):
    p=Path(path).resolve()
    assert excluded(p) is None, (p,excluded(p))
    h=hashlib.sha256(); size=0
    with p.open('rb') as stream:
        while data:=stream.read(1024*1024): h.update(data); size+=len(data)
    row={'sha256':h.hexdigest(),'bytes':size}
    if expected is not None: assert row['sha256']==expected,(str(p),expected,row['sha256'])
    if expected_bytes is not None: assert size==expected_bytes,(p,size,expected_bytes)
    if str(p) in SEEN: assert SEEN[str(p)]==row,('changed during collection',p)
    SEEN[str(p)]=row
    return row


def read(path):
    pin(path)
    return json.loads(Path(path).read_bytes())


def inventory(label,base,entries):
    if isinstance(entries,dict):
        rows=[dict(path=k,sha256=v) if isinstance(v,str) else dict(v,path=k) for k,v in entries.items()]
    else: rows=entries
    checked=0
    for row in rows:
        p=Path(row['path']); p=p if p.is_absolute() else Path(base)/p
        why=excluded(p)
        if why:
            OMITTED.append({'inventory':label,'path':str(p),'reason':why,'saved_sha256':row.get('sha256')})
            continue
        pin(p,row['sha256'],row.get('bytes')); checked+=1
    COUNTS[label]={'declared':len(rows),'public_files_checked':checked,'excluded_references':len(rows)-checked}


def package(path,fields=('files',)):
    p=Path(path); d=read(p)
    for key in fields: inventory(str(p.relative_to(REPO))+':'+key,p.parent,d[key])
    return d


def saved_check(check):
    assert check['exit_code']==0
    if 'source_unchanged' in check: assert check['source_unchanged']
    p=Path(check['log']); pin(p)
    if p.with_suffix('.json').exists():
        assert read(p.with_suffix('.json'))['exit_code']==0


def collect_run018():
    d=read(RUN/'report.json')
    assert d['status']=='passed' and (d['module_count'],d['theorem_pins'])==(72,952)
    assert d['input_hashes_before']==d['input_hashes_after'] and not d['changed_inputs']
    assert not d['changed_companion_sources'] and d['combined_patch_exact_content_verified']
    assert d['all_selected_modules_rooted'] and d['no_clean_full_build_claim']
    archived=RUN/'check_all_formal.py'
    substitutions={E/'integration/check_all_formal.py':archived}
    for name,value in d['input_hashes_before'].items():
        source=Path(name).resolve(); pin(substitutions.get(source,source),value)
    COUNTS['run018_saved_inputs']=len(d['input_hashes_before'])
    pin(RUN/'minidregg-combined-resident.patch',d['combined_patch']['sha256'])
    for row in d['commands']:
        assert row['exit_code']==0
        assert read(RUN/row['log'])['exit_code']==0
    census=read(RUN/'axiom_census.json')
    assert len(census)==72 and sum(x['pin_count'] for x in census.values())==952
    assert sum(x['theorem_count'] for x in census.values())==952
    for row in census.values():
        pin(row['source'],row['sha256'])
        assert row['theorem_count']==row['pin_count']==len(row['pins']) and not row['forbidden_constructs']
    objects=read(RUN/'compiled_olean_hashes.json')
    dependencies=read(RUN/'cached_dependency_artifacts.json')
    # Keep the completed output-hash inventory; do not follow any build/cache bytes.
    assert all('sha256' in row for row in objects.values())
    FACTS['run018']={'saved_status':'passed','modules':72,'theorem_pins':952,
        'project_source_modules_reported':d['project_modules_compiled'],'saved_successful_commands':len(d['commands']),
        'input_hashes_checked':len(d['input_hashes_before']),'compiled_output_hash_records':len(objects),
        'compiled_output_bytes_reread':False,'cached_dependency_metadata_records':len(dependencies),
        'archived_harness_sha256':pin(archived)['sha256'],'snapshot_952_sha256':d['combined_patch']['sha256'],
        'saved_elapsed_seconds':d['elapsed_seconds'],'new_Lean_runs':0,'clean_full_build_claim':False}


def collect_proofs():
    for name,count in [('babybear_folding_tower',48),('polynomial_curve_full_ud',42)]:
        base=F/'formal'/name; d=read(base/'manifest.json')
        assert d['owned_pins']==d['owned_theorems']==count
        assert d['exact_guarded_checks_complete'] and d['all_pins_standard_only']
        for row in d['modules']:
            pin(base/'src'/row['path'],row['sha256']); saved_check(row['check'])
        patches=list(base.glob('*.patch')); assert len(patches)==1
        pin(patches[0],d['patch_sha256'])
        FACTS[name]={'owned_theorems_and_pins':count,'module_count':len(d['modules']),
                     'saved_exact_checks_passed':True,'new_Lean_runs':0,
                     'review_status':'accepted'}
    package(V/'babybear_folding_tower/review_manifest.json',('frozen_public_files','owned_artifacts'))
    curve_review=package(F/'polynomial_curve_full_ud_review/MANIFEST.json')
    assert curve_review['frozen'] and curve_review['verdict'].startswith('ACCEPTED')
    assert curve_review['author_manifest_sha256']==ANCHORS[F/'formal/polynomial_curve_full_ud/manifest.json']
    assert curve_review['report_sha256']==ANCHORS[F/'polynomial_curve_full_ud_review/REPORT.md']
    FACTS['polynomial_curve_full_ud']['review_scope']=curve_review['verdict']
    package(F/'formal/polynomial_curve_kernel/manifest.json')
    package(F/'formal/polynomial_curve_kernel_review/manifest.json')
    FACTS['polynomial_curve_kernel']={'owned_theorems_and_pins':26,'old_interfaces_preserved':16,'reviewed':True}
    package(L/'formal/cse_initialized_references/manifest.json')
    package(V/'cse_initialized_references/manifest.json')
    v=read(L/'formal/cse_initialized_references/results/verification.json')
    assert v['all_package_checks_passed'] and len(v['census']['theorems'])==29
    FACTS['initialized_references']={'pins':29,'saved_package_passed':True,'Rust_refinement_proved':v['rust_refinement_proved']}
    package(F/'p3_folding_transport/manifest.json')
    package(F/'p3_folding_transport_review/MANIFEST.json')
    v=read(F/'p3_folding_transport/formal/verification.json')
    assert v['all_checks_passed'] and v['theorem_count']==15
    FACTS['p3_transport']={'theorem_count':15,'saved_checks_passed':True,'full_closure_build':v['full_closure_build']}
    package(F/'efficient_root_binding/MANIFEST.json',('checked_frozen_inputs','primary_sources','owned_artifacts'))
    package(F/'efficient_root_binding_review/MANIFEST.json')
    FACTS['efficient_root_binding']={'source_math_note_and_review_collected':True,'formalization_or_execution_claim':False}


def collect_ring_sampler():
    for lane in ['ring_candidate','ring_candidate/hardness','finite_sampler']:
        package(PQ/lane/'MANIFEST.json',('artifacts',))
    package(V/'ring_fixed_coordinate/manifest.json')
    package(V/'ring_hardness/review_manifest.json',('frozen_public_files','owned_artifacts'))
    package(V/'finite_sampler/manifest.json',('artifacts',))
    summary=read(PQ/'ring_candidate/hardness/SUMMARY.json')
    assert summary['attempts']==summary['entries']==24 and summary['errors']==summary['timeouts']==0
    assert summary['status']=='PASS'
    results=read(PQ/'finite_sampler/RESULTS.json'); assert results['status']=='PASS'
    FACTS['ring_and_sampler']={'ring_proof_reviewed':True,'saved_estimator_entries':24,
        'new_estimator_entries':0,'baseline_4096_filter':'rejected','repair_16384_filter':'generic heuristics only',
        'repair_ciphertext_bytes':37900653,'repair_public_bytes':379389952,'repair_key_bytes':3801088,
        'finite_sampling_added_loss':results['combined_independent_bit_sampling_loss_bound'],
        'finite_sampler_implemented':False,'computational_security_certified':False,
        'review_scope':'Source/math, generic cost models, bounded independent-bit sampler specification; no new executions'}


def collect_seed_and_long():
    own=package(SEED/'FINAL_MANIFEST.json'); assert len(own['files'])==167
    pre=package(V/'public_seed_adapter/manifest.json')
    post=package(V/'public_seed_adapter/execution/manifest.json')
    assert post['frozen_prelaunch_manifest_sha256']==pin(V/'public_seed_adapter/manifest.json')['sha256']
    collection=read(SEED/'collection.json')
    FACTS['public_seed_adapter']={'completed_public_manifest_entries':167,'prelaunch_and_additive_execution_reviews':True,
                                 'saved_collection':collection,'private_results_attributed_only':True,'new_crypto_runs':0}
    p=package(LONG/'PACKAGE.json'); assert p['file_count']==len(p['files'])==49
    assert not p['private_key_or_plaintext_embedded'] and not p['raw_ciphertexts_embedded_in_package']
    d=read(LONG/'collection.json')
    assert d['success'] and d['phase_order_verified'] and d['new_crypto_invocations']==0
    assert not d['private_files_read'] and d['public_replay_pairs_recompared_as_bytes']==480
    inventory('long_run_saved_collection_records',LONG,d['records'])
    FACTS['completed_nonlinear_long']={'public_package_entries':49,'saved_collection_success':True,
       'replay_pairs_reported':480,'primary_opens_reported':d['authorized_primary_opens_match'],
       'separate_replay_plaintext_opens_reported':d['replay_plaintext_independent_opens'],
       'public_ciphertext_count_reported':d['public_artifacts_match'],
       'public_ciphertext_bytes_reported':d['public_artifact_bytes'],
       'final_correct_reported':d['final_correct'],'final_queries_reported':d['final_queries'],
       'all_checkpoint_correct_reported':d['all_checkpoint_correct'],'all_checkpoint_queries_reported':d['all_checkpoint_queries'],
       'public_wall_seconds_reported':d['public_wall_seconds'],
       'runtime_ciphertext_or_key_bytes_reread':False,'private_findings_attributed':True,'new_execution':False}


def git(argv):
    r=subprocess.run(argv,capture_output=True,text=True)
    COMMANDS.append({'argv':argv,'returncode':r.returncode,'stdout':r.stdout,'stderr':r.stderr})
    assert r.returncode==0
    return r.stdout


def companions():
    b=read(HERE/'overnight_2026-09-08_baseline.json'); out={}
    for name in ('minidregg','breadstuffs'):
        item=b['repositories'][name]; root=Path(item['path'])
        head=git(['git','-C',str(root),'rev-parse','HEAD']).strip()
        status=git(['git','-C',str(root),'status','--porcelain=v1','--untracked-files=all'])
        assert head==item['head'] and status==item['status'],name
        for path,row in item['preexisting_dirty_content'].items():pin(root/path,row['sha256'],row['bytes'])
        out[name]={'head':head,'head_unchanged':True,'status_unchanged':True,
                   'preexisting_dirty_files_unchanged':len(item['preexisting_dirty_content'])}
    return out


def main():
    start=datetime.datetime.now(datetime.timezone.utc).isoformat(); err=None; comp={}
    try:
        for path,expected in ANCHORS.items():pin(path,expected)
        pin(__file__); pin(HERE/'collect_interrupted_run.py'); pin(HERE/'overnight_checkpoint_003.py')
        collect_run018(); collect_proofs(); collect_ring_sampler(); collect_seed_and_long(); comp=companions()
        for path,row in list(SEEN.items()):pin(path,row['sha256'],row['bytes'])
    except Exception:err=traceback.format_exc()
    summary={'all_passed':err is None,'files_hashed':len(SEEN),'inventories':len(COUNTS),
             'named_frozen_anchors':len(ANCHORS),'companion_repositories':len(comp),'excluded_references':len(OMITTED)}
    stdout=json.dumps(summary,sort_keys=True)+'\n'
    result={'schema':'completed-public-overnight-checkpoint-v4','started_utc':start,
      'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'all_passed':err is None,'error':err,
      'scope':'Named completed public packages and saved source/output/review consistency only. Assertions are attributed saved evidence, not rerun claims.',
      'counts':COUNTS,'saved_record_observations':FACTS,'companions':comp,
      'named_anchor_sha256':{str(k.relative_to(REPO)):v for k,v in ANCHORS.items()},
      'files':dict(sorted(SEEN.items())),'excluded_manifest_references':OMITTED,
      'explicitly_deferred':['Active cache/wrapper/export work','Public-seed journal draft','Efficient-root-opening draft',
                             'Microsites','Stopped task paths','Mutable central ledgers and integration aliases',
                             'Raw model, ciphertext, key and private runtime files'],
      'commands_executed':COMMANDS,'collector_command':{'argv':sys.orig_argv,'resolved_executable':sys.executable,
      'resolved_script':str(Path(__file__).resolve()),'cwd':str(Path.cwd()),'returncode':0 if err is None else 1,
      'stdout':stdout,'stderr':err or ''},'new_lean_crypto_model_estimator_or_sampler_runs':0,'private_file_reads':0,'external_queries':0}
    (HERE/'overnight_checkpoint_004.json').write_text(json.dumps(result,indent=2)+'\n')
    sys.stdout.write(stdout)
    if err:sys.stderr.write(err)
    return 0 if err is None else 1


if __name__=='__main__':raise SystemExit(main())
