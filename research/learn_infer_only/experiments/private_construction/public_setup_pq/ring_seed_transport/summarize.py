#!/usr/bin/env python3
"""Summarize saved public receipts only; never opens runtime/private files."""
from pathlib import Path
import collections
import hashlib
import json

HERE=Path(__file__).resolve().parent


def main():
    wp=HERE/'results/candidate001/WORKFLOW.json'
    workflow=json.loads(wp.read_text())
    assert workflow['status']=='PASS' and workflow['sources_unchanged']
    commands=workflow['commands']; groups=collections.defaultdict(list)
    pids=[]; private_reads=[]; writes=[]; rss=[]; outputs=0
    for command in commands:
        path=Path(command['receipt'])
        assert path.is_relative_to(HERE/'results')
        receipt=json.loads(path.read_text()); assert receipt['status']=='PASS'
        pids.append(receipt['pid']); groups[receipt['role_command']].append(command['wall_seconds'])
        rss.append(receipt['peak_rss_bytes_macos']);writes+=receipt['artifact_writes']
        pr=[row for row in receipt['artifact_reads'] if row['private']]
        if command['role']=='public':assert not pr
        else:
            assert all(command['role'] in Path(row['path']).parts for row in pr)
        private_reads+=pr
        if receipt['role_command']=='decode':
            assert receipt['result']['expected_synthetic_lift_matched']; outputs+=1
    assert len(pids)==len(set(pids))==45 and len(private_reads)==outputs==20
    keys=[r for r in writes if r['kind']=='key'];assert len(keys)==16 and all(r['mode']=='0o600' for r in keys)
    kinds=collections.defaultdict(list)
    for row in writes:kinds[row['kind']].append(row)
    summary={'status':'PASS','workflow_sha256':hashlib.sha256(wp.read_bytes()).hexdigest(),
       'total_seconds':workflow['elapsed_seconds'],'actor_processes':len(pids),'unique_actor_pids':len(set(pids)),
       'role_seconds':{kind:{'count':len(v),'total':sum(v),'min':min(v),'max':max(v)} for kind,v in groups.items()},
       'peak_actor_rss_bytes':max(rss),'actual_recipient_keys':16,'absent_recipient_keys':0,
       'designated_outputs_matched':outputs,'public_private_payload_reads':0,'orchestrator_private_payload_reads':0,
       'key_container_bytes_min':min(x['bytes'] for x in keys),'key_container_bytes_max':max(x['bytes'] for x in keys),
       'actual_artifact_sizes':{Path(row['path']).name:{'bytes':row['bytes'],'payload_bytes':row.get('payload_bytes')}
          for row in writes if row['kind'] in ('seeded_a','seeded_public','explicit_registry','ciphertext')},
       'actual_registration_bytes_min':min(x['bytes'] for x in kinds['registration']),
       'actual_registration_bytes_max':max(x['bytes'] for x in kinds['registration']),
       'private_payloads_opened_by_this_summary':0,'new_crypto_runs':0}
    bundle=sum(row['bytes'] for row in writes if row['kind'] in ('seeded_public','explicit_registry'))
    baseline_path=HERE.parent/'ring_transport/SUMMARY.json'
    baseline=json.loads(baseline_path.read_text())
    old=baseline['actual_artifact_sizes']['public.ring']['bytes']
    summary.update({'seeded_issuer_bundle_bytes':bundle,'ideal_uniform_baseline_public_bytes':old,'public_bundle_reduction_factor':old/bundle,'public_bundle_reduction_percent':100*(1-bundle/old),'baseline_summary_sha256':hashlib.sha256(baseline_path.read_bytes()).hexdigest(),'security_mode':'Conditional public-SHAKE seeded setup; ideal-uniform theorem not transferred'})
    (HERE/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
