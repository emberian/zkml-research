#!/usr/bin/env python3
"""Collect named public outputs and public actor receipts; never follow their paths."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
SHARED=REPO/'research/vfhe_2026_09_08/proved_journal/seeded_ring_successor/results/seeded001'
EXPECTED={
 'RESULT.json':'b0945855f9f42dfb2a8c1f959fafcc6a4c81204b409f2cc6ed3c0a017ba8b0e8',
 'PUBLIC_COMPLETE.json':'f98b17b208e3ccea5c4475ce169f2114e57c5b83fe064a12a116a1d46cc955d9',
 'public_setup.json':'ea8c24ebf29c8eb9115c5f785330586e24fb3f1b5aeb8cc4f68f60b2772fdc76',
 'a.ring':'e66665b047d7ed67fc9bf0f961a3d0ec7a5895dd63ecb1626cdb3efa48fdf512',
 'public.ring':'d805d4ed5dc77a7521494aa1d98471c043fe03ac93e4c09662ff0b52f95be1e2',
}
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for data in iter(lambda:f.read(1<<20),b''):h.update(data)
    return h.hexdigest()

def main():
    public={}
    for name,pin in EXPECTED.items():
        path=SHARED/name;actual=sha(path);assert actual==pin,(name,actual)
        public[str(path)]={'sha256':actual,'bytes':path.stat().st_size}
    result=json.loads((SHARED/'RESULT.json').read_text())
    assert result['status']=='PASS' and result['seed_bits']==384
    assert result['sources_unchanged'] and result['public_complete_before_recipient_queries']
    assert result['fresh_encodes']==6 and result['fresh_registered_keys']==16
    assert result['missing_row_secrets']==0 and result['orchestrator_private_payload_reads']==0
    registry_bytes=(HERE/'registry.json').stat().st_size
    actors=[];actor_pins={}
    receipt_paths=list((SHARED/'actors').glob('*.json'))+list((SHARED/'deliveries').glob('delivery-*/transport.json'))
    for path in sorted(receipt_paths):
        if path.name.endswith('.command.json'):continue
        receipt=json.loads(path.read_text())
        if 'role_command' not in receipt:continue
        assert receipt['status']=='PASS',path.name
        actors.append(receipt)
        actor_pins[str(path)]={'sha256':sha(path),'bytes':path.stat().st_size}
    assert len(actors)==53,len(actors)
    by_role={}
    for role,count in [('register',16),('encode',6),('query',16)]:
        times=[a['elapsed_seconds'] for a in actors if a['role_command']==role]
        assert len(times)==count,(role,len(times))
        by_role[role]={'count':count,'min_seconds':min(times),'max_seconds':max(times),'total_seconds':sum(times)}
    # Consume saved metadata only: do not open/stat any artifact path in a receipt.
    keys=[w for a in actors if a['role_command']=='register' for w in a['artifact_writes'] if w['kind']=='key']
    fresh=[w for a in actors if a['role_command']=='encode' for w in a['artifact_writes'] if w['kind']=='ciphertext']
    assert len(keys)==16 and len(fresh)==6
    metrics={'scope':'Saved public actor receipt metadata; artifact paths never followed',
             'actor_receipts':len(actors),'actor_receipt_pins':actor_pins,
             'peak_standalone_actor_rss_bytes_macos':max(a['peak_rss_bytes_macos'] for a in actors),
             'receipt_internal_elapsed':by_role,
             'elapsed_scope':'Per-process receipt timing; parent command wall time includes additional startup/check overhead',
             'key_file_bytes_min':min(w['bytes'] for w in keys),
             'key_file_bytes_max':max(w['bytes'] for w in keys),
             'key_file_bytes_sum':sum(w['bytes'] for w in keys),
             'key_payload_bytes_each':sorted(set(w['payload_bytes'] for w in keys)),
             'fresh_ciphertext_file_bytes_each':sorted(set(w['bytes'] for w in fresh))}
    out={'scope':'[EXECUTED] Public-only collection of the one shared fresh service run; no extra crypto',
         'status':'PASS','shared_public_outputs':public,'result':result,
         'actor_metrics':metrics,
         'issuer_required_public_bytes':result['public_issuer_bundle_bytes']+registry_bytes,
         'fixed_semantic_registry_bytes':registry_bytes,
         'public_registered_payload_bytes':16*16384*289//8,
         'expanded_A_plus_all_P_payload_bytes':(64+577)*16384*289//8,
         'payload_reduction_factor':'641/16 = 40.0625',
         'private_row_payload_bytes':64*16384*29//8,
         'private_payloads_read_by_collector':0,'new_setups_or_encryptions_by_collector':0}
    (HERE/'RUN.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','shared_setup_runs':1,'additional_setups':0,
          'public_issuer_bundle_bytes':result['public_issuer_bundle_bytes'],
          'issuer_with_fixed_registry_bytes':out['issuer_required_public_bytes'],
          'seconds':result['elapsed_seconds'],'matched_scores':result['scalar_scores_matched']}))

if __name__=='__main__':main()
