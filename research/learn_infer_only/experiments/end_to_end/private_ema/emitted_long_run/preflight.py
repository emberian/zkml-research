"""Public fixture integer-oracle/layout preflight; no cryptographic execution."""
from collections import Counter
from common import ROOT, PRIOR, FIXTURE, FIXED, load, save, sha, meta


def main():
    fixture = load(FIXTURE)
    manifest = load(PRIOR / 'utility/manifest.json')
    recorded = manifest['files']['materialized_fixture.json']
    assert {'bytes': FIXTURE.stat().st_size, 'sha256': sha(FIXTURE)} == recorded
    counts = Counter(e['kind'] for e in fixture['events'])
    assert counts == {'Learn':384, 'Infer':96} and fixture['counts'] == {'Learn':384,'Infer':96,'expiry':0}
    assert fixture['history_seeds'] == [67000,67001]
    states, query_bins, seen, history_counts = {}, {}, set(), {}
    final_correct = 0
    for event in fixture['events']:
        hid = event['history_id']; route = event['route']; address = event['bin']
        assert route in [0,1] and address in range(4) and event['event_id'] not in seen
        seen.add(event['event_id'])
        if hid not in states: states[hid] = [[0]*4 for _ in range(2)]; history_counts[hid] = Counter()
        history_counts[hid][event['kind']] += 1
        if event['kind'] == 'Learn':
            assert event['u'] in [-120,120]
            assert event['learn_step'] == history_counts[hid]['Learn']
            state = states[hid][route]
            state[address] = (7*state[address]+event['u'])//8
            assert states[hid] == event['state_after']
        else:
            assert event['ema_score'] == states[hid][route][address]
            assert event['ema_prediction'] == (-1 if event['ema_score']<0 else 1)
            rid = event['record_id']
            if rid in query_bins: assert query_bins[rid] == address
            query_bins[rid] = address
            if event['phase'] == 3: final_correct += int(event['ema_prediction']==event['target'])
    assert all(count=={'Learn':192,'Infer':48} for count in history_counts.values())
    assert len(query_bins)==16 and final_correct==fixture['final']['ema']['correct']==28
    controls = load(FIXED/'summary.json')
    projected = 768*controls['cost_groups']['learn']['wall_seconds_median'] + 192*controls['cost_groups']['infer']['wall_seconds_median']
    output = {'claim':'EXECUTED','fixture':meta(FIXTURE),'matched_original_manifest':True,
              'counts':dict(counts),'expiry':0,'histories':fixture['history_seeds'],
              'fresh_initial_states':4,'initial_explanation':'two histories times two public routes; no initial replay duplication',
              'distinct_query_ciphertexts':16,'fresh_learn_inputs':384,'host_invocations':960,
              'issuer_invocations':404,'public_role_invocations':1364,'replay_pairs':480,
              'private_opens':{'initial_primary_states':4,'learn_primary_selected_route_states':384,'infer_primary_signs':96,'total':484},
              'frozen_integer_oracle_consistent':True,'selected_final_oracle_correct':28,'selected_final_oracle_queries':32,
              'projection_seconds_from_fixed_control_medians':projected,'projection_excludes_hashing_issuer_reader_overhead_and_contention_change':True,
              'projection_source':meta(FIXED/'summary.json'),'crypto_invocations':0}
    save(ROOT/'preflight.json',output); print(__import__('json').dumps(output,indent=2))


if __name__=='__main__': main()
