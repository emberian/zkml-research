"""Check closed normal public computation evidence; no reader or secret access."""
from pathlib import Path
from common import ROOT,UTILITY,REPORTS,load,save,meta,sha,lines,verify_freeze

def main():
    verify_freeze();closed=load(REPORTS/'public_phase.json')
    assert closed['completed'] and closed['reader_invocations']==0
    for row in closed['public_transcripts'].values():assert meta(row['path'])==row
    operations=lines(REPORTS/'public_operations.jsonl');events=lines(REPORTS/'events.jsonl');pairs=lines(REPORTS/'replays.jsonl')
    fixture=load(UTILITY/'materialized_fixture.json')['events']
    assert len(fixture)==len(events)==len(pairs)==480
    assert all(o['binary']!='reader' and o['exit_code']==0 and not o['timed_out'] for o in operations)
    host=[o for o in operations if o['binary']=='host'];assert len(host)==960
    public_files={}
    for o in operations:
        assert o['binary_before']==o['binary_after']
        if o['binary']=='host':
            before=o['public_read_inputs_before'];after=o['public_read_inputs_after']
            assert len(before)==3 and before==after
            assert o['command'][2:5]==[r['path'] for r in before]
            assert not o['reported']['client_key_read']
            assert o['reported']['gate_api_calls']==(
                {'and':180,'xor':264,'not':46,'mux':32,'trivial_encrypt':20} if o['command'][1]=='learn'
                else {'and':0,'xor':0,'not':0,'mux':3,'trivial_encrypt':0})
            for r in before:
                if r['path'] in public_files:assert public_files[r['path']]==r
                public_files[r['path']]=r
    current={}
    for initial in closed['initial_states']:
        current.setdefault(initial['history_id'],{})[str(initial['route'])]=initial['state']
    for ref,e,p in zip(fixture,events,pairs):
        for key in ['event_id','event_ordinal','history_id','history_index','kind','learn_step','phase','route','record_id']:
            assert ref[key]==e[key]
        assert p['event_id']==e['event_id'] and p['kind']==e['kind'] and p['route']==e['route']
        assert e['parents_before']==current[e['history_id']]
        left,right=[operations[p[k]] for k in ['primary_operation','replay_operation']]
        assert left['binary']==right['binary']=='host'
        assert left['name']==e['event_id']+'.primary' and right['name']==e['event_id']+'.replay'
        assert left['public_read_inputs_before']==right['public_read_inputs_before']==p['public_read_inputs']
        assert p['public_read_inputs'][1]==e['parents_before'][str(e['route'])]
        assert p['public_read_inputs'][2]==e['encrypted_request']
        assert p['inputs_equal_across_invocations'] and p['complete_output_bytes_equal']
        assert p['primary_process']!=p['replay_process']
        assert p['primary']==e['output'] and left['command'][-1]==p['primary']['path'] and right['command'][-1]==p['replay']['path']
        a,b=Path(p['primary']['path']),Path(p['replay']['path'])
        assert a.read_bytes()==b.read_bytes()
        for r in [p['primary'],p['replay'],e['encrypted_request']]:public_files[r['path']]=r
        expected=dict(e['parents_before'])
        if e['kind']=='Learn':expected[str(e['route'])]=e['output']
        assert expected==e['parents_after'];current[e['history_id']]=expected
    for path,row in public_files.items():assert meta(path)==row,path
    verify_freeze()
    out={'passed':True,'closed_public_phase_sha256':sha(REPORTS/'public_phase.json'),
         'closed_public_transcript_sha256':{k:v['sha256'] for k,v in closed['public_transcripts'].items()},
         'events_checked':len(events),'host_invocations_checked':len(host),'full_byte_replay_pairs_checked':len(pairs),
         'public_read_input_before_after_checks':3*len(host),'read_tuple_pair_equalities':len(pairs),
         'final_public_file_hashes_checked':len(public_files),'two_route_parent_transitions_checked':len(events),
         'reader_invocations':0,'source_hashes_unchanged':True,
         'scope':'same-author independent public transcript checker; replay uses same pinned TFHE implementation'}
    save(REPORTS/'public_verification.json',out);print(out)

if __name__=='__main__':main()
