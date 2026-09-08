"""Public-only structural audit of the first failed replay. No crypto dispatch."""
import collections
import datetime
import json
import struct
import subprocess
from pathlib import Path
from common import ROOT,PRIOR,REPORTS,RUNTIME,BIN,load,save,sha,meta,lines,verify_freeze

def decode_public_records(path):
    raw=Path(path).read_bytes()
    assert raw[:8]==b'PEMA0001' and raw[8]==1
    assert struct.unpack_from('<Q',raw,9)[0]==len(raw)-17
    count=struct.unpack_from('<Q',raw,17)[0];assert count==32
    offset=25;records=[]
    for index in range(count):
        start=offset
        variant=struct.unpack_from('<I',raw,offset)[0];offset+=4
        assert variant==0 # Ciphertext::Encrypted, first Serde enum variant.
        length=struct.unpack_from('<Q',raw,offset)[0];offset+=8
        assert length==838
        data_start=offset;offset+=length*4;data_end=offset
        modulus=int.from_bytes(raw[offset:offset+16],'little');offset+=16
        scalar_bits=struct.unpack_from('<Q',raw,offset)[0];offset+=8
        assert modulus==0 and scalar_bits==32
        records.append({'record_zero_index':index,'register_zero_index':index//8,'bit_lsb_zero_index':index%8,
                        'start':start,'end_exclusive':offset,'data_start':data_start,'data_end_exclusive':data_end,
                        'coefficient_count':length,'variant':variant,'modulus':modulus,'scalar_bits':scalar_bits})
    assert offset==len(raw)
    return raw,records

freeze=verify_freeze();failure=load(REPORTS/'failure.json')
operations=lines(REPORTS/'public_operations.jsonl');pairs=lines(REPORTS/'replays.jsonl');events=lines(REPORTS/'events.jsonl')
assert failure['error']=="AssertionError('h0-e0014')" and failure['private_drain_executed'] is False
assert len(events)==13 and len(pairs)==14 and len(operations)==61
assert not (REPORTS/'public_phase.json').exists() and not (REPORTS/'private_drain.json').exists()
assert all(o['exit_code']==0 and not o['timed_out'] and o['binary']!='reader' for o in operations)
public_inputs={}
for o in operations:
    assert o['binary_before']==o['binary_after']
    if o['binary']=='host':
        assert o['public_read_inputs_before']==o['public_read_inputs_after']
        assert len(o['public_read_inputs_before'])==3
        for row in o['public_read_inputs_before']:
            path=row['path'];assert Path(path).is_relative_to(RUNTIME/'public')
            if path in public_inputs:assert public_inputs[path]==row
            public_inputs[path]=row
for path,row in public_inputs.items():assert meta(path)==row
comparisons=[]
for i,p in enumerate(pairs):
    a,ar=decode_public_records(p['primary']['path']);b,br=decode_public_records(p['replay']['path'])
    assert ar==br and meta(p['primary']['path'])==p['primary'] and meta(p['replay']['path'])==p['replay']
    left,right=[operations[p[k]] for k in ['primary_operation','replay_operation']]
    assert left['public_read_inputs_before']==right['public_read_inputs_before']==p['public_read_inputs']
    assert p['inputs_equal_across_invocations'] and p['primary_process']!=p['replay_process']
    assert (a==b)==p['complete_output_bytes_equal']==(i<13)
    differences=[j for j in range(len(a)) if a[j]!=b[j]]
    changed=[]
    for r in ar:
        ix=[j for j in differences if r['start']<=j<r['end_exclusive']]
        if not ix:continue
        words=sum(a[j:j+4]!=b[j:j+4] for j in range(r['data_start'],r['data_end_exclusive'],4))
        assert all(r['data_start']<=j<r['data_end_exclusive'] for j in ix)
        changed.append({**r,'changed_bytes':len(ix),'changed_u32_coefficients':words,
                        'first_difference':min(ix),'last_difference':max(ix),
                        'header_and_modulus_metadata_equal':True})
    comparisons.append({'event_id':p['event_id'],'equal':a==b,'serialized_bytes':len(a),
                        'different_bytes':len(differences),'first_difference':min(differences) if differences else None,
                        'last_difference':max(differences) if differences else None,'changed_records':changed})
last=pairs[-1]
source_root=Path('/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/tfhe-1.6.3')
codec_sources=[PRIOR/'src/lib.rs',source_root/'src/boolean/ciphertext/mod.rs',
               source_root/'src/core_crypto/entities/lwe_ciphertext.rs',
               source_root/'src/core_crypto/commons/ciphertext_modulus.rs']
link_command=['otool','-L',str(BIN/'host')]
linked=subprocess.run(link_command,capture_output=True,text=True)
assert linked.returncode==0
public_files=[meta(p) for p in sorted((RUNTIME/'public').rglob('*')) if p.is_file()]
out={'passed_public_evidence_audit':True,'crypto_workload_completed':False,
     'scope':'first scoped complete-byte determinism failure; semantic correctness not assessed',
     'counts':{'accepted_logical_Learn_events':13,'Learn_evaluated_primary':14,'Learn_evaluated_replay':14,
               'replay_pairs_tested':14,'equal_replay_pairs':13,'unequal_replay_pairs':1,'Infer_evaluations':0,
               'query_ciphertexts_issued':16,'Learn_inputs_issued':14,'initial_states_issued':2,'setups':1,
               'role_processes':61,'reader_invocations':0},
     'read_input_before_after_comparisons':84,'sources_unchanged':True,
     'failure':failure,'pair_comparisons':comparisons,'failed_pair':last,
     'failed_pair_operations':[operations[last[k]] for k in ['primary_operation','replay_operation']],
     'thread_environment':load(REPORTS/'started.json')['thread_environment'],
     'runtime_binary_hashes':{n:meta(BIN/n) for n in ['setup','issuer','host','reader']},
     'cargo_toml':meta(PRIOR/'Cargo.toml'),'cargo_lock':meta(PRIOR/'Cargo.lock'),
     'previous_source_manifest':meta(PRIOR/'source_manifest.json'),
     'linked_libraries':{'command':link_command,'exit_code':linked.returncode,'stdout':linked.stdout,'stderr':linked.stderr,
                         'scope':'declared binary links inspected after failure, not a captured loaded-library census'},
     'public_codec_source_locations':[meta(p) for p in codec_sources],
     'public_runtime_files':public_files,
     'preserved_public_transcripts':{p.name:meta(p) for p in [REPORTS/'public_operations.jsonl',REPORTS/'events.jsonl',REPORTS/'replays.jsonl']},
     'run_wall_seconds':load(ROOT/'run.command.json')['wall_seconds'],
     'audited_utc':(load(REPORTS/'public_failure_audit.json')['audited_utc']
                    if (REPORTS/'public_failure_audit.json').exists()
                    else datetime.datetime.now(datetime.timezone.utc).isoformat()),
     'new_crypto_invocations':0,'private_files_read':0,
     'parser_scope':'typed public envelope and Serde/bincode LWE coefficient records only; no plaintext decoding'}
verify_freeze();save(REPORTS/'public_failure_audit.json',out)
print({'counts':out['counts'],'failed_pair_detail':comparisons[-1],
       'public_failure_audit_sha256':sha(REPORTS/'public_failure_audit.json')})
