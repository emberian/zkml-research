"""Public evidence audit only: hashes, envelope identities, transcript/log consistency.
No backend imports, signature/group operations, XOF queries, private reads or sampling.
"""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib
import json
import statistics
import struct

HERE = Path(__file__).resolve().parent
PRELAUNCH = HERE.parent
EXPERIMENTS = PRELAUNCH.parents[1]
ADAPTER = EXPERIMENTS / 'private_construction/designated_span/public_coin_setup/public_seed/adapter'
RUN = ADAPTER / 'reports/normal_001'
PUBLIC = RUN / 'public'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
canonical = lambda obj: json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False).encode('ascii')
digest = lambda obj: hashlib.sha256(canonical(obj)).hexdigest()

def load(path, exact=False):
    def pairs(items):
        out = {}
        for key, value in items:
            assert key not in out
            out[key] = value
        return out
    raw = path.read_bytes()
    obj = json.loads(raw, object_pairs_hook=pairs)
    if exact: assert raw == canonical(obj), path
    return obj

assert sha(PRELAUNCH / 'manifest.json') == 'e3cdb34f400ea9d67574d91e32f5249cdfc4f40039f6ec2a8d5f1e0016283709'
old = load(PRELAUNCH / 'manifest.json')
for name, info in old['files'].items():
    assert (PRELAUNCH / name).stat().st_size == info['bytes'] and sha(PRELAUNCH / name) == info['sha256']
assert sha(ADAPTER / 'SOURCE_PINS.json') == 'be861661892f52e52068d88361fc1519989ae6103a4945a3c6c7e41a8ffc5fac'
pins = load(ADAPTER / 'SOURCE_PINS.json')
for name, expected in pins['source_sha256'].items(): assert sha(ADAPTER / name) == expected
for name, item in pins['copied_predecessors'].items(): assert sha(ADAPTER / name) == sha(Path(item['original'])) == item['sha256']
for name, expected in pins['reviewed_mathematics'].items(): assert sha(Path(name)) == expected
assert sha(Path(pins['native_dependency']['path'])) == pins['native_dependency']['sha256']
assert (ADAPTER / 'PRELAUNCH_REVIEW.json').read_bytes() == (PRELAUNCH / 'PRELAUNCH_REVIEW.json').read_bytes()
gate = load(ADAPTER / 'PRELAUNCH_REVIEW.json')
assert sha(Path(gate['review_report_path'])) == gate['review_report_sha256']
assert gate['disposition'] == 'accepted' and gate['root_notified'] is True
assert sha(PUBLIC / 'PUBLIC_COMPLETE.json') == '6aa0789f106ca326dccb370483f0cec589fe218ed9ff4a5d732ef48f07e2a993'
seal = load(PUBLIC / 'PUBLIC_COMPLETE.json', True)
assert seal['all_public_children_exited'] and seal['private_decryptions_so_far'] == 0
assert seal['source_manifest_sha256'] == sha(ADAPTER / 'SOURCE_PINS.json')
for name, info in seal['files'].items():
    path = PUBLIC / name
    assert path.resolve().is_relative_to(PUBLIC.resolve())
    assert not path.is_symlink() and '.private' not in path.parts
    assert path.stat().st_size == info['bytes'] and sha(path) == info['sha256']
actual = {str(p.relative_to(PUBLIC)) for p in PUBLIC.rglob('*') if p.is_file()}
assert actual == set(seal['files']) | {'PUBLIC_COMPLETE.json'}
assert len(actual) == 139
execution = load(PUBLIC / 'execution_pins.json', True)
assert execution['source_manifest'] == pins and execution['source_manifest_sha256'] == seal['source_manifest_sha256']
assert execution['prelaunch_review'] == gate

ctx = load(PUBLIC / 'context.json', True)
tr = load(PUBLIC / 'transcript.json', True)
registry = load(PUBLIC / 'registry.json', True)
assert sha(PUBLIC / 'transcript.json') == '04586e22ea7f18fd2282745bf2e40fbfe8d8c739e835995bad54c5974aee0e56'
identity = sha(PUBLIC / 'context.json')
assert identity == 'be14f3e3f83759c33238bf62c7511a6d8df897d2646a877b4acf8ef5b33fbbb5'
assert tr['context_id'] == seal['context_id'] == identity
assert tr['status'] == 'accepted' and tr['registry_sha256'] == sha(PUBLIC / 'registry.json')
assert ctx['params_id'] == registry['params_id'] == tr['params_id']
rows = load(ADAPTER / 'source/public_setup/source/crypto/rows.json')
domain = tr['complete_domain']
assert domain['rows'] == ctx['rows'] == rows
assert domain['dimension'] == 577 and domain['row_count'] == 16 and domain['capacity'] == 32
assert domain['pivot_columns'] == list(range(16)) and tr['integer_pivot_determinant'] == -812032080
assert domain['suite'] == 'SHAKE256-direct-bitwords-cap128-v1' and domain['rejection_cap'] == 128
assert tr['domain_sha256_for_inventory_only'] == digest(domain)
assert ctx['setup_id'] == digest({'schema': 'resident-designated-bootstrap-v1', 'params_id': ctx['params_id'], 'rows': rows, 'h': ctx['h']})
source = tr['source_identity']
assert source['manifest_sha256'] == seal['source_manifest_sha256']
assert source['crypto_sources'] == pins['frozen_crypto'] and source['native_dependency'] == pins['native_dependency']
for field, file in [('seed_setup_sha256','seed_setup.py'), ('derive_sha256','derive.py'), ('frozen_direct_setup_sha256','source/public_setup/setup.py')]:
    assert source[field] == pins['source_sha256'][file]
assert len(registry['slots']) == len(domain['complete_registry']) == len(tr['announcements']) == len(ctx['recipients']) == 16
for i in range(16):
    announcement = load(PUBLIC / 'announcements' / f'r{i:02d}.json', True)
    assert announcement == tr['announcements'][i]
    slot, record = registry['slots'][i], ctx['recipients'][i]
    payload = announcement['payload']
    assert slot['row_id'] == payload['row_id'] == record['row_id'] == i
    assert slot['row_sha256'] == payload['row_sha256'] == record['row_sha256'] == digest(rows[i])
    assert domain['complete_registry'][i] == dict(slot, A=payload['A'])
    assert record['A'] == payload['A'] and record['tau'] == tr['derivation']['tau'][i]
    expected_id = digest({'domain':'dedicated-designated-recipient-v1','setup_id':ctx['setup_id'], 'row_id':i,'row_sha256':digest(rows[i]),'A':record['A']})
    assert record['recipient_id'] == expected_id
    assert record['token_sha256'] == digest({k:v for k,v in record.items() if k!='token_sha256'})

# Validate already retained prefix bookkeeping/ranges; do not invoke SHAKE again.
derived = tr['derivation']
assert derived['suite'] == domain['suite'] and bytes.fromhex(derived['seed_hex']) == b'resident-designated-public-seed-positive-001'
assert len(derived['tau']) == 16 and len(derived['U']) == 561 and len(derived['tapes']) == 577
p, q = int(domain['p_hex'],16), int(domain['q_hex'],16)
assert p == 2*q+1 and p.bit_length() == 2048 and q.bit_length() == 2047
histogram = Counter()
for ordinal, tape in enumerate(derived['tapes']):
    role, index, bits, low, upper = ('tau',ordinal,2047,0,q) if ordinal<16 else ('U',ordinal-16,2048,1,p)
    assert (tape['role'],tape['coordinate'],tape['word_bits'],tape['raw_bytes_per_word'],tape['discarded_low_bits']) == (role,index,bits,256,2048-bits)
    counter = tape['accepted_counter']
    assert type(counter) is int and 1 <= counter <= 128 and len(tape['raw_words_hex']) == counter
    values=[]
    for raw in tape['raw_words_hex']:
        assert len(raw) == 512 and bytes.fromhex(raw).hex() == raw
        values.append(int(raw,16) >> (2048-bits))
    assert all(not low <= v < upper for v in values[:-1]) and low <= values[-1] < upper
    assert len(derived[role][index]) == 512 and int(derived[role][index],16) == values[-1]
    histogram[counter] += 1
assert dict(histogram) == {1:577}

commands = [json.loads(line) for line in (PUBLIC/'commands.jsonl').read_text().splitlines()]
assert [r['ordinal'] for r in commands] == list(range(112))
assert all(r['exit_code']==0 and 0 < r['elapsed_ns'] < 300_000_000_000 for r in commands)
assert all(r['command'] != 'reader-decrypt' and 'signed_score' not in r['result'] for r in commands)
def flags(row):
    argv=row['argv']; start=4 if row['command'] is not None else 3
    tail=argv[start:]; assert len(tail)%2==0
    return dict(zip(tail[::2],tail[1::2],strict=True))
sequence=['auth-init']+['recipient-init']*16+['public-build','verify-public','validate-context']+['recipient-finalize']*16
selected={1:0,16:1,32:2,33:3}
for t in range(1,34):
    sequence += ['issuer-encrypt','host-learn']
    if t in selected: sequence += ['encode-query','host-infer']
sequence += [None,'verify-public']
assert [row['command'] for row in commands] == sequence
assert Counter(r['command'] for r in commands) == Counter(sequence)
for row in commands:
    f=flags(row)
    assert row['argv'][:3] == [commands[0]['argv'][0],'-B',str(ADAPTER/row['program'])]
    if '--context' in f: assert f['--context'] == str(PUBLIC/'context.json')
    if '--registry' in f: assert f['--registry'] == str(PUBLIC/'registry.json') and f['--registry-sha256'] == tr['registry_sha256']
    if '--validated-context-sha256' in f: assert f['--validated-context-sha256'] == identity
    for key in ['context_id','key_id']:
        if key in row['result']: assert row['result'][key] == identity
    if row['command']=='recipient-init':
        i=int(f['--row']); assert row['ordinal']==i+1
        assert row['result']['public_announcement_sha256'] == sha(PUBLIC/'announcements'/f'r{i:02d}.json')

HEADER=struct.Struct('>8sB32s32sH32s32s32sQ')
envelopes=0
def envelope(path,kind,recipient=65535):
    global envelopes
    raw=path.read_bytes(); fields=HEADER.unpack(raw[:HEADER.size])
    count=578 if kind==1 else 2
    assert fields[:5] == (b'RSDDH001',kind,bytes.fromhex(ctx['params_id']),bytes.fromhex(identity),recipient)
    ids=(bytes(32),)*3 if kind==1 else tuple(bytes.fromhex(ctx['recipients'][recipient][key]) for key in ['row_sha256','recipient_id','token_sha256'])
    assert fields[5:8]==ids and fields[8]==256*count and len(raw)==HEADER.size+256*count
    # Range only; no subgroup exponentiation or modular arithmetic replay.
    assert all(1 <= int.from_bytes(raw[i:i+256],'big') < p for i in range(HEADER.size,len(raw),256))
    envelopes+=1
    return raw
zero=envelope(PUBLIC/'zero.ct',1)
assert zero[HEADER.size:]==(1).to_bytes(256,'big')*578
learns=[r for r in commands if r['command']=='host-learn']
issuers=[r for r in commands if r['command']=='issuer-encrypt']
for t,(learn,issuer) in enumerate(zip(learns,issuers,strict=True),1):
    f,issue=flags(learn),flags(issuer)
    acc=PUBLIC/('zero.ct' if t==1 else f'states/a{t-1:02d}.ct')
    fresh=PUBLIC/f'ciphertexts/c{t:02d}.ct'; output=PUBLIC/f'states/a{t:02d}.ct'
    assert f['--acc']==str(acc) and f['--fresh']==str(fresh) and f['--out']==str(output)
    assert f.get('--old')==(str(PUBLIC/'ciphertexts/c01.ct') if t==33 else None)
    assert learn['result']['expired_exact_supplied_original'] is (t==33)
    assert issue['--vector']==str(PUBLIC/f'inputs/x{t:02d}.json') and issue['--out']==str(fresh)
    assert load(PUBLIC/f'inputs/x{t:02d}.json',True)==[((t+3)*(j+5)%17)-8 for j in range(577)]
    for path,record in [(fresh,issuer),(output,learn)]:
        raw=envelope(path,1)
        assert record['result']['sha256']==hashlib.sha256(raw).hexdigest() and record['result']['bytes']==len(raw)
infers=[r for r in commands if r['command']=='host-infer']
for (t,i),row in zip(selected.items(),infers,strict=True):
    f=flags(row); output=PUBLIC/f'outputs/o{i:02d}.ct'
    assert f['--acc']==str(PUBLIC/f'states/a{t:02d}.ct') and f['--query']==str(PUBLIC/f'queries/q{i:02d}.json') and f['--out']==str(output)
    query=load(PUBLIC/f'queries/q{i:02d}.json',True)
    expected={'schema':'resident-designated-query-v1','params_id':ctx['params_id'],'context_id':identity,
              **{k:ctx['recipients'][i][k] for k in ['row_id','row_sha256','recipient_id','token_sha256']},'coefficients':rows[i]}
    assert query==expected and load(PUBLIC/f'queries/y{i:02d}.json',True)==rows[i]
    raw=envelope(output,2,i)
    assert row['result']['sha256']==hashlib.sha256(raw).hexdigest() and row['result']['bytes']==len(raw)
assert envelopes==71
assert load(PUBLIC/'drain_tickets.json',True)==[{'learns':t,'row':i,'output':f'outputs/o{i:02d}.ct'} for t,i in selected.items()]

replay=load(PUBLIC/'public_replay.json',True)
assert replay==commands[-2]['result'] and replay['ok'] and replay['context_id']==identity
assert replay['counts']=={'expiries':1,'original_ciphertexts':33,'states':33,'outputs':4}
assert load(PUBLIC/'final_setup_replay.json',True)==commands[-1]['result']
for row in commands:
    if row['command']=='verify-public':
        assert row['result']['ok'] and row['result']['complete_raw_hash_tape_match'] and row['result']['complete_context_byte_match']
        assert row['result']['transcript_sha256']==sha(PUBLIC/'transcript.json')
validation=load(PUBLIC/'context_validation.json',True)
assert validation==commands[19]['result'] and validation['validated'] and validation['source_sha256']==pins['frozen_crypto']
public_report=load(PUBLIC/'public_report.json',True)
aggregate=load(RUN/'RESEARCH_RESULT.json',True)
for obj in [public_report,aggregate]:
    assert obj['ok'] and obj['learns']==33 and obj['infers']==4 and obj['exact_expiries']==1 and obj['context_id']==identity
assert public_report['private_decode_calls_so_far']==0 and public_report['all_public_processes_exited']
assert public_report['public_seed_candidates']==1 and public_report['public_process_calls']==112
assert aggregate['all_four_integer_comparisons_match'] and aggregate['private_decode_processes']==4 and aggregate['public_evidence_closed_before_first_private_decode']
stdout=[json.loads(line) for line in (ADAPTER/'reports/normal_001.stdout.log').read_text().splitlines()]
assert stdout[-1]['ok'] and stdout[-1]['all_match'] and stdout[-2]['stage']=='public_evidence_closed_before_private_drain'
closure_ns=stdout[-2]['elapsed_ns']
assert [r['elapsed_ns'] for r in stdout[:-1]]==sorted(r['elapsed_ns'] for r in stdout[:-1])
assert aggregate['setup_ns']==public_report['setup_ns']==101459136291
assert aggregate['public_phase_ns']==public_report['public_phase_ns']==stdout[-2]['public_phase_ns']==340932174458
assert aggregate['public_phase_ns'] < closure_ns==341002693166 < aggregate['total_ns']==342179553250 < 1200_000_000_000
assert stdout[-1]['total_seconds']==aggregate['total_ns']/1e9 and stdout[-1]['public_phase_seconds']==aggregate['public_phase_ns']/1e9
assert (ADAPTER/'reports/normal_001.stderr.log').stat().st_size==0
assert not (RUN/'STOPPED.json').exists()
assert sorted(path.name for path in (ADAPTER/'reports').iterdir() if path.is_dir())==['normal_001']
costs=defaultdict(list)
for r in commands:costs[r['command'] or 'public-reference'].append(r['elapsed_ns'])
cost_summary={name:{'calls':len(times),'sum_seconds':sum(times)/1e9,'median_seconds':statistics.median(times)/1e9,'max_seconds':max(times)/1e9} for name,times in sorted(costs.items())}
assert sum(r['elapsed_ns'] for r in commands)<aggregate['public_phase_ns']
report={'ok':True,'scope':'Public hashes, framing/ranges and retained source/log/replay evidence only; no signature/group/XOF recomputation, private reads or sampling.',
        'prelaunch_files_unchanged':len(old['files']),'public_files':len(actual),'public_bytes':sum((PUBLIC/n).stat().st_size for n in actual),
        'public_envelopes_checked':envelopes,'public_command_count':len(commands),'command_costs':cost_summary,
        'source_pins_sha256':seal['source_manifest_sha256'],'public_closure_sha256':sha(PUBLIC/'PUBLIC_COMPLETE.json'),
        'context_sha256':identity,'transcript_sha256':sha(PUBLIC/'transcript.json'),'aggregate_sha256':sha(RUN/'RESEARCH_RESULT.json'),
        'accepted_counter_histogram':dict(histogram),'full_registered_recipients':16,
        'replay_results_attributed_to_frozen_public_processes':replay['counts'],'exact_original_expiry_step':33,
        'setup_seconds':aggregate['setup_ns']/1e9,'public_work_timer_seconds':aggregate['public_phase_ns']/1e9,
        'public_closure_checkpoint_seconds':closure_ns/1e9,'total_seconds':aggregate['total_ns']/1e9,
        'closure_overhead_seconds':(closure_ns-aggregate['public_phase_ns'])/1e9,
        'after_closure_to_total_seconds':(aggregate['total_ns']-closure_ns)/1e9,
        'private_comparison_attribution':'four matches and four decode processes reported by aggregate; no private results or timestamps read',
        'ordering_basis':'unchanged reviewed synchronous source, 112 public commands, sealed public transcript, closure stdout before final aggregate; no independent private timestamp observation',
        'normal_failure_or_retry_records_in_public_scope':0,'crypto_or_XOF_invocations':0,'private_file_reads':0}
(HERE/'public_results.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2,sort_keys=True))
