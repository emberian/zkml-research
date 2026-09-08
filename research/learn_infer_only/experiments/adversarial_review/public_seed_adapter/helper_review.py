"""Pure public framing/sampler review. No backend, native library, key, or production setup."""
import collections
import hashlib
import importlib.util
import json
from pathlib import Path
import struct
import sys
from types import SimpleNamespace

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
ADAPTER=ROOT.parents[1]/'private_construction/designated_span/public_coin_setup/public_seed/adapter'
EXPECTED='be861661892f52e52068d88361fc1519989ae6103a4945a3c6c7e41a8ffc5fac'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(ADAPTER/'SOURCE_PINS.json')==EXPECTED
pins=json.loads((ADAPTER/'SOURCE_PINS.json').read_text())
assert sha(ADAPTER/'derive.py')==pins['source_sha256']['derive.py']
spec=importlib.util.spec_from_file_location('reviewed_public_derive',ADAPTER/'derive.py')
d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
assert d.CAP==128 and d.SEED==b'resident-designated-public-seed-positive-001'

def encode(parts):
    return b'resident-designated-public-seed-query-v1\x00'+struct.pack('>I',len(parts))+b''.join(struct.pack('>Q',len(x))+x for x in parts)

def decode(raw):
    prefix=b'resident-designated-public-seed-query-v1\x00';assert raw.startswith(prefix)
    offset=len(prefix);count=struct.unpack_from('>I',raw,offset)[0];offset+=4;parts=[]
    for _ in range(count):
        size=struct.unpack_from('>Q',raw,offset)[0];offset+=8
        parts.append(raw[offset:offset+size]);offset+=size
    assert offset==len(raw)
    return parts

frames=[[],[b''],[b'',b''],[b'ab',b'c'],[b'a',b'bc'],[b'\x00',b'a\x00b'],[b'abc']]
assert len({d.frame(x) for x in frames})==len(frames)
for parts in frames:assert d.frame(parts)==encode(parts) and decode(d.frame(parts))==parts
assert d.canonical({'z':1,'a':'é'})==b'{"a":"\\u00e9","z":1}'
assert d.canonical({'z':1,'a':'é'})==d.canonical({'a':'é','z':1})
query_cases=[]
for role in ['tau','U']:
    for coordinate in [0,1,560]:
        for counter in [1,2,128]:
            expected=[b'complete-domain-bytes',d.SEED,role.encode(),struct.pack('>I',coordinate),struct.pack('>I',counter)]
            raw=d.query_bytes(expected[0],d.SEED,role,coordinate,counter)
            assert raw==encode(expected) and decode(raw)==expected;query_cases.append(raw)
assert len(set(query_cases))==18
histograms={}
for bits in [2,3]:
    values=[d.candidate(bytes([x]),bits) for x in range(256)]
    histogram=collections.Counter(values)
    assert histogram=={v:2**(8-bits) for v in range(2**bits)}
    histograms[str(bits)]=dict(histogram)
wide=bytes(range(256))
assert d.candidate(wide,2047)==int.from_bytes(wide,'big')//2
assert d.candidate(wide,2048)==int.from_bytes(wide,'big')

# One fixed positive public toy descriptor; this is not a production registry.
domain={'schema':'designated-complete-seed-domain-v1','suite':d.SUITE,'p_hex':'07','q_hex':'03',
        'generator':2,'dimension':2,'row_count':1,'rows':[[1,1]],'pivot_columns':[0],
        'rejection_cap':128,'complete_registry':[{'row_id':0,'A':'02','identity':'public-toy-only'}]}
canonical=json.dumps(domain,ensure_ascii=True,allow_nan=False,sort_keys=True,separators=(',',':')).encode('ascii')
actual=d.derive(domain)
reference=[]
for role,bits,lower,upper in [('tau',2,0,3),('U',3,1,7)]:
    words=[]
    for counter in range(1,129):
        raw=hashlib.shake_256(encode([canonical,d.SEED,role.encode(),struct.pack('>I',0),struct.pack('>I',counter)])).digest(1)
        words.append(raw.hex());value=int.from_bytes(raw,'big')//(2**(8-bits))
        if lower<=value<upper:break
    reference.append({'role':role,'accepted_counter':counter,'value':value,'raw_words_hex':words})
for tape,ref in zip(actual['tapes'],reference,strict=True):
    assert tape['role']==ref['role'] and tape['accepted_counter']==ref['accepted_counter']
    assert tape['raw_words_hex']==ref['raw_words_hex']
    assert int(actual[ref['role']][0],16)==ref['value']

# Synthetic public byte sources test cap/range boundaries, not actual seed selection.
def synthetic(mode):
    calls=[]
    def shake(raw):
        parts=decode(raw);assert parts[0]==canonical and parts[1]==d.SEED
        role=parts[2].decode();coordinate=int.from_bytes(parts[3],'big');counter=int.from_bytes(parts[4],'big')
        assert coordinate==0;calls.append((role,counter))
        if mode=='reject_tau':byte=255
        elif role=='tau':byte=0
        elif mode=='reject_U':byte=0
        elif mode=='minus_one_U':byte=223  # high three bits6; low suffix all1
        else:byte={1:0,2:255}.get(counter,63)  # U0 rejects, U7 rejects, U1 accepts
        def digest(width):assert width==1;return bytes([byte])
        return SimpleNamespace(digest=digest)
    original=d.hashlib;d.hashlib=SimpleNamespace(shake_256=shake)
    try:
        try:return {'accepted':True,'result':d.derive(domain),'calls':calls}
        except d.SeedRejected as error:return {'accepted':False,'partial':error.partial,'calls':calls}
    finally:d.hashlib=original

first=synthetic('first_accept')
assert first['accepted'] and first['result']['tau']==['00'] and first['result']['U']==['01']
assert first['calls']==[('tau',1),('U',1),('U',2),('U',3)]
minus=synthetic('minus_one_U');assert minus['result']['U']==['06'] and 6*6%7==1
rejected_tau=synthetic('reject_tau');assert not rejected_tau['accepted']
assert rejected_tau['calls']==[('tau',i) for i in range(1,129)]
assert rejected_tau['partial']['tapes'][0]['accepted_counter'] is None
assert len(rejected_tau['partial']['tapes'][0]['raw_words_hex'])==128
rejected_U=synthetic('reject_U');assert not rejected_U['accepted']
assert rejected_U['calls']==[('tau',1)]+[('U',i) for i in range(1,129)]
assert rejected_U['partial']['tau']==['00'] and rejected_U['partial']['U']==[]
assert rejected_U['partial']['tapes'][1]['accepted_counter'] is None

group_spec=importlib.util.spec_from_file_location('public_group_constants_only',ADAPTER/'source/public_setup/source/crypto/group.py')
group=importlib.util.module_from_spec(group_spec);group_spec.loader.exec_module(group)
assert group.P==2*group.Q+1 and group.Q.bit_length()==2047 and group.P.bit_length()==2048
assert 2*group.Q>2**2047 and 2*(group.P-1)>2**2048
rows=json.loads((ADAPTER/'source/public_setup/source/crypto/rows.json').read_text())
assert len(rows)==16 and all(len(row)==577 for row in rows)
assert 577<2**10
assert sha(ADAPTER/'SOURCE_PINS.json')==EXPECTED
out={'ok':True,'source_pins_sha256':EXPECTED,'framing_roundtrips':len(frames),'domain_coordinate_counter_cases':18,
     'exhaustive_public_byte_inputs':512,'high_bit_histograms':histograms,'production_width_examples':2,
     'actual_SHAKE_public_toy_derivations':1,'public_toy_reference':reference,
     'synthetic_byte_source_cases':['zero_tau_and_first_valid_U','minus_one_U_allowed','tau_cap_exhaustion_128','U_cap_exhaustion_128'],
     'cap_counters_checked':128,'availability_scope':'Ideal independent bits only: one-candidate failure <577/2^128 <2^-118; not a concrete SHAKE guarantee.',
     'group_parameters_checked_as_constants_only':True,'backend_or_native_execution':0,'production_seed_derivations':0,
     'key_generation_or_issuance_or_decryption':0,'private_file_reads':0,'seed_searches':0,
     'scope':'Pure public byte framing, hash recipe comparison and synthetic sampler edge controls; no cryptographic workload.'}
(ROOT/'helper_results.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps(out,indent=2))
