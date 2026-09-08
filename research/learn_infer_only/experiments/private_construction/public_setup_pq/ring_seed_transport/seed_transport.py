#!/usr/bin/env python3
"""Conditional public-SHAKE instantiation; not ideal-uniform compression."""
import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path
import resource
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'ring_transport'
sys.path.insert(0,str(BASE))
import transport as t
from expansion import PublicExpander
from ring import uniform_below

MAGIC=b'RINGREG1'


def hash_bytes(data):return hashlib.sha256(data).hexdigest()


def hex32(value):
    if not isinstance(value,str) or len(value)!=64 or any(c not in '0123456789abcdef' for c in value):
        raise ValueError('noncanonical256-bit digest or seed')
    return bytes.fromhex(value)


def write_public(path,producer,kind):
    path=Path(path).resolve(); fd,tmp=tempfile.mkstemp(prefix='.seed-tmp-',dir=path.parent)
    try:
        os.fchmod(fd,0o644)
        with os.fdopen(fd,'wb') as f:
            producer(f);f.flush();os.fsync(f.fileno())
        os.link(tmp,path)
    finally:Path(tmp).unlink(missing_ok=True)
    row={'path':str(path),'kind':kind,'bytes':path.stat().st_size,'private':False,'mode':'0o644','sha256':t.digest(path)}
    t.WRITES.append(row);return row


def write_json(path,obj,kind):return write_public(path,lambda f:f.write(t.canonical(obj)),kind)


def read_json(path,kind):
    path=Path(path).resolve()
    if path.stat().st_size>16384:raise ValueError('descriptor too large')
    data=path.read_bytes();obj=json.loads(data)
    if t.canonical(obj)!=data:raise ValueError('noncanonical descriptor JSON')
    t.READS.append({'path':str(path),'kind':kind,'private':False})
    return obj


def validate_a(a):
    if not isinstance(a,dict) or set(a)!={'format','profile','parameters','setup_id','policy','recipients','seed'}:
        raise ValueError('invalid seeded-A fields')
    if a['format']!='ring-seeded-a-v1' or a['policy']!='sparse-basis-v1':raise ValueError('unsupported seeded-A format')
    p=t.params(a['profile'])
    if t.canonical(a['parameters'])!=t.canonical(p.__dict__) or a['recipients']!=list(range(p.recipients)):
        raise ValueError('parameter/recipient policy mismatch')
    hex32(a['setup_id']);hex32(a['seed'])
    return p


def a_expander(a):
    p=validate_a(a)
    context={k:v for k,v in a.items() if k!='seed'}
    binding=hashlib.sha256(b'ring-A-context-v1\x00'+t.canonical(context)).digest()
    return p,PublicExpander(hex32(a['seed']),binding)


def expanded_a(a):
    p,e=a_expander(a);ring=t.Ring(p.N,p.q)
    return p,ring,[ring.poly(e.row('A',j,p.N,p.q)) for j in range(p.w)]


def registry_header(a):
    p=validate_a(a)
    return {'format':'ring-seeded-registry-v1','a_sha256':hash_bytes(t.canonical(a)),
            'profile':a['profile'],'setup_id':a['setup_id'],'rows':p.recipients,'N':p.N,'q':p.q}


def write_registry(path,a,rows):
    p=validate_a(a);h=t.canonical(registry_header(a))
    def producer(f):
        f.write(MAGIC+len(h).to_bytes(4,'big')+h)
        t.pack_values(itertools.chain.from_iterable(rows),p.q.bit_length(),p.recipients*p.N,f,upper_bound=p.q)
    return write_public(path,producer,'explicit_registry')


def read_registry(path,a,expected_hash):
    p=validate_a(a);path=Path(path).resolve()
    if t.digest(path)!=expected_hash:raise ValueError('registry digest mismatch')
    with path.open('rb') as f:
        if f.read(8)!=MAGIC:raise ValueError('invalid registry magic')
        length=int.from_bytes(f.read(4),'big')
        expected=t.canonical(registry_header(a))
        if length!=len(expected) or f.read(length)!=expected:raise ValueError('registry header mismatch')
        if path.stat().st_size!=12+length+t.payload_bytes(p.q.bit_length(),p.recipients*p.N):raise ValueError('registry length mismatch')
        values=t.unpack_values(f,p.q.bit_length(),p.recipients*p.N,p.q,require_eof=True)
        rows=[list(itertools.islice(values,p.N)) for _ in range(p.recipients)]
        if next(values,None) is not None or any(len(row)!=p.N for row in rows):raise ValueError('registry payload mismatch')
    t.READS.append({'path':str(path),'kind':'explicit_registry','private':False})
    return rows


def validate_public(public):
    if not isinstance(public,dict) or set(public)!={'format','a','a_sha256','registry_sha256','missing_seed','missing_binding'}:
        raise ValueError('invalid seeded-public fields')
    if public['format']!='ring-seeded-public-v1':raise ValueError('unsupported seeded-public format')
    p=validate_a(public['a'])
    if public['a_sha256']!=hash_bytes(t.canonical(public['a'])):raise ValueError('seeded-A digest mismatch')
    hex32(public['registry_sha256']);hex32(public['missing_seed'])
    binding=hashlib.sha256(b'ring-missing-context-v1\x00'+hex32(public['a_sha256'])+hex32(public['registry_sha256'])).hexdigest()
    if public['missing_binding']!=binding:raise ValueError('registry/domain binding mismatch')
    return p


def init(a):
    p=t.params(a.profile)
    descriptor={'format':'ring-seeded-a-v1','profile':a.profile,'parameters':p.__dict__,
                'setup_id':os.urandom(32).hex(),'policy':'sparse-basis-v1',
                'recipients':list(range(p.recipients)),'seed':os.urandom(32).hex()}
    write_json(a.out,descriptor,'seeded_a')
    return {'actual_private_rows_generated':0,'A_rows_stored':0,'public_A_seed_bytes':32}


def register(a):
    descriptor=read_json(a.public_a,'seeded_a');p,ring,A=expanded_a(descriptor)
    key,product=t.generate_recipient_key(p,A,a.coordinate,t.GaussianSampler())
    ah=hash_bytes(t.canonical(descriptor))
    kh=t.basic_header(descriptor['profile'],'key',descriptor['setup_id'],coordinate=a.coordinate,a_sha256=ah)
    mask=(1<<(8*p.sigma_key).bit_length())-1
    t.write_container(a.key_out,kh,(value&mask for row in key.row for value in row),private=True)
    rh=t.basic_header(descriptor['profile'],'registration',descriptor['setup_id'],coordinate=a.coordinate,a_sha256=ah)
    t.write_container(a.registration_out,rh,product)
    return {'actual_private_rows_generated':1,'recipient_coordinate':a.coordinate,'private_coefficients_generated':p.w*p.N,
            'A_rows_reconstructed':p.w,'A_rows_stored':0}


def finalize(a):
    descriptor=read_json(a.public_a,'seeded_a');p=validate_a(descriptor)
    ah=hash_bytes(t.canonical(descriptor));rows=[None]*p.recipients
    for path in a.registration:
        c=t.Container(path,'registration');h=c.header;i=h['coordinate']
        if h['a_sha256']!=ah or h['profile']!=descriptor['profile'] or h['setup_id']!=descriptor['setup_id'] or rows[i] is not None:
            raise ValueError('wrong/duplicate registration context')
        rows[i]=c.take(p.N);c.finish()
    if any(row is None for row in rows):raise ValueError('incomplete recipient registry')
    reg=write_registry(a.registry_out,descriptor,rows)
    binding=hashlib.sha256(b'ring-missing-context-v1\x00'+bytes.fromhex(ah)+bytes.fromhex(reg['sha256'])).hexdigest()
    # This separate seed is sampled after the exact registered products are fixed.
    public={'format':'ring-seeded-public-v1','a':descriptor,'a_sha256':ah,'registry_sha256':reg['sha256'],
            'missing_seed':os.urandom(32).hex(),'missing_binding':binding}
    validate_public(public);write_json(a.out,public,'seeded_public')
    return {'actual_private_rows_generated':0,'registrations':p.recipients,'absent_private_rows_generated':0,
            'missing_rows_stored':0,'missing_rows_described':p.d-p.recipients,'public_missing_seed_bytes':32}


def encode(a):
    public=read_json(a.public,'seeded_public');p=validate_public(public)
    rows=read_registry(a.registry,public['a'],public['registry_sha256'])
    _,ring,A=expanded_a(public['a'])
    basis=t.SparseBasis(p.d,p.recipients,p.p)
    path=Path(a.input).resolve();x=json.loads(path.read_text())
    t.READS.append({'path':str(path),'kind':'input','private':False})
    if not isinstance(x,list) or len(x)!=p.d or any(type(v) is not int or not 0<=v<p.p for v in x):raise ValueError('invalid plaintext vector')
    transformed=basis.transform(x)
    s=uniform_below(p.q,p.N)
    sp=ring.poly(s);sampler=t.GaussianSampler()
    c0=[ring.mul(row,sp)+ring.poly(sampler.sample(p.sigma_error,p.N)) for row in A]
    floods=uniform_below(2*p.flood+1,p.d)
    expander=PublicExpander(hex32(public['missing_seed']),hex32(public['missing_binding']))
    hs=[]
    for i in range(p.d):
        row=rows[i] if i<p.recipients else expander.row('missing-P',i,p.N,p.q)
        hs.append((ring.const_product(row,s)+floods[i]-p.flood+p.delta*transformed[i])%p.q)
        del row
    ct=t.Ciphertext(c0,hs,1)
    h=t.basic_header(public['a']['profile'],'ciphertext',public['a']['setup_id'],a_sha256=public['a_sha256'],
                     public_sha256=t.digest(a.public),weight=1,terms=None)
    t.emit_cipher(a.out,h,p,ct)
    return {'encoded_coordinates':p.d,'private_rows_read':0,'A_rows_reconstructed':p.w,
            'absent_rows_reconstructed':p.d-p.recipients,'peak_explicit_absent_rows':1,
            'seeded_public_plus_registry_bytes':Path(a.public).stat().st_size+Path(a.registry).stat().st_size}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',required=True)
    sub=ap.add_subparsers(dest='command',required=True)
    p=sub.add_parser('init');p.add_argument('--profile',choices=['toy','candidate_n_probe','candidate_full'],required=True);p.add_argument('--out',required=True)
    p=sub.add_parser('register');p.add_argument('--public-a',required=True);p.add_argument('--coordinate',type=int,required=True);p.add_argument('--key-out',required=True);p.add_argument('--registration-out',required=True)
    p=sub.add_parser('finalize');p.add_argument('--public-a',required=True);p.add_argument('--registration',action='append',required=True);p.add_argument('--registry-out',required=True);p.add_argument('--out',required=True)
    p=sub.add_parser('encode');p.add_argument('--public',required=True);p.add_argument('--registry',required=True);p.add_argument('--input',required=True);p.add_argument('--out',required=True)
    a=ap.parse_args();start=time.perf_counter();status='PASS';error=None;result={}
    try:result=globals()[a.command](a)
    except Exception as exc:status='FAIL';error=f'{type(exc).__name__}: {exc}'
    receipt={'status':status,'role_command':a.command,'pid':os.getpid(),'uid':os.getuid(),
             'elapsed_seconds':time.perf_counter()-start,'peak_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
             'artifact_reads':t.READS,'artifact_writes':t.WRITES,'result':result,'error':error}
    Path(a.receipt).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':status,'role_command':a.command,'elapsed_seconds':receipt['elapsed_seconds'],'error':error}),flush=True)
    return 0 if status=='PASS' else 1


if __name__=='__main__':raise SystemExit(main())
