#!/usr/bin/env python3
"""Role-separated file transport for the frozen fast ring prototype.

Private artifacts are explicitly requested by recipient commands only.
The runner applies additional OS sandbox restrictions to actual subprocesses.
"""
import argparse
from dataclasses import asdict
import hashlib
import itertools
import json
import os
import resource
from pathlib import Path
import stat
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
FAST=HERE.parent/'ring_implementation_fast'
sys.path.insert(0,str(FAST))
from ring import Parameters, Ring, PublicSetup, RecipientKey, RecipientBatch, Ciphertext, SparseBasis, generate_recipient_key
from run import params, fixture
from sampling.sampler import GaussianSampler
from codec import pack_values, unpack_values, payload_bytes

MAGIC=b'RINGTRN1'
READS=[]
WRITES=[]


def canonical(obj):
    return json.dumps(obj,sort_keys=True,separators=(',',':'),ensure_ascii=True,allow_nan=False).encode('ascii')


def digest(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for block in iter(lambda:f.read(1<<20),b''):h.update(block)
    return h.hexdigest()


def basic_header(profile,kind,setup_id=None,**extra):
    return {'format_version':1,'kind':kind,'profile':profile,'parameters':asdict(params(profile)),
            'setup_id':setup_id or os.urandom(32).hex(),**extra}


def shape(h):
    p=params(h['profile']); n=p.N*p.w
    if h['kind']=='a':return p.q.bit_length(),n,p.q
    if h['kind']=='registration':return p.q.bit_length(),p.N,p.q
    if h['kind']=='public':return p.q.bit_length(),(p.w+p.d)*p.N,p.q
    if h['kind']=='key':return (8*p.sigma_key).bit_length(),n,1<<(8*p.sigma_key).bit_length()
    if h['kind']=='ciphertext':return p.q.bit_length(),n+p.d,p.q
    raise ValueError('unknown container kind')


def validate_header(h):
    common={'format_version','kind','profile','parameters','setup_id'}
    extra={'a':set(),'registration':{'coordinate','a_sha256'},'public':{'a_sha256'},
           'key':{'coordinate','a_sha256'},'ciphertext':{'a_sha256','public_sha256','weight','terms'}}
    if not isinstance(h,dict) or h.get('kind') not in extra or set(h)!=common|extra[h['kind']]:
        raise ValueError('invalid header fields')
    if type(h['format_version']) is not int or h['format_version']!=1 or h['profile'] not in ('toy','candidate_n_probe','candidate_full'):
        raise ValueError('unsupported format/profile')
    p=params(h['profile'])
    if canonical(h['parameters'])!=canonical(asdict(p)):
        raise ValueError('parameters do not match the fixed profile')
    for name in ['setup_id','a_sha256','public_sha256']:
        if name in h and (not isinstance(h[name],str) or len(h[name])!=64 or any(c not in '0123456789abcdef' for c in h[name])):
            raise ValueError('noncanonical context digest')
    if 'coordinate' in h and (type(h['coordinate']) is not int or not 0<=h['coordinate']<p.recipients):
        raise ValueError('invalid recipient coordinate')
    if h['kind']=='ciphertext':
        if type(h['weight']) is not int or not 0<=h['weight']<=p.W:raise ValueError('invalid weight')
        if h['terms'] is None:
            if h['weight']!=1:raise ValueError('fresh ciphertext weight must be one')
        else:
            if not isinstance(h['terms'],list) or len(h['terms'])>p.W:raise ValueError('invalid lineage')
            last=''; total=0
            for item in h['terms']:
                if not isinstance(item,list) or len(item)!=2:raise ValueError('invalid lineage item')
                name,coefficient=item
                if not isinstance(name,str) or len(name)!=64 or any(c not in '0123456789abcdef' for c in name) or name<=last:
                    raise ValueError('noncanonical lineage digest/order')
                if type(coefficient) is not int or coefficient==0:raise ValueError('invalid lineage coefficient')
                total+=abs(coefficient); last=name
            if total!=h['weight']:raise ValueError('lineage/weight mismatch')
    return p


def write_container(path,h,values,private=False):
    path=Path(path).resolve(); validate_header(h)
    if private!=(h['kind']=='key'):raise ValueError('private flag/kind mismatch')
    header=canonical(h)
    if len(header)>16384:raise ValueError('header too long')
    width,count,bound=shape(h)
    fd,tmp=tempfile.mkstemp(prefix='.ring-tmp-',dir=path.parent)
    try:
        os.fchmod(fd,0o600 if private else 0o644)
        with os.fdopen(fd,'wb') as out:
            out.write(MAGIC+len(header).to_bytes(4,'big')+header)
            pack_values(values,width,count,out,upper_bound=bound)
            out.flush(); os.fsync(out.fileno())
        os.link(tmp,path)  # atomic, refuses to overwrite an existing artifact
    finally:
        Path(tmp).unlink(missing_ok=True)
    row={'path':str(path),'kind':h['kind'],'bytes':path.stat().st_size,
         'payload_bytes':payload_bytes(width,count),'private':private,'mode':oct(stat.S_IMODE(path.stat().st_mode))}
    if not private:row['sha256']=digest(path)
    WRITES.append(row)
    return row


class Container:
    def __init__(self,path,kind=None):
        self.path=Path(path).resolve(); self.stream=open(self.path,'rb')
        try:
            if self.stream.read(8)!=MAGIC:raise ValueError('invalid magic')
            raw=self.stream.read(4)
            if len(raw)!=4:raise ValueError('truncated length')
            length=int.from_bytes(raw,'big')
            if not 1<=length<=16384:raise ValueError('invalid header length')
            encoded=self.stream.read(length)
            if len(encoded)!=length:raise ValueError('truncated header')
            self.header=json.loads(encoded)
            if canonical(self.header)!=encoded:raise ValueError('noncanonical JSON header')
            self.p=validate_header(self.header)
            if kind and self.header['kind']!=kind:raise ValueError('wrong container kind')
            width,count,bound=shape(self.header)
            if self.path.stat().st_size!=12+length+payload_bytes(width,count):raise ValueError('wrong total length')
            self.values=unpack_values(self.stream,width,count,bound,require_eof=True)
            READS.append({'path':str(self.path),'kind':self.header['kind'],'private':self.header['kind']=='key'})
        except BaseException:
            self.stream.close(); raise

    def take(self,n):
        out=list(itertools.islice(self.values,n))
        if len(out)!=n:raise ValueError('truncated coefficient vector')
        return out

    def finish(self):
        try:
            if next(self.values,None) is not None:raise ValueError('unconsumed payload')
        finally:self.stream.close()


def polynomial_rows(container,ring,count):
    return [ring.poly(container.take(ring.N)) for _ in range(count)]


def load_a(path):
    c=Container(path,'a'); r=Ring(c.p.N,c.p.q)
    a=polynomial_rows(c,r,c.p.w); c.finish()
    return c.header,c.p,r,a


def load_public(path,sampler=None):
    c=Container(path,'public'); p=c.p; ring=Ring(p.N,p.q)
    setup=PublicSetup.__new__(PublicSetup)
    setup.params,setup.sampler,setup.ring=p,sampler,ring
    setup.basis=SparseBasis(p.d,p.recipients,p.p)
    setup.A=polynomial_rows(c,ring,p.w)
    setup.P=[c.take(p.N) for _ in range(p.d)]
    c.finish()
    return c.header,setup


def load_ciphertext(path):
    c=Container(path,'ciphertext'); ring=Ring(c.p.N,c.p.q)
    ct=Ciphertext(polynomial_rows(c,ring,c.p.w),c.take(c.p.d),c.header['weight'])
    c.finish()
    lineage={digest(path):1} if c.header['terms'] is None else dict(c.header['terms'])
    return c.header,c.p,ct,lineage


def context_equal(a,b):
    for name in ['profile','setup_id','parameters','a_sha256']:
        if a.get(name)!=b.get(name):raise ValueError('cross-context artifact')
    if a['kind']=='ciphertext' and b['kind']=='ciphertext' and a['public_sha256']!=b['public_sha256']:
        raise ValueError('cross-public-key ciphertexts')


def emit_cipher(path,header,p,ct):
    ring=Ring(p.N,p.q)
    return write_container(path,header,itertools.chain.from_iterable(
        itertools.chain((ring.coefficients(poly) for poly in ct.c0),[ct.h])))


def command_init(a):
    p=params(a.profile); public=PublicSetup(p,None)
    h=basic_header(a.profile,'a')
    write_container(a.out,h,itertools.chain.from_iterable(public.ring.coefficients(poly) for poly in public.A))
    return {'actual_private_rows_generated':0}


def command_register(a):
    h,p,ring,A=load_a(a.public_a)
    sampler=GaussianSampler()
    key,product=generate_recipient_key(p,A,a.coordinate,sampler)
    ah=digest(a.public_a)
    kh=basic_header(h['profile'],'key',h['setup_id'],coordinate=a.coordinate,a_sha256=ah)
    bits=(8*p.sigma_key).bit_length(); mask=(1<<bits)-1
    write_container(a.key_out,kh,(value&mask for row in key.row for value in row),private=True)
    rh=basic_header(h['profile'],'registration',h['setup_id'],coordinate=a.coordinate,a_sha256=ah)
    write_container(a.registration_out,rh,product)
    return {'actual_private_rows_generated':1,'recipient_coordinate':a.coordinate,'private_coefficients_generated':p.w*p.N}


def command_finalize(a):
    h,p,ring,A=load_a(a.public_a); ah=digest(a.public_a)
    setup=PublicSetup.__new__(PublicSetup)
    setup.params,setup.ring,setup.A,setup.P=p,ring,A,[None]*p.d
    setup.basis=SparseBasis(p.d,p.recipients,p.p); setup.sampler=None
    for path in a.registration:
        c=Container(path,'registration')
        if c.header['setup_id']!=h['setup_id'] or c.header['profile']!=h['profile'] or c.header['a_sha256']!=ah:
            raise ValueError('registration is for a different public A')
        setup.register_public(c.header['coordinate'],c.take(p.N)); c.finish()
    setup.finish()
    ph=basic_header(h['profile'],'public',h['setup_id'],a_sha256=ah)
    rows=itertools.chain((ring.coefficients(poly) for poly in A),setup.P)
    write_container(a.out,ph,itertools.chain.from_iterable(rows))
    return {'actual_private_rows_generated':0,'missing_public_rows_generated_directly':p.d-p.recipients,'registrations':p.recipients}


def command_encode(a):
    h,public=load_public(a.public,GaussianSampler())
    path=Path(a.input).resolve(); READS.append({'path':str(path),'kind':'input','private':False})
    x=json.loads(path.read_text())
    if not isinstance(x,list) or len(x)!=public.params.d or any(type(v) is not int or not 0<=v<public.params.p for v in x):
        raise ValueError('input must be a canonical F_p vector')
    ct=public.encode(x)
    ch=basic_header(h['profile'],'ciphertext',h['setup_id'],a_sha256=h['a_sha256'],public_sha256=digest(a.public),weight=1,terms=None)
    emit_cipher(a.out,ch,public.params,ct)
    return {'encoded_coordinates':public.params.d,'private_rows_read':0}


def evaluate(terms,out,window_capacity=None):
    head=None; result=None; lineage={}; inputs=[]
    for coefficient,path in terms:
        if type(coefficient) is not int:raise ValueError('integer coefficient required')
        h,p,ct,lin=load_ciphertext(path)
        if head is None:
            head=h; ring=Ring(p.N,p.q); result=Ciphertext([ring.ctx(0) for _ in range(p.w)],[0]*p.d,0)
        else:context_equal(head,h)
        inputs.append({'path':str(Path(path).resolve()),'coefficient':coefficient})
        for i,poly in enumerate(ct.c0):result.c0[i]+=coefficient*poly
        for i,value in enumerate(ct.h):result.h[i]=(result.h[i]+coefficient*value)%p.q
        for name,value in lin.items():lineage[name]=lineage.get(name,0)+coefficient*value
    if head is None:raise ValueError('at least one term required')
    lineage={name:value for name,value in lineage.items() if value}
    weight=sum(abs(value) for value in lineage.values())
    if weight>p.W:raise ValueError('canonical live coefficient norm exceeds W')
    if window_capacity is not None and (not 1<=window_capacity<=p.W or len(lineage)>window_capacity or any(v!=1 for v in lineage.values())):
        raise ValueError('invalid live window')
    result.weight=weight
    outhead={**head,'weight':weight,'terms':[[name,lineage[name]] for name in sorted(lineage)]}
    emit_cipher(out,outhead,p,result)
    return {'terms':inputs,'live_fresh_ciphertexts':len(lineage),'live_L1_weight':weight,'private_rows_read':0}


def command_combine(a):
    return evaluate([(int(c),path) for c,path in a.term],a.out)


def command_window(a):
    # Expiry is tied to the complete original file digest, not a claimed tag.
    ah,_,_,alin=load_ciphertext(a.add)
    if ah['terms'] is not None:raise ValueError('window add requires a fresh ciphertext')
    terms=[]
    if a.state:
        sh,_,_,slin=load_ciphertext(a.state); context_equal(sh,ah)
        if any(v!=1 for v in slin.values()):raise ValueError('state is not a positive window')
        if next(iter(alin)) in slin:raise ValueError('duplicate live fresh ciphertext')
        terms.append((1,a.state))
        if a.expire:
            eh,_,_,elin=load_ciphertext(a.expire); context_equal(sh,eh)
            if eh['terms'] is not None or slin.get(next(iter(elin)))!=1:
                raise ValueError('expiry does not name a live original ciphertext')
            terms.append((-1,a.expire))
    elif a.expire:raise ValueError('cannot expire without a state')
    terms.append((1,a.add))
    return evaluate(terms,a.out,a.capacity)


def command_decode(a):
    kc=Container(a.key,'key'); p=kc.p; kh=kc.header
    bits=(8*p.sigma_key).bit_length(); modulus=1<<bits; sign=1<<(bits-1)
    row=[]
    for _ in range(p.w):
        values=[x if x<sign else x-modulus for x in kc.take(p.N)]
        if any(abs(x)>=8*p.sigma_key for x in values):raise ValueError('noncanonical key coefficient')
        row.append(values)
    kc.finish(); key=RecipientKey(kh['coordinate'],row)
    h,_,ct,_=load_ciphertext(a.ciphertext); context_equal(kh,h)
    setup=PublicSetup.__new__(PublicSetup); setup.params=p; setup.ring=Ring(p.N,p.q)
    # The exact single-reader decoder is unchanged from the completed package.
    value=setup.decode(key,ct)
    expected=None
    if a.expected_lift is not None:
        expected=value==a.expected_lift
        if not expected:raise ValueError('designated output differs from expected synthetic lift')
    out=Path(a.out).resolve()
    fd=os.open(out,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
    with os.fdopen(fd,'w') as stream:json.dump({'coordinate':key.coordinate,'integer_lift':value,'residue':value%p.p},stream)
    WRITES.append({'path':str(out),'kind':'designated_output','private':True,'bytes':out.stat().st_size,'mode':oct(stat.S_IMODE(out.stat().st_mode))})
    return {'recipient_coordinate':key.coordinate,'private_rows_read':1,'expected_synthetic_lift_matched':expected}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--receipt',required=True)
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('init'); p.add_argument('--profile',choices=['toy','candidate_n_probe','candidate_full'],required=True); p.add_argument('--out',required=True)
    p=sub.add_parser('register'); p.add_argument('--public-a',required=True); p.add_argument('--coordinate',type=int,required=True); p.add_argument('--key-out',required=True); p.add_argument('--registration-out',required=True)
    p=sub.add_parser('finalize'); p.add_argument('--public-a',required=True); p.add_argument('--registration',action='append',required=True); p.add_argument('--out',required=True)
    p=sub.add_parser('encode'); p.add_argument('--public',required=True); p.add_argument('--input',required=True); p.add_argument('--out',required=True)
    p=sub.add_parser('combine'); p.add_argument('--term',nargs=2,action='append',required=True,metavar=('COEFFICIENT','CIPHERTEXT')); p.add_argument('--out',required=True)
    p=sub.add_parser('window'); p.add_argument('--state'); p.add_argument('--add',required=True); p.add_argument('--expire'); p.add_argument('--capacity',type=int,required=True); p.add_argument('--out',required=True)
    p=sub.add_parser('decode'); p.add_argument('--key',required=True); p.add_argument('--ciphertext',required=True); p.add_argument('--expected-lift',type=int); p.add_argument('--out',required=True)
    a=parser.parse_args(); start=time.perf_counter(); status='PASS'; error=None; result={}
    try:result=globals()['command_'+a.command](a)
    except Exception as exc:status='FAIL'; error=f'{type(exc).__name__}: {exc}'
    receipt={'status':status,'role_command':a.command,'pid':os.getpid(),'elapsed_seconds':time.perf_counter()-start,
             'peak_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'uid':os.getuid(),
             'artifact_reads':READS,'artifact_writes':WRITES,'result':result,'error':error}
    Path(a.receipt).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':status,'role_command':a.command,'elapsed_seconds':receipt['elapsed_seconds'],'error':error}),flush=True)
    return 0 if status=='PASS' else 1


if __name__=='__main__':raise SystemExit(main())
