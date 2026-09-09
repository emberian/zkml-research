#!/usr/bin/env python3
"""Role-separated file transport for the frozen fast ring prototype.

Private artifacts are explicitly requested by recipient commands only.
The runner applies additional OS sandbox restrictions to actual subprocesses.
"""
import argparse
from dataclasses import asdict
import hashlib
import itertools
import io
import json
import os
import resource
from pathlib import Path
import stat
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
FAST=HERE/'source/fast'
sys.path.insert(0,str(FAST))
from ring import Parameters, Ring, PublicSetup, RecipientKey, RecipientBatch, Ciphertext, SparseBasis, generate_recipient_key, uniform_below
from run import params, fixture
from sampling.sampler import GaussianSampler
from codec import pack_values, unpack_values, payload_bytes
from expansion import PublicExpander

from basis import load as load_basis
BASIS=None
BASIS_SHA256=None

def configure_basis(path):
    global BASIS,BASIS_SHA256
    BASIS,BASIS_SHA256=load_basis(path)
    READS.append({'path':str(Path(path).resolve()),'kind':'fixed_semantic_registry','private':False})

MAGIC=b'RINGSSM2'
FORMAT_VERSION=3
SEED_POLICY='honest-dual-seed-384-qrom-v1'
SEED_BITS=384
SEED_BYTES=48
COMMON={'format_version','registry_sha256','kind','profile','parameters','setup_id','seed_policy','seed_bits'}
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
    return {'format_version':FORMAT_VERSION,'registry_sha256':BASIS_SHA256,'kind':kind,'profile':profile,'parameters':asdict(params(profile)),
            'seed_policy':SEED_POLICY,'seed_bits':SEED_BITS,'setup_id':setup_id or os.urandom(32).hex(),**extra}


def a_binding(h):
    context={name:h[name] for name in COMMON}; context['kind']='a'
    return hashlib.sha256(b'ring-semantic-A-384-v1\x00'+canonical(context)).hexdigest()


def a_header(h):
    return {**{name:h[name] for name in COMMON},'kind':'a','a_seed':h['a_seed'],'a_binding':h['a_binding']}


def descriptor_digest(h):
    raw=canonical(a_header(h))
    return hashlib.sha256(MAGIC+len(raw).to_bytes(4,'big')+raw).hexdigest()


def missing_binding(h):
    return hashlib.sha256(b'ring-semantic-missing-384-v1\x00'+
        bytes.fromhex(h['a_sha256'])+bytes.fromhex(h['registry_sha256'])+
        bytes.fromhex(h['products_sha256'])).hexdigest()


def products_digest(h,rows):
    p=params(h['profile'])
    meta=canonical({'format':'ring-semantic-registered-products-v2','a_sha256':h['a_sha256'],
        'registry_sha256':h['registry_sha256'],'coordinates':list(range(p.recipients)),
        'N':p.N,'q':p.q,'seed_policy':SEED_POLICY,'seed_bits':SEED_BITS})
    out=io.BytesIO()
    pack_values(itertools.chain.from_iterable(rows),p.q.bit_length(),p.recipients*p.N,out,upper_bound=p.q)
    return hashlib.sha256(b'ring-semantic-products-v2\x00'+len(meta).to_bytes(4,'big')+meta+out.getvalue()).hexdigest()


def shape(h):
    p=params(h['profile']); n=p.N*p.w
    if h['kind']=='a':return 1,0,2
    if h['kind']=='registration':return p.q.bit_length(),p.N,p.q
    if h['kind']=='public':return p.q.bit_length(),p.recipients*p.N,p.q
    if h['kind']=='key':return (8*p.sigma_key).bit_length(),n,1<<(8*p.sigma_key).bit_length()
    if h['kind']=='ciphertext':return p.q.bit_length(),n+p.d,p.q
    raise ValueError('unknown container kind')


def validate_header(h):
    common=COMMON
    extra={'a':{'a_seed','a_binding'},'registration':{'coordinate','a_sha256'},
           'public':{'a_sha256','a_seed','a_binding','missing_seed','missing_binding','products_sha256'},
           'key':{'coordinate','a_sha256'},'ciphertext':{'a_sha256','public_sha256','weight','terms'}}
    if not isinstance(h,dict) or h.get('kind') not in extra or set(h)!=common|extra[h['kind']]:
        raise ValueError('invalid header fields')
    if type(h['format_version']) is not int or h['format_version']!=FORMAT_VERSION or h['profile']!='candidate_full':
        raise ValueError('unsupported format/profile')
    if h['seed_policy']!=SEED_POLICY or type(h['seed_bits']) is not int or h['seed_bits']!=SEED_BITS:
        raise ValueError('384-bit seed policy required; no downgrade')
    p=params(h['profile'])
    if BASIS is None or h['registry_sha256']!=BASIS_SHA256:raise ValueError('different fixed text-query registry/basis')
    if canonical(h['parameters'])!=canonical(asdict(p)):
        raise ValueError('parameters do not match the fixed profile')
    for name in ['setup_id','a_sha256','public_sha256','registry_sha256','a_binding','missing_binding','products_sha256']:
        if name in h and (not isinstance(h[name],str) or len(h[name])!=64 or any(c not in '0123456789abcdef' for c in h[name])):
            raise ValueError('noncanonical context digest')
    for name in ['a_seed','missing_seed']:
        if name in h and (not isinstance(h[name],str) or len(h[name])!=2*SEED_BYTES or any(c not in '0123456789abcdef' for c in h[name])):
            raise ValueError('exactly48-byte seed required')
    if h['kind'] in ('a','public') and h['a_binding']!=a_binding(h):
        raise ValueError('A seed policy/registry context mismatch')
    if h['kind']=='public':
        if h['a_sha256']!=descriptor_digest(h):raise ValueError('A descriptor digest mismatch')
        if h['missing_binding']!=missing_binding(h):raise ValueError('registered products/missing seed context mismatch')
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
    c.finish()
    expander=PublicExpander(bytes.fromhex(c.header['a_seed']),bytes.fromhex(c.header['a_binding']))
    a=[r.poly(expander.row('A',j,c.p.N,c.p.q)) for j in range(c.p.w)]
    return c.header,c.p,r,a


def load_public(path,sampler=None):
    c=Container(path,'public'); p=c.p; ring=Ring(p.N,p.q)
    rows=[c.take(p.N) for _ in range(p.recipients)]
    c.finish()
    if products_digest(c.header,rows)!=c.header['products_sha256']:
        raise ValueError('canonical registered-product commitment mismatch')
    expander=PublicExpander(bytes.fromhex(c.header['a_seed']),bytes.fromhex(c.header['a_binding']))
    A=[ring.poly(expander.row('A',j,p.N,p.q)) for j in range(p.w)]
    return c.header,p,ring,A,rows


def load_ciphertext(path):
    c=Container(path,'ciphertext'); ring=Ring(c.p.N,c.p.q)
    ct=Ciphertext(polynomial_rows(c,ring,c.p.w),c.take(c.p.d),c.header['weight'])
    c.finish()
    lineage={digest(path):1} if c.header['terms'] is None else dict(c.header['terms'])
    return c.header,c.p,ct,lineage


def context_equal(a,b):
    for name in ['profile','setup_id','parameters','a_sha256','registry_sha256','seed_policy','seed_bits']:
        if a.get(name)!=b.get(name):raise ValueError('cross-context artifact')
    if a['kind']=='ciphertext' and b['kind']=='ciphertext' and a['public_sha256']!=b['public_sha256']:
        raise ValueError('cross-public-key ciphertexts')


def emit_cipher(path,header,p,ct):
    ring=Ring(p.N,p.q)
    return write_container(path,header,itertools.chain.from_iterable(
        itertools.chain((ring.coefficients(poly) for poly in ct.c0),[ct.h])))


def command_init(a):
    p=params(a.profile)
    h=basic_header(a.profile,'a')
    h['a_seed']=os.urandom(SEED_BYTES).hex(); h['a_binding']=a_binding(h)
    write_container(a.out,h,iter(()))
    return {'actual_private_rows_generated':0,'A_rows_stored':0,'A_rows_seed_described':p.w,
            'seed_bits':SEED_BITS,'fixed_registry_before_seed':True}


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
    ac=Container(a.public_a,'a');h,p=ac.header,ac.p;ac.finish();ah=digest(a.public_a)
    rows=[None]*p.recipients
    for path in a.registration:
        c=Container(path,'registration')
        if c.header['setup_id']!=h['setup_id'] or c.header['profile']!=h['profile'] or c.header['a_sha256']!=ah:
            raise ValueError('registration is for a different public A')
        i=c.header['coordinate']
        if rows[i] is not None:raise ValueError('duplicate recipient registration')
        rows[i]=c.take(p.N);c.finish()
    if any(row is None for row in rows):raise ValueError('incomplete recipient registry')
    ph=basic_header(h['profile'],'public',h['setup_id'],a_sha256=ah,a_seed=h['a_seed'],a_binding=h['a_binding'])
    # This exact ordered payload/context commitment precedes missing-seed sampling.
    ph['products_sha256']=products_digest(ph,rows)
    ph['missing_seed']=os.urandom(SEED_BYTES).hex();ph['missing_binding']=missing_binding(ph)
    write_container(a.out,ph,itertools.chain.from_iterable(rows))
    return {'actual_private_rows_generated':0,'absent_private_rows_generated':0,
            'missing_public_rows_seed_described':p.d-p.recipients,'registrations':p.recipients,
            'seed_bits':SEED_BITS,'products_sha256':ph['products_sha256']}


def command_encode(a):
    h,p,ring,A,rows=load_public(a.public)
    path=Path(a.input).resolve(); READS.append({'path':str(path),'kind':'input','private':False})
    x=json.loads(path.read_text())
    if not isinstance(x,list) or len(x)!=p.d or any(type(v) is not int or not 0<=v<p.p for v in x):
        raise ValueError('input must be a canonical F_p vector')
    if any(abs(v if v<=p.p//2 else v-p.p)>127 for v in x) or x[-1]!=0:raise ValueError('semantic issuer expects int8 feature residues and final zero')
    transformed=BASIS.transform(x)
    s=uniform_below(p.q,p.N);sp=ring.poly(s);sampler=GaussianSampler()
    c0=[ring.mul(row,sp)+ring.poly(sampler.sample(p.sigma_error,p.N)) for row in A]
    floods=uniform_below(2*p.flood+1,p.d)
    expander=PublicExpander(bytes.fromhex(h['missing_seed']),bytes.fromhex(h['missing_binding']))
    hs=[]
    for i in range(p.d):
        row=rows[i] if i<p.recipients else expander.row('missing-P',i,p.N,p.q)
        hs.append((ring.const_product(row,s)+floods[i]-p.flood+p.delta*transformed[i])%p.q)
        del row
    ct=Ciphertext(c0,hs,1)
    ch=basic_header(h['profile'],'ciphertext',h['setup_id'],a_sha256=h['a_sha256'],public_sha256=digest(a.public),weight=1,terms=None)
    emit_cipher(a.out,ch,p,ct)
    return {'encoded_coordinates':p.d,'private_rows_read':0,'A_rows_reconstructed':p.w,
            'absent_rows_reconstructed':p.d-p.recipients,'peak_explicit_absent_rows':1,
            'issuer_bundle_bytes':Path(a.public).stat().st_size,'seed_bits':SEED_BITS}


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


def command_query(a):
    kc=Container(a.key,'key'); p=kc.p; kh=kc.header
    bits=(8*p.sigma_key).bit_length(); modulus=1<<bits; sign=1<<(bits-1)
    row=[]
    for _ in range(p.w):
        values=[x if x<sign else x-modulus for x in kc.take(p.N)]
        if any(abs(x)>=8*p.sigma_key for x in values):raise ValueError('noncanonical key coefficient')
        row.append(values)
    kc.finish(); key=RecipientKey(kh['coordinate'],row)
    public_models=Path(a.models).resolve(); READS.append({'path':str(public_models),'kind':'class_snapshot_map','private':False})
    manifest=json.loads(public_models.read_text())
    if manifest['registry_sha256']!=BASIS_SHA256 or manifest['capacity']!=2:raise ValueError('model map registry/capacity mismatch')
    setup=PublicSetup.__new__(PublicSetup); setup.params=p; setup.ring=Ring(p.N,p.q)
    comparisons=[]
    for snapshot in manifest['snapshots']:
        scores={}
        if set(snapshot['classes'])!=set(BASIS.registry['classes']):raise ValueError('wrong fixed class map')
        for label,item in snapshot['classes'].items():
            if type(item['count']) is not int or not 1<=item['count']<=2:raise ValueError('invalid class count')
            h,_,ct,lineage=load_ciphertext(item['path']); context_equal(kh,h)
            if digest(item['path'])!=item['sha256'] or len(lineage)!=item['count'] or any(c!=1 for c in lineage.values()):raise ValueError('class snapshot/count mismatch')
            value=setup.decode(key,ct)
            if abs(value)>item['count']*BASIS.bounds[key.coordinate]:raise ValueError('signed application score out of declared range')
            scores[label]=value
        from fractions import Fraction
        ranked=sorted(scores,key=lambda label:(-Fraction(scores[label],snapshot['classes'][label]['count']),label))
        comparisons.append({'revision':snapshot['revision'],'scores':scores,'prediction':ranked[0]})
    # Recipient deliberately publishes these known-public benchmark scores.
    # It never reads another recipient's private output or key.
    return {'recipient_coordinate':key.coordinate,'registered_query_text':BASIS.registry['queries'][key.coordinate]['text'],'private_rows_read':1,'query_results':comparisons,'output_scope':'Explicit public benchmark scores from this recipient only'}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--receipt',required=True)
    parser.add_argument('--registry',required=True)
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('init'); p.add_argument('--profile',choices=['candidate_full'],required=True); p.add_argument('--out',required=True)
    p=sub.add_parser('register'); p.add_argument('--public-a',required=True); p.add_argument('--coordinate',type=int,required=True); p.add_argument('--key-out',required=True); p.add_argument('--registration-out',required=True)
    p=sub.add_parser('finalize'); p.add_argument('--public-a',required=True); p.add_argument('--registration',action='append',required=True); p.add_argument('--out',required=True)
    p=sub.add_parser('encode'); p.add_argument('--public',required=True); p.add_argument('--input',required=True); p.add_argument('--out',required=True)
    p=sub.add_parser('combine'); p.add_argument('--term',nargs=2,action='append',required=True,metavar=('COEFFICIENT','CIPHERTEXT')); p.add_argument('--out',required=True)
    p=sub.add_parser('window'); p.add_argument('--state'); p.add_argument('--add',required=True); p.add_argument('--expire'); p.add_argument('--capacity',type=int,required=True); p.add_argument('--out',required=True)
    p=sub.add_parser('query'); p.add_argument('--key',required=True); p.add_argument('--models',required=True)
    p=sub.add_parser('decode'); p.add_argument('--key',required=True); p.add_argument('--ciphertext',required=True); p.add_argument('--expected-lift',type=int); p.add_argument('--out',required=True)
    a=parser.parse_args(); configure_basis(a.registry); start=time.perf_counter(); status='PASS'; error=None; result={}
    try:result=globals()['command_'+a.command](a)
    except Exception as exc:status='FAIL'; error=f'{type(exc).__name__}: {exc}'
    receipt={'status':status,'role_command':a.command,'pid':os.getpid(),'elapsed_seconds':time.perf_counter()-start,
             'peak_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'uid':os.getuid(),
             'registry_sha256':BASIS_SHA256,'seed_policy':SEED_POLICY,'seed_bits':SEED_BITS,
             'artifact_reads':READS,'artifact_writes':WRITES,'result':result,'error':error}
    Path(a.receipt).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':status,'role_command':a.command,'elapsed_seconds':receipt['elapsed_seconds'],'error':error}),flush=True)
    return 0 if status=='PASS' else 1


if __name__=='__main__':raise SystemExit(main())
