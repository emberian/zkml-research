#!/usr/bin/env python3
"""Run synthetic, memory-only ring setup/encode/update/designated decoding."""
import argparse
import hashlib
import json
import platform
import resource
import sys
import time
from pathlib import Path
import flint
from ring import Parameters, PublicSetup, Window, Ring, uniform_below, generate_recipient_key
from sampling.sampler import GaussianSampler

HERE = Path(__file__).resolve().parent
Q = 4294967767*2**256+1


class MeteredSampler:
    def __init__(self):
        self.inner = GaussianSampler()
        self.totals = {}

    def sample(self, sigma, count):
        out = self.inner.sample(sigma, count)
        assert len(out) == count and all(-8*sigma < x < 8*sigma for x in out)
        totals = self.totals.setdefault(str(sigma), {})
        for key in ('count', 'seconds', 'proposals', 'direct_threshold_evaluations', 'cap_fallbacks', 'os_random_bytes_requested'):
            totals[key] = totals.get(key, 0)+self.inner.last_stats[key]
        return out


def params(profile):
    if profile == 'toy':
        return Parameters(64, 4, 9, 2, 257, 2013265921, 2, 1, 1024, 8)
    if profile == 'candidate_n_probe':
        return Parameters(16384, 8, 33, 2, 28439893, Q, 2**25, 2**10, 2**247, 32, 8204908842)
    if profile == 'candidate_full':
        return Parameters(16384, 64, 577, 16, 28439893, Q, 2**25, 2**10, 2**247, 32, 8204908842)
    raise ValueError(profile)


def timed(fn):
    start = time.perf_counter()
    value = fn()
    return value, time.perf_counter()-start


def fixture(p, step):
    # Public synthetic input, including both ends of centered input range.
    x = [(12345*(i+1)*(step+1)+17*i*i+31*step) % p.p for i in range(p.d)]
    x[0] = p.p//2 if step % 2 == 0 else p.p//2+1
    x[-1] = p.p-1
    return x


def arithmetic_control():
    # A meaningful independent O(N²) oracle used only at small N.
    cases = 0
    for n in (16, 64):
        ring = Ring(n, 2013265921)
        for iteration in range(3):
            a = [((i+1)**2-79*iteration) % ring.q for i in range(n)]
            b = [((i+2)**3-131*iteration) % ring.q for i in range(n)]
            expected = [0]*n
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    expected[(i+j)%n] += x*y*(1 if i+j<n else -1)
            expected = [x % ring.q for x in expected]
            actual = ring.coefficients(ring.mul(ring.poly(a), ring.poly(b)))
            assert expected == actual
            assert ring.const_product(a,b) % ring.q == expected[0]
            cases += 1
    return {'independent_naive_negacyclic_cases': cases, 'pass': True}


def arithmetic_bench():
    rows=[]
    for n in (64,1024,4096,16384):
        ring=Ring(n,Q)
        a=uniform_below(Q,n); b=uniform_below(Q,n)
        ap=ring.poly(a); bp=ring.poly(b)
        _,seconds=timed(lambda: ring.mul(ap,bp))
        _,dot=timed(lambda: ring.const_product(a,b)%Q)
        rows.append({'N':n,'q_bits':Q.bit_length(),'one_negacyclic_multiply_seconds':seconds,
                     'one_constant_product_seconds':dot})
    return rows


def execute(profile, inputs):
    if inputs < 3:
        raise ValueError('at least three encodes needed for exact expiry')
    p = params(profile)
    sampler = MeteredSampler()
    timings = {'sampler_table_build': sampler.inner.table_seconds}
    setup, timings['public_A'] = timed(lambda: PublicSetup(p,sampler))
    def register_recipients():
        keys=[]
        for i in range(p.recipients):
            key, public_product=generate_recipient_key(p,setup.A,i,sampler)
            setup.register_public(i,public_product)
            keys.append(key)
        return keys
    keys, timings['recipient_keygen_and_publish'] = timed(register_recipients)
    _, timings['missing_public_rows'] = timed(setup.finish)
    assert len(keys)==p.recipients and all(key.coordinate < p.recipients for key in keys)
    print(json.dumps({'event':'setup_complete','profile':profile,'seconds':timings}), flush=True)
    window = Window(setup,2)
    cts=[]; lifts=[]; observations=[]
    for step in range(inputs):
        x=fixture(p,step); transformed=setup.basis.transform(x)
        assert setup.basis.inverse(transformed)==[value%p.p for value in x]
        sample_before=sampler.totals.get(str(p.sigma_error),{}).get('seconds',0)
        ct, enc=timed(lambda: setup.encode(x))
        sample_seconds=sampler.totals[str(p.sigma_error)]['seconds']-sample_before
        decoded, dec=timed(lambda: [setup.decode(key,ct) for key in keys])
        assert decoded == transformed[:p.recipients]
        cts.append(ct); lifts.append(transformed)
        current, upd=timed(lambda: window.push(ct))
        got, win_dec=timed(lambda: [setup.decode(key,current) for key in keys])
        expected=[sum(row[i] for row in lifts[max(0,step-1):step+1]) for i in range(p.recipients)]
        assert got==expected
        # Actual expiry agrees coefficient-for-coefficient with a fresh sum.
        rebuilt=setup.combine([(1,item) for item in cts[max(0,step-1):step+1]])
        assert rebuilt.c0==current.c0 and rebuilt.h==current.h
        observations.append({'step':step,'encode_seconds':enc,'all_recipient_decode_seconds':dec,
             'encode_error_sampler_seconds':sample_seconds,'encode_other_seconds':enc-sample_seconds,
             'window_update_seconds':upd,'window_all_recipient_decode_seconds':win_dec,
             'fresh_recipients_matched':len(decoded),'window_recipients_matched':len(got),
             'live_window_size':len(window.queue),'exact_expiry_rebuild_matched':True})
        print(json.dumps({'event':'encode_complete','profile':profile,**observations[-1]}),flush=True)
    signed, timings['signed_combine'] = timed(lambda: setup.combine([(2,cts[0]),(-1,cts[1])]))
    signed_values, timings['signed_all_recipient_decode'] = timed(lambda: [setup.decode(key,signed) for key in keys])
    assert signed_values==[2*lifts[0][i]-lifts[1][i] for i in range(p.recipients)]
    failed=False
    try: setup.combine([(p.W+1,cts[0])])
    except ValueError: failed=True
    assert failed
    coefficient_bits=p.q.bit_length()
    result={'profile':profile,'status':'PASS','parameters':p.__dict__,
       'classification':'full repaired algebraic dimensions; conditional security assumptions remain' if profile=='candidate_full' else 'toy or reduced-dimension execution; no security inference',
       'timings_seconds':timings,'encodes':observations,'sampler':sampler.totals,
       'fresh_inputs_executed':inputs,'candidate_theorem_T':384,'T384_executed':inputs==384,
       'actual_recipient_rows_generated':len(keys),'absent_recipient_rows_generated':0,
       'signed_combination_recipients_matched':p.recipients,'oversized_combination_rejected':True,
       'packed_sizes_bytes':{'ciphertext':((p.w*p.N+p.d)*coefficient_bits+7)//8,
           'public_A_P':((p.w+p.d)*p.N*coefficient_bits+7)//8,
           'one_key_cutoff':(p.w*p.N*(8*p.sigma_key).bit_length()+7)//8},
       'packing_implemented':False,'peak_process_rss_native':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
       'rss_native_unit':'bytes on macOS; KiB on Linux','raw_keys_coins_inputs_or_ciphertext_persisted':False,
       'privacy_or_hardness_tested':False,'timing_side_channel_claim':False}
    return result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--profile',choices=['toy','candidate_n_probe','candidate_full'],default='toy')
    parser.add_argument('--inputs',type=int,default=3)
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    started=time.perf_counter()
    sources=['ring.py','run.py','sampling/sampler.py']
    before={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in sources}
    result={'python':sys.version,'platform':platform.platform(),'flint_version':flint.__version__,
        'argv':sys.argv,'source_sha256':before,'controls':arithmetic_control(),'arithmetic_bench':arithmetic_bench(),
        'run':execute(args.profile,args.inputs)}
    after={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in sources}
    result['source_unchanged']=before==after
    result['elapsed_seconds']=time.perf_counter()-started
    result['status']='PASS' if result['source_unchanged'] else 'SOURCE_CHANGED'
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'profile':args.profile,'elapsed_seconds':result['elapsed_seconds'],
                      'output':args.output}),flush=True)
    return 0 if result['status']=='PASS' else 2


if __name__=='__main__':raise SystemExit(main())
