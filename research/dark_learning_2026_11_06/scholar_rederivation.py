"""Independent schedule derivation and live small falsifiers; no existing file writes.
Run: python3 scholar_rederivation.py > scholar_rederivation_results.json
"""
import hashlib
import json
import math
import random
from pathlib import Path
import bfv_ref as B
import cosnark as C
import he_matvec as H
import spdz
import step_counts as SC

ROOT = Path(__file__).resolve().parent

def derive(d, queries=64):
    # Independently enumerate two forward and one transposed exchange schedules.
    send = ret = 0
    dc, dr = min(d,64), min(d,128)
    for transpose in (False,False,True):
        for sender in range(3):
            for receiver in range(3):
                if receiver == sender: continue
                send += d//(dr if transpose else dc)
                ret += d//(dc if transpose else dr)
    s = max(5, math.ceil(math.log2(49*d/128)))
    shifts = [s,s,4,s+3]
    # Constant input x,y; trunc openings, lookup, Beaver products, outer masks, MAC.
    nonmat_wire = 6*d + 6*(4*d+d+2*d*sum(2*(x-1) for x in shifts)+2*d+4*d)+12
    # above 2*d*sum... counts two openings per trunc multiplier;
    # +2*d is Hadamard openings and +4*d both outer masks.
    spdz_wire = nonmat_wire + 18*(d*d+d)
    he_wire = nonmat_wire + (send+ret)*49152 + 18*d + 6*(6*d+3)
    # Independent ideal-dealer inventory, steady state.
    base_auth = 2*d + 3*(d*d+2*d) + d*sum(2+x+6*(x-1) for x in shifts) + 255*d + 3*d + 2*(d*d+2*d)
    he_auth = base_auth - 3*(d*d+2*d) + 12*d
    ld = d.bit_length()-1
    vr,vc = 2**(ld//2),2**(ld-ld//2)
    # 20 evaluations: 3 matvec + 4 rank1 matrices = 7; the other 13 are vectors.
    row_combos = 3*(7*d+13*vc +4*d+9*vc)
    cols = 3*queries*(4*d+9*vr)
    hashes = 3*queries*(4*(ld+2)+9*((ld-ld//2)+2))+39
    scmsg = 13*ld
    mults = 13*(d-1)
    opens = 2*mults+scmsg
    spine = dict(witness_elems=4*d*d+9*d, codeword_elems_per_party=4*(4*d*d+9*d),
                 proof_field_elems=row_combos+cols+scmsg+39,proof_hashes=hashes,
                 proving_openings=opens,proving_wire=6*opens+12,
                 raw_share_bits=3*(4*d*d+9*d)*61,encoded_share_bits=12*(4*d*d+9*d)*61,
                 root_bits=39*256)
    return dict(d=d,send=send,returned=ret,spdz_online=spdz_wire,he_online=he_wire,
                he_auth_values=he_auth,spdz_auth_values=base_auth,spine=spine)

def shared_fixture(d,p,seed=4):
    dealer=spdz.Dealer(p,3,seed); eng=spdz.Engine(p,3,dealer)
    rng=random.Random(seed)
    sh=lambda x:dict(enumerate(dealer._share(x%p)))
    vals=lambda:[rng.randrange(7) for _ in range(d)]
    a=[vals() for _ in range(d)]; b=[vals() for _ in range(d)]; x=vals(); h=vals()
    w=dict(W1=[[sh(v) for v in r] for r in a],W2=[[sh(v) for v in r] for r in b],
           x=[sh(v) for v in x],h=[sh(v) for v in h],
           z1=[sh(sum(v*z for v,z in zip(r,x))) for r in a],
           z2=[sh(sum(v*z for v,z in zip(r,h))) for r in b])
    for k in ('d1','d2','b','g1','bg'): w[k]=[sh(0) for _ in range(d)]
    # a valid no-update algebraic spine; actual shared matrices persist unchanged.
    w['W1n']=w['W1']; w['W2n']=w['W2']
    return eng,w

class AcceptanceLedger:
    """Reference acceptance policy, not durable consensus or a cryptographic proof.
    The proof verifier MUST bind context_digest; otherwise this gate is insufficient.
    """
    def __init__(self, parent): self.parent=parent; self.counter=0; self.used=set()
    def accept(self,parent,child,counter,nonce,expected_digest,proved_digest,valid):
        if not valid or parent!=self.parent or counter!=self.counter or nonce in self.used or expected_digest!=proved_digest:
            return False
        self.parent=child; self.counter+=1; self.used.add(nonce); return True

def attacks(p):
    result={}
    # Actual HEMatvec.coins: freezing auth transcript fixes rho. Show the linear kernel
    # that would defeat an early challenge, then change auth and re-derive actual rho.
    eng=spdz.Engine(p,3,spdz.Dealer(p,3,44))
    for i in range(4): eng.auth_plain({0:i,1:0,2:0},'he_auth')
    mv=H.HEMatvec(eng,[],256,2**183)
    rho=mv.coins(4); delta=[rho[1],-rho[0]%p,0,0]
    assert any(delta) and sum(a*b for a,b in zip(delta,rho))%p==0
    for i in range(4):
        phase,shares,v=eng.transcript[i]; shares=dict(shares); shares[0]=(shares[0]+delta[i])%p
        eng.transcript[i]=(phase,shares,(v+delta[i])%p)
    rho2=mv.coins(4)
    residual=sum(a*b for a,b in zip(delta,rho2))%p
    assert residual
    result['freivalds_early_challenge_kernel']={'early_accepts':True,'actual_auth_rehash_refuses':True,'residual':residual}
    # Suffix excludes earlier context; not a plaintext leak or a post-fix adaptive attack.
    rh=mv.coins(4); eng.transcript.insert(0,('old_context',{},123)); eng.transcript.insert(0,('old_context',{},124))
    # suffix length 12: pad enough to make explicitly old prefix irrelevant
    eng.transcript=[('prefix',{},i) for i in range(20)]+eng.transcript[-4:]
    rh=mv.coins(4); eng.transcript[0]=('changed_model_or_epoch',{},999)
    assert mv.coins(4)==rh
    result['freivalds_context_omitted']={'old_prefix_change_keeps_rho':True,'scope':'requires separate committed input/state binding'}
    # Actual engine fixed-seed MAC: one malicious party changes two broadcasts without MAC key.
    e=spdz.Engine(p,3,spdz.Dealer(p,3,9)); rr=random.Random('known'); r=[rr.randrange(p) for _ in range(2)]
    ds=[r[1],-r[0]%p]
    for value,delta in zip([3,5],ds):
        x=dict(enumerate(e.dealer._share(value))); x[0]=((x[0][0]+delta)%p,x[0][1]); e.open(x)
    e.mac_check('known')
    assert all(delta for delta in ds)
    # Countermeasure control: derive challenge from canonical complete frozen broadcasts.
    digest=hashlib.sha256(json.dumps(e.transcript,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    try: e.mac_check(digest); hardened=False
    except spdz.Abort: hardened=True
    assert hardened
    result['fixed_seed_mac_cancellation']={'legacy_accepts_wrong_broadcasts':True,'transcript_bound_control_refuses':hardened,
       'scope':'reference ROM control; production requires commit-then-joint-unpredictable coins and checked sigma commitments'}
    e,w=shared_fixture(4,p)
    parent={k:C.SharePCS(p,[[v[i][0] for row in w[k] for v in row] for i in range(3)],k).roots for k in ('W1','W2')}
    ok,why,c=C.prove_and_verify(e,w,parent=parent); assert ok
    ok2,_,_=C.prove_and_verify(e,w,parent=parent); assert ok2
    stale={k:['00'*32]*3 for k in ('W1','W2')}
    stale_ok,stale_why,_=C.prove_and_verify(e,w,parent=stale); assert not stale_ok
    # Same no-update edge valid twice. A caller must supply atomic full context; roots alone cannot count occurrences.
    ledger=AcceptanceLedger(parent)
    first=ledger.accept(parent,c['child_roots'],0,'n0','context0','context0',ok)
    replay=ledger.accept(parent,c['child_roots'],0,'n0','context0','context0',ok)
    wrongctx=ledger.accept(c['child_roots'],c['child_roots'],1,'n1','context1','context0',ok)
    assert first and not replay and not wrongctx
    result['chain_occurrence']={'honest_accepts':ok,'duplicate_no_update_edge_accepts':ok2,
       'stale_parent_refused':not stale_ok,'stale_reason':stale_why,
       'reference_ledger_replay_refused':not replay,'reference_ledger_context_splice_refused':not wrongctx,
       'scope':'ledger is an in-memory specification, not persistent quorum consensus'}
    for attack in ('forge_W1n','forge_z1','forge_sumcheck','lie_in_u'):
        ee,ww=shared_fixture(4,p)
        # built-in W attack indexes 5: d4 matrix supports it; z attack index3 also valid
        verdict,why,_=C.prove_and_verify(ee,ww,attack=attack)
        assert not verdict,(attack,why)
        result[attack]={'refused':True,'why':why}
    return result

def main():
    p=B.ntt_primes(61,4,16384)[3]
    out={'source_sha256':{k:hashlib.sha256((ROOT/k).read_bytes()).hexdigest() for k in ('he_matvec.py','cosnark.py','spdz.py','step_counts.py')},'counts':[],'small_execution':[]}
    for d in (64,1024,4096):
        row=derive(d); hc=H.counts(d); mc=SC.mpc_counts(d); cc=C.counts_formula(d)
        assert row['send']==hc['cts_sent'] and row['returned']==hc['cts_returned']
        assert row['spdz_online']==mc['steady']['online_wire'],(row,mc)
        assert row['he_online']==mc['steady']['online_wire']-18*(d*d+d)+hc['he_wire']+hc['spdz_wire']
        assert row['he_auth_values']==mc['preprocessing_auth_values']-2*d*d-3*(d*d+2*d)+12*d
        for k in ('witness_elems','codeword_elems_per_party','proof_field_elems','proof_hashes','proving_openings'): assert row['spine'][k]==cc[k],(d,k)
        assert row['spine']['proving_wire']==sum(cc['proving_wire'].values())
        row['spine_t148']=derive(d,148)['spine']
        out['counts'].append(row)
    for d in (4,16,32,64):
        e,w=shared_fixture(d,p); ok,why,c=C.prove_and_verify(e,w); assert ok,why
        row=derive(d)['spine']
        for k in ('witness_elems','codeword_elems_per_party','proof_field_elems','proof_hashes','proving_openings'): assert row[k]==c[k],(d,k,row[k],c[k])
        assert row['proving_wire']==sum(c['proving_wire'].values())
        out['small_execution'].append({'d':d,'accept':ok,'independent_counts_match':True})
    out['attacks']=attacks(p)
    out['pass']=True
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
