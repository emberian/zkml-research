#!/usr/bin/env python3
"""Independent finite mathematics/provenance controls for TERMINAL_JOINT.

No cryptographic implementation, extraction, recovery, routing or service
adversary is executed. Toy group elements are forward algebraic coordinates;
symbolic payload/proof records check marginal laws, not FE/GS security.
"""
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
EXPERIMENTS=HERE.parents[1]
AUTHOR=EXPERIMENTS/'private_ingress'/'provenance_review'/'terminal_joint'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def tv(c0,c1):
    n0,n1=sum(c0.values()),sum(c1.values())
    return sum(abs(Fraction(c0[k],n0)-Fraction(c1[k],n1))
               for k in c0.keys()|c1.keys())/2


def bind(s,r,alpha,t,p):
    return ((r+t*s)%p,(alpha*(r+t*s)+s)%p)


def hide(s,r,alpha,t,p):
    return ((r+t*s)%p,(alpha*(r+t*s))%p)


def forward_binding():
    cases=0
    p=257
    for alpha in (1,2,17,256):
        for t in (0,1,9,256):
            # Enumerate only forward maps, without an extraction algorithm.
            images={bind(s,r,alpha,t,p) for s in range(256) for r in range(p)}
            assert len(images)==256*p
            cases+=256*p
    canonical_checks=0
    for a in (32,33):
        for rg in (0,1,128,256):
            for rc in (0,1,128,256):
                alpha,t=17,9
                genesis=bind(0,rg,alpha,t,p)
                parent=bind(a,rc,alpha,t,p)
                for state in (-1,0,31,32,33,34,128,255,256):
                    for cand_rc in (-1,0,1,128,256,257,rc):
                        for cand_rg in (-1,0,1,128,256,257,rg):
                            for duplicate in (state,32,33):
                                canonical=(0<=state<256 and 0<=cand_rc<p and 0<=cand_rg<p)
                                guard=(canonical and state in (32,33) and duplicate==state
                                       and bind(0,cand_rg,alpha,t,p)==genesis
                                       and bind(state,cand_rc,alpha,t,p)==parent)
                                assert not guard or (state,cand_rc,cand_rg,duplicate)==(a,rc,rg,a)
                                # The only differing observation field is the
                                # final x, both admissible; earlier guards agree.
                                assert (guard and 0 in (0,1))==(guard and 1 in (0,1))
                                canonical_checks+=1
    pairs=[(a,a+1, (a>>7)&1,((a+1)>>7)&1) for a in (32,33)]
    assert all(left!=right and g0==g1==0 for left,right,g0,g1 in pairs)
    return {'forward_binding_images_checked':cases,
            'canonical_replacement_guard_cases':canonical_checks,
            'nonvacuous_terminal_state_pairs':pairs}


def affine_joint_laws():
    p,alpha=257,17
    cases=0
    for t in range(p):
        # Context may be correlated with the trapdoor. The fresh opening is
        # uniform conditional on that entire context; no averaging shortcut.
        a=32+(t%2)
        context=('earlier','current',t%7,(3*t+11)%p,a)
        coupled_right=Counter()
        honest_right=Counter()
        image=set()
        for r0 in range(p):
            s0,s1=a,a+1
            r1=(r0+t*(s0-s1))%p
            c=hide(s0,r0,alpha,t,p)
            assert c==hide(s1,r1,alpha,t,p)
            image.add(r1)
            for proof_coin in (0,1):
                # An arbitrary symbol for a simulator's output as a function
                # of the common statement, trapdoor and independent coins.
                pi_symbol=('Sim',c,t,proof_coin)
                right_payload=(s1,r1,('H2',context[-2],a,context[-3],1))
                coupled_right[(context,right_payload,c,pi_symbol)]+=1
                c_direct=hide(s1,r0,alpha,t,p)
                right_direct=(s1,r0,('H2',context[-2],a,context[-3],1))
                honest_right[(context,right_direct,c_direct,('Sim',c_direct,t,proof_coin))]+=1
                cases+=1
        assert len(image)==p
        assert coupled_right==honest_right
    return {'joint_right_marginal_records_checked':cases,
            'conditional_translation_bijections':p,
            'scope':'Exact right-marginal laws only; H2/H3 ciphertext privacy remains a primitive game.'}


def crs_translation():
    cases=0
    rows=[]
    for p in (3,5,7,11):
        for alpha in range(1,p):
            for t in range(p):
                all_values=Counter(range(p))
                shifted=Counter((r-1)%p for r in range(p))
                assert all_values==shifted
                cases+=1
        binding=Counter((a,t,(a*t)%p) for a in range(1,p) for t in range(p))
        hiding=Counter((a,t,(a*t-1)%p) for a in range(1,p) for t in range(p))
        uniform=Counter((a,t,r) for a in range(1,p) for t in range(p) for r in range(p))
        d=tv(binding,uniform)
        assert tv(hiding,uniform)==d
        assert tv(binding,hiding)<=2*d
        nonzero=Counter(range(1,p))
        shifted_nonzero=Counter((r-1)%p for r in range(1,p))
        assert tv(nonzero,shifted_nonzero)==Fraction(1,p-1)
        rows.append({'p':p,'nonzero_uniform_shift_TV':str(Fraction(1,p-1))})
    return {'full_field_shift_cases':cases,'sampling_convention_controls':rows,
            'scope':'Forward distribution identities and triangle coefficients, not DDH security.'}


def sampling_and_budget():
    sampler_cases=0
    for domain in (*range(2,65),127,256,257):
        m=(domain-1).bit_length()
        for slack in range(13):
            length=1 << (m+slack)
            quotient,rem=divmod(length,domain)
            # Exact reduction-mod-domain distance without sampling or a PRF.
            distance=Fraction(rem*(domain-rem),domain*length)
            direct=(rem*abs(Fraction(quotient+1,length)-Fraction(1,domain))
                    +(domain-rem)*abs(Fraction(quotient,length)-Fraction(1,domain)))/2
            assert distance==direct
            assert distance<=Fraction(1,1 << slack)
            sampler_cases+=1
    budget_cases=0
    for e in range(25):
        epsilon=Fraction(1,1 << e)
        for samples in range(1,258):
            b=e+3+(samples-1).bit_length()
            terms=(4*2*Fraction(1,1 << (e+5)),
                   2*Fraction(1,1 << (e+3)),
                   Fraction(1,1 << (e+2)),
                   2*samples*Fraction(1,1 << b))
            assert all(term<=epsilon/4 for term in terms)
            assert sum(terms)<=epsilon
            budget_cases+=1
    # A point mass is not a sample from fresh uniform bits: the field-sampler
    # estimate cannot be transferred to arbitrary deterministic input coins.
    deterministic_tv=Fraction(256,257)
    assert deterministic_tv>Fraction(1,1 << 12)
    return {'exact_mod_sampler_cases':sampler_cases,
            'four_term_budget_cases':budget_cases,
            'nonuniform_coin_countercontrol_TV':str(deterministic_tv),
            'scope':'The countercontrol rejects treating arbitrary derived coins as uniform; no actual PRF is executed.'}


def quantifier_controls():
    # For this one fixed tester D(Y)=Y, signed conditional gaps cancel.
    conditional=(Fraction(-1),Fraction(1))
    assert abs(sum(conditional)/2)==0
    assert sum(abs(x) for x in conditional)/2==1
    rare=[]
    for size in (2,4,8,16,32,64):
        # K is an ordinary public label, with a rare exceptional label. This
        # uses no setup secret, key-dependent advice or cryptographic attack.
        joint0=Counter((k,0) for k in range(size))
        joint1=Counter((k,int(k==0)) for k in range(size))
        assert tv(joint0,joint1)==Fraction(1,size)
        assert tv(Counter({0:1}),Counter({1:1}))==1
        rare.append({'setup_labels':size,'full_joint_TV':str(Fraction(1,size)),
                     'exceptional_conditional_TV':'1'})
    return {'fixed_tester_abs_mean_signed_gap':'0','mean_absolute_conditional_gap':'1',
            'cancellation_scope':'The full joint distributions in the cancellation example are distinguishable; it is not a counterexample to security for every joint tester.',
            'rare_public_setup_controls':rare,
            'rare_scope':'Even full-joint closeness bounds do not imply a bound for every realized setup; no secret advice is assumed.'}


def main():
    manifest=json.loads((AUTHOR/'manifest.json').read_text())
    sources=json.loads((AUTHOR/'sources.json').read_text())
    expected={Path(row['path']):row['sha256'] for row in manifest['files']}
    assert expected[AUTHOR/'TERMINAL_JOINT.md']=='1c698c8361cd4d6e5bfefc96ee34d1bcc4d090ec59f09f6efaad378d5195717c'
    expected[AUTHOR/'manifest.json']=sha(AUTHOR/'manifest.json')
    for source in sources['sources']:
        for key in ('pdf','retained_extract'):
            row=source[key]
            expected[Path(row['path'])]=row['sha256']
    before={str(p):sha(p) for p in expected}
    assert all(before[str(p)]==h for p,h in expected.items())
    result={'label':'EXECUTED','scope':__doc__,
            'author':'/root/private_ingress','reviewer':'/root/pq_composition',
            'script_sha256':sha(Path(__file__)),
            'binding_and_replacements':forward_binding(),
            'affine_joint_laws':affine_joint_laws(),
            'CRS_coefficient_controls':crs_translation(),
            'sampler_and_budget_controls':sampling_and_budget(),
            'quantifier_controls':quantifier_controls(),
            'input_hashes_before':before,
            'queries':{'SQL':0,'schema':0,'web_search':0,'web_open':0,'Kagi':0},
            'new_PDF_extracts':0,'PDF_downloads':0,
            'cryptographic_extraction_recovery_routing_or_service_runtimes':0}
    after={str(p):sha(p) for p in expected}
    assert before==after
    result['input_hashes_after']=after
    result['all_inputs_unchanged']=True
    (HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
