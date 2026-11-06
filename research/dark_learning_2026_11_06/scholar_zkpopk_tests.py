"""Run the actual ZK protocol and all falsifiers at N=8; count-only N=8192.
Run from any working directory: python3 path/to/scholar_zkpopk_tests.py.
"""
import copy
import hashlib
import json
import math
import random
from pathlib import Path

import bfv_ref as bfv
import scholar_zkpopk as Z


def main():
    out={"scope":"N=8 exact ZK reference, classical ROM only; N=8192 count-only", "tests":{}}
    tests=out["tests"]
    rng=random.Random(81209)
    N=8; primes=bfv.ntt_primes(17,4,2*N); Q=math.prod(primes[:3]); t=primes[3]
    reg,s,epk=Z.keygen(N,primes[:3],t,"verifier-owned-registry-seed",rng=rng)
    context=dict(epoch=7,step=42,operation="forward",block=0,sender=0,recipient=1,parent="abc123",layout="coeff-64")
    m=[rng.randrange(t) for _ in range(N)]
    env=Z.encrypt_and_prove(reg,s,epk,m,context,rng=rng)
    rel=Z.Relation(reg,env["ciphertext"],context)
    tests["honest"]=Z.verify(rel,env["proof"])
    assert tests["honest"][0]
    wire=Z.encode_proof(rel,env["proof"])
    decoded=Z.decode_proof(rel,wire)
    tests["compact_roundtrip"]=Z.verify(rel,decoded)
    assert tests["compact_roundtrip"][0]
    counted=Z.counts(N,Q,t)
    exact_bytes=10+counted["repetitions"]*(96+1+(rel.size*(rel.mod-1).bit_length()+7)//8+(rel.bit_count+7)//8+64)
    assert len(wire)==exact_bytes==counted["compact_proof_bytes"]
    out["toy"]=dict(N=N,primes=primes[:3],t=t,measured_wire_bytes=len(wire),formula_wire_bytes=exact_bytes,
                    proof_contains_raw_witness=False,statement_bits=rel.mod.bit_length(),binary_witness_bits=rel.bit_count)
    sch=bfv.BFV(N,Q,t); sch.s=s
    ct=Z.accept_ciphertext(reg,env,context)
    assert sch.decrypt(ct)==m
    P=[rng.randint(-2,2) for _ in range(N)]
    prod=Z.multiply_verified(P,reg,env,context)
    assert sch.decrypt(prod)==[x%t for x in bfv.negacyclic_mul(P,m)[0]]
    tests["gate_then_matvec_product"]=[True,"decrypts to P*m exactly"]
    for name, bad in (("proof_none",None),("proof_list",[])):
        tests[name]=Z.verify(rel,bad)
        assert not tests[name][0]
    # The lattice input compiler is independently multiplied as a sparse
    # polynomial matrix. Recover witness privately for this control only.
    a=env["ciphertext"][1]
    phase=[(x+y)%Q for x,y in zip(env["ciphertext"][0],Z.conv(a,s))]
    eta=[bfv.centered(t*ph-Q*mm,t*Q) for ph,mm in zip(phase,m)]
    witness=rel.witness(s,epk,m,eta)
    import scholar_zkpopk_lazer_params as LP
    compiled=LP.compile_linear(rel,witness)
    assert LP.check_compiled(compiled)
    tests["lattice_relation_compiler"]=[True,dict(shape=compiled["shape"],degree=N)]
    # Three accepting Stern branches reveal a binary preimage; verify the
    # extraction identity at the exact composite modulus, without division.
    r=[rng.randrange(rel.mod) for _ in range(rel.size)]
    z=[(x+y)%rel.mod for x,y in zip(r,witness)]
    extracted=[(x-y)%rel.mod for x,y in zip(z,r)]
    assert extracted==witness and rel.apply(extracted)==rel.target
    tests["three_branch_extraction"]=[True,"binary extracted witness satisfies A*x=target"]

    def refused(name,ct=None,proof=None,ctx=None,registry=None):
        rr=Z.Relation(registry or reg,ct or env["ciphertext"],ctx or context)
        verdict=Z.verify(rr,proof or env["proof"])
        tests[name]=verdict
        assert not verdict[0],name
    badct=copy.deepcopy(env["ciphertext"]); badct[0][0]=(badct[0][0]+Q//t)%Q
    refused("wrong_plaintext_offset",ct=badct)
    badct=copy.deepcopy(env["ciphertext"]); badct[1][0]=(badct[1][0]+primes[0])%Q
    refused("mixed_limb_ciphertext",ct=badct)
    refused("stale_parent",ctx=dict(context,parent="old-parent"))
    refused("different_recipient",ctx=dict(context,recipient=2))
    refused("different_epoch",ctx=dict(context,epoch=8))
    pp=copy.deepcopy(env["proof"]); pp["responses"][0]["v"][0]=(pp["responses"][0]["v"][0]+1)%rel.mod
    refused("changed_response",proof=pp)
    pp=copy.deepcopy(env["proof"]); pp["responses"][0]["v"].pop()
    refused("short_response",proof=pp)
    pp=copy.deepcopy(env["proof"]); pp["responses"][0]["v"][0]=rel.mod
    refused("noncanonical_response",proof=pp)
    pp=copy.deepcopy(env["proof"]); pp["responses"].pop()
    refused("missing_repetition",proof=pp)
    pp=copy.deepcopy(env["proof"])
    j=next(i for i,r in enumerate(pp["responses"]) if r["c"]==2)
    pp["responses"][j]["px"][0]=2
    refused("nonbinary_secret",proof=pp)
    for name,blob in (("truncated_packet",wire[:-1]),("trailing_bytes",wire+b"x")):
        try: Z.decode_proof(rel,blob)
        except ValueError as e: tests[name]=[False,str(e)]
        else: raise AssertionError(name)
    malicious=Z.Registry(N,reg.primes,t,reg.seed,reg.key_id,tuple([1]+[0]*(N-1)),reg.b)
    refused("malicious_key_a_is_one",registry=malicious)
    try:
        Z.encrypt_and_prove(reg,[2]+s[1:],epk,m,context,rng=rng)
    except ValueError as e: tests["out_of_range_secret"]=[False,str(e)]
    else: raise AssertionError("out_of_range_secret")

    # At c1=0 and c0=floor(Q/(2t)), the scaled phase is half a Q away from
    # every Q*m lattice point: strictly outside +/- (8.5t). Thus no witness
    # exists regardless of the secret key; this is a false encryption relation.
    false_ct=([Q//(2*t)]+[0]*(N-1),[0]*N)
    distance=min(t*false_ct[0][0],Q-t*false_ct[0][0])
    assert distance>8*t+(t-1)//2
    false_rel=Z.Relation(reg,false_ct,context)
    forged=Z.simulate_known_challenges(false_rel,rng=rng)
    legacy=Z.verify(false_rel,forged,legacy=True)
    fixed=Z.verify(false_rel,forged)
    tests["known_challenge_forgery_legacy"]=legacy
    tests["known_challenge_forgery_bound"]=fixed
    assert legacy[0] and not fixed[0]
    tests["false_statement_distance"]=[True,dict(distance=distance,allowed=8*t+(t-1)//2)]
    import he_matvec
    saved_product=he_matvec.ptxct
    product_calls=[]
    def forbidden_product(*args):
        product_calls.append(True)
        raise AssertionError("recipient multiplied before admission")
    he_matvec.ptxct=forbidden_product
    try:
        try: Z.multiply_verified(P,reg,dict(ciphertext=false_ct,proof=forged),context)
        except ValueError as e: tests["gate_refuses_before_product"]=[False,str(e)]
        else: raise AssertionError("gate_refuses_before_product")
        assert product_calls==[]
    finally:
        he_matvec.ptxct=saved_product
    tests["rejected_ciphertext_product_calls"]=[True,len(product_calls)]

    # Count exact compact representation; this performs no N8192 ring operation.
    large=bfv.ntt_primes(61,4,16384); bigQ=math.prod(large[:3]); bigt=large[3]
    c=Z.counts(8192,bigQ,bigt)
    c["compact_proof_bytes"]=10+c["repetitions"]*(96+1+(c["extended_witness_coordinates"]*c["statement_modulus_bits"]+7)//8+(c["binary_witness_bits"]+7)//8+64)
    c["compact_proof_bits"]=8*c["compact_proof_bytes"]
    out["N8192_count_only"]=c
    out["step_counts"]={}
    from he_matvec import counts as hecounts
    for d in (64,1024,4096):
        sent=hecounts(d)["cts_sent"]
        # he_matvec sends identical block ciphertexts to each of two recipients,
        # but current statement includes recipient, so separate proof statements.
        out["step_counts"][str(d)]=dict(delivered_proofs=sent,delivered_proof_bits=sent*c["compact_proof_bits"],
                                       previous_unbuilt_commitment_bits=hecounts(d)["zkpopk_bits"])
    base=Path(__file__).resolve().parent
    out["source_sha256"]={name:hashlib.sha256((base/name).read_bytes()).hexdigest()
        for name in ("scholar_zkpopk.py","scholar_zkpopk_tests.py","scholar_zkpopk_lazer_params.py","he_matvec.py","bfv_ref.py")}
    out["all_expected_outcomes"]=True
    print(json.dumps(out,indent=2))
    return out

if __name__=="__main__":
    main()
