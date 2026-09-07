#!/usr/bin/env python3
"""Targeted malformed degree / seeded normalization checks on saved run001."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from crypto_boundary_review import fields, pack, payload_blob, canonical

HERE=Path(__file__).resolve().parent
RUNTIME=HERE/'runtime/run_001'
BINARY=RUNTIME/'resident-crypto'
records=[]


def short_degree_ct(payload):
    result=[]
    for n,w,v in fields(payload):
        if n==1:
            poly=[]
            for rn,rw,rv in fields(v):
                if rn==2:
                    rv=8
                if rn==3:
                    # First eight encoded coefficients from each exact modulus.
                    assert len(rv)==4096*(41+42)//8
                    rv=rv[:41]+rv[4096*41//8:4096*41//8+42]
                poly.append((rn,rw,rv))
            v=pack(poly)
        result.append((n,w,v))
    return pack(result)


def run(name, command, expected):
    argv=[str(BINARY.resolve())]+[str(x) for x in command]
    p=subprocess.run(argv,capture_output=True,text=True,timeout=30)
    records.append({'name':name,'command':argv,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    assert p.returncode==expected,(name,p.returncode,p.stdout,p.stderr)
    return json.loads(p.stdout) if p.returncode==0 else None


honest=(RUNTIME/'a1.ct').read_bytes()
short=RUNTIME/'coherent_short_degree.ct'
short.write_bytes(payload_blob(honest,short_degree_ct(honest[81:])))
run('short_degree_strict',['inspect','--ct',short],2)
run('short_degree_normalize',['normalize','--ct',short,'--out',RUNTIME/'short_normalized.ct'],2)
pk=(RUNTIME/'a.pk').read_bytes()
pk_fields=fields(pk[81:])
assert len(pk_fields)==1 and pk_fields[0][:2]==(1,2)
inner=pk_fields[0][2]
bad_payload=pack([(1,2,short_degree_ct(inner))])
bad_pk=payload_blob(pk[:41]+hashlib.sha256(bad_payload).digest()+pk[73:],bad_payload)
bad_pk_path=RUNTIME/'coherent_short_degree.pk'
bad_pk_path.write_bytes(bad_pk)
run('short_degree_public_key',['issuer-encrypt','--pk',bad_pk_path,
    '--vector',RUNTIME/'public_a.json','--out',RUNTIME/'short_pk_encrypted.ct'],2)

# The public-key payload contains a real seeded encryption of zero. Exposing its
# already public ciphertext tests seeded normalization without making another key.
seeded=RUNTIME/'public_seeded_zero.ct'
seeded.write_bytes(payload_blob(honest,inner))
run('seeded_not_canonical_full',['inspect','--ct',seeded],2)
normal=RUNTIME/'public_seeded_zero_full.ct'
run('seeded_normalize',['normalize','--ct',seeded,'--out',normal],0)
run('normalized_is_canonical',['inspect','--ct',normal],0)
score=run('normalized_zero_read',['reader-decrypt','--sk',RUNTIME/'a.sk','--ct',normal],0)
assert score['signed_score']==0

# Canonical ciphertext form is not an authorization or integrity proof: change
# a power-basis coefficient in the serialized body, keeping all syntax canonical.
changed=[]
for i,(n,w,v) in enumerate(fields(honest[81:])):
    if i==0 and n==1:
        rows=[]
        for rn,rw,rv in fields(v):
            if rn==3:rv=bytes([rv[0]^1])+rv[1:]
            rows.append((rn,rw,rv))
        v=pack(rows)
    changed.append((n,w,v))
tampered=RUNTIME/'canonical_coefficient_mutation.ct'
tampered.write_bytes(payload_blob(honest,pack(changed)))
run('canonical_coefficient_mutation_passes_syntax',['inspect','--ct',tampered],0)

out={'classification':'EXECUTED codec domain checks; intentionally separates syntax from cryptographic provenance',
     'command':[sys.executable,str(Path(__file__).resolve())],
     'source_sha256':hashlib.sha256((RUNTIME/'main.rs').read_bytes()).hexdigest(),
     'binary_sha256':hashlib.sha256(BINARY.read_bytes()).hexdigest(),
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'short_degree_CT_and_PK_rejected':True,'seeded_normalization_honest_zero':True,
     'canonical_ciphertext_mutation_is_syntactically_valid':True,
     'records':records,
     'scope':'Full-key helper is a trusted arithmetic oracle. Journal must bind and verify admitted/proposed full ciphertexts; inspect alone is not integrity.'}
(HERE/'codec_domain_review_001.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
