#!/usr/bin/env python3
"""[EXECUTED] Seal completed public QROM package; no research/control rerun."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PQ=HERE.parent

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()

expected={
 'ring_seed_security_successor/MANIFEST.json':'4323f8e2af04121974d711c8e164d86dd88872f9baf62ac4eb93ae4c21c29702',
 'ring_seed_security_successor/THEOREM.md':'9c333a923f95c00598b5582aed603a4db838da99850b476f2411f0af1d2fb87a',
 'ring_seed_security_successor/transcript_programming/KERNEL.md':'08af89d3facefae4d74553a56a683f9577fc0289481addc48572794e155be109',
 'ring_seed_security_successor/CHECKS.json':'522726e96e83115ee65f7642ca7d00933ea8f7f9f48739fc28aae7f358868152',
 'ring_seed_transport/MANIFEST.json':'2d61addad6b34a65486e9b68d25f7efb5292d97d6bd251e30879ad772764ef24',
 'ring_seed_transport/expansion/public_expander.py':'ab175083b2a38e382776f07a52a0d8b84e8886085f40f083117de273f0d0aba4',
 'ring_candidate/RING_REGULARITY.md':'2926555d5842bb71af7b16caec3eef512a9c7cfea99e877b862bcfea79d30e85',
 'finite_sampler/SPEC.md':'2fef91992b092f93f6023a02b0072008a2f4f46e5601ea8fd71eb8d0972e1576',
}
inputs={}
for rel,pin in expected.items():
    actual=sha(PQ/rel);assert actual==pin,(rel,actual)
    inputs[str(PQ/rel)]={'sha256':actual,'frozen_input_matched':True}
source=Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2020/1361.pdf')
assert sha(source)=='a185688a1ffd8352f433033545a73c9698539df92de517dbea29342c5fe56e53'
inputs[str(source)]={'sha256':sha(source),'source_scope':'Theorem1/Figure2,Theorem6 proof,AppendixA'}
child=HERE/'quantum_simulation/MANIFEST.json'
assert sha(child)=='27c2f8c0ff006c03fa41f68e6fdda4201b4e2b937b01a8233c63210d4c87e15a'
for row in json.loads(child.read_text())['external_primary_sources']:
    if row['path'].startswith('/Users/'):
        inputs[row['path']]={'sha256':row['sha256'],'source_hash_attributed_to_child_seal':True}
artifacts={str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*'))
           if p.is_file() and '__pycache__' not in p.parts and p!=HERE/'MANIFEST.json'}
out={'status':'COMPLETE','scope':'[DERIVED] Honest fixed-coalition QROM theorem conditional on exact QPT power-basis Ring-LWE and explicit resources/advice; no concrete SHAKE/security-bit claim',
     'artifacts':artifacts,'public_inputs':inputs,
     'actual_seed_bytes_each':32,'prequery_budget_each_stage':'2^64',
     'two_world_programming_bound':'2^-94 + 2^-191',
     'full_bound':'768 epsilon_QR + 2^-94 + 2^-168 + 2^-191',
     'unimplemented_seed_corollaries_bytes':[48,64],
     'search_counts_including_child':{'web_queries':4,'Scry_SQL':0,'web_opens':0,'PDF_downloads':0},
     'quantum_or_crypto_executions':0,'private_reads':0,
     'integration':'Root integration; no independent-review queue required'}
(HERE/'MANIFEST.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','artifacts':len(artifacts),'public_inputs':len(inputs),
                  'theorem_sha256':sha(HERE/'THEOREM.md'),'manifest_sha256':sha(HERE/'MANIFEST.json')}))
