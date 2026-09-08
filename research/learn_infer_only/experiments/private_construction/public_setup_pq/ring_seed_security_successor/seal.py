#!/usr/bin/env python3
"""[EXECUTED] Hash explicit public inputs and this successor's public files."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PQ=HERE.parent
MIRROR=Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for data in iter(lambda:f.read(1024*1024),b''): h.update(data)
    return h.hexdigest()

expected={
 'ring_seed_transport/MANIFEST.json':'2d61addad6b34a65486e9b68d25f7efb5292d97d6bd251e30879ad772764ef24',
 'ring_seed_transport/expansion/public_expander.py':'ab175083b2a38e382776f07a52a0d8b84e8886085f40f083117de273f0d0aba4',
 'ring_candidate/CANDIDATE.md':'5010b72b024aa7154504a7c0dd0de306fe0068b3af3b33b5026b444c510a0dc2',
 'ring_candidate/RING_REGULARITY.md':'2926555d5842bb71af7b16caec3eef512a9c7cfea99e877b862bcfea79d30e85',
 'finite_sampler/SPEC.md':'2fef91992b092f93f6023a02b0072008a2f4f46e5601ea8fd71eb8d0972e1576',
 'ring_implementation_fast/sampling/sampler.py':'5fcd4bc7fe3d2cb3c70911582b2a12aec23322ea69ed6d443e0abf1940e01de8',
 'ring_implementation_fast/sampling/proposal_screen.c':'cb295627adeedbcb62f26fdb5acc4ede4fb9de2673efd38d55c7e08601174ac4',
 'ring_implementation_fast/sampling/reference.py':'2258da232fb6a3459f58c9842f9560baef7796bacaedfd757a4ae27b37c033dd',
 'ring_implementation_fast/ring.py':'18c503120c8a2f44ade190ca9c68f5b4a6c7aca6e54c13210172788d6e54f567',
 'ring_candidate/extracts/2021-046.txt':'1c041f582042c6b811ec56c66e84d734c0cee36f7a7823c333b9360ab5fdcf2c',
 'ring_candidate/extracts/2013-293.txt':'bb8e859a3184bff5870150932861b46e4c29dcd354e3cdbea4dc98fc94dc5e56',
}
inputs={}
for rel,pin in expected.items():
    actual=sha(PQ/rel)
    assert actual==pin,(rel,actual,pin)
    inputs[str(PQ/rel)]={"sha256":actual,"expected_hash_matched":True}
for rel in ['ring_seed_transport/seed_transport.py','ring_candidate/hardness/GRID.json',
            'finite_sampler/MANIFEST.json','ring_transport/transport.py']:
    inputs[str(PQ/rel)]={"sha256":sha(PQ/rel)}
for rel,pin in {
 '2021/46.pdf':'8b5a43ee653081a0d7cf94bc7584e80ed60a6a525c41d15fdc61734ea7c6c20f',
 '2013/293.pdf':'6b22c0bca6f3234a3aaa769a42c106c1816b12edffef2332bf7835c78d3c21e0',
}.items():
    actual=sha(MIRROR/rel); assert actual==pin
    inputs[str(MIRROR/rel)]={"sha256":actual,"expected_hash_matched":True}
kernel=HERE/'transcript_programming/MANIFEST.json'
assert sha(kernel)=='bd749a5f6c211b27764bac9ef62bedf7cae250ad2dcce272e9e675b8a09173f6'
files={}
for path in sorted(HERE.rglob('*')):
    if not path.is_file() or '__pycache__' in path.parts or path==HERE/'MANIFEST.json':continue
    files[str(path.relative_to(HERE))]=sha(path)
out={"scope":"[DERIVED/EXECUTED] Classical programmable-ROM theorem and deterministic finite ledger, conditional on exact Ring-LWE; no concrete SHAKE/QROM/security-bit claim",
     "status":"COMPLETE","artifacts":files,"public_inputs":inputs,
     "search_counts":{"Scry_SQL":0,"web_searches":0,"web_opens":0,"PDF_downloads":0},
     "prohibited_operations_performed":[],
     "root_integration":"Root read theorem; no independent-review completion gate"}
(HERE/'MANIFEST.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({"status":"PASS","artifacts":len(files),"public_inputs":len(inputs),
                  "theorem_sha256":sha(HERE/'THEOREM.md'),
                  "manifest_sha256":sha(HERE/'MANIFEST.json')}))
