"""Seal named public source/math review artifacts only."""
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
EST=ROOT/'research/learn_infer_only/experiments/he_closure_costs/estimator'


def pin(path):
    path=Path(path).resolve()
    assert not {'.private','private','signer_route','verified_route'}.intersection(path.parts)
    if 'runtime' in path.parts:
        assert path.is_relative_to(EST/'runtime/pinned-estimator') or path==EST/'runtime/estimator-src.tar' or path==EST/'runtime/sage/lib/python3.12/site-packages/sage/rings/integer.pyx'
    assert path.is_relative_to(ROOT) or path.is_relative_to('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
    data=path.read_bytes()
    return {'path':str(path),'bytes':len(data),'sha256':sha256(data).hexdigest()}


inputs=json.loads((HERE/'INPUTS.json').read_text())
results=json.loads((HERE/'results.json').read_text())
assert results['status']=='PASS'
assert (HERE/'stdout.txt').read_bytes()==(HERE/'results.json').read_bytes()
assert (HERE/'stderr.txt').read_bytes()==b''
for expected in inputs['frozen_public_artifacts']:
    assert pin(expected['path'])==expected
visual={'scope':'Primary HYL Theorem2 p26 independently rendered and visually read; prior HYL/MP/GPV reads reused.',
        'HYL_PDF':pin('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/1613.pdf'),
        'HYL_page26':pin(HERE/'renders/hyl26.png'),
        'prior_HYL_MP_GPV_access':pin(HERE.parent/'smudged_fixed_coordinate/visual_access.json')}
(HERE/'visual_access.json').write_text(json.dumps(visual,indent=2)+'\n')
owned=['.gitignore','REPORT.md','INPUTS.json','check.py','results.json','stdout.txt','stderr.txt','seal.py','visual_access.json']
manifest={'scope':'Independent source/math and retained estimator-output review. No reviewer estimator, Sage, lattice or crypto execution.',
          'frozen_public_artifacts':inputs['frozen_public_artifacts'],
          'owned_artifacts':[pin(HERE/f) for f in owned],
          'author_artifacts_unchanged':True,
          'command':'python3 research/learn_infer_only/experiments/adversarial_review/smudged_hardness/seal.py'}
(HERE/'review_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'PASS','report':pin(HERE/'REPORT.md'),
                  'review_manifest':pin(HERE/'review_manifest.json'),
                  'frozen_public_files_unchanged':len(inputs['frozen_public_artifacts'])},indent=2))
