"""Pin read-only sources and finite public controls; no formal or crypto execution."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[2]
AUTHOR=HERE.parent/'formal/full_ud_commitment_timing'
REVIEW=RESEARCH/'learn_infer_only/experiments/adversarial_review/full_ud_root_resolution'
VCV=Path('/Users/ember/src/VCV-io-2026-09/VCVio/CryptoFoundations/MerkleTree')
P3=Path('/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7')
MIRROR=Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
def pin(path):
    data=path.read_bytes()
    return {'path':str(path),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}

author=json.loads((AUTHOR/'manifest.json').read_text())
for row in author['modules']:
    assert pin(AUTHOR/'src'/row['path'])['sha256']==row['sha256']
evidence=json.loads((AUTHOR/'source-evidence.json').read_text())
for name,row in evidence['sources'].items():
    assert pin(Path(name))['sha256']==row['sha256']

frozen=[AUTHOR/name for name in ['manifest.json','source-evidence.json','README.md',
                                 'full-ud-commitment-timing.patch']]
frozen += [AUTHOR/'src'/row['path'] for row in author['modules']]
frozen += [REVIEW/name for name in ['REPORT.md','manifest.json','source_pins.json']]
sources=[Path(name) for name in evidence['sources']]
sources += [Path('/Users/ember/dev/breadstuffs/Cargo.lock'),P3/'merkle-tree/src/mmcs.rs']
sources += [VCV/name for name in ['Extractor.lean','Inductive/Defs.lean',
            'MultiExtractability/Game.lean','MultiExtractability/Sequential.lean',
            'MultiExtractability/Stateful.lean','MultiExtractability/StrongBound.lean']]
sources += [MIRROR/'2016/116.pdf',MIRROR/'2023/1071.pdf']
excluded={'MANIFEST.json','pin_artifacts.log'}
owned=[p for p in sorted(HERE.iterdir()) if p.is_file() and p.name not in excluded
       and not p.name.startswith('source_')]
out={'scope':'Source/math audit; no formalization or cryptographic attack execution.',
     'vcvio_commit':'ffd0ca198fe6e640c0dd7f0f9c599943caacbf64',
     'p3_commit':'82cfad73cd734d37a0d51953094f970c531817ec',
     'checked_frozen_inputs':[pin(p) for p in frozen],
     'primary_sources':[pin(p) for p in sources],
     'owned_artifacts':[pin(p) for p in owned]}
text=json.dumps(out,indent=2)+'\n'
(HERE/'MANIFEST.json').write_text(text)
print(text,end='')
