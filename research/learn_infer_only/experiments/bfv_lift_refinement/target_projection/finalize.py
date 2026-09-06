#!/usr/bin/env python3
"""Compact deterministic fixtures and pin the validated target projection package."""
import gzip,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent;FORMAL=ROOT.parents[2]/'formal/bfv_lift_refinement/target_projection'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fixtures=[]
for name in ['optimized-descriptor.json','retained-inputs.json','captured-source-variables.json']:
 p=ROOT/name;raw=p.read_bytes();out=p.with_suffix(p.suffix+'.gz');out.write_bytes(gzip.compress(raw,mtime=0));assert gzip.decompress(out.read_bytes())==raw
 fixtures.append(dict(path=str(out),sha256=sha(out),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),compressed_bytes=out.stat().st_size,uncompressed_bytes=len(raw)))
(ROOT/'.gitignore').write_text('/optimized-descriptor.json\n/retained-inputs.json\n/captured-source-variables.json\n__pycache__/\n')
valid=json.loads((FORMAL/'validation-summary.json').read_text());assert all(sha(Path(p))==h for p,h in valid['sources_sha256'].items())
assert sha(FORMAL/'minidregg-fhe-target-projection.patch')==valid['patch_sha256']
c=json.loads((ROOT/'check-results.json').read_text());old=json.loads((ROOT.parent/'source_certificate/check-results.json').read_text())
files=list(ROOT.glob('*.py'))+list(FORMAL.glob('*.py'))+list(FORMAL.glob('*.md'))+list((FORMAL/'Compiler').glob('*.lean'))
combined=dict(gates=c['optimized_gates']+old['optimized_gates'],variables=c['variables']+old['variables'],zero_checks=c['zero_checks']+old['optimized_zero_checks'])
manifest=dict(label='EXECUTED artifact pins and DERIVED two-descriptor arithmetic cost sums',command=[sys.executable,str(Path(__file__).resolve())],formal_patch_sha256=valid['patch_sha256'],exact_axiom_pins=22,fixtures=fixtures,sources=[dict(path=str(p),sha256=sha(p)) for p in sorted(files)],combined_source_and_target=combined,naive_full_tensor_repetition={k:v*3*4096 for k,v in combined.items()},cost_scope='Two separate descriptor arithmetic counts; excludes external equality checks, source provenance/convolution/NTT, commitment/proof overhead. Repetition is neither lower bound nor latency. No charge to the separate sliding-window Learn bill.',metered_search_queries=0,pdf_downloads=0)
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(dict(fixtures=fixtures,combined=combined),indent=2))
