#!/usr/bin/env python3
"""Retain deterministic compact fixtures and a final provenance/cost manifest."""
import gzip,hashlib,json,platform,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent;FORMAL=ROOT.parents[2]/'formal/bfv_lift_refinement/source_certificate'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fixtures=[]
for name in ['optimized-descriptor.json','retained-inputs.json']:
 p=ROOT/name;payload=p.read_bytes();out=p.with_suffix(p.suffix+'.gz');out.write_bytes(gzip.compress(payload,mtime=0));assert gzip.decompress(out.read_bytes())==payload
 fixtures.append(dict(path=str(out),sha256=sha(out),uncompressed_sha256=hashlib.sha256(payload).hexdigest(),compressed_bytes=out.stat().st_size,uncompressed_bytes=len(payload)))
(ROOT/'.gitignore').write_text('/optimized-descriptor.json\n/retained-inputs.json\n__pycache__/\n')
check=json.loads((ROOT/'check-results.json').read_text());validation=json.loads((FORMAL/'validation-summary.json').read_text())
files=list(ROOT.glob('*.py'))+list(FORMAL.glob('*.py'))+list((FORMAL/'Compiler').glob('*.lean'))
manifest=dict(label='EXECUTED final source certificate artifact pins and DERIVED naive repetition cost',command=[sys.executable,str(Path(__file__).resolve())],python=sys.version,platform=platform.platform(),fixtures=fixtures,sources=[dict(path=str(p),sha256=sha(p)) for p in sorted(files)],formal_patch_sha256=validation['patch_sha256'],formal_total_exact_axiom_pins=validation['total_pins'],naive_full_tensor=dict(coefficients=3*4096,optimized_gates=check['optimized_gates']*3*4096,variables=check['variables']*3*4096,zero_checks=check['optimized_zero_checks']*3*4096,label='Uniform independent coefficient repetition only; excludes convolution, provenance and proof overhead; not a lower bound or benchmark; no contribution to the separate sliding-window Learn bill'),metered_search_queries=0,pdf_downloads=0)
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(dict(fixtures=fixtures,naive_full_tensor=manifest['naive_full_tensor']),indent=2))
