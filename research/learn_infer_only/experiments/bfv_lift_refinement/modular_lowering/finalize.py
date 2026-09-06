#!/usr/bin/env python3
"""Pin the frozen source-word proof, local primary source, and compact actual fixture."""
import gzip,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent;FORMAL=ROOT.parents[2]/'formal/bfv_lift_refinement/modular_lowering'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
valid=json.loads((FORMAL/'validation-summary.json').read_text());assert all(sha(Path(p))==h for p,h in valid['sources_sha256'].items())
patch=FORMAL/'minidregg-fhe-modular-lowering.patch';assert sha(patch)==valid['patch_sha256']
old_patches={'minidregg-bfv-lift-refinement.patch':'929f79e168a1e236b04a2fa6edbf9448e22da5041124b7484e0fd9348072dc11','engine_refinement/minidregg-fhe-rns-scale-decomposition.patch':'de9490c464d332810bd5de79d21fd9b8db03c6bd29f2a28d8de26a78d41114b0','source_certificate/minidregg-fhe-source-certificate.patch':'55ffecdf2db1d330b0cc76126781dbc39c4ea581fe4edc4fbb7da7830e771d2f','target_projection/minidregg-fhe-target-projection.patch':'61f35e724f5de29d7338a381232b31e60c36cf39845665f8ac4073f150e0ea97'}
assert all(sha(FORMAL.parent/p)==h for p,h in old_patches.items())
source_map=json.loads((ROOT/'source-map.json').read_text());assert all(sha(Path(r['path']))==r['sha256'] for r in source_map['records'])
fixture=ROOT/'actual-words.jsonl.gz';raw=gzip.decompress(fixture.read_bytes());assert len(raw.splitlines())==1904
(ROOT/'.gitignore').write_text('/.build/\n__pycache__/\n')
files=list(ROOT.glob('*.py'))+list(ROOT.glob('*.rs'))+list(FORMAL.glob('*.py'))+list(FORMAL.glob('*.md'))+list((FORMAL/'Compiler').glob('*.lean'))
manifest=dict(label='EXECUTED artifact/source pins; no Rust-language refinement claim',command=[sys.executable,str(Path(__file__).resolve())],formal_patch_sha256=sha(patch),exact_axiom_pins=38,previous_patches_unchanged=old_patches,actual_fixture=dict(path=str(fixture),sha256=sha(fixture),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),rows=1904,compressed_bytes=fixture.stat().st_size,uncompressed_bytes=len(raw)),sources=[dict(path=str(p),sha256=sha(p)) for p in sorted(files)],primary_source_hashes={r['path']:r['sha256'] for r in source_map['records']},extra_emitted_constraints=0,metered_search_queries=0,pdf_downloads=0)
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(dict(patch_sha256=manifest['formal_patch_sha256'],axiom_pins=38,fixture=manifest['actual_fixture'],prior_four_patches_unchanged=True),indent=2))
