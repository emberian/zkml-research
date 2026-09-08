#!/usr/bin/env python3
"""Public bytes only: freeze execution inputs or compare them without executing crypto."""
import hashlib,json,pathlib,sys,datetime
r=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
if sys.argv[1]=='freeze':
 owned=[r/x for x in ['Cargo.toml','Cargo.lock','src/main.rs','src/prior_rotation.rs','Compiler/TfheSignedDecomposition.lean','Compiler/TfheCmuxDecomposition.lean','EmitTfheCmuxDecomposition.lean','run_record.py','pin.py','target/release/tfhe-bootstrap-decomposition-proof','build/Compiler/TfheSignedDecomposition.olean','build/Compiler/TfheCmuxDecomposition.olean']]
 owned+=list((r/'fixtures/normal_001').glob('*'))+list((r/'artifacts').glob('*'))
 prev=json.loads((r.parent/'bootstrap_rotation_successor/execution_pins.json').read_text())
 deps=[pathlib.Path(x['path']) for x in prev['read_only_dependencies']]
 deps+=[r.parent/'bootstrap_rotation_successor'/x for x in ['MANIFEST.json','execution_pins.json','src/main.rs','Compiler/TfheInitialRotation.lean','build/Compiler/TfheInitialRotation.olean','artifacts/template_ir2.json','results/proof001/proof.bin']]
 deps+=[pathlib.Path('/Users/ember/dev/minidregg')/x for x in ['Compiler/PredCompile.lean','.lake/build/lib/lean/Compiler/PredCompile.olean']]
 tfhe=pathlib.Path('/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/tfhe-1.6.3/src/core_crypto')
 deps += [pathlib.Path('/Users/ember/dev/zkml-research/research/learn_infer_only/formal/integer_certificate_emission/optimization/Compiler/AirSimplify.lean'),(r/'build/Compiler/AirSimplify.olean').resolve()]
 deps+=[tfhe/x for x in ['commons/math/decomposition/decomposer.rs','commons/math/decomposition/iter.rs','commons/numeric/unsigned.rs','fft_impl/fft64/math/decomposition.rs']]
 old=(r.parent/'bootstrap_rotation_successor/src/main.rs').read_bytes();new=(r/'src/prior_rotation.rs').read_bytes()
 assert new.startswith(old)
 out={'schema':'tfhe-cmux-decomposition-input-pins-v1','recorded_after_proof_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'owned':[rec(p) for p in owned],'read_only_dependencies':[rec(p) for p in dict.fromkeys(deps)],'prior_consumer_unchanged_prefix_bytes':len(old),'prior_consumer_prefix_sha256':hashlib.sha256(old).hexdigest()}
 (r/'execution_pins.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'sha256':sha(r/'execution_pins.json'),'owned':len(owned),'dependencies':len(out['read_only_dependencies'])}))
elif sys.argv[1]=='check':
 pins=json.loads((r/'execution_pins.json').read_text());rows=pins['owned']+pins['read_only_dependencies']
 mismatches=[x for x in rows if rec(pathlib.Path(x['path']))!=x]
 old=(r.parent/'bootstrap_rotation_successor/src/main.rs').read_bytes();prefix=(r/'src/prior_rotation.rs').read_bytes()[:len(old)]
 assert prefix==old;assert not mismatches,mismatches
 r0=r.parent/'bootstrap_rotation_successor';m=json.loads((r0/'MANIFEST.json').read_text())
 # Original manifests are pinned above; exact dependency inputs are individually rehashed.
 out={'claim':'EXECUTED public-only input integrity comparison','execution_pins_sha256':sha(r/'execution_pins.json'),'checked_files':len(rows),'all_unchanged':True,'prior_consumer_prefix_unchanged':True}
 (r/'results/integrity.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
else:raise SystemExit('freeze | check')
