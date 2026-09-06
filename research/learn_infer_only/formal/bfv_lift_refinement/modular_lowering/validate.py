#!/usr/bin/env python3
"""Fresh isolated compilation of the source-word arithmetic and entire frozen BFV chain.
Run through read-only minidregg lake env. Does not invoke concrete-checker kernel reduction.
"""
import difflib,hashlib,json,os,re,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;COMP=Path('/Users/ember/dev/minidregg');FORMAL=ROOT.parent.parent
SOURCE_MODS=['FheSourceCertificate','FheSourceCertificateLayout','FheSourceCertificateEmit','FheSourceCertificateOptimized','FheSourceCertificateVerifier','FheSourceCertificateWitness']
TARGET_MODS=['FheTargetProjection','FheTargetProjectionLayout','FheTargetProjectionEmit','FheTargetProjectionVerifier','FheTargetProjectionWitness']
MODS=['FheShoupWord','FheBarrettWord','FheRnsModularAccumulation','FheRnsSourceWord']
DEPS=[ROOT.parent/'Compiler/BFVScaleLiftRefinement.lean',ROOT.parent/'engine_refinement/Compiler/FheRnsScaleDecomposition.lean',FORMAL/'integer_certificate_emission/Compiler/IntegerCertificateEmission.lean',FORMAL/'integer_certificate_emission/optimization/Compiler/AirSimplify.lean']
DEPS += [ROOT.parent/'source_certificate/Compiler'/f'{m}.lean' for m in SOURCE_MODS]
DEPS += [ROOT.parent/'target_projection/Compiler'/f'{m}.lean' for m in TARGET_MODS]
records=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd=COMP,env=None):
 start=time.monotonic();r=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,text=True,capture_output=True)
 records.append(dict(command=list(map(str,cmd)),cwd=str(cwd),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,elapsed_seconds=time.monotonic()-start));(ROOT/'validation.json').write_text(json.dumps(records,indent=2)+'\n')
 if r.returncode:raise SystemExit(r.stdout+r.stderr)
 return r.stdout
sources=[ROOT/'Compiler'/f'{m}.lean' for m in MODS];before={str(p):sha(p) for p in DEPS+sources}
assert before[str(DEPS[0])]=='1abe56f822ba911e85b0697887cf2317eecc990433f460dedc95a3085ccab2fd'
assert before[str(DEPS[1])]=='486e63dc09d79c10858f9b1e37cbf6b7a5b63841c23e8cbb914cc0e2b8b49167'
pins={}
for p in sources:
 s=p.read_text();count=len(re.findall(r'^theorem ',s,re.M));assert count==s.count('#guard_msgs in');pins[p.stem]=count
 assert not re.search(r'^\s*(axiom|sorry|admit)\b|\b(native_decide|ofReduceBool)\b|^#eval',s,re.M)
assert sum(pins.values())==38
base=(COMP/'Compiler.lean').read_text();lines=base.splitlines(True);i=next(i for i,l in enumerate(lines) if l.startswith('import Compiler.BfvProofController'))
lines.insert(i+1,'import Compiler.FheRnsSourceWord  -- pinned source-word arithmetic; Rust arrays/NTT/provenance remain open\n');new=''.join(lines)
patch=''.join(difflib.unified_diff(base.splitlines(True),new.splitlines(True),fromfile='a/Compiler.lean',tofile='b/Compiler.lean'))
for p in sources:patch+=''.join(difflib.unified_diff([],p.read_text().splitlines(True),fromfile='/dev/null',tofile='b/Compiler/'+p.name))
patchpath=ROOT/'minidregg-fhe-modular-lowering.patch';patchpath.write_text(patch)
run(['git','rev-parse','HEAD']);run(['lean','--version'])
with tempfile.TemporaryDirectory(prefix='.validation-',dir=ROOT) as td:
 temp=Path(td);(temp/'Compiler').mkdir()
 for p in (COMP/'.lake/build/lib/lean/Compiler').iterdir():(temp/'Compiler'/p.name).symlink_to(p)
 env=os.environ.copy();env['LEAN_PATH']=str(temp)+':'+env['LEAN_PATH']
 for source in DEPS+sources:
  out=temp/'Compiler'/source.with_suffix('.olean').name
  if out.is_symlink():out.unlink()
  run(['lean','-o',out,source],source.parent.parent,env)
 (temp/'Compiler.lean').write_text(new)
 run(['lean','-o',temp/'Compiler.olean',temp/'Compiler.lean'],temp,env)
run(['bash','scripts/check-import-boundary.sh'])
run(['git','apply','--check',patchpath])
run(['git','apply','--check',ROOT.parent/'minidregg-bfv-lift-refinement.patch',ROOT.parent/'engine_refinement/minidregg-fhe-rns-scale-decomposition.patch',ROOT.parent/'source_certificate/minidregg-fhe-source-certificate.patch',ROOT.parent/'target_projection/minidregg-fhe-target-projection.patch',patchpath])
assert before=={str(p):sha(p) for p in DEPS+sources},'Source changed during validation'
summary=dict(label='EXECUTED fresh isolated dependency chain plus side-effect-free Compiler umbrella; no full Minidregg build',exact_axiom_pins=pins,total_pins=38,sources_sha256=before,patch_sha256=sha(patchpath),all_commands_passed=True,not_claimed=['universal target emitted-layout completeness','whole concrete composite-checker kernel witness','committed-source/proof-protocol binding','Rust language/compiler/array semantics and NTT provenance','private release or master-read absence'])
(ROOT/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
