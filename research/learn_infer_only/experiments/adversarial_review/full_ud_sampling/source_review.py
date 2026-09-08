#!/usr/bin/env python3
"""Read-only frozen-source, patch-byte and declaration-census checks."""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
FORMAL=REPO/'research/proof_frontier/2026-09-08/formal'
SAMPLE=FORMAL/'full_ud_sampling_budget'
BABY=FORMAL/'full_ud_babybear'
MAIN=Path('/Users/ember/dev/minidregg')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def save(name,x):
    (HERE/name).write_text(json.dumps(x,indent=2)+'\n')

spec=importlib.util.spec_from_file_location('integration_census',
    REPO/'research/learn_infer_only/experiments/integration/check_all_formal.py')
census=importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
checks={}
cases=[('Selvage.FullUDSamplingBudget',SAMPLE/'FullUDSamplingBudget.lean',
        SAMPLE/'full-ud-sampling-budget.patch',
        'a4bd35ea6f1e1ada77a20a3c8634b7dd7ac89aa0231be3a7db464955c5761c04',
        '589ae51ff846889eb5403b1b415755a06a1fd4865466e22fa63902addd9f8852'),
       ('Selvage.BabyBearFullUD',BABY/'BabyBearFullUD.lean',
        BABY/'babybear-full-ud.patch',
        '03f80a278b95dfb767eaf6657ee63b26a643900df5d0cbfb4c1a579399314978',
        'fa8a815069f628ef4ae34a1eda2c91989fd3af87c55ccc8f4056aa78d9bc6e25')]
pins={}
for module,source,patch,source_hash,patch_hash in cases:
    assert sha(source)==source_hash and sha(patch)==patch_hash
    sections=patch.read_text().split('diff --git ')[1:]
    assert len(sections)==1
    lines=sections[0].splitlines(keepends=True)
    assert 'new file mode 100644\n' in lines and '--- /dev/null\n' in lines
    dest=next(x.strip()[6:] for x in lines if x.startswith('+++ b/'))
    assert dest==module.replace('.','/')+'.lean'
    start=next(i for i,x in enumerate(lines) if x.startswith('@@'))
    assert all(x.startswith('+') for x in lines[start+1:])
    content=''.join(x[1:] for x in lines[start+1:]).encode()
    assert content==source.read_bytes()
    pins[module]=census.census(source.read_text(),module)
    checks[module]=dict(source=str(source),source_sha256=source_hash,
        patch=str(patch),patch_sha256=patch_hash,exact_patch_source=True,
        declarations=pins[module]['theorem_count'],pins=pins[module]['pin_count'])
assert checks['Selvage.FullUDSamplingBudget']['declarations']==25
assert checks['Selvage.BabyBearFullUD']['declarations']==12
save('census.json',pins)

sm=json.loads((SAMPLE/'manifest.json').read_text())
bp=json.loads((BABY/'provenance.json').read_text())
assert sm['frozen'] and sm['checked']['exit_code']==0 and sm['checked']['source_unchanged']
assert sm['source_sha256']==checks['Selvage.FullUDSamplingBudget']['source_sha256']
assert bp['check']['exit_code']==0 and bp['check']['source_unchanged']
assert bp['source_sha256']==checks['Selvage.BabyBearFullUD']['source_sha256']
assert sha(MAIN/'Selvage/BabyBearExt4.lean')==bp['field_source_sha256']
assert sha(FORMAL/'full_ud/manifest.json')==bp['core_manifest_sha256']
assert (SAMPLE/'logs/final-pinned.log').read_text()==''
assert (BABY/'logs/bridge-pins-01.log').read_text()==''
dependencies=json.loads((SAMPLE/'dependency-pins.json').read_text())
dep_results=[]
for item in dependencies['direct_and_used_sources']:
    p=Path(item['path'])
    assert sha(p)==item['sha256']
    local=Path(*p.parts[-2:])
    olean=p.parent.parent/'.lake/build/lib/lean'/local.with_suffix('.olean')
    assert sha(olean)==item['olean_sha256']
    # Existing companion definitions must agree with the checked clone.
    companion=MAIN/local
    if companion.exists():
        assert companion.read_bytes()==p.read_bytes()
    dep_results.append(dict(source=str(p),source_sha256=sha(p),
                            olean=str(olean),olean_sha256=sha(olean),
                            existing_main_equal=companion.exists()))

audited_paths=[MAIN/'Selvage/HalfThresholdFriCoherent.lean',
    MAIN/'Selvage/HalfThresholdFriQuery.lean',MAIN/'Selvage/HalfThresholdFriTranscript.lean',
    MAIN/'Selvage/Commitment.lean',MAIN/'Selvage/BabyBearExt4.lean',
    MAIN/'Selvage/ReedSolomon.lean',MAIN/'Selvage/CorrelatedAgreement.lean',
    MAIN/'Selvage/Proximity.lean',MAIN/'Selvage/ProximityGapUD.lean',
    MAIN/'Assurance/ErrorBudget.lean',MAIN/'Assurance/ErrorBudget120.lean',
    MAIN/'Assurance/MixedFieldBudget.lean',MAIN/'Assurance/TwoRegimeQueryBudget.lean',
    SAMPLE/'manifest.json',SAMPLE/'README.md',SAMPLE/'dependency-pins.json',
    BABY/'provenance.json',BABY/'README.md',FORMAL/'full_ud/manifest.json']
parameter=FORMAL.parent/'parameter_delta'
audited_paths += [parameter/f for f in ['ANALYSIS.md','SOURCE_MAP.md','derive.py','results.json','source-pins.json']]
result=dict(status='PASS',checks=checks,dependency_object_pins=dep_results,
    read_source_pins=[dict(path=str(p),sha256=sha(p)) for p in audited_paths],
    producer_checks_only=True,new_lean_builds=0,external_queries=0,
    census_instrument_sha256=sha(Path(census.__file__)),script_sha256=sha(Path(__file__)))
save('source_verification.json',result)
print(json.dumps(dict(status='PASS',source_modules=2,theorems=37,pins=37,
    checked_dependency_source_and_object_pairs=len(dep_results),new_lean_builds=0,
    hashes={k:v['source_sha256'] for k,v in checks.items()}),indent=2))
