#!/usr/bin/env python3
"""Read frozen evidence and replay only an additive text patch in an owned directory."""
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / 'efficient_root_opening'
EXPECTED = {
    'manifest.json': '9b18d46259b37570d073999589ed06daee9e1cbbe57dbed232c2dc8c24a9b7ef',
    'efficient-root-opening.patch': 'c1d7aebabd8d755192d38c3628b266e1351a3703b03fa66f0dd042fef645d5b2',
    'src/Selvage/EfficientRootOpening.lean': 'defd19242e66118333d477cd14bcb1b108c4d517b1e55861dee66f35647dafe6',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    for name, digest in EXPECTED.items():
        assert sha(AUTHOR / name) == digest, name
    manifest = json.loads((AUTHOR / 'manifest.json').read_text())
    for name, digest in manifest['files'].items():
        assert sha(AUTHOR / name) == digest, name
    evidence = json.loads((AUTHOR / 'source-evidence.json').read_text())
    assert evidence['dependencies'] == manifest['dependencies']
    for dep in manifest['dependencies']:
        assert sha(Path(dep['path'])) == dep['sha256'], dep['path']
        local = Path(manifest['checkout']) / 'Selvage' / Path(dep['path']).name
        assert sha(local) == dep['sha256'], str(local)
    for name, digest in evidence['frozen_prior_audit_and_review'].items():
        assert sha(Path(name)) == digest, name
    checker = HERE.parents[3] / 'learn_infer_only/experiments/integration/check_all_formal.py'
    assert sha(checker) == manifest['root_census_script_sha256']
    source = AUTHOR / 'src/Selvage/EfficientRootOpening.lean'
    text = source.read_text()
    code = re.sub(r'/\-.*?\-/|--[^\n]*', '', text, flags=re.S)
    assert not re.search(r'\b(sorry|sorryAx|axiom|admit|unsafe|native_decide|noncomputable)\b', code)
    assert 'Classical.choose' not in code
    assert re.findall(r'^import (.+)$', code, re.M) == ['Selvage.BinaryMerkle', 'Selvage.OracleLogExtraction']
    stack, names = [], []
    for line in code.splitlines():
        if line.startswith('namespace '):
            stack.append(line[len('namespace '):].strip())
        elif line.startswith('end '):
            assert stack.pop() == line[len('end '):].strip()
        elif line.startswith('theorem '):
            names.append('.'.join(stack + [line.split()[1]]))
    assert not stack
    pins = re.findall(r"/-- info: '([^']+)' depends on axioms: \[([^\]]*)\] -/\s*#guard_msgs \(whitespace := lax\) in #print axioms ([\w.]+)", text)
    assert names == [n for n, _, _ in pins] == [requested for _, _, requested in pins]
    assert len(names) == 20
    assert names == json.loads((AUTHOR / 'declaration-names.json').read_text())
    census = json.loads((AUTHOR / 'integration_census.json').read_text())
    assert names == [x['qualified_name'] for x in census['qualified_declarations']]
    assert [(n, a.split(', ')) for n, a, _ in pins] == [(x['theorem'], x['axioms']) for x in census['pins']]
    for _, axioms, _ in pins:
        assert set(axioms.split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'}
    final = json.loads((AUTHOR / 'logs/final-freeze.json').read_text())
    assert final['exit_code'] == 0 and final['source_unchanged']
    assert final['source_sha256'] == sha(source)
    assert not (AUTHOR / 'logs/final-freeze.log').read_bytes()
    assert manifest['modules'][0]['check'] == final
    assert len(text.splitlines()) == manifest['modules'][0]['lines'] == 412
    patch = AUTHOR / 'efficient-root-opening.patch'
    assert re.findall(r'^\+\+\+ b/(.+)$', patch.read_text(), re.M) == ['Selvage/EfficientRootOpening.lean']
    commands = []
    with tempfile.TemporaryDirectory(dir=HERE, prefix='patch_') as tmp:
        for args in (['git', 'init', '-q'], ['git', 'apply', '--check', str(patch)], ['git', 'apply', str(patch)]):
            r = subprocess.run(args, cwd=tmp, capture_output=True, text=True)
            commands.append(dict(command=args, cwd=tmp, exit_code=r.returncode,
                                 stdout=r.stdout, stderr=r.stderr))
            assert r.returncode == 0, commands[-1]
        assert (Path(tmp) / 'Selvage/EfficientRootOpening.lean').read_bytes() == source.read_bytes()
    result = dict(expected_freeze=EXPECTED, artifact_pins_checked=len(manifest['files']),
                  dependency_pins_checked=len(manifest['dependencies']),
                  prior_audit_pins_checked=len(evidence['frozen_prior_audit_and_review']),
                  root_census_script_pin_matches=True, theorem_pins=20,
                  exact_patch_replay=True, added_module_only=True, umbrella_import_added=False,
                  final_guard_record_matches=True, final_guard_log_empty=True,
                  all_checks_passed=True, new_lean_runs=0, new_crypto_runs=0,
                  patch_commands=commands)
    (HERE / 'VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n')
    (HERE / 'INPUTS.json').write_text(json.dumps(dict(freeze=EXPECTED,
       artifact_pins=manifest['files'], dependencies=manifest['dependencies'],
       prior_audit_pins=evidence['frozen_prior_audit_and_review'],
       root_census_script_sha256=manifest['root_census_script_sha256']), indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'patch_commands'}, indent=2))


if __name__ == '__main__':
    main()
