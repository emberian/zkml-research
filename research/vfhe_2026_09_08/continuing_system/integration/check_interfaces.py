#!/usr/bin/env python3
"""Import the proposed app in isolation and check real engine pins; no cryptography."""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
APP = HERE.parent
RESEARCH = APP.parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    before = {name: sha(APP / name) for name in ('core.py', 'backend.py')}
    for path in (HERE / 'proposed').glob('*.py'):
        compile(path.read_text(), str(path), 'exec')
    with tempfile.TemporaryDirectory(prefix='continuing-engine-import-') as tmp:
        root = Path(tmp)
        for child in RESEARCH.iterdir():
            if child.name != 'continuing_system':
                (root / child.name).symlink_to(child, target_is_directory=child.is_dir())
        app = root / 'continuing_system'; app.mkdir()
        for name in ('core.py', 'backend.py', 'engines.py'):
            shutil.copyfile(HERE / 'proposed' / name, app / name)
        (app / 'linear').symlink_to(APP / 'linear', target_is_directory=True)
        sys.dont_write_bytecode = True
        spec = importlib.util.spec_from_file_location('continuing_engine_proposal_check', app / 'core.py')
        core = importlib.util.module_from_spec(spec); spec.loader.exec_module(core)
        issuer = core.backend.Backend()
        results = []
        for score, proof in (('squared', 'compact'), ('linear', 'compact'), ('linear', 'matched')):
            engine = core.engines.Engine.new(core.backend, issuer, score, proof)
            reopened = core.engines.Engine(core.backend, issuer, engine.descriptor)
            assert reopened.info == engine.info
            if score == 'squared':
                assert engine.descriptor is None
                assert core.engines.policy(core.POLICY, None) is core.POLICY
            else:
                assert engine.output_key == 'dot_ciphertext_sha256'
                assert engine.info['sum_key'] == 'sum_dot' and not engine.needs_capture
            results.append({'engine': score + '/' + proof, 'pins_checked': True, **engine.info})
        try:
            core.engines.Engine.new(core.backend, issuer, 'squared', 'matched')
        except ValueError:
            pass
        else:
            raise AssertionError('unsupported score/backend combination accepted')
        help_result = subprocess.run([sys.executable, app / 'core.py', 'init', '--help'],
                                     text=True, capture_output=True, check=True)
        assert '--score' in help_result.stdout and '--proof-backend' in help_result.stdout
        assert 'common' not in sys.modules and 'pipeline' not in sys.modules
        legacy_genesis = APP / 'runtime/lifecycle/resident/journal/genesis.json'
        legacy = None
        if legacy_genesis.exists():
            genesis = json.loads(legacy_genesis.read_text())
            assert genesis['policy'] == core.POLICY and 'engine' not in genesis
            old = core.engines.Engine(core.backend, core.backend.Backend(genesis['backend']))
            assert old.info == core.metadata(legacy_genesis.parents[1])
            legacy = {'genesis_sha256': sha(legacy_genesis), 'policy_unchanged': True,
                      'legacy_backend_pins_checked': True, 'journal_opened': False}
    assert before == {name: sha(APP / name) for name in before}
    print(json.dumps({'scope': 'syntax/import, actual profile byte pins, CLI flags and legacy genesis metadata only',
                      'crypto_launched': False, 'live_source_unchanged': before,
                      'engines': results, 'legacy_genesis': legacy}, indent=2))


if __name__ == '__main__':
    main()
