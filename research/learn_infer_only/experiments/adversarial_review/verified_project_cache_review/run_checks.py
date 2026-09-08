#!/usr/bin/env python3
"""Independent rerun of saved synthetic file tests in this review's scratch."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / 'verified_project_cache_implementation'
spec = importlib.util.spec_from_file_location('saved_cache_tests', AUTHOR / 'test_verified_project_cache.py')
tests = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tests)
with tempfile.TemporaryDirectory(prefix='synthetic-', dir=HERE) as scratch:
    tests.cache.BUILD_ROOT = Path(scratch).resolve()
    suite = unittest.defaultTestLoader.loadTestsFromModule(tests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    summary = {'status': 'PASS' if result.wasSuccessful() else 'FAIL',
               'tests': result.testsRun, 'failures': len(result.failures), 'errors': len(result.errors),
               'lean_builds': 0, 'actual_exports': 0, 'overlay_installations': 0,
               'scope': 'Synthetic public file tests only; redirected object scratch owned by this review.'}
    (HERE / 'results.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    sys.exit(0 if result.wasSuccessful() else 1)
