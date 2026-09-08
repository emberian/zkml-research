#!/usr/bin/env python3
"""File/provenance checks against synthetic records; no Lean or real cache export."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
HELPER = HERE.parents[1] / 'integration/verified_project_cache.py'
spec = importlib.util.spec_from_file_location('verified_project_cache', HELPER)
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(data, bytes):
        path.write_bytes(data)
    elif isinstance(data, str):
        path.write_text(data)
    else:
        path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


class CacheFilesTest(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='synthetic-project-cache-')
        self.root = Path(self.scratch.name).resolve()
        cache.BUILD_ROOT.mkdir(exist_ok=True)
        self.storage = tempfile.TemporaryDirectory(prefix='synthetic-cache-objects-', dir=cache.BUILD_ROOT)
        self.object_dir = Path(self.storage.name).resolve() / 'seed'
        self.run = self.root / 'producer/results'
        self.build = self.root / 'producer/build'
        self.metadata = self.root / 'public-export'
        self.sources = {
            'Theory.Base': '-- Synthetic source only.\ndef x := 1\n',
            'Theory.Consumer': 'import Theory.Base\ndef y := x\n',
            'Theory': 'import Theory.Consumer\n',
            'Compiler': '-- Synthetic umbrella\n',
            'Selvage': '-- Synthetic umbrella\n',
            'Assurance': '-- Synthetic umbrella\n',
        }
        for name, text in self.sources.items():
            write(self.build / 'source' / (name.replace('.', '/') + '.lean'), text)
            write(self.build / 'olean' / (name.replace('.', '/') + '.olean'), b'SYNTHETIC NON-LEAN OBJECT:' + name.encode())
        external = self.root / 'public-external'
        toolchain = self.root / 'public-toolchain'
        write(external / 'Init.olean', b'SYNTHETIC INIT: NOT A LEAN ARTIFACT')
        write(external / 'Ext/Extra.olean', b'SYNTHETIC EXTERNAL OBJECT')
        write(toolchain / 'bin/lean', b'NOT EXECUTABLE: SYNTHETIC COMPILER IDENTITY')
        write(toolchain / 'lib/runtime', b'SYNTHETIC PUBLIC RUNTIME BYTES')
        self.policy = {
            'schema': 'explicit-lean-cli-policy-v1', 'compiler': str(toolchain / 'bin/lean'),
            'toolchain_root': str(toolchain), 'external_roots': [str(external)],
            'forbidden_project_roots': [str(self.root / 'forbidden-main-project-cache')],
            'lean_version': 'SYNTHETIC VERSION; NO LEAN EXECUTION', 'platform': 'synthetic-test-platform',
            'lean_options': [], 'semantic_environment': {},
        }
        write(self.run / 'check_all_formal.py', '# Synthetic archived harness; never executed.\n')
        self.harness_sha = cache.file_pin(self.run / 'check_all_formal.py')['sha256']
        manifest = {'lanes': [], 'expected_theorem_pins': 0, 'synthetic_fixture': True}
        write(self.run / 'core_manifest.json', manifest)
        input_pins = {str(self.root / 'original/check_all_formal.py'): self.harness_sha,
                      str(self.root / 'original/core_manifest.json'): cache.file_pin(self.run / 'core_manifest.json')['sha256']}
        self.lean_path = ':'.join([str(self.build / 'olean'), *self.policy['external_roots']])
        nodes, inventory = cache._source_tree(self.build / 'source')
        self.order = cache._topo(nodes)
        logs = []
        def log(label, command, **extra):
            record = {'label': label, 'command': command, 'cwd': str(self.build / 'source'),
                      'exit_code': 0, 'stdout': '', 'stderr': '', 'elapsed_seconds': 0.0, **extra}
            filename = f'{len(logs) + 1:03}_{label}.json'
            write(self.run / filename, record)
            logs.append({'label': label, 'log': filename, 'exit_code': 0})
        log('lean_version', [self.policy['compiler'], '--version'], stdout=self.policy['lean_version'] + '\n')
        for gate in ('boundary_applied_source', 'boundary_existing_companion', 'combined_patch_check', 'combined_patch_apply'):
            log(gate, ['SYNTHETIC SAVED RECORD; NOT EXECUTED'])
        base_sources = [row['source_relative'] for name, row in nodes.items() if name != 'Theory.Consumer']
        log('companion_source_list', ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '*.lean'], stdout='\n'.join(base_sources) + '\n')
        outputs = {}
        for name in self.order:
            rel = name.replace('.', '/')
            source, output = self.build / 'source' / (rel + '.lean'), self.build / 'olean' / (rel + '.olean')
            pin = cache.file_pin(source)['sha256']
            log('lean_' + name.replace('.', '_'), [self.policy['compiler'], '-o', str(output), str(source)],
                lean_path=self.lean_path, source=str(source), source_sha256_before=pin, source_sha256_after=pin)
            outputs[name] = {'path': str(output), 'sha256': cache.file_pin(output)['sha256']}
        write(self.run / 'compiled_olean_hashes.json', outputs)
        write(self.run / 'cached_dependency_artifacts.json', [])
        for period in ('before', 'after'):
            write(self.run / f'companion_source_hashes_{period}.json', {'synthetic-public-source': 'same'})
        write(self.run / 'applied_source_hashes.json', {rel: pin['sha256'] for rel, pin in inventory.items()})
        write(self.run / 'axiom_census.json', {'Theory.Consumer': {'dest': 'Theory/Consumer.lean'}})
        write(self.run / 'combined.patch', 'SYNTHETIC PATCH; NOT APPLIED OR EXECUTED\n')
        self.report = {
            'status': 'passed', 'rebuild_project_source_closure': True,
            'combined_patch_exact_content_verified': True, 'all_selected_modules_rooted': True,
            'changed_inputs': [], 'changed_companion_sources': [],
            'input_hashes_before': input_pins, 'input_hashes_after': copy.deepcopy(input_pins),
            'companion_head_before': 'synthetic-head', 'companion_head_after': 'synthetic-head',
            'companion_status_before': '', 'companion_status_after': '',
            'umbrella_builds': list(cache.UMBRELLAS), 'manifest': manifest,
            'combined_patch': {'path': str(self.root / 'original/combined.patch'), 'sha256': cache.file_pin(self.run / 'combined.patch')['sha256']},
            'commands': logs, 'full_compile_order': self.order, 'project_modules_compiled': len(nodes),
            'lean_path': self.lean_path, 'synthetic_fixture': True,
        }
        self.save_report()

    def tearDown(self):
        self.storage.cleanup()
        self.scratch.cleanup()

    def save_report(self):
        write(self.run / 'report.json', self.report)
        self.report_sha = cache.file_pin(self.run / 'report.json')['sha256']

    def export(self):
        self.exported = cache.export_completed_run(run_dir=self.run, build_dir=self.build,
            metadata_dir=self.metadata, object_dir=self.object_dir, compiler_policy=self.policy,
            expected_report_sha256=self.report_sha, expected_harness_sha256=self.harness_sha)
        return self.exported

    def prospective(self):
        root = self.root / 'next/source'
        shutil.copytree(self.build / 'source', root)
        return root

    def plan(self, source=None, policy=None, selected=None):
        source = source or self.prospective()
        return cache.plan_admission(manifest_path=Path(self.exported['manifest_path']),
            expected_sha256=self.exported['manifest_pin']['sha256'], source_root=source,
            selected_modules=selected or ['Theory.Consumer'], overlay_root=self.root / 'next/olean',
            compiler_policy=policy or self.policy)

    def stage(self, plan):
        # The test acts as the wrapper; the helper never installs these copies.
        overlay = Path(plan['overlay_root'])
        overlay.mkdir(parents=True)
        for row in plan['ordered_copies']:
            target = Path(row['destination'])
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(row['source'], target)

    def test_unchanged_export_plan_and_destination_recheck(self):
        self.export()
        before = cache._files(self.metadata)
        plan = self.plan()
        self.assertEqual([r['module'] for r in plan['ordered_copies']], ['Theory.Base', 'Theory.Consumer'])
        self.assertEqual({r['module'] for r in plan['ordered_rebuilds']}, set(cache.UMBRELLAS))
        self.assertFalse(Path(plan['overlay_root']).exists())
        self.assertEqual(cache._files(self.metadata), before)
        self.stage(plan)
        self.assertEqual(cache.verify_staged_copies(plan)['copied_modules'], 2)
        self.assertTrue(cache.recheck_plan_inputs(plan)['ok'])

    def test_changed_dependency_invalidates_reverse_closure(self):
        self.export()
        source = self.prospective()
        write(source / 'Theory/Base.lean', 'def x := 2\n')
        plan = self.plan(source)
        self.assertEqual(len(plan['ordered_copies']), 0)
        self.assertEqual(len(plan['ordered_rebuilds']), 6)
        self.assertIn('project_dependency_rebuilt', plan['decisions']['Theory.Consumer']['reasons'])

    def test_new_module_and_changed_import(self):
        self.export()
        source = self.prospective()
        write(source / 'Theory/New.lean', 'def fresh := 1\n')
        write(source / 'Theory.lean', 'import Theory.Consumer Theory.New\n')
        plan = self.plan(source, selected=['Theory.New'])
        self.assertEqual(len(plan['ordered_copies']), 2)
        self.assertEqual(len(plan['ordered_rebuilds']), 5)
        self.assertIn('new_module', plan['decisions']['Theory.New']['reasons'])

    def test_external_byte_change_rebuilds_everything(self):
        self.export()
        write(Path(self.policy['external_roots'][0]) / 'Ext/Extra.olean', b'CHANGED PUBLIC EXTERNAL')
        self.assertEqual(len(self.plan()['ordered_copies']), 0)

    def test_absent_external_root_is_pinned_and_appearance_invalidates(self):
        missing = self.root / 'absent-public-external'
        self.policy['external_roots'].insert(0, str(missing))
        self.lean_path = ':'.join([str(self.build / 'olean'), *self.policy['external_roots']])
        self.report['lean_path'] = self.lean_path
        for row in self.report['commands']:
            path = self.run / row['log']
            log = json.loads(path.read_text())
            if 'lean_path' in log:
                log['lean_path'] = self.lean_path
                write(path, log)
        self.save_report()
        self.export()
        source = self.prospective()
        self.assertEqual(len(self.plan(source)['ordered_copies']), 2)
        missing.mkdir()
        self.assertEqual(len(self.plan(source)['ordered_copies']), 0)

    def test_toolchain_byte_change_rebuilds_everything(self):
        self.export()
        write(Path(self.policy['compiler']), b'CHANGED SYNTHETIC COMPILER')
        self.assertEqual(len(self.plan()['ordered_rebuilds']), 6)

    def test_unsupported_policy_field_rejected(self):
        self.policy['ambient_environment'] = {'UNRELATED': 'DO NOT INVENTORY'}
        with self.assertRaises(cache.CacheError):
            self.export()

    def test_failed_producer_not_exported(self):
        self.report['status'] = 'running'
        self.save_report()
        with self.assertRaises(cache.CacheError):
            self.export()
        self.assertFalse(self.metadata.exists())

    def test_selected_only_producer_not_exported(self):
        self.report['rebuild_project_source_closure'] = False
        self.save_report()
        with self.assertRaises(cache.CacheError):
            self.export()

    def test_exact_archived_harness_required(self):
        write(self.run / 'check_all_formal.py', '# changed\n')
        with self.assertRaises(cache.CacheError):
            self.export()

    def test_compile_source_before_after_binding_required(self):
        row = next(r for r in self.report['commands'] if r['label'] == 'lean_Theory_Base')
        log = json.loads((self.run / row['log']).read_text())
        log['source_sha256_after'] = '0' * 64
        write(self.run / row['log'], log)
        with self.assertRaises(cache.CacheError):
            self.export()

    def test_saved_object_byte_hash_required(self):
        write(self.build / 'olean/Theory/Base.olean', b'CHANGED OBJECT')
        with self.assertRaises(cache.CacheError):
            self.export()

    def test_producer_unknown_sidecar_rejected(self):
        write(self.build / 'olean/Theory/Base.olean.server', b'UNRECORDED PART')
        with self.assertRaises(cache.CacheError):
            self.export()

    def test_export_object_tamper_rejected_before_planning(self):
        self.export()
        write(self.object_dir / 'olean/Theory/Base.olean', b'CHANGED EXPORTED OBJECT')
        with self.assertRaises(cache.CacheError):
            self.plan()

    def test_export_evidence_tamper_rejected(self):
        self.export()
        write(self.metadata / 'evidence/check_all_formal.py', '# changed\n')
        with self.assertRaises(cache.CacheError):
            self.plan()

    def test_export_object_symlink_rejected(self):
        self.export()
        target = self.object_dir / 'olean/Theory/Base.olean'
        target.unlink()
        target.symlink_to(self.build / 'olean/Theory/Base.olean')
        with self.assertRaises(cache.CacheError):
            self.plan()

    def test_main_project_root_alias_rejected(self):
        self.policy['forbidden_project_roots'] = list(self.policy['external_roots'])
        with self.assertRaises(cache.CacheError):
            self.export()

    def test_project_namespace_external_fallback_rejected(self):
        external = Path(self.policy['external_roots'][0])
        write(external / 'Theory/Missing.olean', b'SHADOWED EXTERNAL')
        self.export()
        source = self.prospective()
        write(source / 'Theory/Consumer.lean', 'import Theory.Base Theory.Missing\n')
        with self.assertRaisesRegex(cache.CacheError, 'namespace shadows'):
            self.plan(source)

    def test_external_namespace_first_root_rule(self):
        self.export()
        shadow = self.root / 'shadow-external'
        write(shadow / 'Ext/Other.olean', b'SHADOWING NAMESPACE')
        policy = copy.deepcopy(self.policy)
        policy['external_roots'].insert(0, str(shadow))
        source = self.prospective()
        write(source / 'Theory/Consumer.lean', 'import Theory.Base Ext.Extra\n')
        with self.assertRaisesRegex(cache.CacheError, 'Namespace shadowing'):
            self.plan(source, policy)

    def test_external_file_link_escape_rejected(self):
        outside = self.root / 'outside.bin'
        write(outside, b'OUTSIDE EXPLICIT COHORT')
        (Path(self.policy['external_roots'][0]) / 'escape.olean').symlink_to(outside)
        with self.assertRaisesRegex(cache.CacheError, 'escapes explicit roots'):
            self.export()

    def test_unrooted_new_selection_rejected(self):
        self.export()
        source = self.prospective()
        write(source / 'Theory/Unrooted.lean', 'def unrooted := 0\n')
        with self.assertRaises(cache.CacheError):
            self.plan(source, selected=['Theory.Unrooted'])

    def test_source_change_after_admission_rejected(self):
        self.export()
        plan = self.plan()
        write(Path(plan['source_root']) / 'Theory/Base.lean', 'def x := 3\n')
        with self.assertRaises(cache.CacheError):
            cache.recheck_plan_inputs(plan)

    def test_external_change_after_admission_rejected(self):
        self.export()
        plan = self.plan()
        write(Path(self.policy['external_roots'][0]) / 'Init.olean', b'LATE CHANGE')
        with self.assertRaises(cache.CacheError):
            cache.recheck_plan_inputs(plan)

    def test_destination_tamper_or_sidecar_rejected(self):
        self.export()
        plan = self.plan()
        self.stage(plan)
        write(Path(plan['overlay_root']) / 'Theory/Base.olean.private', b'UNPLANNED PRIVATE PART')
        with self.assertRaises(cache.CacheError):
            cache.verify_staged_copies(plan)

    def test_prepopulated_destination_rejected_before_copy(self):
        self.export()
        write(self.root / 'next/olean/Unknown.olean', b'AMBIENT OBJECT')
        with self.assertRaises(cache.CacheError):
            self.plan()

    def test_import_parser_rejects_unsupported_or_cycle(self):
        self.export()
        source = self.prospective()
        write(source / 'Theory/Base.lean', 'public import Ext.Extra\n')
        with self.assertRaises(cache.CacheError):
            self.plan(source)
        write(source / 'Theory/Base.lean', 'import Theory.Consumer\n')
        with self.assertRaises(cache.CacheError):
            self.plan(source)

    def test_wrong_parent_manifest_pin_rejected(self):
        self.export()
        self.exported['manifest_pin']['sha256'] = '0' * 64
        with self.assertRaises(cache.CacheError):
            self.plan()

    def test_empty_directory_namespace_shadow_rejected(self):
        self.export()
        plan = self.plan()
        self.stage(plan)
        (Path(plan['overlay_root']) / 'Init').mkdir()
        with self.assertRaisesRegex(cache.CacheError, 'Unplanned directory'):
            cache.verify_staged_copies(plan)

    def test_modified_copy_record_cannot_borrow_plan_digest(self):
        self.export()
        plan = self.plan()
        plan['ordered_copies'][0]['source'] = str(self.build / 'olean/Theory/Base.olean')
        plan['plan_sha256'] = cache.digest({k: v for k, v in plan.items() if k != 'plan_sha256'})
        with self.assertRaisesRegex(cache.CacheError, 'copy/rebuild records differ'):
            cache.recheck_plan_inputs(plan)

    def test_final_output_observation_and_copied_byte_guard(self):
        self.export()
        plan = self.plan()
        self.stage(plan)
        for row in plan['ordered_rebuilds']:
            write(Path(row['output']), b'SYNTHETIC WRAPPER OUTPUT; NO COMPILATION:' + row['module'].encode())
        result = cache.verify_final_outputs(plan)
        self.assertEqual(len(result['object_files']), 6)
        self.assertFalse(result['cache_seed_promotion_permitted'])
        write(Path(plan['ordered_copies'][0]['destination']), b'LATE COPIED OBJECT CHANGE')
        with self.assertRaisesRegex(cache.CacheError, 'Copied object changed'):
            cache.verify_final_outputs(plan)


if __name__ == '__main__':
    unittest.main(verbosity=2)
