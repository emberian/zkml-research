#!/usr/bin/env python3
"""Read-only schema inspection and a metadata-only verified-cache planning proposal.

No producer, installer, compiler, subprocess or cache mutation is implemented.
The plan assumes the byte-verification/export gates in REPORT.md have run. Its
output is a conditional dependency plan, never permission to install artifacts.
"""
import argparse
import copy
import datetime
import hashlib
import json
from pathlib import Path

UMBRELLAS = ('Theory', 'Compiler', 'Selvage', 'Assurance')


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def file_hash(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        while block := stream.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()


def topo(nodes):
    pending = {name: set(row['project_dependencies']) for name, row in nodes.items()}
    assert all(deps <= nodes.keys() for deps in pending.values()), 'Missing project dependency'
    result = []
    while pending:
        ready = sorted(name for name, deps in pending.items() if not deps)
        assert ready, 'Cyclic or incomplete project dependency graph'
        result.extend(ready)
        for name in ready:
            del pending[name]
        for deps in pending.values():
            deps.difference_update(ready)
    return result


def closed_graph(nodes):
    assert set(UMBRELLAS) <= nodes.keys(), 'All four umbrellas must be represented'
    order = topo(nodes)
    seen, todo = set(), list(UMBRELLAS)
    while todo:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            todo.extend(nodes[name]['project_dependencies'])
    assert seen == set(nodes), 'Only the exact complete four-umbrella project closure is eligible'
    for row in nodes.values():
        assert len(row['imports']) == len(set(row['imports'])), 'Duplicate import needs explicit normalization'
        assert row['project_dependencies'] == [name for name in row['imports'] if name in nodes]
    return order


def closure_keys(nodes, cohort_key, policy_key):
    keys = {}
    for name in closed_graph(nodes):
        row = nodes[name]
        keys[name] = digest({'schema': 'verified-project-module-input-v1', 'name': name,
                             'source_sha256': row['source_sha256'], 'imports': row['imports'],
                             'external_toolchain_cohort': cohort_key, 'compile_policy': policy_key,
                             'project_dependencies': [(dep, keys[dep], nodes[dep]['artifact_bundle'])
                                                      for dep in row['project_dependencies']]})
    return keys


def plan_reuse(prior, current):
    """Plan from verified metadata; REPORT.md specifies the mandatory file checks."""
    assert prior['schema'] == 'verified-project-cache-v1'
    assert current['schema'] == 'prospective-project-closure-v1'
    producer = prior['producer']
    assert producer['status'] == 'passed' and producer['rebuild_project_source_closure'] is True
    assert producer['project_objects_inherited'] == 0
    assert producer['report_sha256'] and producer['archived_harness_sha256']
    assert prior['cohort_basis'] == 'post_success_observed_trusted_external_cohort'
    old, new = prior['modules'], current['modules']
    assert producer['project_modules_compiled'] == len(old)
    old_keys = closure_keys(old, prior['external_toolchain_cohort_sha256'], prior['compile_policy_sha256'])
    assert old_keys == prior['module_input_keys'], 'Saved transitive input binding differs'
    order = closed_graph(new)
    assert set(current['selected_modules']) <= set(new)
    same_cohort = current['external_toolchain_cohort_sha256'] == prior['external_toolchain_cohort_sha256']
    same_policy = current['compile_policy_sha256'] == prior['compile_policy_sha256']
    decisions = {}
    for name in order:
        row = new[name]
        reasons = []
        if name in UMBRELLAS:
            reasons.append('umbrella_always_rebuilt')
        if not same_cohort:
            reasons.append('external_or_toolchain_cohort_changed')
        if not same_policy:
            reasons.append('compile_policy_changed')
        if name not in old:
            reasons.append('new_module')
        else:
            previous = old[name]
            for key in ('source_sha256', 'imports', 'project_dependencies'):
                if row[key] != previous[key]:
                    reasons.append(key + '_changed')
            if not previous['artifact_bundle'] or '.olean' not in previous['artifact_bundle']:
                reasons.append('missing_pinned_main_olean')
        if any(decisions[dep]['action'] == 'rebuild' for dep in row['project_dependencies']):
            reasons.append('project_dependency_rebuilt')
        decisions[name] = {'action': 'rebuild' if reasons else 'reuse', 'reasons': reasons}
        if not reasons:
            decisions[name]['artifact_bundle'] = old[name]['artifact_bundle']
            decisions[name]['verified_input_key'] = old_keys[name]
    return {'schema': 'conditional-project-cache-plan-v1', 'authorization_to_install_cache': False,
            'required_gate': 'Verify exported/current source, graph, report, harness, artifact bundles, environment cohort and resolver bytes as specified in REPORT.md.',
            'order': order, 'decisions': decisions,
            'reuse_count': sum(row['action'] == 'reuse' for row in decisions.values()),
            'rebuild_count': sum(row['action'] == 'rebuild' for row in decisions.values()),
            'project_cache_fallback_permitted': False,
            'historical_external_prepost_attestation_claim': False}


def inspect_run(root):
    """Inspect only saved schemas and completed log files, without running the harness."""
    root = Path(root).resolve()
    expected = ['report.json', 'check_all_formal.py', 'compiled_olean_hashes.json',
                'applied_source_hashes.json', 'axiom_census.json',
                'companion_source_hashes_before.json', 'companion_source_hashes_after.json',
                'cached_dependency_artifacts.json']
    artifacts = {}
    schemas = {}
    for name in expected:
        path = root / name
        artifacts[name] = {'exists': path.is_file()}
        if path.is_file():
            artifacts[name].update(sha256=file_hash(path), bytes=path.stat().st_size)
            if path.suffix == '.json':
                obj = json.loads(path.read_bytes())
                schemas[name] = {'kind': type(obj).__name__, 'entries': len(obj),
                                 'keys_sample': list(obj)[:20] if isinstance(obj, dict) else []}
    report = json.loads((root / 'report.json').read_bytes()) if artifacts['report.json']['exists'] else None
    logs = sorted(root.glob('*_lean_*.json'))
    sample = None
    if logs:
        obj = json.loads(logs[-1].read_bytes())
        sample = {'path': str(logs[-1]), 'sha256': file_hash(logs[-1]), 'keys': list(obj),
                  'source_sha256_before': obj.get('source_sha256_before'),
                  'source_sha256_after': obj.get('source_sha256_after'), 'exit_code': obj['exit_code']}
    return {'schema': 'read-only-integration-cache-schema-inspection-v1',
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'run_directory': str(root), 'artifacts': artifacts, 'schemas': schemas,
            'completed_module_log_files_observed': len(logs), 'completed_log_schema_sample': sample,
            'saved_report_status': report.get('status') if report else None,
            'eligible_for_export_now': bool(report and report.get('status') == 'passed'
                                           and report.get('rebuild_project_source_closure')
                                           and artifacts['compiled_olean_hashes.json']['exists']),
            'note': 'Eligibility here checks completion prerequisites only; a separate verified export/cohort is still required.',
            'lean_or_build_executions': 0, 'files_modified_in_subject_run': 0}


def self_check():
    # Small ordinary dependency plans, without filesystem cache objects or Lean.
    def row(source, dependencies):
        return {'source_sha256': digest(source), 'imports': list(dependencies),
                'project_dependencies': list(dependencies), 'artifact_bundle': {'.olean': digest('object:' + source)}}
    nodes = {'Library.Base': row('base', []), 'Library.Consumer': row('consumer', ['Library.Base'])}
    nodes.update({u: row(u, ['Library.Consumer'] if u == 'Theory' else []) for u in UMBRELLAS})
    old = {'schema': 'verified-project-cache-v1', 'cohort_basis': 'post_success_observed_trusted_external_cohort',
           'producer': {'status': 'passed', 'rebuild_project_source_closure': True, 'project_objects_inherited': 0,
                        'project_modules_compiled': len(nodes), 'report_sha256': digest('report'), 'archived_harness_sha256': digest('harness')},
           'modules': nodes, 'external_toolchain_cohort_sha256': digest('external'), 'compile_policy_sha256': digest('policy')}
    old['module_input_keys'] = closure_keys(nodes, old['external_toolchain_cohort_sha256'], old['compile_policy_sha256'])
    new = {'schema': 'prospective-project-closure-v1', 'modules': copy.deepcopy(nodes), 'selected_modules': ['Library.Consumer'],
           'external_toolchain_cohort_sha256': old['external_toolchain_cohort_sha256'], 'compile_policy_sha256': old['compile_policy_sha256']}
    unchanged = plan_reuse(old, new)
    assert unchanged['reuse_count'] == 2 and unchanged['rebuild_count'] == 4
    new['modules']['Library.Base']['source_sha256'] = digest('changed-base')
    changed = plan_reuse(old, new)
    assert changed['reuse_count'] == 0 and changed['rebuild_count'] == 6
    new['modules'] = copy.deepcopy(nodes)
    new['external_toolchain_cohort_sha256'] = digest('changed-external')
    environment = plan_reuse(old, new)
    assert environment['reuse_count'] == 0 and environment['rebuild_count'] == 6
    return {'ok': True, 'schema': 'cache-planner-metadata-self-check-v1',
            'unchanged_plan': {'reuse': 2, 'rebuild': 4}, 'changed_dependency_plan': {'reuse': 0, 'rebuild': 6},
            'changed_environment_plan': {'reuse': 0, 'rebuild': 6},
            'scope': 'Pure Python dependency-plan fixtures; no actual cache approval, copying, Lean or build execution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--inspect-run', type=Path)
    choice.add_argument('--self-check', action='store_true')
    choice.add_argument('--prior-export', type=Path)
    parser.add_argument('--prospective', type=Path)
    args = parser.parse_args()
    if args.inspect_run:
        result = inspect_run(args.inspect_run)
    elif args.self_check:
        result = self_check()
    else:
        assert args.prospective, 'A prospective verified metadata file is required'
        result = plan_reuse(json.loads(args.prior_export.read_bytes()), json.loads(args.prospective.read_bytes()))
    result['helper_sha256'] = file_hash(__file__)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
