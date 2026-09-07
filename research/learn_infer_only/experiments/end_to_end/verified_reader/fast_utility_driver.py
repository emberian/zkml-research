#!/usr/bin/env python3
"""Persistent-host integration of the unchanged complete utility runner.

The shared staging routine and utility worker are reused byte-for-byte. A
Run subclass replaces only public host proposal calls with the existing
host_runtime stdio worker. Authority, verifier and issuer roles are unchanged.
"""
from __future__ import annotations
import argparse
import collections
import gzip
import hashlib
import json
from pathlib import Path
import select
import shutil
import subprocess
import sys
import tarfile
import time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
UTILITY_SHA = 'f623dbf5d903c6a6ced87cfb5735dd1bda47f861665f8d88670184f6dc463847'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(Path(path).read_bytes())


def dump(path, value):
    Path(path).write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def outer(args):
    import utility_driver as utility
    assert sha((HERE / 'utility_driver.py').read_bytes()) == UTILITY_SHA
    runtime, reports = Path(args.runtime).resolve(), Path(args.reports).resolve()

    def launch(command, **kwargs):
        # This is the shared stage's sole subprocess launch, after it has frozen
        # all source and fixture bytes. Extend that snapshot, then launch this
        # wrapper so the unchanged utility worker sees the Run subclass.
        assert '--worker' in command and Path(command[1]).name == 'utility_driver.py'
        e2e = runtime / 'e2e'
        host = HERE.parent / 'host_runtime'
        target = e2e / 'host_runtime'
        (target / 'frozen_core').mkdir(parents=True)
        host_pins = load(host / 'source_pins.json')
        pins = load(reports / 'source_pins.json')
        for name in ['host.py', 'source_pins.json']:
            raw = (host / name).read_bytes()
            (target / name).write_bytes(raw)
            pins['host_runtime/' + name] = sha(raw)
        for name, record in host_pins['core'].items():
            raw = (host / 'frozen_core' / name).read_bytes()
            assert sha(raw) == record['sha256']
            if (e2e / 'journal' / name).exists():
                assert raw == (e2e / 'journal' / name).read_bytes()
            (target / 'frozen_core' / name).write_bytes(raw)
            pins['host_runtime/frozen_core/' + name] = sha(raw)
        assert sha((e2e / 'resident-crypto').read_bytes()) == host_pins['crypto_binary_sha256']
        raw = Path(__file__).read_bytes()
        dest = e2e / 'verified_reader/fast_utility_driver.py'
        dest.write_bytes(raw)
        pins['verified_reader/fast_utility_driver.py'] = sha(raw)
        dump(reports / 'source_pins.json', pins)
        with tarfile.open(reports / 'source_snapshot.tar.gz', 'w:gz') as archive:
            for name in sorted(pins):
                if name != 'resident-crypto':
                    archive.add(e2e / name, arcname=name)
        baseline = HERE / 'reports/utility_001/report.json'
        paired = host / 'results/run_001/report.json'
        shutil.copyfile(baseline, reports / 'baseline_utility_report.json')
        dump(reports / 'comparison_provenance.json', {
            'baseline_full_utility_report_sha256': sha(baseline.read_bytes()),
            'paired_host_report_sha256': sha(paired.read_bytes()),
            'paired_host_only_speedup': load(paired)['host_caller_speedup_including_worker_startup'],
            'scope': 'Full utility comparison uses separate runs with fresh OS randomness; paired host-only result is a distinct experiment.'})
        command = [*command]
        command[1] = str(dest)
        dump(reports / 'command.json', {'argv': command})
        return subprocess.run(command, **kwargs)

    # Replace only this module's launch namespace, not global subprocess.run.
    # The unchanged stage function still performs every source/fixture check.
    utility.subprocess = SimpleNamespace(run=launch, STDOUT=subprocess.STDOUT)
    utility.stage(args)


def worker(args):
    import utility_driver as utility
    assert sha((HERE / 'utility_driver.py').read_bytes()) == UTILITY_SHA
    sys.path.insert(0, str(HERE.parent / 'journal'))
    import run as run_module
    from common import canonical, require
    BaseRun = run_module.Run
    reports = Path(args.reports).resolve()

    class PersistentRun(BaseRun):
        def __init__(self, root, queries, binary):
            self.host_worker = None
            self.worker_events = []
            super().__init__(root, queries, binary=binary)
            self.worker_argv = [sys.executable, str(HERE.parent / 'host_runtime/host.py'), 'serve',
                                '--config', str(self.root / 'host_config.json'),
                                '--cas', str(self.host_cas.root)]
            self.worker_log = (self.root / 'host_worker.stderr').open('wb')
            self.worker_started = time.perf_counter_ns()
            self.host_worker = subprocess.Popen(self.worker_argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                                 stderr=self.worker_log)
            require(select.select([self.host_worker.stdout], [], [], 30)[0], 'hostWorkerStartupTimeout')
            ready = json.loads(self.host_worker.stdout.readline())
            require(ready == {'ok': True, 'ready': True}, 'hostWorkerReady')
            self.worker_startup_ns = time.perf_counter_ns() - self.worker_started
            self.worker_pid = self.host_worker.pid

        def role(self, command, **kwargs):
            if command != 'propose':
                return super().role(command, **kwargs)
            require(set(kwargs) == {'config', 'head', 'authorization', 'cas', 'out'}, 'hostProposalArguments')
            require(Path(kwargs['config']).resolve() == self.root / 'host_config.json', 'fixedPublicHostConfig')
            require(Path(kwargs['cas']).resolve() == self.host_cas.root.resolve(), 'fixedPublicHostCAS')
            message = {key: str(kwargs[key]) for key in ['head', 'authorization', 'out']}
            raw = canonical(message) + b'\n'
            start = time.perf_counter_ns()
            self.host_worker.stdin.write(raw)
            self.host_worker.stdin.flush()
            require(select.select([self.host_worker.stdout], [], [], 180)[0], 'hostWorkerProposalTimeout')
            response = self.host_worker.stdout.readline()
            elapsed = time.perf_counter_ns() - start
            reply = json.loads(response)
            require(reply.get('ok'), 'hostWorkerRejected:' + str(reply))
            stats = reply['request_stats']
            require(stats['cas_get_calls'] == stats['full_blob_sha256_calls'], 'everyHostGetRehashed')
            action = load(kwargs['authorization'])['payload']
            record = {'event_id': action['request_id'], 'kind': action['kind'],
                      'worker_pid': self.worker_pid, 'request_bytes': len(raw), 'response_bytes': len(response),
                      'caller_ns': elapsed, 'inside_propose_ns': reply['elapsed_ns'],
                      'request_stats': stats, 'cumulative_stats': reply['cumulative_stats'],
                      'inspection_cache_entries': reply['inspection_cache_entries'],
                      'proposal_result': reply['result']}
            self.worker_events.append(record)
            with (self.root / 'host_worker.jsonl').open('ab') as sink:
                sink.write(canonical(record) + b'\n')
            # Preserve the role-call evidence interface of the shared runner.
            call = {'role_process': 'propose', 'transport': 'persistent_stdio',
                    'worker_argv': self.worker_argv, 'message': message, 'elapsed_ns': elapsed,
                    'exit_code': 0, 'stdout': canonical(reply['result']).decode(), 'stderr': ''}
            self.calls.append(call)
            with (self.root / 'role_calls.jsonl').open('ab') as sink:
                sink.write(canonical(call) + b'\n')
            return reply['result']

        def close(self):
            if self.host_worker is not None:
                self.host_worker.stdin.close()
                require(self.host_worker.wait(timeout=30) == 0, 'hostWorkerCleanExit')
                lifetime = time.perf_counter_ns() - self.worker_started
                self.worker_log.close()
                root_report = reports / self.root.name
                rows = self.worker_events
                require(len(rows) == 240, 'oneWorkerCompleteHistory')
                counts = collections.Counter()
                for row in rows:
                    counts.update(row['request_stats']['crypto_calls'])
                actual = collections.Counter()
                cache = {}
                for line in (self.root / 'commands.jsonl').read_bytes().splitlines():
                    call = json.loads(line)
                    if call['role'] == 'host':
                        actual[call['command'][1]] += 1
                        if call['command'][1] == 'inspect':
                            meta = json.loads(call['stdout'])
                            cache[meta['sha256']] = meta
                require(actual == counts, 'hostMeterMatchesActualCryptoLog')
                final = rows[-1]['cumulative_stats']
                require(final['requests'] == 240 and final['crypto_calls'] == dict(counts), 'cumulativeHostCounts')
                require(len(cache) == rows[-1]['inspection_cache_entries'], 'cacheMetadataReconstruction')
                report = {'ok': True, 'worker_processes': 1, 'worker_pid': self.worker_pid,
                          'requests': len(rows), 'startup_ns': self.worker_startup_ns,
                          'lifetime_including_idle_pipeline_and_shutdown_ns': lifetime,
                          'proposal_caller_total_ns': sum(r['caller_ns'] for r in rows),
                          'proposal_inside_function_total_ns': sum(r['inside_propose_ns'] for r in rows),
                          'proposal_caller_plus_startup_ns': self.worker_startup_ns + sum(r['caller_ns'] for r in rows),
                          'stats': final, 'every_get_fully_rehashed': True,
                          'actual_crypto_log_matches_meter': True,
                          'inspection_cache_entries': len(cache),
                          'cache_canonical_json_bytes': len(canonical(cache)),
                          'stdio_request_bytes': sum(r['request_bytes'] for r in rows),
                          'stdio_response_bytes': sum(r['response_bytes'] for r in rows),
                          'worker_argv': self.worker_argv,
                          'cache_scope': 'Public inspection metadata grows with distinct ciphertexts; no eviction. Lifetime is one full history. JSON size is not heap/RSS.',
                          'trust_scope': 'Same SHA256/full reads, pinned binary checks, validators and public authority/verifier recomputation; no new credential or OS isolation.'}
                dump(root_report / 'host_worker_report.json', report)
                with gzip.open(root_report / 'host_worker.jsonl.gz', 'wb') as sink:
                    sink.write((self.root / 'host_worker.jsonl').read_bytes())
            super().close()

    run_module.Run = PersistentRun
    started = time.perf_counter_ns()
    utility.worker(args)
    full = load(reports / 'report.json')
    baseline = load(reports / 'baseline_utility_report.json')
    worker_reports = [load(reports / f'history_{h}/host_worker_report.json') for h in [0, 1]]
    measured = time.perf_counter_ns() - started
    comparison = {'ok': True, 'schema': 'complete-utility-persistent-host-comparison-v1',
                  'events': full['events'], 'learns': full['learns'], 'infers': full['infers'],
                  'expiries': full['expiries'], 'all_oracle_matches': full['all_oracle_matches'],
                  'baseline_total_ns': baseline['elapsed_ns'], 'optimized_total_ns': full['elapsed_ns'],
                  'wrapper_worker_elapsed_ns': measured,
                  'full_e2e_speedup_separate_runs': baseline['elapsed_ns'] / full['elapsed_ns'],
                  'baseline_host_inspect_calls': sum(h['crypto_process_costs']['main_pipeline:host:inspect']['count'] for h in baseline['histories']),
                  'optimized_host_inspect_calls': sum(w['stats']['crypto_calls']['inspect'] for w in worker_reports),
                  'worker_processes': 2, 'workers': worker_reports,
                  'source_pins': load(reports / 'source_pins.json'),
                  'baseline_report_sha256': sha((reports / 'baseline_utility_report.json').read_bytes()),
                  'paired_host_result': load(reports / 'comparison_provenance.json'),
                  'scope': 'Actual complete optimized normal workload through unchanged authority/verifier. Comparison is two separate runs with fresh OS randomness on shared hardware, not a paired statistical speedup. No model encoding, adversarial tests, live-text workload or privacy claim.'}
    dump(reports / 'fast_report.json', comparison)
    print(json.dumps({'ok': True, 'optimized_total_ns': full['elapsed_ns'],
                      'full_e2e_speedup_separate_runs': comparison['full_e2e_speedup_separate_runs'],
                      'fast_report': str(reports / 'fast_report.json')}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--runtime', default=str(HERE / 'runtime/fast_utility_001'))
    parser.add_argument('--reports', default=str(HERE / 'reports/fast_utility_001'))
    parser.add_argument('--binary', default=str(HERE.parent / 'crypto/target/release/resident-crypto'))
    args = parser.parse_args()
    worker(args) if args.worker else outer(args)


if __name__ == '__main__':
    main()
