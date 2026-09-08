"""One pure metadata control for the documented interrupted-attempt policy."""
import json
from pathlib import Path
import shutil
import sqlite3
import tempfile
import delivery as d

HERE = Path(__file__).resolve().parent
s = d.s

def main():
    request = s.read(HERE/'results/demo001/request6.json')
    original_run = d.subprocess.run
    calls = []
    def forbidden(*args, **kwargs):
        calls.append(True)
        raise AssertionError('Incomplete delivery must not start a process')
    with tempfile.TemporaryDirectory(prefix='public-incomplete-control-', dir=HERE) as directory:
        root = Path(directory)
        for name in ('genesis.json', 'registry.json'):
            shutil.copyfile(HERE/'runtime/demo001'/name, root/name)
        source = sqlite3.connect((HERE/'runtime/demo001/journal.sqlite3').as_uri()+'?mode=ro', uri=True)
        target = sqlite3.connect(root/'journal.sqlite3')
        try: source.backup(target)
        finally: target.close(); source.close()
        db = d.connection(root)
        db.execute('INSERT INTO deliveries VALUES(?,?,?,?,?,?,?)', (request['request_id'], request['delivery_id'],
                   s.digest(request), s.canonical(request).decode(), 'running', None, None))
        db.close()
        d.subprocess.run = forbidden
        try:
            try: d.deliver(root, request)
            except s.Refused as error:
                assert error.code == 'delivery_incomplete_no_automatic_reexecution'
                assert error.evidence == {'status': 'running'}
            else: raise AssertionError('Expected refusal')
        finally: d.subprocess.run = original_run
        assert calls == []
    result = {'status': 'PASS', 'controls': 1,
              'injected_state': 'Public temporary ledger row in running status; no crashed crypto run claimed',
              'refusal': 'delivery_incomplete_no_automatic_reexecution', 'subprocess_invocations': 0,
              'private_artifact_reads': 0, 'normal_demo_unchanged': True}
    d.once(HERE/'results/INCOMPLETE_CONTROL.json', result)
    print(json.dumps(result))

if __name__ == '__main__': main()
