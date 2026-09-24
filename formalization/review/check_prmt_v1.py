#!/usr/bin/env python3
"""Recheck the PRMT reference and three compiling faults without model calls."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_worker_evidence import verify as verify_archive
from worker_replay import audit_dependencies, scan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    evidence = ROOT / 'formalization/results/prmt-v1/evidence-manifest.json'
    verify_archive(evidence)
    manifest = json.loads(evidence.read_text())
    with tarfile.open(evidence.parent / manifest['archive'], 'r:gz') as archive:
        def read(name):
            return archive.extractfile(name).read()
        preflight = json.loads(read('preflight/preflight.json'))
        task = json.loads(read('attempts/prmt-001/task.json'))
        cases = {r['case']: read('preflight/' + r['case'] + '.lean')
                 for r in preflight['records']}
    work = out / 'worktree'
    subprocess.run(['git', 'worktree', 'add', '--detach', str(work), task['base_commit']],
                   cwd=ROOT, check=True, capture_output=True)
    results = []
    for record in preflight['records']:
        case = record['case']
        body = cases[case]
        assert hashlib.sha256(body).hexdigest() == record['sha256']
        candidate = work / 'Ptx/Prmt32.lean'
        candidate.write_bytes(body)
        scan([candidate])

        def run(command, label):
            result = subprocess.run(command, cwd=work, capture_output=True, text=True)
            log = result.stdout + result.stderr
            (out / (case + '-' + label + '.log')).write_text(log)
            return result.returncode, log

        code, log = run(['lake', 'build', 'Ptx.Prmt32'], 'build')
        assert code == 0, log
        audit = out / (case + '-audit.lean')
        audit.write_text('import Ptx.Prmt32\n' + ''.join(
            '#print axioms ' + name + '\n' for name in record['declarations']))
        code, log = run(['lake', 'env', 'lean', str(audit)], 'audit')
        assert code == 0, log
        audit_dependencies(log, record['declarations'])
        for driver in ['prmt-v1.lean', 'prmt-concrete-v1.lean']:
            path = 'formalization/checks/' + driver
            pin = next(ref['sha256'] for ref in task['sources'] if ref['path'] == path)
            assert hashlib.sha256((work / path).read_bytes()).hexdigest() == pin
            code, log = run(['lake', 'env', 'lean', path], driver)
            if case == 'control':
                assert code == 0, log
            else:
                assert code != 0 and 'decide' in log and 'false' in log, log
        results.append(dict(record, rechecked=True))
        (out / 'report.json').write_text(json.dumps(
            {'base_commit': task['base_commit'], 'cases': results}, indent=2) + '\n')
        print(case, 'verified', flush=True)


if __name__ == '__main__':
    main()
