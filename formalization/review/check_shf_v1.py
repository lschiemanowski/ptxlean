#!/usr/bin/env python3
"""Replay funnel-shift mutation controls in an isolated checkout; no model calls."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_implemented_forms import declaration_sites
from worker_replay import audit_dependencies, scan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    task = json.loads((ROOT / 'formalization/tasks/shf-v1.json').read_text())
    recipe = json.loads((ROOT / 'formalization/review/candidates/shf-001.json').read_text())
    original = (ROOT / 'Ptx/Shf32.lean').read_text()
    assert hashlib.sha256(original.encode()).hexdigest() == recipe['files'][0]['sha256']
    # Change the candidate's own equations along with its computation. These faulty
    # modules still prove their own contracts; frozen external laws must reject them.
    cases = {
        'control': original,
        'swap_sources': original.replace('b <<<', 'a <<<').replace('a >>>', 'b >>>'),
        'wrap_is_clamp': original.replace('c.toNat % 32', 'min c.toNat 32'),
        'clamp_at_31': original.replace('min c.toNat 32', 'min c.toNat 31'),
    }
    work = out / 'worktree'
    subprocess.run(['git', 'worktree', 'add', '--detach', str(work), task['base_commit']],
                   cwd=ROOT, check=True, capture_output=True)
    drivers = ['shf-v1.lean', 'shf-concrete-v2.lean']
    for driver in drivers:
        (work / 'formalization/checks' / driver).write_bytes(
            (ROOT / 'formalization/checks' / driver).read_bytes())
    results = []
    for name, body in cases.items():
        path = work / 'Ptx/Shf32.lean'
        path.write_text(body)
        (out / (name + '.lean')).write_text(body)
        scan([path])
        names = [n for n, k, _ in declaration_sites(body) if k in ('def', 'theorem')]

        def run(command, label):
            r = subprocess.run(command, cwd=work, capture_output=True, text=True)
            log = r.stdout + r.stderr
            (out / (name + '-' + label + '.log')).write_text(log)
            return r.returncode, log

        code, log = run(['lake', 'build', 'Ptx.Shf32'], 'build')
        assert code == 0, log
        audit = out / (name + '-audit.lean')
        audit.write_text('import Ptx.Shf32\n' + ''.join('#print axioms ' + n + '\n' for n in names))
        code, log = run(['lake', 'env', 'lean', str(audit)], 'audit')
        assert code == 0, log
        audit_dependencies(log, names)
        outcomes = {}
        for driver in drivers:
            code, log = run(['lake', 'env', 'lean', 'formalization/checks/' + driver], driver)
            if name == 'control':
                assert code == 0, log
            else:
                assert code != 0 and 'error:' in log, log
                if 'concrete' in driver:
                    assert 'decide' in log and 'false' in log, log
            outcomes[driver] = 'pass' if code == 0 else 'reject'
        results.append(dict(case=name, sha256=hashlib.sha256(body.encode()).hexdigest(),
                            build='pass', audit='pass', declarations=names, checks=outcomes))
        (out / 'report.json').write_text(json.dumps(dict(base_commit=task['base_commit'],
            driver_sha256={d: hashlib.sha256((ROOT/'formalization/checks'/d).read_bytes()).hexdigest()
                           for d in drivers}, cases=results), indent=2) + '\n')
        print(name, 'verified', flush=True)


if __name__ == '__main__':
    main()
