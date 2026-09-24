#!/usr/bin/env python3
"""Recheck the four frozen reviewer cases without model calls."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import model_review as m
from check_implemented_forms import declaration_sites
from worker_replay import audit_dependencies, scan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    directory = ROOT / 'formalization/review/derived-v1'
    labels = json.loads((directory / 'labels.json').read_text())
    work = out / 'worktree'
    subprocess.run(['git', 'worktree', 'add', '--detach', str(work), labels['base_commit']],
                   cwd=ROOT, check=True, capture_output=True)
    reports = []
    for case in labels['cases']:
        cid = case['case']
        recipe_path = directory / (cid + '.json')
        assert m.sha(recipe_path.read_bytes()) == case['recipe_sha256']
        recipe = json.loads(recipe_path.read_text())
        packet = m.packet(recipe)
        assert m.sha(m.encoded(packet)) == case['packet_sha256']
        ref = next(f for f in recipe['files'] if f['role'] == 'candidate')
        path = work / ref['path']
        # Every case patch adds just this leaf to the frozen base.
        path.unlink(missing_ok=True)
        subprocess.run(['git', 'apply', str(ROOT / recipe['patch']['path'])],
                       cwd=work, check=True)
        assert m.sha(path.read_bytes()) == ref['sha256']
        module = ref['path'][:-5].replace('/', '.')
        declarations = [name for name, kind, _ in declaration_sites(path.read_text())
                        if kind in ('def', 'theorem')]
        scan([path])
        def run(command, stem):
            result = subprocess.run(command, cwd=work, capture_output=True, text=True)
            text = result.stdout + result.stderr
            (out / (cid + '-' + stem + '.log')).write_text(text)
            return result.returncode, text
        code, log = run(['lake', 'build', module], 'build')
        assert code == 0, log
        audit = out / (cid + '-audit.lean')
        audit.write_text('import ' + module + '\n' + ''.join(
            '#print axioms ' + name + '\n' for name in declarations))
        code, log = run(['lake', 'env', 'lean', str(audit)], 'audit')
        assert code == 0, log
        audit_dependencies(log, declarations)
        driver_path = 'formalization/checks/' + case['family'] + '-concrete-v1.lean'
        driver = out / (cid + '-concrete.lean')
        driver.write_bytes(subprocess.check_output(
            ['git', 'show', labels['base_commit'] + ':' + driver_path], cwd=ROOT))
        code, log = run(['lake', 'env', 'lean', str(driver)], 'driver')
        if case['variant'] == 'fixture':
            assert code == 0, log
        else:
            assert code != 0 and 'decide' in log and 'false' in log, log
        reports.append(dict(case, build='pass', dependency_audit='pass',
                            declarations=declarations,
                            independent_check='pass' if code == 0 else 'rejects_false_assertion'))
        (out / 'report.json').write_bytes(m.encoded({
            'base_commit': labels['base_commit'], 'cases': reports}))
        print(cid, 'verified', flush=True)


if __name__ == '__main__':
    main()
