#!/usr/bin/env python3
"""Offline, post-generation acceptance calibration; not pre-dispatch evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_implemented_forms import declaration_sites
from worker_replay import audit_dependencies


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, default=ROOT / 'integration/torchlean/PtxBinary32/ReciprocalInstruction.lean')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    code = args.candidate.read_text()
    driver_path = ROOT / 'formalization/checks/reciprocal-instruction-v2.lean'
    driver = driver_path.read_text()
    assert driver.startswith('import PtxBinary32.ReciprocalInstruction\n')
    body = driver.split('\n', 1)[1]
    declarations = [name for name, _, _ in declaration_sites(code)]
    audit = '\n' + '\n'.join('#print axioms ' + name for name in declarations) + '\n'
    variants = {
        'control': code,
        'ignore_operand': code.replace('(i.source.eval s)', '(0 : Word)'),
        'approximate_spelling': code.replace('"rcp.rn.f32"', '"rcp.approx.f32"'),
        'weaken_target': code.replace('20 ≤ target.sm', '0 ≤ target.sm'),
    }
    assert len(set(variants.values())) == len(variants)
    report = {'timing': 'post-generation; missing pre-dispatch reference preflight is an explicit workflow deviation',
              'candidate_sha256': hashlib.sha256(code.encode()).hexdigest(),
              'driver_sha256': hashlib.sha256(driver.encode()).hexdigest(),
              'declarations': declarations, 'cases': {}}
    for name, source in variants.items():
        case = {}
        for phase, contents in [('audit', source + audit), ('driver', source + body)]:
            path = out / (name + '-' + phase + '.lean')
            path.write_text(contents)
            command = ['lake', '--no-cache', 'env', 'lean', str(path)]
            result = subprocess.run(command, cwd=ROOT / 'integration/torchlean',
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            log = out / (name + '-' + phase + '.log')
            log.write_text(result.stdout)
            case[phase] = {'command': command, 'exit_code': result.returncode,
                           'source_sha256': hashlib.sha256(contents.encode()).hexdigest(),
                           'log_sha256': hashlib.sha256(result.stdout.encode()).hexdigest()}
            if phase == 'audit':
                if result.returncode:
                    raise RuntimeError(f'{name}: mutant failed compilation; this is not a semantic rejection')
                audit_dependencies(result.stdout, declarations)
            elif name == 'control':
                if result.returncode:
                    raise RuntimeError('Original candidate must pass the driver')
            elif result.returncode == 0:
                raise RuntimeError(f'{name}: mutation escaped independent checks')
            elif 'error:' not in result.stdout or 'timeout' in result.stdout.lower():
                raise RuntimeError(f'{name}: failure must be a Lean rejection, not a timeout')
        report['cases'][name] = case
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    report['outcome'] = 'pass'
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Control passed; three compiling, axiom-audited semantic mutations rejected.')


if __name__ == '__main__':
    main()
