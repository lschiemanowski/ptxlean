#!/usr/bin/env python3
"""Certify saved Poisson GPU solutions with the proved exact Lean residual checker.

The checker does not trust PTX arithmetic or the GPU's reported residual. It uses
exact rational values of the saved arena and solution words. This is an a
posteriori certificate, not an instruction-level proof of the solver.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import struct
import tempfile
import subprocess

ROOT = Path(__file__).resolve().parents[1]
INTEGRATION = ROOT / 'integration/torchlean'
EXE = INTEGRATION / '.lake/build/bin/poissonResidual'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def proof_sources():
    files = [*sorted(INTEGRATION.glob('Poisson*.lean')),
             INTEGRATION / 'lakefile.toml', INTEGRATION / 'lake-manifest.json',
             INTEGRATION / 'lean-toolchain', INTEGRATION / 'check.py',
             Path(__file__).resolve()]
    return {str(p.relative_to(ROOT)): digest(p) for p in files}


def build():
    spec = importlib.util.spec_from_file_location('poisson_integration_check', INTEGRATION / 'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.dependencies()
    version = subprocess.check_output(['lake', '--no-cache', 'env', 'lean', '--version'],
                                      cwd=INTEGRATION, text=True).strip()
    pin = (INTEGRATION / 'lean-toolchain').read_text().strip().removeprefix('leanprover/lean4:v')
    if not version.startswith(f'Lean (version {pin},'):
        raise ValueError('unexpected Lean toolchain')
    compiled = subprocess.run(['lake', '--no-cache', 'build', 'poissonResidual'],
                              cwd=INTEGRATION, text=True, capture_output=True)
    if compiled.returncode:
        raise RuntimeError(compiled.stdout + compiled.stderr)
    checker.dependencies()
    audited = ['PtxTorchLean.Poisson.Certificate.certified_residual',
               'PtxTorchLean.Poisson.Certificate.Input.acceptedRequest_sound',
               'PtxTorchLean.Poisson.Certificate.Input.decodeWord_real']
    with tempfile.TemporaryDirectory(prefix='poisson-proof-audit-') as directory:
        driver = Path(directory) / 'Audit.lean'
        driver.write_text('import PoissonResidualInput\n' +
                          ''.join('#print axioms ' + name + '\n' for name in audited))
        audit = subprocess.run(['lake', '--no-cache', 'env', 'lean', driver],
                               cwd=INTEGRATION, check=True, text=True, capture_output=True)
        checker.audit_dependencies(audit.stdout, audited)
    return version, compiled.stdout + compiled.stderr + audit.stdout


def words(data, fields, name):
    field = fields[name]
    if field['kind'] != 'd':
        raise ValueError(f'{name}: expected binary64 buffer')
    return list(struct.unpack_from('<' + 'Q' * field['count'], data, field['offset']))


def request(folder):
    layout = json.loads((folder / 'layout.json').read_text())
    observed = json.loads((folder / 'observed.json').read_text())
    data = (folder / 'arena.bin').read_bytes()
    fields = layout['fields']
    # The wire checker reconstructs the uniform-square boundary. Bind that
    # mask to the uploaded bytes too, rather than silently certifying a
    # different boundary condition if an archive was assembled incorrectly.
    width = layout['n'] * layout['degree'] + 1
    boundary = fields['boundary']
    if boundary['kind'] != 'I' or boundary['count'] != width * width:
        raise ValueError('invalid boundary buffer shape')
    flags = struct.unpack_from('<' + 'I' * boundary['count'], data, boundary['offset'])
    expected = [i % width in (0, width - 1) or i // width in (0, width - 1)
                for i in range(width * width)]
    if [bool(flag) for flag in flags] != expected:
        raise ValueError('uploaded boundary disagrees with certificate equations')
    cell = fields['cells']
    if cell['kind'] != 'I':
        raise ValueError('expected 32-bit connectivity')
    result = {key: words(data, fields, key) for key in ('B', 'D', 'W', 'load')}
    result.update(n=layout['n'], degree=layout['degree'],
                  cells=list(struct.unpack_from('<' + 'I' * cell['count'], data, cell['offset'])),
                  solution=[struct.unpack('<Q', struct.pack('<d', x))[0] for x in observed['solution']],
                  rtol=words(data, fields, 'rtol')[0], atol=words(data, fields, 'atol')[0])
    return result


def run_checker(requests, input_path, output_path):
    save(input_path, requests)
    completed = subprocess.run([EXE, input_path, output_path], capture_output=True, text=True)
    if not output_path.exists():
        raise RuntimeError(completed.stdout + completed.stderr)
    return completed.returncode, json.loads(output_path.read_text())


def certify(run_directory, output):
    run_directory = run_directory.resolve()
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source_hashes = proof_sources()
    report = {'schema_version': 1, 'status': 'running', 'checks': [], 'skipped': [],
              'proof_sources_sha256': source_hashes,
              'theorem': 'PtxTorchLean.Poisson.Certificate.certified_residual',
              'claim': 'Exact requested residual bound and zero boundary for represented setup coefficients; no PDE or PTX trace theorem.'}
    try:
        run = json.loads((run_directory / 'report.json').read_text())
        if run['numerical_status'] != 'pass':
            raise ValueError('requires a completed numerical run')
        for name, expected in run['artifacts'].items():
            path = run_directory / name
            path.resolve().relative_to(run_directory)
            if digest(path) != expected:
                raise ValueError(f'artifact hash mismatch: {name}')
        report['run_artifacts'] = run['artifacts']
        version, log = build()
        report['lean_version'] = version
        (output / 'build.log').write_text(log)
        selected = []
        for case in run['cases']:
            folder = run_directory / case['directory']
            observed = json.loads((folder / 'observed.json').read_text())
            if observed['reason'] != case['reason']:
                raise ValueError('case status mismatch')
            if observed['reason'] == 'converged':
                selected.append((case['directory'], request(folder)))
            else:
                report['skipped'].append({'directory': case['directory'], 'reason': observed['reason']})
        if not selected:
            raise ValueError('no converged results to certify')
        status, results = run_checker([r for _, r in selected], output / 'inputs.json', output / 'outputs.json')
        if len(results) != len(selected):
            raise ValueError('certificate count mismatch')
        for (name, _), result in zip(selected, results, strict=True):
            report['checks'].append({'directory': name, **result})
        if status or any(r.get('accepted') is not True for r in results):
            raise AssertionError('a GPU result failed the exact residual/boundary certificate')

        # Negative controls bind acceptance to values, boundary, shape and finite
        # decoding. They cannot pass merely because the source run said converged.
        sample = next(r for _, r in selected if r['n'] == 2 and r['degree'] == 1)
        bad_boundary = copy.deepcopy(sample)
        bad_boundary['solution'][0] = 0x3ff0000000000000
        bad_interior = copy.deepcopy(sample)
        bad_interior['solution'][4] = 0
        nonfinite = copy.deepcopy(sample)
        nonfinite['W'][0] = 0x7ff0000000000000
        wrong_shape = copy.deepcopy(sample)
        wrong_shape['B'].pop()
        bad_mesh = copy.deepcopy(sample)
        bad_mesh['cells'][0] = 1
        status, rejected = run_checker([bad_boundary, bad_interior, nonfinite, wrong_shape, bad_mesh],
                                       output / 'negative-inputs.json', output / 'negative-outputs.json')
        if status == 0 or len(rejected) != 5 or any(r.get('accepted') is True for r in rejected):
            raise AssertionError('negative certificate controls were not rejected')
        report['negative_controls'] = ['nonzero boundary', 'wrong interior solution',
                                       'nonfinite weight', 'wrong basis shape', 'wrong connectivity']
        if proof_sources() != source_hashes:
            raise AssertionError('proof/checker sources changed during certification')
        report['artifacts'] = {p.name: digest(p) for p in sorted(output.iterdir()) if p.is_file()}
        report['status'] = 'pass'
        save(output / 'certification.json', report)
        print(f'Exact Lean residual certificates passed: {len(results)} GPU solutions; 5 negative controls rejected.', flush=True)
        return report
    except BaseException as e:
        report['status'] = 'fail'
        report['error'] = str(e)
        save(output / 'certification.json', report)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    certify(args.run, args.output)


if __name__ == '__main__':
    main()
