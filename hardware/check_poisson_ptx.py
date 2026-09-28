#!/usr/bin/env python3
"""Bind true_residual's emitted instructions to its parameterized Lean program.

This checks one entry, not the other Poisson kernels or parallel memory admission.
The Lean proof concerns instruction semantics; this text/ABI binding is checked
by this frontend and remains separate from compiler or GPU conformance.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
INTEGRATION = ROOT / 'integration/torchlean'
HEADER = [
    '.reqntid 256, 1, 1', '{',
    '.reg .u32 %lane, %cell, %i, %j, %k, %idx, %node, %cursor, %end, %other, %flag, %flag2, %global;',
    '.reg .b64 %base, %off, %addr, %shared;',
    '.reg .f64 %a, %b, %c, %d, %acc, %acc2, %prod, %value;',
    '.reg .pred %live, %p0, %p1, %p2, %p3;',
]


def parameters(layout):
    if type(layout['n']) is not int or layout['n'] < 1 or type(layout['degree']) is not int or layout['degree'] not in (1, 2, 3, 4):
        raise ValueError('unsupported mesh dimensions')
    if type(layout['bytes']) is not int or not (0 < layout['bytes'] < 2**64):
        raise ValueError('invalid allocation size')
    count = (layout['n'] * layout['degree'] + 1) ** 2
    if not (0 < count < 2**30):
        raise ValueError('vector exceeds the backend index domain')
    result = {'count': count}
    for key, field in [('rhs', 'rhs'), ('ap', 'ap'), ('output', 'true_r')]:
        f = layout['fields'][field]
        if f['kind'] != 'd' or f['count'] != count or type(f['offset']) is not int or not (0 <= f['offset'] < 2**64) or f['offset'] % 8:
            raise ValueError(f'invalid binary64 layout: {field}')
        if f['offset'] + count * 8 > layout['bytes']:
            raise ValueError(f'buffer outside arena: {field}')
        result[key] = f['offset']
    for key in ('rhs', 'ap'):
        if not (result['output'] + count*8 <= result[key] or result[key] + count*8 <= result['output']):
            raise ValueError('output overlaps a read-only input array')
    launch = layout['launches']['true_residual']
    if launch != dict(groups=(count + 255)//256, threads=256, shared_bytes=0):
        raise ValueError('launch shape differs from the reviewed entry')
    return result


def verify_entry(ptx, expected, layout):
    if any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('comments are outside the exact emitted frontend dialect')
    lines = [line.strip() for line in ptx.splitlines() if line.strip()]
    if lines[:3] not in [
            ['.version 9.2', '.target sm_120', '.address_size 64'],
            ['.version 9.4', '.target sm_120', '.address_size 64']]:
        raise ValueError('unreviewed module target/version')
    entries = re.findall(r'\.visible \.entry true_residual\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
    if len(entries) != 1 or len(re.findall(r'\.entry\s+true_residual\b', ptx)) != 1:
        raise ValueError('expected exactly one true_residual entry')
    actual = [line.strip() for line in entries[0].splitlines() if line.strip()]
    if actual != HEADER + expected:
        raise ValueError('true_residual instructions/declarations differ from the Lean program')
    parameters(layout)
    return dict(entry='true_residual', instruction_count=len(expected),
                entry_sha256=hashlib.sha256(entries[0].encode()).hexdigest(),
                theorem='PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.correspondence',
                scope='Closed residual launch: arbitrary per-byte sources from initial memory or actual stores; disjoint output, arbitrary publication order. Necessary-source overapproximation, not complete PTX admission or host visibility.')


def read_artifact(run, report, name):
    path = run/name
    path.resolve().relative_to(run.resolve())
    if name not in report['artifacts']:
        raise ValueError(f'consumed artifact missing from manifest: {name}')
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != report['artifacts'][name]:
        raise ValueError(f'artifact hash mismatch: {name}')
    return data


def check(run, output):
    report = json.loads((run/'report.json').read_text())
    if report['numerical_status'] != 'pass' or not report['cases']:
        raise ValueError('requires a completed nonempty numerical run')
    for name in report['artifacts']:
        read_artifact(run, report, name)
    if output.exists():
        raise ValueError('output already exists')
    sources = [*sorted((INTEGRATION/'PoissonPTX').glob('*.lean')), INTEGRATION/'PoissonPTXMain.lean',
               INTEGRATION/'check.py', INTEGRATION/'lakefile.toml', INTEGRATION/'lake-manifest.json',
               INTEGRATION/'lean-toolchain', Path(__file__).resolve()]
    hashes = {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    spec = importlib.util.spec_from_file_location('integration_check', INTEGRATION/'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.dependencies()
    version = subprocess.check_output(['lake', '--no-cache', 'env', 'lean', '--version'], cwd=INTEGRATION, text=True)
    pin = (INTEGRATION/'lean-toolchain').read_text().strip().removeprefix('leanprover/lean4:v')
    if not version.startswith(f'Lean (version {pin},'):
        raise ValueError('unexpected Lean toolchain')
    subprocess.run(['lake', '--no-cache', 'build', 'poissonPTX', 'PoissonPTX.ParallelResidualLayout', 'PoissonPTX.WeakPadding'], cwd=INTEGRATION, check=True,
                   stdout=sys.stderr)
    audited = ['PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.Arena.correspondence',
               'PtxTorchLean.Poisson.PTX.Weak.Residual.Parallel.witness_sources',
               'PtxTorchLean.Poisson.PTX.Weak.Residual.padding']
    with tempfile.TemporaryDirectory(prefix='poisson-instruction-audit-') as folder:
        driver = Path(folder)/'Audit.lean'
        driver.write_text('import PoissonPTX.ParallelResidualLayout\nimport PoissonPTX.WeakPadding\n' +
                          ''.join('#print axioms '+name+'\n' for name in audited))
        audit = subprocess.run(['lake', '--no-cache', 'env', 'lean', driver], cwd=INTEGRATION,
                               check=True, text=True, capture_output=True)
        checker.audit_dependencies(audit.stdout, audited)
    layouts = [json.loads(read_artifact(run, report, c['directory']+'/layout.json')) for c in report['cases']]
    params = [parameters(l) for l in layouts]
    emitted = subprocess.run([INTEGRATION/'.lake/build/bin/poissonPTX'],
                             input=json.dumps(params)+'\n', text=True, capture_output=True, check=True)
    programs = json.loads(emitted.stdout)
    results = []
    for case, layout, program in zip(report['cases'], layouts, programs, strict=True):
        result = verify_entry(read_artifact(run, report, case['directory']+'/kernel.ptx').decode(), program, layout)
        results.append(dict(directory=case['directory'], parameters=parameters(layout), **result))
    checker.dependencies()
    if hashes != {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}:
        raise ValueError('proof/frontend sources changed during checking')
    result = dict(status='pass', checked=results, audited_theorems=audited,
                  axiom_audit=audit.stdout,
                  source_sha256=hashes,
                  source_run_report_sha256=hashlib.sha256((run/'report.json').read_bytes()).hexdigest(),
                  source_run_artifacts=report['artifacts'])
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        raise ValueError('output already exists')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'Emitted true_residual matches the proved instruction program in {len(results)} saved layouts.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    check(args.run, args.output)
