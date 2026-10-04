#!/usr/bin/env python3
"""Bind the complete initialize entry to its fetched parallel Lean proof.

Admitted input bytes determine the masked rhs/r copy, the identical quotient
words in z/p, and positive-zero x. The proof includes outside-byte preservation
and a finite active-coordinate execution. Padding is proved locally. Full PTX
admission, CUDA visibility, host composition and GPU conformance are separate.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile

from check_poisson_ptx import ROOT, INTEGRATION, read_artifact, HEADER


def parameters(layout):
    n, degree = layout['n'], layout['degree']
    if type(n) is not int or n < 1 or type(degree) is not int or degree not in (1, 2, 3, 4):
        raise ValueError('unsupported mesh dimensions')
    count = (n*degree+1)**2
    if count >= 2**30 or type(layout['bytes']) is not int or not 0 < layout['bytes'] < 2**64:
        raise ValueError('unsupported index or allocation extent')
    fields = [('boundary', count, 'I', 4), ('load', count, 'd', 8),
              ('rhs', count, 'd', 8), ('r', count, 'd', 8), ('diagonal', count, 'd', 8),
              ('z', count, 'd', 8), ('p', count, 'd', 8), ('x', count, 'd', 8)]
    ranges = []
    for name, size, kind, width in fields:
        field = layout['fields'][name]
        off = field['offset']
        if field['kind'] != kind or field['count'] != size or type(off) is not int or off < 0 or off % width:
            raise ValueError('invalid field representation')
        end = off + size*width
        if end > layout['bytes']:
            raise ValueError('field outside arena')
        if any(not (end <= start or stop <= off) for start, stop in ranges):
            raise ValueError('overlapping fields')
        ranges.append((off, end))
    if layout['launches']['initialize'] != dict(groups=(count+255)//256, threads=256, shared_bytes=0):
        raise ValueError('unreviewed vector launch')
    return [count, *(start for start, _ in ranges)]


def verify_entry(ptx, expected, layout):
    parameters(layout)
    if len(expected) != 43 or any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('incomplete program or unreviewed comments')
    lines = [line.strip() for line in ptx.splitlines() if line.strip()]
    if lines[:3] not in ([f'.version {v}', '.target sm_120', '.address_size 64'] for v in ('9.2', '9.4')):
        raise ValueError('unreviewed module target/version')
    entries = re.findall(r'\.visible \.entry initialize\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
    if len(entries) != 1 or len(re.findall(r'\.entry\s+initialize\b', ptx)) != 1:
        raise ValueError('missing or duplicate entry')
    actual = [line.strip() for line in entries[0].splitlines() if line.strip()]
    if actual != HEADER+expected:
        raise ValueError('initialize differs from proved instruction list')
    return dict(entry='initialize', instructions=len(expected),
                sha256=hashlib.sha256(('\n'.join(actual)+'\n').encode()).hexdigest())


def check(run, output):
    if output.exists():
        raise ValueError('output already exists')
    report = json.loads((run/'report.json').read_text())
    if report['numerical_status'] != 'pass' or not report['cases']:
        raise ValueError('requires completed saved cases')
    for name in report['artifacts']:
        read_artifact(run, report, name)
    spec = importlib.util.spec_from_file_location('integration_check', INTEGRATION/'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.dependencies()
    paths = [*checker.sources(), INTEGRATION/'lakefile.toml', INTEGRATION/'lake-manifest.json',
             INTEGRATION/'lean-toolchain', INTEGRATION/'check.py', Path(__file__).resolve(),
             ROOT/'hardware/check_poisson_ptx.py', ROOT/'hardware/poisson_kernels.py']
    def hashes():
        return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    before = hashes()
    names = ['PtxTorchLean.Poisson.PTX.Initialize.'+name for name in
             ('correct', 'entry_correct', 'body_exists', 'entry_exists', 'inactive', 'inactive_exists',
              'entry_length', 'Arena.parallel_correct', 'Arena.parallel_exists', 'Arena.publication_outside')]
    layouts = [json.loads(read_artifact(run, report, case['directory']+'/layout.json'))
               for case in report['cases']]
    expressions = ['Initialize.rendered '+' '.join(map(str, parameters(layout))) for layout in layouts]
    lean = ['lake', '--no-cache', 'env', 'lean', '-j1', '-M5120']
    with tempfile.TemporaryDirectory(prefix='poisson-initialization-') as tmp:
        path = Path(tmp)/'Render.lean'
        path.write_text('import PoissonPTX.InitializeText\nimport PoissonPTX.InitializeExists\nopen PtxTorchLean.Poisson.PTX\n'+
            ''.join('#print axioms '+name+'\n' for name in names)+
            'def main : IO Unit := IO.println (Lean.toJson (['+', '.join(expressions)+
            '] : List (List String))).compress\n')
        lines = subprocess.check_output(lean+['--run', str(path)], cwd=INTEGRATION,
                                        text=True, timeout=120).splitlines()
    rendered = json.loads(lines[-1])
    audit = '\n'.join(lines[:-1])+'\n'
    checker.audit_dependencies(audit, names)
    checked = [dict(directory=case['directory'], entry=verify_entry(
        read_artifact(run, report, case['directory']+'/kernel.ptx').decode(), code, layout))
        for case, code, layout in zip(report['cases'], rendered, layouts, strict=True)]
    checker.dependencies()
    if hashes() != before:
        raise ValueError('sources changed during checking')
    result = dict(status='pass', scope=__doc__.strip(), checked=checked,
        source_sha256=before, audited_theorems=names, axiom_audit=audit,
        source_run_report_sha256=hashlib.sha256((run/'report.json').read_bytes()).hexdigest())
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'Checked {len(checked)} complete initialization entries.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.run, args.output)
