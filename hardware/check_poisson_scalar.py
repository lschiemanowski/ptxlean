#!/usr/bin/env python3
"""Bind complete scalar residual-norm and restart-flag entries to Lean.

The proofs cover fetched instructions, actual byte sources, numerical/status
publication, byte frames and finite source-compatible execution. Necessary
single-thread causality is explicit; complete PTX memory admission, CUDA
transport, host composition and GPU conformance remain separate.
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
from check_poisson_control import arena_parameters, FIELDS


def parameters(layout):
    offsets = dict(zip((name for name, _ in FIELDS), arena_parameters(layout), strict=True))
    for entry in ('residual_norm', 'restart_flag'):
        if layout['launches'][entry] != dict(groups=1, threads=1, shared_bytes=0):
            raise ValueError('unreviewed scalar launch')
    return [offsets[name] for name in ('true_square', 'residual', 'active')]


def verify_entry(ptx, expected, layout, entry):
    parameters(layout)
    if entry not in ('residual_norm', 'restart_flag'):
        raise ValueError('unreviewed scalar entry')
    if len(expected) != dict(residual_norm=13, restart_flag=8)[entry] or any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('incomplete program or unreviewed comments')
    lines = [line.strip() for line in ptx.splitlines() if line.strip()]
    if lines[:3] not in ([f'.version {v}', '.target sm_120', '.address_size 64'] for v in ('9.2', '9.4')):
        raise ValueError('unreviewed module target/version')
    entries = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
    if len(entries) != 1 or len(re.findall(r'\.entry\s+'+entry+r'\b', ptx)) != 1:
        raise ValueError('missing or duplicate entry')
    actual = [line.strip() for line in entries[0].splitlines() if line.strip()]
    if actual != ['.reqntid 1, 1, 1', *HEADER[1:]]+expected:
        raise ValueError(entry+' differs from proved instruction list')
    return dict(entry=entry, instructions=len(expected),
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
             ROOT/'hardware/check_poisson_ptx.py', ROOT/'hardware/check_poisson_control.py', ROOT/'hardware/poisson_kernels.py']
    def hashes():
        return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    before = hashes()
    names = ['PtxTorchLean.Poisson.PTX.Scalar.'+namespace+'.'+name
             for namespace in ('Norm', 'RestartFlag') for name in ('entry_correct', 'entry_exists', 'entry_length', 'admitted_publication', 'admitted_exists')]
    layouts = [json.loads(read_artifact(run, report, case['directory']+'/layout.json'))
               for case in report['cases']]
    expressions = []
    for layout in layouts:
        source_offset, output_offset, active = parameters(layout)
        expressions.extend([f'Scalar.Text.norm {source_offset} {output_offset}', f'Scalar.Text.restartFlag {active}'])
    lean = ['lake', '--no-cache', 'env', 'lean', '-j1', '-M5120']
    with tempfile.TemporaryDirectory(prefix='poisson-scalar-') as tmp:
        path = Path(tmp)/'Render.lean'
        path.write_text('import PoissonPTX.ScalarText\nimport PoissonPTX.ScalarNormAdmission\nopen PtxTorchLean.Poisson.PTX\n'+
            ''.join('#print axioms '+name+'\n' for name in names)+
            'def main : IO Unit := IO.println (Lean.toJson (['+', '.join(expressions)+
            '] : List (List String))).compress\n')
        lines = subprocess.check_output(lean+['--run', str(path)], cwd=INTEGRATION,
                                        text=True, timeout=120).splitlines()
    rendered = json.loads(lines[-1])
    audit = '\n'.join(lines[:-1])+'\n'
    checker.audit_dependencies(audit, names)
    if len(rendered) != 2*len(layouts):
        raise ValueError('incomplete rendering')
    checked = []
    for i, (case, layout) in enumerate(zip(report['cases'], layouts, strict=True)):
        ptx = read_artifact(run, report, case['directory']+'/kernel.ptx').decode()
        for j, entry in enumerate(('residual_norm', 'restart_flag')):
            checked.append(dict(directory=case['directory'], entry=verify_entry(ptx, rendered[2*i+j], layout, entry)))
    checker.dependencies()
    if hashes() != before:
        raise ValueError('sources changed during checking')
    result = dict(status='pass', scope=__doc__.strip(), checked=checked,
        source_sha256=before, audited_theorems=names, axiom_audit=audit,
        source_run_report_sha256=hashlib.sha256((run/'report.json').read_bytes()).hexdigest())
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'Checked {len(checked)} complete scalar entries.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.run, args.output)
