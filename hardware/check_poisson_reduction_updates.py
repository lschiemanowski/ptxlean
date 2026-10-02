#!/usr/bin/env python3
"""Bind the six-instruction active-lane update in saved Poisson reductions.

This checks all eight updates in each of six dot entries, their immediate
lane guards and following barriers, and the block/shared allocation. It does
not bind the strided input loop, prologue, final scalar store, or entire entry.
The Lean theorem uses a scalar shared-byte view; concurrent source selection,
the rounded fold/tree, and full solver correspondence remain separate.
No GPU execution is performed. Pinned integration dependencies must be built.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile

from check_poisson_ptx import ROOT, INTEGRATION, read_artifact

STRIDES = (128, 64, 32, 16, 8, 4, 2, 1)
ENTRIES = ('dot_rhs', 'dot_rz', 'dot_pap', 'dot_next', 'dot_rr', 'dot_true')


def verify_updates(ptx, rendered):
    if any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('comments are outside the exact generated dialect')
    if len(rendered) != len(STRIDES) or any(len(code) != 6 for code in rendered):
        raise ValueError('expected eight six-instruction Lean updates')
    lines = [line.strip() for line in ptx.splitlines() if line.strip()]
    if lines[:3] not in ([f'.version {v}', '.target sm_120', '.address_size 64'] for v in ('9.2', '9.4')):
        raise ValueError('unreviewed target/version')
    checked = []
    for entry in ENTRIES:
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1 or len(re.findall(r'\.entry\s+'+entry+r'\b', ptx)) != 1:
            raise ValueError('entry missing or duplicated: '+entry)
        body = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        if body[0] != '.reqntid 256, 1, 1' or body.count('.shared .align 8 .b8 scratch[2048];') != 1:
            raise ValueError('unexpected reduction allocation or block shape')
        positions = []
        for stride, code in zip(STRIDES, rendered, strict=True):
            guard = f'setp.ge.u32 %p0, %lane, {stride};'
            branch, label = f'@%p0 bra next_{stride};', f'next_{stride}:'
            if any(body.count(line) != 1 for line in (guard, branch, label)):
                raise ValueError('missing or duplicated stage boundary')
            pos = body.index(guard)
            expected = [guard, branch, *code, label, 'bar.sync 0;']
            if body[pos:pos+len(expected)] != expected:
                raise ValueError(f'{entry}/{stride}: differs from proved local update')
            positions.append(pos)
            checked.append(dict(entry=entry, stride=stride,
                sha256=hashlib.sha256(('\n'.join(code)+'\n').encode()).hexdigest()))
        if any(b != a+10 for a, b in zip(positions, positions[1:])):
            raise ValueError('stages are reordered or separated by extra instructions')
    return checked


def check(run, output):
    if output.exists():
        raise ValueError('output already exists')
    report = json.loads((run/'report.json').read_text())
    if report['numerical_status'] != 'pass' or not report['cases']:
        raise ValueError('requires a completed nonempty saved run')
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
    lean = ['lake', '--no-cache', 'env', 'lean', '-j1', '-M5120']
    subprocess.run(lean+['-o', '.lake/build/lib/lean/PoissonPTX/ReductionUpdate.olean',
        'PoissonPTX/ReductionUpdate.lean'], cwd=INTEGRATION, check=True, timeout=120)
    names = ['PtxTorchLean.Poisson.PTX.Reduction.Update.'+name for name in
        ('effect', 'run_update', 'correct', 'fetched_correct', 'fetched_exists', 'valid_of_active')]
    with tempfile.TemporaryDirectory(prefix='poisson-reduction-update-') as tmp:
        path = Path(tmp)/'Render.lean'
        path.write_text('import PoissonPTX.ReductionUpdate\nimport PoissonPTX.Text\n'+
            ''.join('#print axioms '+name+'\n' for name in names)+
            'open PtxTorchLean.Poisson.PTX\n'+
            'def main : IO Unit := IO.println (Lean.toJson '+
            '(([128,64,32,16,8,4,2,1] : List Nat).map fun stride => '+
            '(Reduction.Update.code (BitVec.ofNat 64 (stride*8))).map Text.data)).compress\n')
        lines = subprocess.check_output(lean+['--run', str(path)], cwd=INTEGRATION,
            text=True, timeout=120).splitlines()
    rendered = json.loads(lines[-1])
    audit = '\n'.join(lines[:-1])+'\n'
    checker.audit_dependencies(audit, names)
    checked = [dict(directory=case['directory'], updates=verify_updates(
        read_artifact(run, report, case['directory']+'/kernel.ptx').decode(), rendered))
        for case in report['cases']]
    checker.dependencies()
    if hashes() != before:
        raise ValueError('sources changed during checking')
    result = dict(status='pass', scope=__doc__.strip(), checked=checked,
        source_sha256=before, audited_theorems=names, axiom_audit=audit,
        source_run_report_sha256=hashlib.sha256((run/'report.json').read_bytes()).hexdigest())
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'Checked {sum(len(c["updates"]) for c in checked)} local reduction updates in {len(checked)} saved layouts.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.run, args.output)
