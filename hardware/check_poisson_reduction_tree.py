#!/usr/bin/env python3
"""Bind the complete 76-instruction Poisson shared tree to its Lean program.

Checks actual comparison instructions, resolved branch destinations, initial
publication, all updates and barriers. The global input loop and output tail
remain outside this slice. Events use stable logical slot identities; the Lean
position map proves their correspondence with native instruction positions.
No GPU run, compiler conformance or complete PTX memory admission is claimed.
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
from check_poisson_reduction_updates import ENTRIES


def verify_tree(ptx, rendered):
    if any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('comments outside reviewed dialect')
    if len(rendered) != 76:
        raise ValueError('expected the complete 76-instruction Lean tree')
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
            raise ValueError('unexpected allocation or block shape')
        if body.count('finish:') != 1 or body.count('setp.ne.u32 %p0, %lane, 0;') != 1:
            raise ValueError('missing or duplicate slice boundary')
        begin, end = body.index('finish:')+1, body.index('setp.ne.u32 %p0, %lane, 0;')
        labels, instructions = {}, []
        for line in body[begin:end]:
            if line.endswith(':'):
                label = line[:-1]
                if not re.fullmatch(r'next_[0-9]+', label) or label in labels:
                    raise ValueError('unreviewed or duplicate tree label')
                labels[label] = len(instructions)
            else:
                instructions.append(line)
        for label in labels:
            if body.count(label+':') != 1:
                raise ValueError('ambiguous branch destination')
        for pos, line in enumerate(instructions):
            branch = re.fullmatch(r'@%p0 bra (next_[0-9]+);', line)
            if branch:
                if branch[1] not in labels:
                    raise ValueError('undefined branch label')
                instructions[pos] = f'@%p0 bra #{labels[branch[1]]};'
        if instructions != rendered:
            raise ValueError(entry+': differs from proved complete native tree')
        # The omitted loop may enter only at the initial publication, not
        # halfway through a guard or after a barrier.
        for line in body[:begin-1]+body[end:]:
            if 'bra ' in line and line not in ('@%p0 bra finish;', 'bra loop;'):
                raise ValueError('external branch may bypass part of the tree')
        checked.append(dict(entry=entry, instructions=len(instructions),
            sha256=hashlib.sha256(('\n'.join(instructions)+'\n').encode()).hexdigest()))
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
        ROOT/'hardware/check_poisson_ptx.py', ROOT/'hardware/check_poisson_reduction_updates.py',
        ROOT/'hardware/poisson_kernels.py']
    def hashes():
        return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    before = hashes()
    lean = ['lake', '--no-cache', 'env', 'lean', '-j1', '-M5120']
    subprocess.run(lean+['-o', '.lake/build/lib/lean/PoissonPTX/ReductionNative.olean',
        'PoissonPTX/ReductionNative.lean'], cwd=INTEGRATION, check=True, timeout=120)
    names = ['PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.'+name for name in
        ('correct', 'exists_correct', 'safe', 'positions', 'compare_fetch', 'branch_fetch', 'data_fetch', 'sync_release', 'zero_displacement')]
    with tempfile.TemporaryDirectory(prefix='poisson-reduction-update-') as tmp:
        path = Path(tmp)/'Render.lean'
        path.write_text('import PoissonPTX.ReductionNative\nimport PoissonPTX.ReductionNativeText\n'+
            ''.join('#print axioms '+name+'\n' for name in names)+
            'def main : IO Unit := IO.println (Lean.toJson '+
            'PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native.rendered).compress\n')
        lines = subprocess.check_output(lean+['--run', str(path)], cwd=INTEGRATION,
            text=True, timeout=120).splitlines()
    rendered = json.loads(lines[-1])
    audit = '\n'.join(lines[:-1])+'\n'
    checker.audit_dependencies(audit, names)
    checked = [dict(directory=case['directory'], trees=verify_tree(
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
    print(f'Checked {sum(len(c["trees"]) for c in checked)} complete native shared trees in {len(checked)} saved layouts.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.run, args.output)
