#!/usr/bin/env python3
"""Bind each Poisson dot entry's setup and complete strided input loop.

The proved per-lane loop uses a scalar read snapshot; connecting that snapshot
to the entire concurrent entry remains a separate memory-source obligation.
No GPU execution or compiler/hardware conformance is established here.
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

FIELDS = dict(dot_rhs=('rhs', 'rhs'), dot_rz=('r', 'z'), dot_pap=('p', 'ap'),
              dot_next=('r', 'z'), dot_rr=('r', 'r'), dot_true=('true_r', 'true_r'))


def parameters(layout):
    n, degree = layout['n'], layout['degree']
    if type(n) is not int or n < 1 or type(degree) is not int or degree not in (1, 2, 3, 4):
        raise ValueError('unsupported mesh dimensions')
    count = (n*degree+1)**2
    if count >= 2**30 or type(layout['bytes']) is not int or not 0 < layout['bytes'] < 2**64:
        raise ValueError('unsupported index or allocation extent')
    result = {}
    for entry, fields in FIELDS.items():
        offsets = []
        for name in fields:
            field = layout['fields'][name]
            off = field['offset']
            if field['kind'] != 'd' or field['count'] != count or type(off) is not int or off < 0 or off % 8:
                raise ValueError('invalid binary64 input field')
            if off + count*8 > layout['bytes']:
                raise ValueError('input field outside arena')
            offsets.append(off)
        launch = layout['launches'][entry]
        if launch != dict(groups=1, threads=256, shared_bytes=2048):
            raise ValueError('unsupported dot-product launch')
        result[entry] = [count, *offsets]
    return result


def verify_input(ptx, rendered):
    if any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('comments outside reviewed dialect')
    lines = [line.strip() for line in ptx.splitlines() if line.strip()]
    if lines[:3] not in ([f'.version {v}', '.target sm_120', '.address_size 64'] for v in ('9.2', '9.4')):
        raise ValueError('unreviewed target/version')
    if set(rendered) != set(FIELDS):
        raise ValueError('missing or extra rendered input programs')
    checked = []
    for entry, expected in rendered.items():
        if len(expected) != 20:
            raise ValueError('expected complete twenty-instruction input program')
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1 or len(re.findall(r'\.entry\s+'+entry+r'\b', ptx)) != 1:
            raise ValueError('entry missing or duplicated')
        body = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        header = HEADER + ['.shared .align 8 .b8 scratch[2048];']
        if body[:len(header)] != header or body.count('finish:') != 1 or body.count('loop:') != 1:
            raise ValueError('unexpected entry declaration or control labels')
        stop = body.index('finish:')
        instructions, labels = [], {}
        for line in body[len(header):stop+1]:
            if line.endswith(':'):
                labels[line[:-1]] = len(instructions)
            else:
                instructions.append(line)
        if labels != dict(loop=6, finish=20):
            raise ValueError('incorrect loop boundaries')
        for pos, line in enumerate(instructions):
            branch = re.fullmatch(r'(@%p0 )?bra (loop|finish);', line)
            if branch:
                instructions[pos] = f'{branch[1] or ""}bra #{labels[branch[2]]};'
        if instructions != expected:
            raise ValueError(entry+': differs from proved input program')
        # The tree and epilogue cannot reenter the input loop.
        for line in body[stop+1:]:
            if re.search(r'\bbra\s+(loop|finish);', line):
                raise ValueError('reentry from omitted continuation')
        checked.append(dict(entry=entry, instructions=len(instructions),
            sha256=hashlib.sha256(('\n'.join(instructions)+'\n').encode()).hexdigest()))
    return checked


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
    names = ['PtxTorchLean.Poisson.PTX.DotInput.'+name for name in
             ('input_correct', 'input_exists', 'arrays_valid', 'contribution_array', 'progress', 'lane_copy')]
    layouts = [parameters(json.loads(read_artifact(run, report, case['directory']+'/layout.json')))
               for case in report['cases']]
    expressions = []
    for layout in layouts:
        entries = []
        for name, (count, left, right) in layout.items():
            entries.append(f'({json.dumps(name)}, DotInput.rendered {count} {left} {right})')
        expressions.append('['+', '.join(entries)+']')
    lean = ['lake', '--no-cache', 'env', 'lean', '-j1', '-M5120']
    with tempfile.TemporaryDirectory(prefix='poisson-dot-input-') as tmp:
        path = Path(tmp)/'Render.lean'
        path.write_text('import PoissonPTX.DotInputText\nopen PtxTorchLean.Poisson.PTX\n'+
            ''.join('#print axioms '+name+'\n' for name in names)+
            'def main : IO Unit := IO.println (Lean.toJson (['+', '.join(expressions)+
            '] : List (List (String × List String)))).compress\n')
        lines = subprocess.check_output(lean+['--run', str(path)], cwd=INTEGRATION,
                                        text=True, timeout=120).splitlines()
    rendered = json.loads(lines[-1])
    audit = '\n'.join(lines[:-1])+'\n'
    checker.audit_dependencies(audit, names)
    checked = [dict(directory=case['directory'], inputs=verify_input(
        read_artifact(run, report, case['directory']+'/kernel.ptx').decode(), dict(code)))
        for case, code in zip(report['cases'], rendered, strict=True)]
    checker.dependencies()
    if hashes() != before:
        raise ValueError('sources changed during checking')
    result = dict(status='pass', scope=__doc__.strip(), checked=checked,
        source_sha256=before, audited_theorems=names, axiom_audit=audit,
        source_run_report_sha256=hashlib.sha256((run/'report.json').read_bytes()).hexdigest())
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'Checked {sum(len(c["inputs"]) for c in checked)} complete input programs in {len(checked)} layouts.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.run, args.output)
