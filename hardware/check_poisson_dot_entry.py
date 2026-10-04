#!/usr/bin/env python3
"""Bind complete Poisson dot entries to the 104-position concurrent program.

The current theorems recover each returned lane's rounded input partial sum
from whole-history source admission, identify its initial shared publication,
and prove output-address ownership and actual completion of all nine barriers.
The concurrent tree value join, final result publication and whole-entry existence
remain separate obligations. This check does not establish GPU conformance.
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
from check_poisson_dot_input import parameters as input_parameters, FIELDS

OUTPUTS = dict(dot_rhs='rhs_square', dot_rz='rho', dot_pap='denominator',
               dot_next='rho_next', dot_rr='rr', dot_true='true_square')


def parameters(layout):
    entries = input_parameters(layout)
    for entry, (count, left, right) in entries.items():
        field = layout['fields'][OUTPUTS[entry]]
        off = field['offset']
        if (field['kind'] != 'd' or field['count'] != 1 or type(off) is not int
                or off < 0 or off % 8 or off+8 > layout['bytes']):
            raise ValueError('invalid output word')
        if any(not (off+8 <= start or start+count*8 <= off) for start in (left, right)):
            raise ValueError('output overlaps input')
        entries[entry] = [count, left, right, off]
    return entries


def verify_entry(ptx, rendered):
    if any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('comments outside reviewed dialect')
    lines = [line.strip() for line in ptx.splitlines() if line.strip()]
    if lines[:3] not in ([f'.version {v}', '.target sm_120', '.address_size 64'] for v in ('9.2', '9.4')):
        raise ValueError('unreviewed target/version')
    if set(rendered) != set(FIELDS):
        raise ValueError('missing or extra rendered dot entries')
    checked = []
    for entry, expected in rendered.items():
        if len(expected) != 104:
            raise ValueError('expected complete 104-instruction dot entry')
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1 or len(re.findall(r'\.entry\s+'+entry+r'\b', ptx)) != 1:
            raise ValueError('entry missing or duplicated')
        body = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        header = HEADER + ['.shared .align 8 .b8 scratch[2048];']
        if body[:len(header)] != header:
            raise ValueError('unexpected entry declaration')
        instructions, labels = [], {}
        for line in body[len(header):]:
            if line.endswith(':'):
                name = line[:-1]
                if name in labels:
                    raise ValueError('duplicate label')
                labels[name] = len(instructions)
            else:
                instructions.append(line)
        expected_labels = dict(loop=6, finish=20)
        expected_labels.update({f'next_{stride}': 32+9*i for i, stride in enumerate((128,64,32,16,8,4,2,1))})
        if labels != expected_labels:
            raise ValueError('incorrect control boundaries')
        for pos, line in enumerate(instructions):
            branch = re.fullmatch(r'(@%p0 )?bra (\w+);', line)
            if branch:
                if branch[2] not in labels:
                    raise ValueError('unknown branch target')
                instructions[pos] = f'{branch[1] or ""}bra #{labels[branch[2]]};'
        if instructions != expected:
            raise ValueError(entry+': differs from complete proved instruction list')
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
             ROOT/'hardware/check_poisson_ptx.py', ROOT/'hardware/check_poisson_dot_input.py', ROOT/'hardware/poisson_kernels.py']
    def hashes():
        return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    before = hashes()
    names = ['PtxTorchLean.Poisson.PTX.Concurrent.Dot.'+name for name in
             ('completed_input_correct', 'publication_contents', 'publication_memory_bound', 'returned_barriers', 'stores_output', 'input_observations', 'input_region', 'length')]
    layouts = [parameters(json.loads(read_artifact(run, report, case['directory']+'/layout.json')))
               for case in report['cases']]
    expressions = []
    for layout in layouts:
        entries = []
        for name, (count, left, right, out) in layout.items():
            entries.append(f'({json.dumps(name)}, Concurrent.Dot.rendered {count} {left} {right} {out})')
        expressions.append('['+', '.join(entries)+']')
    lean = ['lake', '--no-cache', 'env', 'lean', '-j1', '-M5120']
    with tempfile.TemporaryDirectory(prefix='poisson-dot-entry-') as tmp:
        path = Path(tmp)/'Render.lean'
        path.write_text('import PoissonPTX.DotProgramText\nimport PoissonPTX.DotPublicationSafety\nimport PoissonPTX.DotReturns\nopen PtxTorchLean.Poisson.PTX\n'+
            ''.join('#print axioms '+name+'\n' for name in names)+
            'def main : IO Unit := IO.println (Lean.toJson (['+', '.join(expressions)+
            '] : List (List (String × List String)))).compress\n')
        lines = subprocess.check_output(lean+['--run', str(path)], cwd=INTEGRATION,
                                        text=True, timeout=120).splitlines()
    rendered = json.loads(lines[-1])
    audit = '\n'.join(lines[:-1])+'\n'
    checker.audit_dependencies(audit, names)
    checked = [dict(directory=case['directory'], entries=verify_entry(
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
    print(f'Checked {sum(len(c["entries"]) for c in checked)} complete dot-entry programs in {len(checked)} layouts.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.run, args.output)
