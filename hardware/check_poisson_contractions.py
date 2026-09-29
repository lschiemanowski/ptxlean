#!/usr/bin/env python3
"""Bind local cell contraction and shared-store blocks to their proved Lean programs.

Complete middle-phase bodies are bound to the concurrent Lean program with
kernel-checked control, address and numerical certificates for Q1--Q4. Completed
middle-slice executions satisfying necessary byte-source constraints store all
six TorchLean intermediate tensors. The gather, prologue, final output, full
launch composition and complete PTX memory admission remain open.
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


def parameters(layout):
    width = layout['degree'] + 1
    if type(layout['degree']) is not int or not 2 <= width <= 5:
        raise ValueError('expected Q1--Q4')
    if type(layout['bytes']) is not int or not 0 < layout['bytes'] < 2**64:
        raise ValueError('invalid arena size')
    result = {'width': width}
    for name in ('B', 'D', 'W'):
        field = layout['fields'][name]
        if (field['kind'] != 'd' or field['count'] != width*width or
                type(field['offset']) is not int or field['offset'] < 0 or
                field['offset'] % 8 or field['offset']+width*width*8 > layout['bytes']):
            raise ValueError('invalid matrix layout')
        result[name] = field['offset']
    return result


def verify_blocks(ptx, rendered, layout):
    params = parameters(layout)
    if any(t in ptx for t in ('//', '/*', '*/')):
        raise ValueError('comments are outside the exact generated dialect')
    lines = [l.strip() for l in ptx.splitlines() if l.strip()]
    if lines[:3] not in ([f'.version {v}', '.target sm_120', '.address_size 64'] for v in ('9.2', '9.4')):
        raise ValueError('unreviewed PTX target/version')
    if [name for name, _ in rendered] != ['bu', 'du', 'dx', 'dy', 'bl', 'dl', 'x', 'y']:
        raise ValueError('expected eight ordered contraction plans')
    checked = []
    for entry in ('element_probe', 'element_p', 'element_x'):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1 or len(re.findall(r'\.entry\s+'+entry+r'\b', ptx)) != 1:
            raise ValueError('entry missing or duplicated')
        body = [l.strip() for l in bodies[0].splitlines() if l.strip()]
        if body[0] != '.reqntid 32, 1, 1' or f'.shared .align 8 .b8 scratch[{7*params["width"]**2*8}];' not in body:
            raise ValueError('unexpected shared layout or thread shape')
        starts = [i for i, line in enumerate(body) if re.fullmatch(r'mov.f64 %acc2?, 0d0000000000000000;', line)]
        if len(starts) != 8:
            raise ValueError('missing or extra contraction initialization')
        for start, (name, code) in zip(starts, rendered, strict=True):
            if body[start:start+len(code)] != code:
                raise ValueError(f'{entry}/{name}: emitted contraction differs from proved program')
            checked.append(dict(entry=entry, contraction=name, instructions=len(code),
                                sha256=hashlib.sha256(('\n'.join(code)+'\n').encode()).hexdigest()))
    return checked


def verify_stores(ptx, rendered, layout, contractions):
    parameters(layout)
    if [plane for plane, _ in rendered] != list(range(7)):
        raise ValueError('expected seven ordered shared-store plans')
    checked = []
    for entry in ('element_probe', 'element_p', 'element_x'):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1:
            raise ValueError('entry missing or duplicated')
        body = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        ends = [i for i, line in enumerate(body) if 'st.shared' in line]
        if len(ends) != 7:
            raise ValueError('missing or extra shared store')
        for end, (plane, code) in zip(ends, rendered, strict=True):
            if len(code) != 3 or end < 2 or body[end-2:end+1] != code:
                raise ValueError(f'{entry}/plane {plane}: shared store differs from proved program')
            adjacent = {1: 'bu', 2: 'du', 5: 'bl', 6: 'dl'}.get(plane)
            if adjacent is not None:
                combined = dict(contractions)[adjacent] + code
                if end+1 < len(combined) or body[end+1-len(combined):end+1] != combined:
                    raise ValueError(f'{entry}/{adjacent}: contraction is not adjacent to its proved store')
            checked.append(dict(entry=entry, plane=plane, adjacent_contraction=adjacent, instructions=len(code),
                                sha256=hashlib.sha256(('\n'.join(code)+'\n').encode()).hexdigest()))
    return checked


def verify_control(ptx, layout):
    """Check the generated five-phase skeleton, separately from body semantics."""
    width = parameters(layout)['width']
    checked = []
    for entry in ('element_probe', 'element_p', 'element_x'):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1:
            raise ValueError('entry missing or duplicated')
        body = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        if body[0] != '.reqntid 32, 1, 1':
            raise ValueError('barrier fragment requires the generated 32-thread block')
        guards = [i for i, line in enumerate(body) if line.startswith('@')]
        labels = [i for i, line in enumerate(body) if line.endswith(':')]
        barriers = [i for i, line in enumerate(body) if line.startswith(('bar.', 'barrier.'))]
        if len(guards) != 5 or len(labels) != 5 or len(barriers) != 4:
            raise ValueError('unexpected phase control count')
        prelude = [f'setp.lt.u32 %live, %lane, {width*width};',
                   f'div.u32 %i, %lane, {width};', f'rem.u32 %j, %lane, {width};']
        if body[guards[0]-3:guards[0]] != prelude:
            raise ValueError('unexpected live-lane predicate or matrix coordinates')
        for phase, (guard, label) in enumerate(zip(guards, labels, strict=True)):
            if body[guard] != f'@!%live bra stage_{phase}_done;' or body[label] != f'stage_{phase}_done:' or guard >= label:
                raise ValueError('guard must skip its body to its own phase boundary')
            for line in body[guard+1:label]:
                if line.startswith(('bra', 'bar.', 'barrier.', 'ret', 'exit', 'call', '@')) or '%live' in line:
                    raise ValueError('unsupported body control or predicate modification')
            if phase < 4:
                if barriers[phase] != label+1 or body[label+1] != 'bar.sync 0;' or guards[phase+1] != label+2:
                    raise ValueError('all lanes must meet the unpredicated barrier before the next phase')
            elif body[label+1:] != ['ret;']:
                raise ValueError('unexpected final phase exit')
        checked.append(dict(entry=entry, participants=32, active_lanes=width*width,
                            phase_count=5, barrier_resource=0, completed_boundaries=4))
    return checked


def verify_middle(ptx, rendered, layout):
    """Bind every instruction of phases 1--3, including weights and controls."""
    params = parameters(layout)
    width = params['width']
    if (params['B'], params['D'], params['W']) != (0, width*width*8+32, 2*(width*width*8+32)):
        raise ValueError('middle layout has no kernel-checked structural certificate')
    verify_control(ptx, layout)
    if len(rendered) != 3 or any(not body for body in rendered):
        raise ValueError('expected three nonempty middle phase bodies')
    checked = []
    for entry in ('element_probe', 'element_p', 'element_x'):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1:
            raise ValueError('entry missing or duplicated')
        lines = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        pc = 0
        phases = []
        for phase, code in enumerate(rendered, 1):
            begin = lines.index(f'@!%live bra stage_{phase}_done;')
            end = lines.index(f'stage_{phase}_done:')
            if lines[begin+1:end] != code:
                raise ValueError(f'{entry}/phase {phase}: complete middle body differs from Lean program')
            phases.append(dict(phase=phase, guard_pc=pc, barrier_pc=pc+1+len(code),
                               body_instructions=len(code)))
            pc += len(code)+2
        checked.append(dict(entry=entry, instructions=pc, phases=phases,
                            sha256=hashlib.sha256(json.dumps(rendered).encode()).hexdigest()))
    return checked


def check(run, output):
    if output.exists():
        raise ValueError('output already exists')
    report = json.loads((run/'report.json').read_text())
    if report['numerical_status'] != 'pass' or not report['cases']:
        raise ValueError('requires a completed nonempty saved run')
    for name in report['artifacts']:
        read_artifact(run, report, name)
    paths = [*sorted((INTEGRATION/'PoissonPTX').glob('*.lean')), INTEGRATION/'PoissonContractionsMain.lean',
             INTEGRATION/'PoissonQuadCorrespondence.lean', INTEGRATION/'check.py',
             INTEGRATION/'lakefile.toml', INTEGRATION/'lake-manifest.json', INTEGRATION/'lean-toolchain',
             Path(__file__).resolve(), ROOT/'hardware/check_poisson_ptx.py']
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    spec = importlib.util.spec_from_file_location('integration_check', INTEGRATION/'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.dependencies()
    version = subprocess.check_output(['lake', '--no-cache', 'env', 'lean', '--version'], cwd=INTEGRATION, text=True)
    pin = (INTEGRATION/'lean-toolchain').read_text().strip().removeprefix('leanprover/lean4:v')
    if not version.startswith(f'Lean (version {pin},'):
        raise ValueError('toolchain differs from pin')
    subprocess.run(['lake', '--no-cache', 'build', 'poissonContractions', 'PoissonPTX.ContractionFetched',
                    'PoissonPTX.ContractionLayout', 'PoissonPTX.SharedPlane', 'PoissonPTX.CellMiddleChecks',
                    'PoissonPTX.ConcurrentComputedStore', 'PoissonPTX.CellMiddleInputs',
                    'PoissonPTX.CellMiddleCorrespondence'], cwd=INTEGRATION, check=True)
    names = ['PtxTorchLean.Poisson.PTX.Contraction.'+n for n in
             ('fetched_correct', 'fetched_exists', 'valid_of_matrix', 'plans_accumulator')]
    names += ['PtxTorchLean.Poisson.PTX.SharedStore.'+n for n in
              ('fetched_correct', 'fetched_exists', 'valid_of_plane', 'fetched_contraction_store', 'fetched_contraction_store_exists')]
    names += ['PtxTorchLean.Poisson.PTX.SharedPlane.'+n for n in
              ('store_address', 'published_store', 'published_contraction', 'order_independent', 'contraction_value')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Checks.'+n for n in
              ('q1', 'q2', 'q3', 'q4', 'checked', 'coverage', 'unique', 'publication')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.Replay.'+n for n in
              ('run_view', 'contraction', 'stored_contraction', 'published_contraction')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Inputs.'+n for n in
              ('shared_stores', 'global_readonly', 'input_readonly', 'initial_value')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.Symbolic.'+n for n in
              ('data_sound', 'runs_invariant')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellMiddle.Numeric.'+n for n in
              ('loads', 'stores', 'load_location', 'all_reads', 'store_expression',
               'producer', 'plane_equations', 'completed_middle', 'completed_store')]
    with tempfile.TemporaryDirectory(prefix='poisson-contraction-audit-') as tmp:
        p = Path(tmp)/'Audit.lean'
        p.write_text('import PoissonPTX.SharedPlane\nimport PoissonPTX.ContractionFetched\nimport PoissonPTX.ContractionLayout\nimport PoissonPTX.ContractionText\nimport PoissonPTX.CellMiddleChecks\nimport PoissonPTX.ConcurrentComputedStore\nimport PoissonPTX.CellMiddleInputs\nimport PoissonPTX.CellMiddleCorrespondence\n'+
                     ''.join('#print axioms '+n+'\n' for n in names))
        audit = subprocess.check_output(['lake', '--no-cache', 'env', 'lean', p], cwd=INTEGRATION, text=True)
        checker.audit_dependencies(audit, names)
    layouts = [json.loads(read_artifact(run, report, c['directory']+'/layout.json')) for c in report['cases']]
    rendered = json.loads(subprocess.check_output([INTEGRATION/'.lake/build/bin/poissonContractions'],
        input=json.dumps([parameters(l) for l in layouts])+'\n', text=True))
    checked = [dict(directory=c['directory'], blocks=verify_blocks(
        read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['contractions'], layout),
        stores=verify_stores(read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['stores'], layout, code['contractions']),
        control=verify_control(read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), layout),
        middle=verify_middle(read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['middle'], layout))
        for c, layout, code in zip(report['cases'], layouts, rendered, strict=True)]
    checker.dependencies()
    if hashes != {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}:
        raise ValueError('proof/frontend sources changed during checking')
    result = dict(status='pass', scope=__doc__.strip(), checked=checked, audited_theorems=names,
                  axiom_audit=audit, source_sha256=hashes,
                  source_run_report_sha256=hashlib.sha256((run/'report.json').read_bytes()).hexdigest(),
                  source_run_artifacts=report['artifacts'])
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        raise ValueError('output already exists')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(f'Checked {sum(len(c["blocks"]) for c in checked)} contraction blocks and '
          f'{sum(len(c["stores"]) for c in checked)} shared-store blocks in {len(checked)} saved layouts.')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    check(args.run, args.output)
