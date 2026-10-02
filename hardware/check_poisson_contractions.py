#!/usr/bin/env python3
"""Bind local cell contraction and shared-store blocks to their proved Lean programs.

Complete middle-phase bodies are bound to the concurrent Lean program with
kernel-checked control, address and numerical certificates for Q1--Q4. Completed
middle-slice executions satisfying necessary byte-source constraints store all
six TorchLean intermediate tensors. The final body has a fetched, snapshot-based
store theorem and phase-by-phase composition with actual middle stores. A
concurrent arithmetic extension now justifies the actual final loads using one
whole-history source assignment and connects its result to the fetched store.
The arithmetic theorem derives its middle prefix and continuation at the last
barrier from a single run. A combined concurrent index/store/return machine now
derives that arithmetic execution, its ordered event embedding and result
register relation, with only global output stores omitted. Byte-source
restriction preserves retained reads when those stores are beyond the bounded
coefficient region. Actual store addresses now follow from launch bounds, and
each completed active lane's stored bytes have its TorchLean value. Actual store
occurrence and recorded values imply an order-independent published global
tensor equal to TorchLean. This mathematical publication leaves CUDA host
visibility and complete PTX memory admission open.
The seven-instruction register prologue is separately proved from launch context
and bound with its declarations to each emitted element entry. The twelve-step
active gather has a fetched snapshot proof, derived layout safety and a TorchLean
input theorem; its complete body is bound for all three source vectors. The
concurrent 21-instruction prefix now derives original input reads, gathered bits,
actual barrier completion and the arithmetic launch contract. Actual store
coverage, values, padding exclusion and byte ownership are also proved. Actual
first-barrier ordering and preservation by the arithmetic/output body now derive
continuation reads from those gathered stores. Source rebasing now connects the
actual gather to the numerical body and its published TorchLean cell tensor.
A single native-counter run now derives the prefix/body split and joint-history
input admission, and publishes the TorchLean cell tensor. Remaining solver
entry composition and launch composition remain open. The isolated assembly
traversal now has ordered-fold correctness and general existence from allocated
input arrays; its emitted loop slice is bound separately. Entry setup, masking,
output publication and inter-launch visibility are not part of that slice.
A coefficient representation contract also connects the complete cell theorem
to the stated TorchLean operator, with equal quadrature and node dimensions.
Saved output extents are checked disjoint; this is concrete layout evidence,
separate from the general launch-derived address theorem and GPU conformance.
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
    field = layout['fields']['element']
    if (field['kind'] != 'd' or type(field['count']) is not int or field['count'] <= 0
            or field['count'] % (width*width) or field['count'] >= 2**32
            or type(field['offset']) is not int or field['offset'] < 0 or field['offset'] % 8
            or field['offset']+field['count']*8 > layout['bytes']):
        raise ValueError('invalid element-output extent')
    coefficient_end = max(result[name]+width*width*8 for name in ('B', 'D', 'W'))
    if field['offset'] < coefficient_end:
        raise ValueError('element output overlaps coefficient region')
    result['output'] = field['offset']
    cells = layout['fields']['cells']
    if (cells['kind'] != 'I' or cells['count'] != field['count'] or
            type(cells['offset']) is not int or cells['offset'] < 0 or cells['offset'] % 4 or
            cells['offset']+cells['count']*4 > layout['bytes']):
        raise ValueError('invalid connectivity extent')
    indices = layout['fields']['entries']
    if (indices['kind'] != 'I' or type(indices['count']) is not int or indices['count'] != field['count']
            or type(indices['offset']) is not int or indices['offset'] < 0 or indices['offset'] % 4
            or indices['offset']+indices['count']*4 > layout['bytes']):
        raise ValueError('invalid assembly contribution-index extent')
    result['entries'] = indices['offset']
    result['cells'] = cells['offset']
    result['sources'] = []
    for name in ('probe', 'p', 'x'):
        f = layout['fields'][name]
        if (f['kind'] != 'd' or type(f['count']) is not int or f['count'] <= 0 or
                type(f['offset']) is not int or f['offset'] < 0 or f['offset'] % 8 or
                f['offset']+f['count']*8 > layout['bytes']):
            raise ValueError('invalid gather source extent')
        result['sources'].append(f['offset'])
    return result


def output_separation(layout):
    params = parameters(layout)
    field = layout['fields']['element']
    return dict(coefficient_end=max(params[name]+params['width']**2*8 for name in ('B', 'D', 'W')),
                output_start=params['output'], output_end=params['output']+field['count']*8,
                output_words=field['count'])


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


def verify_prologue(ptx, rendered, layout):
    """Bind the complete declared entry and all seven setup instructions."""
    width = parameters(layout)['width']
    if len(rendered) != 7:
        raise ValueError('expected seven prologue instructions')
    if any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('comments are outside the exact generated dialect')
    declarations = [
        '.reqntid 32, 1, 1', '{',
        '.reg .u32 %lane, %cell, %i, %j, %k, %idx, %node, %cursor, %end, %other, %flag, %flag2, %global;',
        '.reg .b64 %base, %off, %addr, %shared;',
        '.reg .f64 %a, %b, %c, %d, %acc, %acc2, %prod, %value;',
        '.reg .pred %live, %p0, %p1, %p2, %p3;',
        f'.shared .align 8 .b8 scratch[{7*width*width*8}];']
    checked = []
    for entry in ('element_probe', 'element_p', 'element_x'):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1 or len(re.findall(r'\.entry\s+'+entry+r'\b', ptx)) != 1:
            raise ValueError('entry missing or duplicated')
        body = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        guard = '@!%live bra stage_0_done;'
        if body.count(guard) != 1 or body[:body.index(guard)] != declarations + rendered:
            raise ValueError('entry declarations or complete prologue differ from proved program')
        checked.append(dict(entry=entry, instructions=7, participants=32,
                            shared_bytes=7*width*width*8))
    return checked


def verify_entry(ptx, rendered, layout):
    """Bind the concurrent setup/guard/gather/barrier program as one prefix."""
    parameters(layout)
    if len(rendered) != 3 or any(len(code) != 22 for code in rendered):
        raise ValueError('expected three complete 21-instruction entry prefixes plus label')
    checked = []
    for entry, code in zip(('element_probe', 'element_p', 'element_x'), rendered, strict=True):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1:
            raise ValueError('entry missing or duplicated')
        body = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        scratch = [i for i, line in enumerate(body) if line.startswith('.shared ')]
        boundary = '@!%live bra stage_1_done;'
        if len(scratch) != 1 or body.count(boundary) != 1:
            raise ValueError('entry declaration or arithmetic boundary missing')
        if body[scratch[0]+1:body.index(boundary)] != code:
            raise ValueError('complete concurrent entry prefix differs from proved program')
        checked.append(dict(entry=entry, instructions=21, barrier_pc=20, resume_pc=21))
    return checked


def verify_gather(ptx, rendered, layout):
    """Bind all twelve active gather instructions, including the four-byte load."""
    parameters(layout)
    if len(rendered) != 3 or any(len(code) != 12 for code in rendered):
        raise ValueError('expected three twelve-instruction gathers')
    checked = []
    for entry, code in zip(('element_probe', 'element_p', 'element_x'), rendered, strict=True):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1:
            raise ValueError('entry missing or duplicated')
        body = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        guard, done = '@!%live bra stage_0_done;', 'stage_0_done:'
        if body.count(guard) != 1 or body.count(done) != 1:
            raise ValueError('gather guard or boundary missing or duplicated')
        first, last = body.index(guard)+1, body.index(done)
        if body[first:last] != code or body[last+1:last+2] != ['bar.sync 0;']:
            raise ValueError('gather body differs from proved program')
        checked.append(dict(entry=entry, instructions=12, index_bytes=4, value_bytes=8))
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


def verify_final(ptx, rendered, layout):
    """Bind the complete active final body, index/address/store and return."""
    parameters(layout)
    verify_control(ptx, layout)
    if len(rendered) < 7 or rendered[-1] != 'ret;':
        raise ValueError('expected final-body program ending in ret')
    checked = []
    for entry in ('element_probe', 'element_p', 'element_x'):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1:
            raise ValueError('entry missing or duplicated')
        lines = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        begin = lines.index('@!%live bra stage_4_done;')
        end = lines.index('stage_4_done:')
        if lines[begin+1:end] != rendered[:-1] or lines[end+1:] != ['ret;']:
            raise ValueError(f'{entry}: final body differs from proved program')
        checked.append(dict(entry=entry, instructions=len(rendered),
                            sha256=hashlib.sha256(('\n'.join(rendered)+'\n').encode()).hexdigest()))
    return checked


def verify_whole(ptx, code, layout):
    """Bind every instruction and native branch/barrier counter to Lean lists."""
    verify_prologue(ptx, code['prologue'], layout)
    verify_entry(ptx, code['entries'], layout)
    verify_middle(ptx, code['middle'], layout)
    verify_final(ptx, code['final'], layout)
    count, (barriers, branches) = code['shape']
    checked = []
    for entry in ('element_probe', 'element_p', 'element_x'):
        body = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)[0]
        lines = [line.strip() for line in body.splitlines() if line.strip()]
        begin = next(i for i,line in enumerate(lines) if line.startswith('.shared '))+1
        instructions, labels = [], {}
        for line in lines[begin:]:
            if line.endswith(':'):
                if line[:-1] in labels:
                    raise ValueError('duplicate instruction label')
                labels[line[:-1]] = len(instructions)
            else:
                instructions.append(line)
        actual_barriers = [pc for pc,line in enumerate(instructions) if line == 'bar.sync 0;']
        actual_branches = []
        for pc,line in enumerate(instructions):
            if line.startswith('@'):
                match = re.fullmatch(r'@!%live bra (\w+);', line)
                if not match or match[1] not in labels:
                    raise ValueError('unresolved branch target')
                actual_branches.append([pc,labels[match[1]]])
        if len(instructions) != count or actual_barriers != barriers or actual_branches != branches:
            raise ValueError('absolute instruction counters differ from fetched Lean programs')
        checked.append(dict(entry=entry, instructions=count, barriers=barriers, branches=branches,
                            sha256=hashlib.sha256(('\n'.join(instructions)+'\n').encode()).hexdigest()))
    return checked


def verify_assembly_loop(ptx, rendered, layout):
    """Bind the ordered traversal slice, excluding entry setup/mask/store."""
    parameters(layout)
    if len(rendered) != 15 or rendered[0] != 'loop:' or rendered[-1] != 'done:':
        raise ValueError('expected complete assembly traversal with exit label')
    if any(token in ptx for token in ('//', '/*', '*/')):
        raise ValueError('comments are outside the exact generated dialect')
    checked = []
    for entry in ('assemble_probe', 'assemble_ap'):
        bodies = re.findall(r'\.visible \.entry '+entry+r'\(\.param \.u64 arena\)\s*([^}]+)}', ptx)
        if len(bodies) != 1:
            raise ValueError('assembly entry missing or duplicated')
        lines = [line.strip() for line in bodies[0].splitlines() if line.strip()]
        if lines.count('loop:') != 1 or lines.count('done:') != 1:
            raise ValueError('assembly traversal labels missing or duplicated')
        start, end = lines.index('loop:'), lines.index('done:')
        if lines[start:end+1] != rendered:
            raise ValueError('assembly traversal differs from proved loop')
        checked.append(dict(entry=entry, instructions=13,
                            scope='Loop slice only; entry setup, masking, output and inter-launch memory remain separate.',
                            sha256=hashlib.sha256(('\n'.join(rendered)+'\n').encode()).hexdigest()))
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
                    'PoissonPTX.CellMiddleCorrespondence', 'PoissonPTX.CellFinalSnapshot',
                    'PoissonPTX.CellFinalLayout', 'PoissonPTX.CellConsumerRun', 'PoissonPTX.CellOutputSeparation', 'PoissonPTX.CellTailResult', 'PoissonPTX.CellTailOwners', 'PoissonPTX.CellOutputTensor', 'PoissonPTX.CellPrologueEntry', 'PoissonPTX.CellGatherTensor', 'PoissonPTX.CellEntryLaunch', 'PoissonPTX.CellEntryProducers', 'PoissonPTX.CellEntryStoreTensor', 'PoissonPTX.CellEntryContinuation', 'PoissonPTX.CellEntryCorrespondence', 'PoissonPTX.CellEntryJointCorrespondence', 'PoissonPTX.CellWholeCorrespondence', 'PoissonPTX.CellOperatorCorrespondence', 'PoissonPTX.AssemblyLayout'], cwd=INTEGRATION, check=True)
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
    names += ['PtxTorchLean.Poisson.PTX.CellFinal.'+n for n in
              ('arithmetic_correct', 'fetched_correct', 'fetched_exists', 'inputs_of_matrices',
               'index_exact', 'location_exact', 'output_valid', 'read_wordBytes',
               'phase_result', 'completed_from_middle', 'exists_from_middle')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.Extension.'+n for n in
              ('run_append_code', 'compatible_prefix', 'performed_prefix', 'view_append')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.'+n for n in
              ('checked', 'loads', 'results', 'publication', 'load_view', 'tail_readonly',
               'all_reads', 'register_value', 'completed_arithmetic', 'stored_local', 'tail_completion', 'split', 'completed_run', 'stored_run')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.Cut.'+n for n in
              ('crossing_state', 'step_prefix', 'split_run')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.Projection.'+n for n in
              ('compatible', 'across', 'performed', 'separated_by_fence')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Coefficients.'+n for n in
              ('checked', 'read_bounds')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.Output.'+n for n in
              ('after_coefficients', 'fetched_preserves_coefficients', 'distinct_outputs', 'projected_arithmetic')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.WithTail.'+n for n in
              ('halted_blocks', 'synchronize_related', 'front_step', 'project_filtered')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.'+n for n in
              ('clipped', 'padding_return', 'tail_events', 'arithmetic_filtered', 'result_under_store_bounds')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address.'+n for n in
              ('tail_ready', 'runs_ready', 'runs_keeps', 'store_address', 'stored_word')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.'+n for n in
              ('store_bounds', 'coefficient_nowrap', 'result_from_launch', 'stored_from_launch', 'stores_disjoint')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Publication.'+n for n in
              ('store_value', 'completed_wrote', 'safe_records', 'present_record', 'published_word',
               'published_outside', 'location_entry', 'published_entry', 'published_tensor')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.GlobalPublication.'+n for n in
              ('word', 'permuted_word', 'outside')]
    names += ['PtxTorchLean.Poisson.PTX.CellPrologue.'+n for n in
              ('execute_sound', 'execute_complete', 'execution', 'fetched_exists', 'fetched_correct',
               'memories', 'other_register', 'ready', 'coordinates', 'thread_registers')]
    names += ['PtxTorchLean.Poisson.PTX.CellGather.'+n for n in
              ('execution', 'correct', 'stored', 'registers', 'fetched_correct', 'fetched_exists',
               'index_exact', 'connectivity_address', 'node_inside', 'valid_of_layout', 'torchlean')]
    names += ['PtxTorchLean.Poisson.PTX.CellEntry.'+n for n in
              ('no_global_store', 'index_value', 'word_value', 'actual_trace', 'completed_lane',
               'gathered_bits', 'gathered_torchlean', 'completed_barrier', 'arithmetic_launch')]
    names += ['PtxTorchLean.Poisson.PTX.CellEntry.'+n for n in
              ('recorded_store', 'completed_wrote', 'store_active', 'recorded_gather', 'recorded_torchlean')]
    names += ['PtxTorchLean.Poisson.PTX.CellEntry.Producers.'+n for n in
              ('info', 'producer', 'byte_owner', 'different_writers')]
    names += ['PtxTorchLean.Poisson.PTX.CellEntry.' + name for name in ('completed_arrivals', 'store_before_arrival', 'store_before_completion', 'continuation_read')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.preserves_gather']
    names += ['PtxTorchLean.Poisson.PTX.CellEntry.' + name for name in ('publication_sound', 'publication_torchlean', 'body_sources', 'body_result', 'published_result', 'cell_result', 'cell_tensor')]
    names += ['PtxTorchLean.Poisson.PTX.Concurrent.SourceCut.' + name for name in ('compatible', 'performed')]
    names += ['PtxTorchLean.Poisson.PTX.CellEntry.joint_cell_tensor']
    names += ['PtxTorchLean.Poisson.PTX.CellEntry.Control.' + name for name in
              ('launch', 'live_gather', 'index_run', 'output_fence', 'joint_indices', 'source_step', 'joint_words', 'joint_sources')]
    names += ['PtxTorchLean.Poisson.PTX.CellWhole.' + name for name in ('executions', 'histories', 'sources', 'output_bounds', 'tensor')]
    names += ['PtxTorchLean.Poisson.PTX.CellWhole.operator_tensor']
    names += ['PtxTorchLean.Poisson.PTX.CoefficientRepresentation.' + name for name in ('tensors', 'calculation')]
    names += ['PtxTorchLean.Poisson.PTX.Assembly.' + name for name in ('body_correct', 'traversal_correct', 'fetched_correct', 'traversal_exists', 'fetched_exists', 'valid_of_layout', 'layout_correct', 'layout_exists')]
    with tempfile.TemporaryDirectory(prefix='poisson-contraction-audit-') as tmp:
        p = Path(tmp)/'Audit.lean'
        p.write_text('import PoissonPTX.CellOperatorCorrespondence\nimport PoissonPTX.AssemblyLayout\nimport PoissonPTX.CellWholeCorrespondence\nimport PoissonPTX.CellEntryJointCorrespondence\nimport PoissonPTX.CellEntryCorrespondence\nimport PoissonPTX.CellEntryContinuation\nimport PoissonPTX.CellEntryProducers\nimport PoissonPTX.CellEntryStoreTensor\nimport PoissonPTX.CellEntryLaunch\nimport PoissonPTX.CellGatherTensor\nimport PoissonPTX.CellPrologueEntry\nimport PoissonPTX.CellOutputTensor\nimport PoissonPTX.CellTailOwners\nimport PoissonPTX.CellTailResult\nimport PoissonPTX.CellOutputSeparation\nimport PoissonPTX.CellConsumerRun\nimport PoissonPTX.SharedPlane\nimport PoissonPTX.ContractionFetched\nimport PoissonPTX.ContractionLayout\nimport PoissonPTX.ContractionText\nimport PoissonPTX.CellMiddleChecks\nimport PoissonPTX.ConcurrentComputedStore\nimport PoissonPTX.CellMiddleInputs\nimport PoissonPTX.CellMiddleCorrespondence\nimport PoissonPTX.CellFinalSnapshot\nimport PoissonPTX.CellFinalLayout\n'+
                     ''.join('#print axioms '+n+'\n' for n in names))
        audit = subprocess.check_output(['lake', '--no-cache', 'env', 'lean', p], cwd=INTEGRATION, text=True)
        checker.audit_dependencies(audit, names)
    layouts = [json.loads(read_artifact(run, report, c['directory']+'/layout.json')) for c in report['cases']]
    rendered = json.loads(subprocess.check_output([INTEGRATION/'.lake/build/bin/poissonContractions'],
        input=json.dumps([parameters(l) for l in layouts])+'\n', text=True))
    checked = [dict(directory=c['directory'], assembly_loop=verify_assembly_loop(
        read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['assembly'], layout), whole_entry=verify_whole(
        read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code, layout), entry_prefix=verify_entry(
        read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['entries'], layout), gather=verify_gather(
        read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['gathers'], layout), prologue=verify_prologue(
        read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['prologue'], layout), separation=output_separation(layout), blocks=verify_blocks(
        read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['contractions'], layout),
        stores=verify_stores(read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['stores'], layout, code['contractions']),
        control=verify_control(read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), layout),
        middle=verify_middle(read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['middle'], layout),
        final=verify_final(read_artifact(run, report, c['directory']+'/kernel.ptx').decode(), code['final'], layout))
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
