#!/usr/bin/env python3
"""Compare the Lean numerical port with frozen outputs from the supplied Torch file.

Default checks use only Python's standard library and the pinned Lean project.
--reference PATH regenerates an independent live comparison (requires Torch).
--record additionally saves those reference outputs; never done by normal checks.
"""
import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INTEGRATION = ROOT / 'integration/torchlean'
FIXTURE = HERE / 'reference.json'


def requests():
    items = [dict(n=n, degree=p) for p in range(1, 5) for n in (1, 2, 4)]
    items += [dict(n=8, degree=4)]
    items += [dict(n=2, degree=p, source='polynomial') for p in range(1, 5)]
    items += [dict(n=2, degree=2, source='zero'),
              dict(n=2, degree=2, maxiter=0),
              dict(n=2, degree=2, maxiter=1, rtol=1e-30),
              dict(n=2, degree=2, source='polynomial', check_every=1),
              dict(n=2, degree=2, source='constant')]
    return items


def reference(path, cases):
    import torch
    torch.set_num_threads(1)
    spec = importlib.util.spec_from_file_location('poisson_reference', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    out = []
    for case in cases:
        n, p = case['n'], case['degree']
        mesh = module.quadrilateral_square(n, p)
        op = module.TensorPoisson(mesh)
        source_name = case.get('source', 'sine')
        poly = lambda x: x[..., 0]*(1-x[..., 0])*x[..., 1]*(1-x[..., 1])
        poly_grad = lambda x: torch.stack(((1-2*x[..., 0])*x[..., 1]*(1-x[..., 1]),
                                         x[..., 0]*(1-x[..., 0])*(1-2*x[..., 1])), dim=-1)
        sources = {'sine': module.sine_source,
                   'polynomial': lambda x: 2*(x[..., 0]*(1-x[..., 0])+x[..., 1]*(1-x[..., 1])),
                   'constant': lambda x: torch.ones_like(x[..., 0]),
                   'zero': lambda x: torch.zeros_like(x[..., 0])}
        rhs = op.load(sources[source_name])
        solved = module.solve_pcg(op, rhs, **{k:v for k,v in case.items() if k in ('rtol','atol','maxiter','check_every')})
        errors = module.tensor_error_norms(mesh, solved.solution, poly, poly_grad) if source_name == 'polynomial' else module.tensor_error_norms(mesh, solved.solution)
        x,y = mesh.points[:,0],mesh.points[:,1]
        probe = x*x+2*x*y-3*y+1
        out.append(dict(n=n,degree=p,nodes=len(mesh.points),interior_unknowns=len(op.interior),
            points=mesh.points.tolist(),cells=mesh.cells.reshape(n*n,-1).tolist(),
            boundary=mesh.boundary.tolist(),interior=op.interior.tolist(),lobatto=op.nodes.tolist(),
            q=op.q.tolist(),weights=op.weights.tolist(),B=op.B.flatten().tolist(),D=op.D.flatten().tolist(),
            diagonal=op.diagonal.tolist(),load=rhs.tolist(),probe=probe.tolist(),applied=op.apply(probe).tolist(),
            solution=solved.solution.tolist(),converged=solved.converged,reason=solved.reason,
            iterations=solved.iterations,true_residual_norm=solved.residual_norm,
            relative_residual=solved.relative_residual,tolerance=solved.tolerance,
            l2_error=errors[0] if source_name in ('sine','polynomial') else None,
            h1_seminorm_error=errors[1] if source_name in ('sine','polynomial') else None))
    return dict(source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                source_name=path.name,python=platform.python_version(),torch=torch.__version__,
                device='cpu',dtype='float64',requests=cases,outputs=out)


def flat(x):
    if isinstance(x,list):
        return [z for y in x for z in flat(y)]
    return [x]


def compare(actual, expected, field, abs_tol, rel_tol):
    a,b=flat(actual),flat(expected)
    assert len(a)==len(b),(field,'size mismatch')
    for i,(x,y) in enumerate(zip(a,b)):
        assert math.isfinite(x) and math.isfinite(y),(field,i,'nonfinite')
        assert abs(x-y) <= abs_tol+rel_tol*abs(y),(field,i,x,y,'difference',abs(x-y))
    return max((abs(x-y) for x,y in zip(a,b)),default=0)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference',type=Path)
    parser.add_argument('--record',action='store_true')
    args=parser.parse_args()
    if args.record and args.reference is None: parser.error('--record requires --reference')
    expected=reference(args.reference,requests()) if args.reference else json.loads(FIXTURE.read_text())
    assert expected['requests']==requests(),'fixture request drift'
    subprocess.run(['lake','--no-cache','build','poissonQuad'],cwd=INTEGRATION,check=True)
    cases=requests()
    invalid=[dict(n=0),dict(degree=0),dict(degree=5),dict(check_every=0),dict(rtol=0),dict(rtol=-1),dict(values=[]),dict(load=[]),dict(n=True),dict(dtype="float32"),dict(device="cuda"),42]
    with tempfile.TemporaryDirectory(prefix='ptxlean-poisson-') as tmp:
        src,dst=Path(tmp)/'requests.json',Path(tmp)/'outputs.json'
        src.write_text(json.dumps(cases+invalid))
        subprocess.run([str(INTEGRATION/'.lake/build/bin/poissonQuad'),'--request',str(src),'--output',str(dst)],check=True)
        output=json.loads(dst.read_text())
    assert len(output)==len(cases)+len(invalid)
    assert all('error' in x for x in output[len(cases):]),'invalid input accepted'
    maxima={}
    for i,(case,a,b) in enumerate(zip(cases,output,expected['outputs'])):
        assert 'error' not in a,(case,a)
        for field in ('n','degree','nodes','interior_unknowns','cells','boundary','interior','converged','reason'):
            assert a[field]==b[field],(case,field,a[field],b[field])
        # Fixed allowances, declared before recording evidence; no tolerance fallback.
        for field in ('points','lobatto','q','weights','B','D','diagonal','load','probe','applied','tolerance'):
            err=compare(a[field],b[field],field,2e-12,2e-12)
            maxima[field]=max(maxima.get(field,0),err)
        for field in ('solution','true_residual_norm','relative_residual','l2_error','h1_seminorm_error'):
            if b[field] is None:
                assert a[field] is None
                continue
            err=compare(a[field],b[field],field,2e-11,2e-9)
            maxima[field]=max(maxima.get(field,0),err)
        assert all(x==0 for x,bd in zip(a['solution'],a['boundary']) if bd),'nonzero boundary'
        if a['converged']: assert a['true_residual_norm']<=a['tolerance']
        if case.get('maxiter')==0: assert a['iterations']==0
        if case.get('source')=='polynomial' and case['degree']>=2:
            ideal=[x*(1-x)*y*(1-y) for x,y in a['points']]
            compare(a['solution'],ideal,'polynomial solution',2e-12,0)
            assert a['l2_error']<2e-12 and a['h1_seminorm_error']<2e-11
    # Refinement decreases both field and gradient errors for each degree.
    for p in range(1,5):
        coarse=output[cases.index(dict(n=2,degree=p))]
        fine=output[cases.index(dict(n=4,degree=p))]
        assert fine['l2_error']<coarse['l2_error']/2
        assert fine['h1_seminorm_error']<coarse['h1_seminorm_error']/1.5
    sources=[*sorted(INTEGRATION.glob('PoissonQuad*.lean')),Path(__file__),
             INTEGRATION/'lean-toolchain',INTEGRATION/'lake-manifest.json']
    report=dict(source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
                cases=len(cases),rejections=len(invalid),max_absolute_differences=maxima,
                default_example=output[12],reference_source_sha256=expected['source_sha256'])
    print(json.dumps({k:v for k,v in report.items() if k not in ('default_example','source_sha256')},indent=2))
    default=report['default_example']
    print('Default n=8 Q4:',{k:default[k] for k in ('iterations','relative_residual','l2_error','h1_seminorm_error')})
    if args.record:
        FIXTURE.write_text(json.dumps(expected,indent=2,allow_nan=False)+'\n')
        report['default_example']={k:default[k] for k in ('iterations','relative_residual','l2_error','h1_seminorm_error')}
        (HERE/'comparison.json').write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
    print('Poisson Python correspondence checks passed (numerical evidence, not a proof).')

if __name__=='__main__':main()
