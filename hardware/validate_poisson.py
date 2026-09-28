#!/usr/bin/env python3
"""Run authored binary64 Poisson PTX against the current Lean numerical reference.

No implicit toolchain upgrade, numerical tolerance fallback, benchmark or claim
that this backend is formalized by the existing binary32 PTX execution model.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import shutil
import subprocess
import sys

from poisson_kernels import Layout,module
from poisson_runtime import Session,solve

ROOT=Path(__file__).resolve().parents[1]
INTEGRATION=ROOT/'integration/torchlean'


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def clean(x):
    if isinstance(x,float) and not math.isfinite(x):return None
    if isinstance(x,dict):return {k:clean(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [clean(v) for v in x]
    return x


def save(path,value):
    Path(path).write_text(json.dumps(clean(value),indent=2,allow_nan=False)+'\n')


def run(command,**kw):
    p=subprocess.run(list(map(str,command)),text=True,capture_output=True,**kw)
    if p.returncode:raise RuntimeError(f'{command}: exit {p.returncode}\n{p.stdout}\n{p.stderr}')
    return p.stdout+p.stderr


def sources():
    paths=[*sorted(INTEGRATION.glob('PoissonQuad*.lean')),ROOT/'hardware/cuda_driver.py',
           *sorted((ROOT/'hardware').glob('*poisson*.py')),ROOT/'hardware/poisson_runtime.py',
           ROOT/'hardware/poisson_kernels.py',INTEGRATION/'lean-toolchain',
           INTEGRATION/'lake-manifest.json',INTEGRATION/'lakefile.toml']
    return {str(p.relative_to(ROOT)):sha(p) for p in paths}


def suite():
    # Same numerical cases as the CPU source comparison, plus non-polynomial
    # operator probes and longer solves that exercise more of the PCG recurrence.
    frozen=json.loads((ROOT/'examples/poisson/reference.json').read_text())
    cases=[dict(x) for x in frozen['requests']]
    for p in range(1,5):
        n=3;size=(n*p+1)**2
        cases.append(dict(n=n,degree=p,values=[((i*17)%31-15)/8 for i in range(size)]))
    cases.append(dict(n=8,degree=4,source='constant',check_every=3,maxiter=200))
    cases.append(dict(n=16,degree=2,source='constant',check_every=7,maxiter=200))
    cases.append(dict(n=4,degree=3,source='constant',rtol=1e-14,check_every=1,maxiter=200))
    cases.append(dict(n=2,degree=2,load=[1e308]*25))
    return cases


def compare(a,b,atol,rtol,label):
    if len(a)!=len(b):raise AssertionError(label+': shape mismatch')
    maximum=0.
    for i,(x,y) in enumerate(zip(a,b,strict=True)):
        if not math.isfinite(x) or not math.isfinite(y) or abs(x-y)>atol+rtol*abs(y):
            raise AssertionError(f'{label}[{i}]: GPU {x}, reference {y}')
        maximum=max(maximum,abs(x-y))
    return maximum


def validate_result(observed,ref,case):
    if observed['reason']!=ref['reason'] or observed['converged']!=ref['converged']:
        raise AssertionError(f"solve status differs: {observed['reason']} vs {ref['reason']}")
    metrics={
        'operator_max_absolute_difference':compare(observed['applied'],ref['applied'],2e-12,2e-12,'operator'),
        'solution_max_absolute_difference':compare(observed['solution'],ref['solution'],2e-11,2e-9,'solution')}
    if any(x!=0 for x,bd in zip(observed['solution'],ref['boundary'],strict=True) if bd):
        raise AssertionError('nonzero boundary solution')
    if observed['converged'] and not (math.isfinite(observed['true_residual_norm']) and observed['true_residual_norm']<=observed['tolerance']):
        raise AssertionError('false convergence')
    if case.get('maxiter')==0 and observed['iterations']!=0:raise AssertionError('maxiter=0 performed iterations')
    if case.get('source')=='polynomial' and case['degree']>=2:
        ideal=[x*(1-x)*y*(1-y) for x,y in ref['points']]
        metrics['polynomial_max_absolute_error']=compare(observed['solution'],ideal,2e-12,0,'polynomial')
    return metrics


def replay(directory):
    report=json.loads((directory/'report.json').read_text())
    if report['numerical_status']!='pass':raise ValueError('only completed numerical runs can be replayed')
    # The immutable input manifests and saved binaries are used directly.
    for file,digest in report['artifacts'].items():
        if sha(directory/file)!=digest:raise ValueError(f'artifact hash mismatch: {file}')
    for item in report['cases']:
        folder=directory/item['directory']
        case=json.loads((folder/'request.json').read_text())
        ref=json.loads((folder/'reference.json').read_text())
        layout=Layout(ref,case)
        saved=json.loads((folder/'layout.json').read_text())
        layout.launches=saved['launches']
        if layout.manifest()!=saved or bytes(layout.data)!=(folder/'arena.bin').read_bytes():
            raise ValueError('layout or initialized data differs from saved artifact')
        with Session(layout,folder/'kernel.cubin') as session:actual=solve(session,case)
        validate_result(actual,ref,case)
        previous=json.loads((folder/'observed.json').read_text())
        if clean(actual)!=previous:raise AssertionError(f"non-reproducible replay: {item['directory']}")
    print(f"Poisson GPU replay passed: {len(report['cases'])} cases")


def validate(args):
    directory=args.output.resolve();directory.mkdir(parents=True,exist_ok=False)
    report=dict(schema_version=1,status='running',numerical_status='running',cases=[],artifacts={},
                started_at=datetime.now(timezone.utc).isoformat(),source_sha256=sources(),
                formal_project_ptx_version='9.4',emitted_ptx_version=args.ptx_version,target=args.target,
                claim='Empirical binary64 PTX implementation; not a verified PTX refinement of PoissonQuad.',
                tolerances={'operator':{'atol':2e-12,'rtol':2e-12},'solution':{'atol':2e-11,'rtol':2e-9},'polynomial':{'atol':2e-12,'rtol':0}},
                sanitizers={'status':'not_run'})
    try:
        spec=importlib.util.spec_from_file_location('integration_check',INTEGRATION/'check.py')
        checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker);checker.dependencies()
        report['lean_version']=run(['lake','--no-cache','env','lean','--version'],cwd=INTEGRATION).strip()
        pin=(INTEGRATION/'lean-toolchain').read_text().strip().removeprefix('leanprover/lean4:v')
        if not report['lean_version'].startswith(f'Lean (version {pin},'):raise ValueError('Lean version mismatch')
        report['git_commit']=run(['git','rev-parse','HEAD'],cwd=ROOT).strip()
        report['git_status']=run(['git','status','--porcelain'],cwd=ROOT)
        report['compiler']=shutil.which('ptxas') or '/usr/local/cuda/bin/ptxas'
        report['compiler_sha256']=sha(report['compiler'])
        report['compiler_version']=run([report['compiler'],'--version']).strip()
        report['gpu']=run(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader']).strip()
        (directory/'build.log').write_text(run(['lake','--no-cache','build','poissonQuad'],cwd=INTEGRATION))
        requests=suite();save(directory/'requests.json',requests)
        (directory/'export.log').write_text(run([INTEGRATION/'.lake/build/bin/poissonQuad','--request',directory/'requests.json','--output',directory/'references.json']))
        refs=json.loads((directory/'references.json').read_text())
        if len(refs)!=len(requests):raise AssertionError('reference count mismatch')
        for index,(case,ref) in enumerate(zip(requests,refs,strict=True)):
            if 'error' in ref:raise ValueError(ref['error'])
            name=f'{index:02d}-n{case["n"]}-q{case["degree"]}'
            folder=directory/name;folder.mkdir()
            save(folder/'request.json',case);save(folder/'reference.json',ref)
            layout=Layout(ref,case)
            (folder/'kernel.ptx').write_text(module(layout,args.ptx_version,args.target))
            save(folder/'layout.json',layout.manifest());(folder/'arena.bin').write_bytes(layout.data)
            command=[report['compiler'],'-arch='+args.target,'--fmad=false','-O2','-v',folder/'kernel.ptx','-o',folder/'kernel.cubin']
            compiled=subprocess.run(list(map(str,command)),text=True,capture_output=True)
            (folder/'assembler.log').write_text(compiled.stdout+compiled.stderr);compiled.check_returncode()
            with Session(layout,folder/'kernel.cubin') as session:
                report['selected_device']=session.device_info
                observed=solve(session,case)
            save(folder/'observed.json',observed) # Persist results before any numerical assertion.
            metrics=validate_result(observed,ref,case)
            # Independent application of the Lean operator to the GPU solution
            # checks the reported residual without trusting the GPU's reduction.
            residual_request=dict(case,values=observed['solution'],maxiter=0)
            save(folder/'residual-request.json',[residual_request])
            run([INTEGRATION/'.lake/build/bin/poissonQuad','--request',folder/'residual-request.json','--output',folder/'residual-reference.json'])
            independent=json.loads((folder/'residual-reference.json').read_text())[0]
            if 'error' in independent:raise ValueError(independent['error'])
            residual=math.hypot(*(a-b for a,b,bd in zip(ref['load'],independent['applied'],ref['boundary'],strict=True) if not bd))
            if math.isfinite(residual)!=math.isfinite(observed['true_residual_norm']) or (math.isfinite(residual) and abs(residual-observed['true_residual_norm'])>2e-12+2e-10*residual):
                raise AssertionError('reported residual disagrees with independently applied Lean operator')
            if observed['converged'] and residual>observed['tolerance']+2e-12:
                raise AssertionError('independent residual does not corroborate convergence')
            item=dict(directory=name,request=case,reason=observed['reason'],iterations=observed['iterations'],
                      relative_residual=observed['relative_residual'],independent_lean_residual=residual,
                      restarts=observed['restarts'],launch_count=len(observed['launches']),**metrics)
            # Values can be long; full exact request is preserved in the case artifact.
            item['request']={k:v for k,v in case.items() if k!='values'}
            report['cases'].append(item)
            print(f'{name}: {observed["reason"]}, operator delta {metrics["operator_max_absolute_difference"]:.3g}, solution delta {metrics["solution_max_absolute_difference"]:.3g}',flush=True)
        if sources()!=report['source_sha256']:raise AssertionError('checked sources changed during execution')
        checker.dependencies()
        report['artifacts']={str(p.relative_to(directory)):sha(p) for p in sorted(directory.rglob('*')) if p.is_file() and p.name!='report.json'}
        report['numerical_status']='pass';report['status']='pass'
        save(directory/'report.json',report)
        if args.sanitizers:
            outcomes={}
            sanitizer=shutil.which('compute-sanitizer') or '/usr/local/cuda/bin/compute-sanitizer'
            report['sanitizer_version']=run([sanitizer,'--version'])
            for tool in ('memcheck','racecheck','synccheck','initcheck'):
                command=[sanitizer,'--tool',tool,'--error-exitcode','86',sys.executable,Path(__file__).resolve(),'--replay',directory]
                p=subprocess.run(list(map(str,command)),capture_output=True,text=True)
                log=p.stdout+p.stderr;(directory/f'{tool}.log').write_text(log)
                if p.returncode or not ('ERROR SUMMARY: 0 errors' in log or 'RACECHECK SUMMARY: 0 hazards' in log):
                    raise AssertionError(f'{tool} failed; see log')
                outcomes[tool]=dict(status='pass',log=f'{tool}.log',sha256=sha(directory/f'{tool}.log'))
                print(f'{tool}: pass',flush=True)
            report['sanitizers']=dict(status='pass',tools=outcomes)
        report['completed_at']=datetime.now(timezone.utc).isoformat();save(directory/'report.json',report)
    except BaseException as e:
        report['status']='fail';report['error']=str(e);save(directory/'report.json',report)
        raise


def main():
    p=argparse.ArgumentParser(description=__doc__)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--replay',type=Path)
    p.add_argument('--ptx-version',choices=['9.2','9.4'],default='9.4');p.add_argument('--target',choices=['sm_120'],default='sm_120')
    p.add_argument('--sanitizers',action='store_true');args=p.parse_args()
    if args.replay:replay(args.replay.resolve())
    else:validate(args)

if __name__=='__main__':main()
