#!/usr/bin/env python3
"""Emit, assemble and compare the existing Lean dense forward on a real GPU.

No backward, softmax, timing, autotuning, tolerance fallback or vendor source
redistribution. Every failure leaves the case inputs and emitted artifacts.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
from datetime import datetime, timezone

from cuda_driver import Cuda
from exact_reference import dense, decode, float_word, word_float

ROOT = Path(__file__).resolve().parents[1]
INTEGRATION = ROOT / 'integration/torchlean'
TORCH_VERSION = '2.11.0+cu130'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(args, **kwargs):
    return subprocess.run(list(map(str, args)), check=True, text=True, capture_output=True, **kwargs).stdout


def save(path, obj):
    Path(path).write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n')


def cases(seed):
    result = []
    def add(name, m, n, words):
        result.append(dict(name=name, rows=m, columns=n, depth=(max(1,n)-1).bit_length(), words=words))
    def vals(name, m, n, numbers):
        add(name,m,n,list(map(float_word,numbers)))
    vals('padded-three',2,3,[1,2,3,1,2,3,-1,-2,-3,1,1])
    vals('empty-input',3,0,[2,-3,0])
    vals('empty-output',0,3,[1,2,3])
    vals('both-empty',0,0,[])
    vals('relu-corner',3,1,[1,1,1,1,-1,-1-2**-23,-1+2**-24])
    add('signed-zero',2,1,[0x80000000,0x3f800000,0xbf800000,0x80000000,0])
    add('subnormal',3,1,[1,0x3f800000,0xbf800000,0x3f000000,0,0,0])
    add('rounding-ties',2,1,[0x3f800000,0x3f800000,0x3f800001,float_word(2**-24),float_word(2**-24)])
    add('unfused-rounding',1,1,[0x3f800001,0x3f7ffffe,0xbf800000])
    vals('cancellation',2,4,[2**24,1,-2**24,1,1,1,1,1,1,-1,1,-1,0,1])
    vals('large-finite',1,2,[2**60,2**60,2**50,-2**50,2**80])
    rng = random.Random(seed)
    for n in [1,2,3,7,16,31,32,33,64,127,128,255,256,511,512,1023,1024]:
        for m in [1,33] if n <= 64 else [2]:
            # Binary32 inputs with broad magnitudes and genuine rounding/cancellation.
            values = [math.ldexp(rng.uniform(-1,1),rng.randrange(-12,13)) for _ in range(n+m*n+m)]
            vals(f'random-{m}x{n}',m,n,values)
    return result


def module(export, version, target):
    if version not in ('9.2','9.4') or target != 'sm_120':
        raise ValueError('unreviewed PTX version or GPU target')
    width, depth = export['width'], export['depth']
    header = f'''.version {version}
.target {target}
.address_size 64
.visible .entry dense_relu(.param .u64 arena)
.reqntid {width}, 1, 1
{{
.reg .b32 %r<16>;
.reg .b64 %a<8>;
.reg .pred %p<2>;
.reg .b32 %physicalThread;
.reg .b64 %globalBase, %sharedBase, %effective, %initOffset;
.shared .align 4 .b8 scratch[{4*export['shared_words']}];
// Entry adapter: logical thread = row group * padded width + physical lane.
ld.param.u64 %globalBase, [arena];
mov.u64 %sharedBase, scratch;
mov.u32 %r0, %ctaid.x;
shl.b32 %r0, %r0, {depth};
mov.u32 %physicalThread, %tid.x;
add.u32 %r0, %r0, %physicalThread;
// Initialize all shared planes to match GridDense.initial exactly.
cvt.u64.u32 %initOffset, %physicalThread;
shl.b64 %initOffset, %initOffset, 2;
add.u64 %effective, %sharedBase, %initOffset;
'''
    for plane in range(depth+1):
        header += f"st.shared.b32 [%effective+{4*plane*width}], 0;\n"
    header += "bar.sync 0;\n// Begin body emitted directly from Dense.Compact.program.\n"
    for site in export['program']:
        header += f"// formal pc {site['pc']}\n"+'\n'.join(site['ptx'])+'\n'
    return header+'}\n'


def source_hashes():
    paths = [*sorted((INTEGRATION/'PtxBinary32').glob('*.lean')),
             *sorted(INTEGRATION.glob('*.lean')), *sorted((ROOT/'Ptx').rglob('*.lean')), ROOT/'Ptx.lean',
             *sorted((ROOT/'hardware').glob('*.py'))]
    for base in [ROOT,INTEGRATION]:
        paths += [base/name for name in ('lean-toolchain','lakefile.toml','lake-manifest.json')]
    return {str(p.relative_to(ROOT)):sha(p) for p in paths}


def torch_words(case, torch):
    n,m=case['columns'],case['rows']
    values=[word_float(w) for w in case['words']]
    x=torch.tensor(values[:n],dtype=torch.float32,device='cuda')
    w=torch.tensor(values[n:n+m*n],dtype=torch.float32,device='cuda').reshape(m,n)
    b=torch.tensor(values[n+m*n:],dtype=torch.float32,device='cuda')
    with torch.no_grad():
        y=torch.relu(w@x+b)
    return [x & 0xffffffff for x in y.cpu().view(torch.int32).tolist()]


def saved(directory):
    report=json.loads((directory/'report.json').read_text())
    if report['status'] != 'pass':
        raise ValueError('only a completed numerical run can be replayed')
    for file,key in [('cases.json','input_sha256'),('exports.json','export_sha256')]:
        if sha(directory/file)!=report[key]:
            raise ValueError(f'{file}: recorded artifact hash mismatch')
    for receipt in report['cases']:
        for kind in ('ptx','cubin'):
            if sha(directory/receipt[kind])!=receipt[kind+'_sha256']:
                raise ValueError(f'{kind}: recorded artifact hash mismatch')
    return report


def replay(directory):
    report=saved(directory)
    request=json.loads((directory/'cases.json').read_text())
    exports=json.loads((directory/'exports.json').read_text())
    cuda=Cuda()
    try:
        for case,export,receipt in zip(request,exports,report['cases'],strict=True):
            cubin=directory/receipt['cubin']
            if sha(cubin)!=receipt['cubin_sha256']:
                raise ValueError('compiled artifact hash mismatch')
            packet=case['words']+[0xdeadbeef]*case['rows']
            actual=cuda.execute(cubin,packet,case['rows'],export['width'],4*export['shared_words'])
            if actual != case['words']+export['expected']:
                raise AssertionError(f"replay mismatch: {case['name']}")
        print(f"GPU replay passed: {len(request)} cases")
    finally:
        cuda.close()


def validate(args):
    os.environ['NVIDIA_TF32_OVERRIDE']='0'
    import torch
    if torch.__version__ != TORCH_VERSION:
        raise RuntimeError(f'Expected torch {TORCH_VERSION}, got {torch.__version__}; review and repin before changing')
    # Explicit full-precision FP32, no autocast, no TF32, no compilation.
    torch.backends.cuda.matmul.fp32_precision='ieee'
    torch.backends.cudnn.conv.fp32_precision='ieee'
    directory=args.output.resolve()
    directory.mkdir(parents=True,exist_ok=False)
    # Rebuild from current source and verify that external dependencies match the lock.
    import importlib.util
    spec=importlib.util.spec_from_file_location('integration_check', INTEGRATION/'check.py')
    checker=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.dependencies()
    version=run(['lake','--no-cache','env','lean','--version'],cwd=INTEGRATION).strip()
    pin=(INTEGRATION/'lean-toolchain').read_text().strip().removeprefix('leanprover/lean4:v')
    if not version.startswith(f'Lean (version {pin},'):
        raise RuntimeError('Lean toolchain differs from pin')
    (directory/'build.log').write_text(run(['lake','--no-cache','build','PtxHardwareDense','PtxGridDenseForward'],cwd=INTEGRATION))
    before=source_hashes()
    request=cases(args.seed)
    save(directory/'cases.json',request)
    try:
        export_cmd=['lake','--no-cache','env','lean','--run','HardwareDenseMain.lean',directory/'cases.json',directory/'exports.json']
        log=run(export_cmd,cwd=INTEGRATION)
        (directory/'export.log').write_text(log)
        exports=json.loads((directory/'exports.json').read_text())
        cuda=Cuda()
        if (cuda.attribute(75),cuda.attribute(76)) != (12,0):
            cuda.close()
            raise ValueError('this reviewed adapter currently requires compute capability 12.0')
        report=dict(schema_version=1,status='running',started_at=datetime.now(timezone.utc).isoformat(),
                    git_commit=run(['git','rev-parse','HEAD'],cwd=ROOT).strip(),
                    git_status=run(['git','status','--porcelain'],cwd=ROOT),source_sha256=before,
                    model_ptx_version='9.4',emitted_ptx_version=args.ptx_version,target=args.target,
                    gpu=run(['nvidia-smi','--query-gpu=name,uuid,compute_cap,driver_version','--format=csv,noheader']).strip(),
                    compiler_path=shutil.which('ptxas'),compiler_sha256=sha(shutil.which('ptxas')),compiler_version=run(['ptxas','--version']),
                    lean_version=version,python_version=sys.version,python_executable=sys.executable,
                    compatibility_review='hardware/ptx-compatibility.md',
                    dependency_revisions=json.loads((INTEGRATION/'lake-manifest.json').read_text()),
                    torch_version=torch.__version__,torch_cuda=torch.version.cuda,
                    torch_settings={'matmul.fp32_precision':'ieee','cudnn.conv.fp32_precision':'ieee','autocast':False,'NVIDIA_TF32_OVERRIDE':'0'},
                    seed=args.seed,repeat=args.repeat,cases=[],
                    guarantee='Empirical validation; emitter, entry adapter, CUDA execution and Python reference are not formally verified.',
                    theorem='PtxTorchLean.GridDenseForward.universal_forward',
                    program='Ptx.Scalar.Parallel.Dense.Compact.program',
                    sanitizers={'status':'not_run'})
        try:
            for case,export in zip(request,exports,strict=True):
                name=case['name']; ptx=directory/f'{name}.ptx'; cubin=directory/f'{name}.cubin'
                ptx.write_text(module(export,args.ptx_version,args.target))
                cmd=['ptxas',f'-arch={args.target}','--fmad=false','-O2','-v',ptx,'-o',cubin]
                compiled=subprocess.run(list(map(str,cmd)),text=True,capture_output=True)
                (directory/f'{name}.ptxas.log').write_text(compiled.stdout+compiled.stderr)
                compiled.check_returncode()
                expected,ideal,budget,torch_budget=dense(case)
                if expected!=export['expected']:
                    raise AssertionError(f'{name}: independent rational evaluator disagrees with Lean')
                packet=case['words']+[0xdeadbeef]*case['rows']
                for _ in range(args.repeat):
                    actual=cuda.execute(cubin,packet,case['rows'],export['width'],4*export['shared_words'])
                    save(directory/f'{name}.observed.json', {'gpu_words':actual})
                    if actual[:export['output_base']] != case['words']:
                        raise AssertionError(f'{name}: changed input storage')
                    if actual[export['output_base']:] != expected:
                        save(directory/'failure.json',{'case':case,'expected':expected,'actual':actual})
                        raise AssertionError(f'{name}: GPU/Lean bit mismatch')
                tw=torch_words(case,torch)
                save(directory/f'{name}.observed.json', {'gpu_words':actual,'torch_words':tw})
                errors=[abs(decode(a)-b) for a,b in zip(expected,ideal,strict=True)]
                te=[abs(decode(a)-b) for a,b in zip(tw,ideal,strict=True)]
                if any(a>b for a,b in zip(errors,budget,strict=True)):
                    raise AssertionError(f'{name}: formal-formula error allowance exceeded')
                if any(a>b for a,b in zip(te,torch_budget,strict=True)):
                    raise AssertionError(f'{name}: PyTorch diagnostic envelope exceeded')
                receipt=dict(name=name,rows=case['rows'],columns=case['columns'],width=export['width'],
                             shared_bytes=4*export['shared_words'],in_numerical_domain=True,
                             domain_checks='finite inputs; exact product, tree-add and bias-add ranges; zero encoding error',
                             output_words=expected,torch_output_words=tw,ideal=list(map(str,ideal)),
                             absolute_error=list(map(str,errors)),theorem_formula_allowance=list(map(str,budget)),
                             torch_absolute_error=list(map(str,te)),torch_diagnostic_allowance=list(map(str,torch_budget)),
                             torch_bit_differences=sum(a!=b for a,b in zip(tw,expected,strict=True)),
                             ptx=ptx.name,ptx_sha256=sha(ptx),cubin=cubin.name,cubin_sha256=sha(cubin),
                             assembler_command=list(map(str,cmd)))
                report['cases'].append(receipt)
                save(directory/'report.json',report)
                print(f"PASS {name}: {case['rows']}x{case['columns']}, GPU=Lean=exact-rounding; real bound and PyTorch check passed",flush=True)
        finally:
            cuda.close()
        checker.dependencies()
        if source_hashes()!=before:
            raise RuntimeError('source changed during validation')
        report.update(status='pass',completed_at=datetime.now(timezone.utc).isoformat(),
                      input_sha256=sha(directory/'cases.json'),export_sha256=sha(directory/'exports.json'))
        save(directory/'report.json',report)
        if args.sanitizers:
            sanitizer=shutil.which('compute-sanitizer')
            if not sanitizer:
                raise RuntimeError('requested Compute Sanitizer is unavailable')
            outcomes={}
            for tool in ('memcheck','racecheck','synccheck','initcheck'):
                cmd=[sanitizer,'--tool',tool,'--error-exitcode','86',sys.executable,Path(__file__).resolve(),'--replay',directory]
                result=subprocess.run(list(map(str,cmd)),text=True,capture_output=True)
                log=result.stdout+result.stderr
                logpath=directory/f'{tool}.log'
                logpath.write_text(log)
                result.check_returncode()
                summary=('RACECHECK SUMMARY: 0 hazards' if tool=='racecheck' else 'ERROR SUMMARY: 0 errors')
                if summary not in log:
                    raise RuntimeError(f'{tool}: missing clean sanitizer summary')
                outcomes[tool]={'status':'pass','command':list(map(str,cmd)),'log':logpath.name,'sha256':sha(logpath)}
                print(f'PASS {tool}: clean GPU-only replay',flush=True)
            report['sanitizers']={'status':'pass','version':run([sanitizer,'--version']),'tools':outcomes}
            save(directory/'report.json',report)
    except Exception as e:
        if (directory/'report.json').exists():
            failed=json.loads((directory/'report.json').read_text())
            failed['status']='fail'
            save(directory/'report.json',failed)
        save(directory/'error.json',{'type':type(e).__name__,'message':str(e)})
        raise


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    p.add_argument('--replay',type=Path,help='GPU-only replay of exact saved inputs/binaries for sanitizer runs')
    p.add_argument('--ptx-version',choices=['9.2','9.4'],default='9.4',help='explicitly select 9.2 only with the documented compatibility restriction')
    p.add_argument('--target',choices=['sm_120'],default='sm_120')
    p.add_argument('--sanitizers',action='store_true',help='also run four GPU-only Compute Sanitizer replays')
    p.add_argument('--seed',type=int,default=20260928)
    p.add_argument('--repeat',type=int,default=3)
    args=p.parse_args()
    if args.replay:
        replay(args.replay.resolve())
    elif args.output and args.repeat>0:
        validate(args)
    else:
        p.error('provide --output and a positive repeat count, or --replay')


if __name__=='__main__':
    main()
