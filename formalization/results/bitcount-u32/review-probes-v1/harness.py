#!/usr/bin/env python3
"""Offline, isolated read-metadata mutation. Does not modify the candidate replay."""
from pathlib import Path
import datetime, hashlib, json, re, shutil, subprocess, tempfile

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
ATTEMPT = ROOT / '.formalization-runs/luna/attempts/bitcount-003'
CHECKER = ROOT / 'formalization/checks/bitcount-u32-v2.lean'
WORK = Path(tempfile.mkdtemp(prefix='ptxlean-bitcount-read-metadata-')) / 'worktree'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
report = {'schema':'ptxlean.bitcount-review-probes/v1','started_at':now(),'model_calls':0,
          'worktree':str(WORK),'commands':[], 'mutation':'Omit unary source register from Op.reads; evaluator arithmetic/state update unchanged.'}
def save(): (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
def run(name,argv,cwd=WORK):
    started=now()
    with (OUT/(name+'.stdout.log')).open('w') as out, (OUT/(name+'.stderr.log')).open('w') as err:
        result=subprocess.run(argv,cwd=cwd,stdout=out,stderr=err)
    record={'name':name,'argv':argv,'cwd':str(cwd),'started_at':started,'finished_at':now(),
            'returncode':result.returncode,'stdout':name+'.stdout.log','stderr':name+'.stderr.log'}
    report['commands'].append(record);save();print(name,result.returncode,flush=True)
    return result.returncode
try:
    for src,dst in [(ATTEMPT/'task.json','task.json'),(ATTEMPT/'candidate.patch','candidate.patch'),(CHECKER,'acceptance.lean')]:
        shutil.copy2(src,OUT/dst)
    task=json.loads((OUT/'task.json').read_text());base=task['base_commit']
    report.update(base_commit=base,candidate_patch_sha256=sha(OUT/'candidate.patch'),task_sha256=sha(OUT/'task.json'),
                  driver_sha256=sha(OUT/'acceptance.lean'),script_sha256=sha(Path(__file__)),sources=task['sources'])
    assert report['candidate_patch_sha256']=='23f275350ed3b1a94aebd39c3ab9d3123cd9641151188e1c247ecdc17fa395d2'
    assert report['driver_sha256']=='59bddc3cceb558578f8ace3e71dc2c107a31a0895b4bf649d363296c3a83c27a'
    assert run('setup-worktree',['git','worktree','add','--detach',str(WORK),base],ROOT)==0
    assert run('setup-apply',['git','apply','--',str(OUT/'candidate.patch')])==0
    assert run('setup-lean-version',['lake','env','lean','--version'])==0
    module=(WORK/'Ptx/IntegerBitCount.lean').read_text()
    names=['Ptx.Scalar.IntegerBitCount.'+n for n in re.findall(r'^(?:@\[[^\]]+\]\s*)?theorem (\w+)',module,re.M)]
    names+=['Ptx.Scalar.Text.decode_encode','Ptx.Scalar.Text.decodeOp_supported']
    (OUT/'audit.lean').write_text('import Ptx.IntegerBitCount\n'+''.join('#print axioms '+n+'\n' for n in names))
    report['audit_declarations']=names
    report['control_source_sha256']={p:sha(WORK/p) for p in task['allowed_paths']}
    assert run('control-build',['lake','build','Ptx','Ptx.IntegerBitCount'])==0
    assert run('control-acceptance',['lake','env','lean',str(OUT/'acceptance.lean')])==0
    assert run('control-audit',['lake','env','lean',str(OUT/'audit.lean')])==0
    scalar=WORK/'Ptx/Scalar.lean';original=scalar.read_text()
    before='  | .unary32 _ _ source => source.reads'
    assert original.count(before)==1
    scalar.write_text(original.replace(before,'  | .unary32 _ _ _source => []'))
    mutation=subprocess.check_output(['git','diff','--','Ptx/Scalar.lean'],cwd=WORK,text=True)
    # Store the mutation relative to the accepted candidate, not relative to its base.
    import difflib
    (OUT/'omit-unary-read.mutation.patch').write_text(''.join(difflib.unified_diff(original.splitlines(True),scalar.read_text().splitlines(True),fromfile='a/Ptx/Scalar.lean',tofile='b/Ptx/Scalar.lean')))
    report['mutated_source_sha256']={p:sha(WORK/p) for p in task['allowed_paths']}
    assert run('omit-unary-read-build',['lake','build','Ptx','Ptx.IntegerBitCount'])==0
    assert run('omit-unary-read-proof-elaboration',['lake','env','lean','Ptx/IntegerBitCount.lean'])==0
    assert run('omit-unary-read-audit',['lake','env','lean',str(OUT/'audit.lean')])==0
    rejected=run('omit-unary-read-acceptance',['lake','env','lean',str(OUT/'acceptance.lean')])
    assert rejected!=0
    for prefix in ['control','omit-unary-read']:
        text=(OUT/(prefix+'-audit.stdout.log')).read_text()
        found={n:set(d.split(', ')) for n,d in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)}
        for n in re.findall(r"'([^']+)' does not depend on any axioms",text):found[n]=set()
        assert set(found)==set(names)
        assert all(ds<={'propext','Classical.choice','Quot.sound'} for ds in found.values())
    failures=(OUT/'omit-unary-read-acceptance.stdout.log').read_text()
    assert 'expected' in failures and 'error:' in failures
    report['outcome']='pass: control builds/accepts; metadata-only mutation builds and its proofs/audits pass, but frozen acceptance rejects.'
    report['limitations']='One deliberately injected metadata fault; not a completeness or quantified sensitivity claim for the evaluator.'
finally:
    report['finished_at']=now();save()
