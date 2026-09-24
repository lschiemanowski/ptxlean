from pathlib import Path
import subprocess,json,hashlib,datetime,difflib,sys,tempfile,shutil,re
root=Path('/home/lothar/workspace/ptxlean')
leaf,attempt,stem=sys.argv[1:]
out=root/'formalization/results'/stem/'review-probes';out.mkdir(parents=True,exist_ok=True)
work=Path(tempfile.mkdtemp(prefix='ptx-'+stem+'-probe-'))/'worktree'
a=root/'.formalization-runs/luna/attempts'/attempt
cfg=json.loads((root/'formalization/checks'/f'{stem}-v2.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
report={'schema_version':1,'started_at':now(),'model_calls':0,'attempt':attempt,'commands':[],'worktree':str(work),'candidate_patch_sha256':sha(a/'candidate.patch'),'driver_sha256':sha(root/cfg['checks'][0])}
def save(): (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
def run(name,args,cwd=work):
  with (out/(name+'.log')).open('w') as f: p=subprocess.run(args,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
  report['commands'].append({'name':name,'argv':args,'cwd':str(cwd),'exit_code':p.returncode,'log':name+'.log'});save();return p.returncode
try:
  task=json.loads((a/'task.json').read_text());report['base_commit']=task['base_commit']
  shutil.copy2(__file__,out/'harness.py');shutil.copy2(root/cfg['checks'][0],out/'acceptance.lean')
  assert run('setup',['git','worktree','add','--detach',str(work),task['base_commit']],root)==0
  assert run('apply',['git','apply',str(a/'candidate.patch')])==0
  (out/'audit.lean').write_text('import Ptx.'+leaf+'\n'+'\n'.join('#print axioms '+d for d in cfg['declarations'])+'\n')
  assert run('control-build',['lake','build','Ptx.'+leaf])==0
  assert run('control-driver',['lake','env','lean',str(out/'acceptance.lean')])==0
  assert run('control-audit',['lake','env','lean',str(out/'audit.lean')])==0
  path=work/'Ptx'/(leaf+'.lean');before=path.read_text()
  if leaf=='Select32':
    old='else .error (.unsupportedMnemonic statement.mnemonic)';new='else .error (.invalidOperands statement.mnemonic)'
    report['mutation']='Misclassify every unsupported mnemonic as invalid operands; accepted instruction semantics unchanged.'
  else:
    old='target.isa = 94 ∧ 10 ≤ target.sm';new='target.isa = 94 ∧ 20 ≤ target.sm'
    report['mutation']='Raise the target feature floor from sm_10 to sm_20 without changing arithmetic or proofs.'
  assert before.count(old)==1
  after=before.replace(old,new);path.write_text(after)
  report['source_before_sha256']=hashlib.sha256(before.encode()).hexdigest();report['source_after_sha256']=sha(path)
  (out/'mutation.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/Ptx/'+leaf+'.lean',tofile='b/Ptx/'+leaf+'.lean')))
  assert run('mutation-build',['lake','build','Ptx.'+leaf])==0
  assert run('mutation-audit',['lake','env','lean',str(out/'audit.lean')])==0
  assert run('mutation-driver',['lake','env','lean',str(out/'acceptance.lean')])!=0
  for label in ['control-audit','mutation-audit']:
    txt=(out/(label+'.log')).read_text();deps={n:set(filter(None,d.split(', '))) for n,d in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",txt)}
    deps.update({n:set() for n in re.findall(r"'([^']+)' does not depend on any axioms",txt)})
    assert set(deps)==set(cfg['declarations']);assert all(d<={'propext','Classical.choice','Quot.sound'} for d in deps.values())
  report['outcome']='pass';report['qualification']='Chosen mutation rejected although its complete module and standard-axiom audit pass; not a completeness or statistical sensitivity claim.'
finally:report['finished_at']=now();save()
