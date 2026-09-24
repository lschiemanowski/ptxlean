import argparse,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'scripts'))
import model_review as m
from worker_replay import audit_dependencies
parser=argparse.ArgumentParser(description='Build blinded controls and seeded faults without model calls.')
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
root=ROOT;out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
work=out/'worktree';base='2e0f514a5de4409c669390f468fff2b2038b352f'
subprocess.run(['git','worktree','add','--detach',str(work),base],check=True,capture_output=True)
checks={
 'r01':'example : Ptx.Scalar.Select32.compute 7 9 true = 7 := by decide',
 'r02':'example : Ptx.Scalar.Select32.compute 7 9 true = 7 := by decide',
 'r03':'example : (match Ptx.Scalar.Select32.Text.decode ⟨.always, "selp.b32", []⟩ with | .error (.invalidOperands _) => true | _ => false) = true := by decide',
 'r04':'example : Ptx.Scalar.SignedMinMax32.SupportedTarget ⟨94, 10⟩ := by constructor <;> decide',
 'r05':'example : Ptx.Scalar.SignedMinMax32.SupportedTarget ⟨94, 10⟩ := by constructor <;> decide'}
reports=[]
for case in json.loads((root/'formalization/review/cases/labels.json').read_text())['cases']:
 cid=case['case'];recipe=json.loads((root/f'formalization/review/cases/{cid}.json').read_text());p=recipe['files'][0]['path'];module=p[:-5].replace('/','.')
 subprocess.run(['git','checkout',base,'--','Ptx/Select32.lean','Ptx/SignedMinMax32.lean'],cwd=work,check=True)
 if 'patch' in recipe:subprocess.run(['git','apply',str(root/recipe['patch']['path'])],cwd=work,check=True)
 log=subprocess.run(['lake','build',module],cwd=work,capture_output=True,text=True);(out/(cid+'-build.log')).write_text(log.stdout+log.stderr)
 assert log.returncode==0,(cid,'build failed')
 declarations=['Ptx.Scalar.'+module.split('.')[-1]+'.'+n for n in ['eval_true_iff','eval_false_iff','eval_frame','eval_deterministic','eval_exists','step_origin','step_exists','Text.decode_encode','Text.decode_iff']]
 audit=out/(cid+'-audit.lean');audit.write_text('import '+module+'\n'+'\n'.join('#print axioms '+n for n in declarations)+'\n')
 run=subprocess.run(['lake','env','lean',str(audit)],cwd=work,capture_output=True,text=True);(out/(cid+'-audit.log')).write_text(run.stdout+run.stderr);assert run.returncode==0;audit_dependencies(run.stdout+run.stderr,declarations)
 driver=out/(cid+'-check.lean');driver.write_text('import '+module+'\n'+checks[cid]+'\n'+(checks['r03']+'\n' if cid=='r01' else ''))
 run=subprocess.run(['lake','env','lean',str(driver)],cwd=work,capture_output=True,text=True);(out/(cid+'-check.log')).write_text(run.stdout+run.stderr)
 if case['kind']=='control':assert run.returncode==0,(cid,run.stdout+run.stderr)
 else:assert run.returncode!=0 and 'false' in run.stdout+run.stderr and 'decide' in run.stdout+run.stderr,(cid,run.stdout+run.stderr)
 reports.append(dict(case,build='pass',dependency_audit='pass',independent_check='pass' if run.returncode==0 else 'rejects_exact_seed',declarations=declarations))
 (out/'report.json').write_bytes(m.encoded({'base_commit':base,'cases':reports}))
 print(cid,'verified',flush=True)
