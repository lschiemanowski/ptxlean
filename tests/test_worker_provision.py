"""Offline provisioning: actual Git/worktrees and fake local build/model processes."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import worker_provision as p
import worker_run as w
import test_worker_run as legacy


class ProvisionTests(legacy.WorkerTests):
    def setUp(self):
        super().setUp()
        self.bin = self.home/'bin'; self.bin.mkdir()
        self.env = patch.dict(os.environ, {'PATH': str(self.bin)+os.pathsep+os.environ['PATH']})
        self.env.start(); self.addCleanup(self.env.stop)
        for name in ['lake','lean']:
            path = self.bin/name
            path.write_text('''#!/usr/bin/python3
import os,pathlib,sys
if sys.argv[1:] == ['--version']:
    if os.environ.get('VERSION_DRIFT'):
        pathlib.Path('result.txt').write_text('drift during version probe')
    print('Lean/Lake version 4.34.0')
elif sys.argv[1:3] == ['exe','cache']:
    print('official cache route')
    sys.exit(int(os.environ.get('CACHE_FAIL','0')))
elif sys.argv[1] == 'build':
    target=pathlib.Path('.lake/build/lib/lean/Prerequisite.olean')
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(b'compiled pinned prerequisite')
    print('source build')
    sys.exit(int(os.environ.get('BUILD_FAIL','0')))
else:
    raise RuntimeError(sys.argv)
'''); path.chmod(0o755)
        self.project='.'
        self.config(self.repo)
        (self.repo/'.gitignore').write_text('.lake/\n__pycache__/\n')
        self.pin()

    def config(self, directory):
        directory.mkdir(parents=True,exist_ok=True)
        (directory/'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
        (directory/'lakefile.toml').write_text('name = "fixture"\n')
        w.atomic_json(directory/'lake-manifest.json',{'lakeDir':'.lake','packagesDir':'.lake/packages','packages':[]})

    def pin(self):
        w.git(self.repo,'add','-A');w.git(self.repo,'commit','-qm','provision fixture')
        self.base=w.git(self.repo,'rev-parse','HEAD').decode().strip()
        self.task['base_commit']=self.base
        self.task['sources']=[{'path':'source.txt','sha256':w.sha((self.repo/'source.txt').read_bytes())}]
        for directory in sorted({'.',self.project}):
            for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
                path=str(Path(directory)/name)
                self.task['sources'].append({'path':path,'sha256':w.sha((self.repo/path).read_bytes())})
        w.atomic_json(self.task_file,self.task)

    def prepare(self, attempt='first', **kwargs):
        return p.prepare(self.task_file,self.repo,self.campaign,attempt,['Prerequisite'],**kwargs)

    def directory(self, attempt='first'):
        return self.campaign/'attempts'/attempt

    def tree(self, attempt='first'):
        return Path(w.read_json(self.directory(attempt)/'plan.json')['worktree'])

    def no_calls(self):
        self.assertFalse((self.campaign/'ledger.json').exists())

    def fake_session(self):
        return self.fake("print(json.dumps({'type':'thread.started','thread_id':'session-one'}))")

    def dependency(self):
        source=self.home/'dep';source.mkdir()
        subprocess.run(['git','init','-q',str(source)],check=True)
        w.git(source,'config','user.name','test');w.git(source,'config','user.email','t@example.invalid')
        (source/'Proof.lean').write_text('def original := 1\n')
        w.git(source,'add','.');w.git(source,'commit','-qm','dependency')
        revision=w.git(source,'rev-parse','HEAD').decode().strip()
        manifest=self.repo/self.project/'lake-manifest.json'
        data=w.read_json(manifest);data['packages']=[{'type':'git','name':'mathlib','url':'https://example.invalid/mathlib',
                                                  'rev':revision,'subDir':None}]
        w.atomic_json(manifest,data);self.pin()
        local=self.repo/self.project/'.lake/packages/mathlib';local.parent.mkdir(parents=True)
        local.symlink_to(source,target_is_directory=True)
        (source/'Proof.lean').write_text('dirty must not copy')
        (source/'.lake').mkdir();(source/'.lake/stale.olean').write_text('must not copy')
        return source,revision

    def test_prepare_installs_local_source_before_build_and_keeps_it_immutable(self):
        self.local_task()
        ready=self.prepare('local-prepared')
        worktree=self.campaign/'attempts/local-prepared/worktree'
        self.assertEqual((worktree/w.LOCAL_SOURCE).read_bytes(),(self.repo/w.LOCAL_SOURCE).read_bytes())
        self.assertEqual((self.campaign/'attempts/local-prepared/prepared.patch').read_bytes(),b'')
        (worktree/w.LOCAL_SOURCE).write_bytes(b'changed after preparation')
        with self.assertRaisesRegex(ValueError,'source|boundary'):
            p.run(self.repo,self.campaign,'local-prepared',self.fake())
        self.assertFalse((self.campaign/'ledger.json').exists())

    def test_prepare_and_run_are_separate_and_recorded(self):
        ready=self.prepare();self.assertEqual(ready['state'],'ready');self.no_calls()
        manifest=w.read_json(self.directory()/'ready.json')
        self.assertIn('.lake/build/lib/lean/Prerequisite.olean',manifest['artifacts'])
        self.assertEqual(len(manifest['versions']),2)
        receipt=p.run(self.repo,self.campaign,'first',self.fake_session())
        self.assertEqual(receipt['state'],'completed');self.assertTrue(receipt['boundary']['eligible_for_review'])
        self.assertEqual(receipt['provisioning_sha256'],ready['ready_sha256'])
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']),1)
        with self.assertRaisesRegex(ValueError,'already recorded'):
            p.run(self.repo,self.campaign,'first',self.fake_session())

    def test_failed_build_retry_keeps_logs_and_consumes_no_call(self):
        with patch.dict(os.environ,{'BUILD_FAIL':'2'}): failed=self.prepare()
        self.assertEqual(failed['state'],'failed');self.no_calls()
        old={c['log']:(self.directory()/c['log']).read_bytes() for c in failed['commands']}
        with self.assertRaisesRegex(ValueError,'not ready'):
            p.run(self.repo,self.campaign,'first',self.fake_session())
        ready=p.retry(self.repo,self.campaign,'first')
        self.assertEqual(ready['state'],'ready');self.assertEqual(len(ready['phases']),2);self.no_calls()
        for name,data in old.items():self.assertEqual((self.directory()/name).read_bytes(),data)
        self.assertTrue(list(self.directory().glob('run-check-*.json')))

    def test_missing_root_pin_is_rejected_without_attempt(self):
        self.task['sources']=[s for s in self.task['sources'] if s['path']!='lake-manifest.json']
        w.atomic_json(self.task_file,self.task)
        with self.assertRaisesRegex(ValueError,'immutable task source'):self.prepare()
        self.no_calls();self.assertFalse(self.directory().exists())

    def test_source_candidate_artifact_and_record_drift_rejected(self):
        for index,kind in enumerate(['source','candidate','artifact','task','ready','log','tool']):
            attempt='drift-'+str(index);self.prepare(attempt);tree=self.tree(attempt);directory=self.directory(attempt)
            if kind=='source':(tree/'source.txt').write_text('drift')
            elif kind=='candidate':(tree/'result.txt').write_text('unrecorded allowed change')
            elif kind=='artifact':(tree/'.lake/build/lib/lean/Prerequisite.olean').write_text('drift')
            elif kind=='task':(directory/'task.json').write_text('{}')
            elif kind=='ready':(directory/'ready.json').write_text('{}')
            elif kind=='log':
                log=w.read_json(directory/'ready.json')['commands'][0]['log'];(directory/log).write_text('drift')
            else:
                lean=self.bin/'lean';original=lean.read_text();lean.write_text(original.replace('4.34.0','4.35.0'))
            with self.subTest(kind=kind),self.assertRaises(ValueError):
                p.run(self.repo,self.campaign,attempt,self.fake_session())
            if kind=='tool':lean.write_text(original)
            self.no_calls()

    def test_independent_dependency_objects_and_official_cache_failure(self):
        source,rev=self.dependency()
        with patch.dict(os.environ,{'CACHE_FAIL':'1'}):ready=self.prepare()
        self.assertEqual(ready['state'],'ready');self.assertEqual(ready['official_cache']['exit_code'],1)
        target=self.tree()/'.lake/packages/mathlib'
        self.assertEqual(w.git(target,'rev-parse','HEAD').decode().strip(),rev)
        self.assertFalse(target.is_symlink());self.assertEqual((target/'Proof.lean').read_text(),'def original := 1\n')
        self.assertFalse((target/'.lake/stale.olean').exists())
        self.assertEqual((source/'Proof.lean').read_text(),'dirty must not copy')

    def test_dependency_tracked_and_untracked_drift_rejected(self):
        self.dependency()
        for i,filename in enumerate(['Proof.lean','Hidden.lean']):
            attempt='dep-'+str(i);self.prepare(attempt)
            (self.tree(attempt)/'.lake/packages/mathlib'/filename).write_text('drift')
            with self.assertRaisesRegex(ValueError,'Dependency .* sources changed'):
                p.run(self.repo,self.campaign,attempt,self.fake_session())
            self.no_calls()

    def test_dependency_symlink_rejected_on_retry(self):
        self.dependency()
        with patch.dict(os.environ,{'BUILD_FAIL':'1'}):self.prepare()
        target=self.tree()/'.lake/packages/mathlib'
        target.rename(target.with_name('kept'));target.symlink_to(target.with_name('kept'),target_is_directory=True)
        result=p.retry(self.repo,self.campaign,'first')
        self.assertEqual(result['state'],'failed');self.assertIn('symbolic',result['error']);self.no_calls()

    def test_subproject_build_location_and_cache_exemption(self):
        self.project='integration/torchlean';self.config(self.repo/self.project)
        self.task['replay_project']=self.project;self.pin()
        ready=self.prepare();self.assertEqual(ready['state'],'ready')
        self.assertTrue((self.tree()/self.project/'.lake/build/lib/lean/Prerequisite.olean').is_file())
        self.assertTrue(all(c['cwd']==str(self.tree()/self.project) for c in ready['commands'] if c['argv'][0]!='git'))
        receipt=p.run(self.repo,self.campaign,'first',self.fake_session())
        self.assertTrue(receipt['boundary']['eligible_for_review'])

    def test_resume_prepared_parent_must_still_be_latest(self):
        self.prepare();p.run(self.repo,self.campaign,'first',self.fake_session())
        feedback=self.home/'feedback.md';feedback.write_text('Improve proof')
        ready=p.prepare(None,self.repo,self.campaign,'prepared-repair',['Prerequisite'],'first',feedback)
        self.assertEqual(ready['state'],'ready')
        w.resume(self.repo,self.campaign,'other-repair','first',feedback,self.fake_session())
        with self.assertRaisesRegex(ValueError,'latest recorded'):
            p.run(self.repo,self.campaign,'prepared-repair',self.fake_session())
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']),2)

    def test_resume_runs_same_session_and_retains_prior_receipt(self):
        self.prepare();p.run(self.repo,self.campaign,'first',self.fake_session())
        prior=(self.directory()/'receipt.json').read_bytes()
        feedback=self.home/'feedback.md';feedback.write_text('Repair')
        ready=p.prepare(None,self.repo,self.campaign,'repair',['Prerequisite'],'first',feedback)
        self.assertEqual(ready['state'],'ready')
        receipt=p.run(self.repo,self.campaign,'repair',self.fake_session())
        self.assertEqual(receipt['resumed_session_id'],'session-one')
        self.assertEqual(receipt['resume_from'],'first');self.assertEqual((self.directory()/'receipt.json').read_bytes(),prior)
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']),2)

    def test_checkout_lock_blocks_run_without_call(self):
        self.prepare()
        with w.worktree_locked(self.campaign,self.tree()):
            with self.assertRaisesRegex(ValueError,'already in use'):
                p.run(self.repo,self.campaign,'first',self.fake_session())
        self.no_calls()

    def test_checkpoint_still_blocks_call_201(self):
        self.prepare()
        w.atomic_json(self.campaign/'ledger.json',{'schema_version':1,'checkpoint':200,
            'calls':[{'attempt':f'old-{i}'} for i in range(200)]})
        with self.assertRaisesRegex(ValueError,'200 calls reserved'):
            p.run(self.repo,self.campaign,'first',self.fake_session())
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']),200)
        self.assertFalse((self.directory()/'events.jsonl').exists())

    def test_worker_dependency_drift_is_ineligible(self):
        self.dependency();self.prepare()
        fake=self.fake("(root/'.lake/packages/mathlib/Proof.lean').write_text('worker drift')")
        receipt=p.run(self.repo,self.campaign,'first',fake)
        self.assertFalse(receipt['boundary']['eligible_for_review']);self.assertIn('provisioning_drift',receipt)

    def test_failed_retry_rejects_changed_allowed_candidate(self):
        with patch.dict(os.environ,{'BUILD_FAIL':'1'}):self.prepare()
        (self.tree()/'result.txt').write_text('not recorded')
        result=p.retry(self.repo,self.campaign,'first')
        self.assertEqual(result['state'],'failed');self.assertIn('candidate patch changed',result['error']);self.no_calls()

    def test_interrupted_preparation_retry_preserves_phase(self):
        original=subprocess.run
        def interrupt(args, **kwargs):
            if args[:2] == ['lake','build']:
                raise KeyboardInterrupt()
            return original(args, **kwargs)
        with patch.object(p.subprocess,'run',side_effect=interrupt):
            with self.assertRaises(KeyboardInterrupt):self.prepare()
        failed=w.read_json(self.directory()/'preparation.json')
        self.assertEqual(failed['state'],'interrupted');self.no_calls()
        ready=p.retry(self.repo,self.campaign,'first')
        self.assertEqual(ready['state'],'ready')
        self.assertEqual(ready['phases'][0]['state'],'interrupted')
        self.assertEqual(ready['phases'][1]['previous_state'],'interrupted')

    def test_tool_probe_cannot_change_source_then_dispatch(self):
        self.prepare()
        with patch.dict(os.environ,{'VERSION_DRIFT':'1'}):
            with self.assertRaisesRegex(ValueError,'candidate changed during'):
                p.run(self.repo,self.campaign,'first',self.fake_session())
        self.no_calls()

    def test_ready_repair_pins_complete_parent_receipt(self):
        self.prepare();p.run(self.repo,self.campaign,'first',self.fake_session())
        feedback=self.home/'feedback.md';feedback.write_text('Repair')
        p.prepare(None,self.repo,self.campaign,'repair',['Prerequisite'],'first',feedback)
        parent=w.read_json(self.directory()/'receipt.json');parent['reported_models']=['changed']
        w.atomic_json(self.directory()/'receipt.json',parent)
        with self.assertRaisesRegex(ValueError,'parent record changed'):
            p.run(self.repo,self.campaign,'repair',self.fake_session())
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']),1)

    def test_changed_provisioner_blocks_ready_dispatch(self):
        self.prepare()
        with patch.object(p,'helper_hashes',return_value={}):
            with self.assertRaisesRegex(ValueError,'helper version changed'):
                p.run(self.repo,self.campaign,'first',self.fake_session())
        self.no_calls()

    def test_dependency_origin_and_artifact_drift_rejected(self):
        self.dependency()
        for i,kind in enumerate(['origin','artifact']):
            attempt='dependency-extra-'+str(i);self.prepare(attempt)
            target=self.tree(attempt)/'.lake/packages/mathlib'
            if kind=='origin':
                w.git(target,'remote','set-url','origin','https://example.invalid/changed')
            else:
                artifact=target/'.lake/build/lib/lean/Extra.olean'
                artifact.parent.mkdir(parents=True);artifact.write_text('unrecorded dependency artifact')
            with self.assertRaisesRegex(ValueError,'origin changed|artifacts changed'):
                p.run(self.repo,self.campaign,attempt,self.fake_session())
            self.no_calls()


# Reuse fixtures without duplicating legacy runner tests.
for name in list(legacy.WorkerTests.__dict__):
    if name.startswith('test_') and name not in ProvisionTests.__dict__:
        setattr(ProvisionTests,name,None)
