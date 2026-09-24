import concurrent.futures
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('worker_run', Path(__file__).resolve().parents[1] / 'scripts/worker_run.py')
w = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(w)


class WorkerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.home = Path(self.temp.name)
        self.repo = self.home / 'repo'
        self.repo.mkdir()
        subprocess.run(['git', 'init', '-q', str(self.repo)], check=True)
        for key, value in [('user.name', 'test'), ('user.email', 'test@example.invalid')]:
            w.git(self.repo, 'config', key, value)
        (self.repo / 'source.txt').write_text('pinned semantics\n')
        w.git(self.repo, 'add', 'source.txt')
        w.git(self.repo, 'commit', '-qm', 'fixture')
        self.base = w.git(self.repo, 'rev-parse', 'HEAD').decode().strip()
        self.task = {'schema_version': 1, 'id': 'fixture', 'base_commit': self.base,
                     'prompt': 'A test task', 'allowed_paths': ['result.txt'],
                     'sources': [{'path': 'source.txt', 'sha256': w.sha(b'pinned semantics\n')}]}
        self.task_file = self.home / 'task.json'
        w.atomic_json(self.task_file, self.task)
        self.campaign = self.home / 'campaign'

    def fake(self, extra='', exit_code=0):
        path = self.home / 'fake-codex'
        path.write_text('''#!/usr/bin/python3
import json,os,pathlib,sys
args=sys.argv
root=pathlib.Path(args[args.index('--cd')+1])
assert 'CODEX_API_KEY' not in os.environ and 'OPENAI_API_KEY' not in os.environ
(root/'result.txt').write_text('candidate\\n')
pathlib.Path(args[args.index('--output-last-message')+1]).write_text('done')
print(json.dumps({'type':'turn.completed','usage':{'input_tokens':7,'output_tokens':3}}))
''' + extra + f'\nsys.exit({exit_code})\n')
        path.chmod(0o755)
        return str(path)

    def local_task(self):
        body = b"Synthetic external source input\n"
        pin = {'isa_version':'9.4','artifact':'index.html','sha256':w.sha(body),'bytes':len(body)}
        manifest = self.repo/w.LOCAL_MANIFEST
        manifest.parent.mkdir(parents=True)
        manifest.write_text(json.dumps(pin))
        (self.repo/'.gitignore').write_text('.ptx-source/\n')
        w.git(self.repo,'add','.')
        w.git(self.repo,'commit','-qm','pin local source without distributing it')
        self.task['base_commit']=w.git(self.repo,'rev-parse','HEAD').decode().strip()
        self.task['sources'] += [
            {'path':w.LOCAL_MANIFEST,'sha256':w.sha(manifest.read_bytes())},
            {'path':w.LOCAL_SOURCE,'sha256':w.sha(body),'local_only':True}]
        local=self.repo/w.LOCAL_SOURCE;local.parent.mkdir(parents=True);local.write_bytes(body)
        w.atomic_json(self.task_file,self.task)
        return local

    def test_local_source_is_copied_but_never_enters_candidate_patch(self):
        local=self.local_task()
        receipt=w.execute(self.task_file,self.repo,self.campaign,'local',self.fake())
        worker=Path(receipt['worktree'])
        self.assertEqual((worker/w.LOCAL_SOURCE).read_bytes(),local.read_bytes())
        self.assertTrue(receipt['boundary']['eligible_for_review'])
        self.assertEqual(receipt['boundary']['changed_paths'],['result.txt'])
        self.assertNotIn(w.LOCAL_SOURCE.encode(),(self.campaign/'attempts/local/candidate.patch').read_bytes())

    def test_changed_local_source_blocks_before_any_model_call(self):
        self.local_task().write_bytes(b'wrong bytes')
        with self.assertRaisesRegex(ValueError,'Local source byte count|Source hash mismatch'):
            w.execute(self.task_file,self.repo,self.campaign,'local',self.fake())
        self.assertFalse((self.campaign/'ledger.json').exists())

    def test_worker_altering_local_source_is_rejected(self):
        self.local_task()
        receipt=w.execute(self.task_file,self.repo,self.campaign,'local',
            self.fake("(root/'"+w.LOCAL_SOURCE+"').write_text('changed')"))
        self.assertFalse(receipt['boundary']['eligible_for_review'])
        self.assertEqual(receipt['boundary']['altered_sources'],[w.LOCAL_SOURCE])

    def test_local_source_requires_committed_manifest_in_task(self):
        self.local_task()
        self.task['sources']=[x for x in self.task['sources'] if x['path']!=w.LOCAL_MANIFEST]
        with self.assertRaisesRegex(ValueError,'committed manifest'):w.validate_task(self.task,self.repo)

    def test_complete_is_not_accepted_and_patch_includes_new_file(self):
        with patch.dict('os.environ', {'CODEX_API_KEY': 'must-not-reach-worker', 'OPENAI_API_KEY': 'must-not-reach-worker'}):
            receipt = w.execute(self.task_file, self.repo, self.campaign, 'first', self.fake())
        self.assertEqual(receipt['state'], 'completed')
        self.assertEqual(receipt['acceptance'], 'not_reviewed')
        self.assertTrue(receipt['boundary']['eligible_for_review'])
        self.assertEqual(receipt['reported_usage'][0]['input_tokens'], 7)
        self.assertEqual(receipt['reported_models'], [])
        self.assertEqual(w.sha((self.campaign/'attempts/first/runner.py').read_bytes()), receipt['runner_sha256'])
        self.assertIn(b'+candidate', (self.campaign/'attempts/first/candidate.patch').read_bytes())
        self.assertFalse((self.repo/'result.txt').exists())
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']), 1)

    def test_failure_consumes_call_and_duplicate_cannot_rerun(self):
        receipt = w.execute(self.task_file, self.repo, self.campaign, 'failed', self.fake(exit_code=2))
        self.assertEqual(receipt['state'], 'failed')
        with self.assertRaises(ValueError):
            w.execute(self.task_file, self.repo, self.campaign, 'failed', self.fake())
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']), 1)

    def test_source_mismatch_before_dispatch(self):
        self.task['sources'][0]['sha256'] = '0'*64
        w.atomic_json(self.task_file, self.task)
        with self.assertRaisesRegex(ValueError, 'Source hash'):
            w.execute(self.task_file, self.repo, self.campaign, 'bad', self.fake())
        self.assertFalse((self.campaign/'ledger.json').exists())

    def test_uses_committed_source_not_working_edit(self):
        (self.repo/'source.txt').write_text('uncommitted source edit')
        w.validate_task(self.task, self.repo)
        receipt = w.execute(self.task_file, self.repo, self.campaign, 'pinned', self.fake())
        self.assertEqual((Path(receipt['worktree'])/'source.txt').read_text(), 'pinned semantics\n')

    def test_outside_edit_is_retained_but_ineligible(self):
        receipt = w.execute(self.task_file, self.repo, self.campaign, 'outside', self.fake("(root/'source.txt').write_text('changed')\n"))
        self.assertFalse(receipt['boundary']['eligible_for_review'])
        self.assertEqual(receipt['boundary']['outside_allowed'], ['source.txt'])

    def test_changed_head_is_ineligible(self):
        receipt = w.execute(self.task_file, self.repo, self.campaign, 'commit', self.fake("import subprocess\nsubprocess.run(['git','-C',str(root),'add','result.txt'],check=True)\nsubprocess.run(['git','-C',str(root),'commit','-qm','forbidden commit'],check=True)\n"))
        self.assertFalse(receipt['boundary']['head_unchanged'])
        self.assertFalse(receipt['boundary']['eligible_for_review'])

    def test_failed_launch_reserved_and_recorded(self):
        with self.assertRaises(FileNotFoundError):
            w.execute(self.task_file, self.repo, self.campaign, 'missing', str(self.home/'no-executable'))
        self.assertEqual(w.read_json(self.campaign/'ledger.json')['calls'][0]['state'], 'failed')
        self.assertEqual(w.read_json(self.campaign/'attempts/missing/receipt.json')['acceptance'], 'not_reviewed')

    def test_checkpoint_atomic_and_stale_reservations_count(self):
        # Reservations represent even runs lost before writing a final receipt.
        for i in range(199):
            w.reserve(self.campaign, f'old-{i}', self.task)
        def reserve(i):
            try:
                return w.reserve(self.campaign, f'concurrent-{i}', self.task)['call']
            except ValueError:
                return None
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            results = list(pool.map(reserve, [0, 1]))
        self.assertEqual(sorted(r for r in results if r is not None), [200])
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']), 200)

    def test_source_output_overlap_rejected(self):
        self.task['allowed_paths'].append('source.txt')
        with self.assertRaisesRegex(ValueError, 'Pinned source'):
            w.validate_task(self.task, self.repo)

    def test_ignored_outputs_still_break_boundary(self):
        (self.repo/'.gitignore').write_text('hidden.txt\n.lake/\n')
        w.git(self.repo, 'add', '.gitignore'); w.git(self.repo, 'commit', '-qm', 'ignore fixture')
        self.task['base_commit'] = w.git(self.repo, 'rev-parse', 'HEAD').decode().strip()
        w.atomic_json(self.task_file, self.task)
        receipt = w.execute(self.task_file, self.repo, self.campaign, 'ignored', self.fake("(root/'hidden.txt').write_text('hidden')\n(root/'.lake').mkdir()\n(root/'.lake'/'cache').write_text('generated')\n"))
        self.assertEqual(receipt['boundary']['outside_allowed'], ['hidden.txt'])
        self.assertIn(b'hidden', (self.campaign/'attempts/ignored/candidate.patch').read_bytes())

    def test_non_object_output_does_not_lose_receipt(self):
        receipt = w.execute(self.task_file, self.repo, self.campaign, 'json', self.fake("print('null')\nprint('not json')\n"))
        self.assertEqual(receipt['non_json_lines'], 2)
        self.assertEqual(receipt['state'], 'completed')
        self.assertTrue((self.campaign/'attempts/json/candidate.patch').exists())

    def test_unsafe_paths_rejected(self):
        for path in ['../escape', '/absolute', '.git/config', '.lake/build', './result.txt']:
            with self.subTest(path=path), self.assertRaises(ValueError):
                w.relative_path(path)

    def feedback(self):
        path = self.home / 'feedback.md'
        path.write_text('Complete remaining proofs.\n')
        return path

    def initial(self):
        return w.execute(self.task_file, self.repo, self.campaign, 'first', self.fake("print(json.dumps({'type':'thread.started','thread_id':'11111111-1111-1111-1111-111111111111'}))\n"))

    def repair(self, name='repair', parent='first', extra='', code=0):
        return w.resume(self.repo, self.campaign, name, parent, self.feedback(), self.fake("print(json.dumps({'type':'thread.started','thread_id':'11111111-1111-1111-1111-111111111111'}))\n" + extra, code))

    def test_resume_preserves_artifacts_and_reserves_before_dispatch(self):
        first = self.initial()
        original = self.campaign/'attempts/first'
        saved = {p.name:p.read_bytes() for p in original.iterdir() if p.is_file()}
        extra = ("assert 'resume' in args\n"
                 "assert args[-2]=='11111111-1111-1111-1111-111111111111'\n"
                 f"ledger=json.loads(pathlib.Path({str(self.campaign/'ledger.json')!r}).read_text())\n"
                 "assert ledger['calls'][-1]['attempt']=='repair' and ledger['calls'][-1]['state']=='started'\n"
                 "(root/'result.txt').write_text('repaired\\n')\n")
        second = self.repair(extra=extra)
        self.assertEqual(second['worktree'], first['worktree'])
        self.assertEqual(second['base_commit'], first['base_commit'])
        self.assertEqual(second['call'], 2)
        self.assertEqual(second['resume_from'], 'first')
        self.assertTrue(second['session_matches_requested'])
        self.assertTrue(second['boundary']['eligible_for_review'])
        self.assertEqual(second['acceptance'], 'not_reviewed')
        self.assertIn(b'+repaired', (self.campaign/'attempts/repair/candidate.patch').read_bytes())
        self.assertEqual(saved, {p.name:p.read_bytes() for p in original.iterdir() if p.is_file()})
        self.assertEqual((self.campaign/'attempts/repair/task.json').read_bytes(), saved['task.json'])

    def test_resume_rejects_worktree_drift(self):
        first = self.initial()
        (Path(first['worktree'])/'result.txt').write_text('unrecorded edit')
        with self.assertRaisesRegex(ValueError, 'does not match'):
            self.repair()
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']), 1)

    def test_resume_rejects_altered_prior_artifacts(self):
        self.initial()
        path = self.campaign/'attempts/first/candidate.patch'
        saved = path.read_bytes(); path.write_bytes(b'tampered')
        with self.assertRaisesRegex(ValueError, 'patch record changed'):
            self.repair()
        path.write_bytes(saved)
        path = self.campaign/'attempts/first/task.json'
        task = w.read_json(path); task['prompt']='different task'; w.atomic_json(path, task)
        with self.assertRaisesRegex(ValueError, 'task record changed'):
            self.repair()
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']), 1)

    def test_resume_lock_rejects_concurrent_use(self):
        first = self.initial()
        with w.worktree_locked(self.campaign, Path(first['worktree'])):
            with self.assertRaisesRegex(ValueError, 'already in use'):
                self.repair()
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']), 1)

    def test_resume_requires_latest_attempt(self):
        self.initial(); self.repair()
        with self.assertRaisesRegex(ValueError, 'latest recorded'):
            self.repair(name='stale')
        self.assertEqual(self.repair(name='third', parent='repair')['call'], 3)

    def test_resume_requires_session_and_terminal_record(self):
        self.initial()
        (self.campaign/'attempts/first/events.jsonl').write_text('{}\n')
        with self.assertRaisesRegex(ValueError, 'exactly one Codex session'):
            self.repair()
        path=self.campaign/'attempts/first/receipt.json'
        receipt=w.read_json(path); receipt['state']='started'; w.atomic_json(path,receipt)
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            self.repair()

    def test_resume_failed_call_is_counted(self):
        self.initial()
        result=self.repair(code=2)
        self.assertEqual(result['state'], 'failed')
        self.assertEqual(result['call'], 2)
        self.assertEqual(w.read_json(self.campaign/'ledger.json')['calls'][-1]['state'], 'failed')

    def test_resume_respects_checkpoint(self):
        self.initial()
        for i in range(198):
            w.reserve(self.campaign, f'other-{i}', self.task)
        self.assertEqual(self.repair()['call'], 200)
        with self.assertRaisesRegex(ValueError, '200 calls reserved'):
            self.repair(name='over', parent='repair')
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']), 200)

    def test_resume_unresolved_reservation_blocks_stale_parent(self):
        first = self.initial()
        w.reserve(self.campaign, 'crashed', self.task, worktree=first['worktree'], resume_from='first')
        with self.assertRaisesRegex(ValueError, 'latest recorded'):
            self.repair()
        self.assertEqual(len(w.read_json(self.campaign/'ledger.json')['calls']), 2)


if __name__ == '__main__':
    unittest.main()
