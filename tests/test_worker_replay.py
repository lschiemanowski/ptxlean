"""Offline mechanical-gate tests: real Git reconstruction, fake build processes."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
SPEC = importlib.util.spec_from_file_location('worker_replay_under_test', SCRIPTS / 'worker_replay.py')
r = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(r)


class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.home = Path(self.temp.name)
        self.repo = self.home / 'repo'
        self.repo.mkdir()
        subprocess.run(['git', 'init', '-q', str(self.repo)], check=True)
        for key, value in [('user.name', 'test'), ('user.email', 'test@example.invalid')]:
            r.git(self.repo, 'config', key, value)
        (self.repo / 'Ptx').mkdir()
        (self.repo / 'Ptx.lean').write_text('import Ptx.Base\n')
        (self.repo / 'Ptx/Base.lean').write_text('def baseline : Nat := 1\n')
        (self.repo / 'source.txt').write_text('pinned PTX semantics\n')
        r.git(self.repo, 'add', '.')
        r.git(self.repo, 'commit', '-qm', 'baseline')
        self.base = r.git(self.repo, 'rev-parse', 'HEAD').decode().strip()
        self.task = {'schema_version': 1, 'id': 'fixture', 'base_commit': self.base,
                     'prompt': 'Add the requested theorem', 'allowed_paths': ['Ptx/New.lean'],
                     'sources': [{'path': 'source.txt', 'sha256': r.sha(b'pinned PTX semantics\n')}]}
        self.attempt = self.home / 'attempt'
        self.attempt.mkdir()
        self.worker = self.attempt / 'worktree'
        r.git(self.repo, 'worktree', 'add', '--detach', str(self.worker), self.base)
        r.atomic_json(self.attempt / 'task.json', self.task)
        self.receipt = {'attempt': 'fixture-001', 'base_commit': self.base,
                        'task_sha256': r.sha(json.dumps(self.task, sort_keys=True).encode()),
                        'state': 'completed', 'finished_at': '2026-09-23T00:00:00Z'}
        self.replace_candidate('namespace Ptx.New\ntheorem result : True := True.intro\nend Ptx.New\n')
        self.driver = self.home / 'contract.lean'
        self.driver.write_text('import Ptx.New\n#check Ptx.New.result\n')
        self.destination = self.home / 'replay'
        self.real_run = subprocess.run
        self.stages = []

    def replace_candidate(self, text):
        (self.worker / 'Ptx/New.lean').write_text(text)
        candidate, boundary = r.patch_and_boundary(self.worker, self.base, self.task['allowed_paths'])
        (self.attempt / 'candidate.patch').write_bytes(candidate)
        self.receipt.update(patch_sha256=r.sha(candidate), boundary=boundary)
        r.atomic_json(self.attempt / 'receipt.json', self.receipt)

    def fake_build(self, fail=None, audit=None, drift=False, launch_error=False):
        if audit is None:
            audit = "'Ptx.New.result' depends on axioms: [propext]\n"
        def run(args, **kwargs):
            if args[0] == 'git':
                return self.real_run(args, **kwargs)
            self.assertIn(args[0], ['bash', 'lake'])
            stage = ('baseline' if args[0] == 'bash' else 'modules' if args[1] == 'build'
                     else 'audit' if Path(args[-1]).name == 'audit.lean' else 'driver')
            self.stages.append(stage)
            checkout = Path(kwargs['cwd'])
            self.assertNotEqual(checkout, self.worker)
            if stage == 'baseline':
                self.assertFalse((checkout / '.lake').exists(), 'Worker build cache was copied')
                self.assertEqual(args, ['bash', 'scripts/check.sh', '--clean'])
                (checkout / '.lake').mkdir()
                (checkout / '.lake/cache').write_text('new checker build')
            if stage == fail and launch_error:
                raise FileNotFoundError('fake missing executable')
            output = audit if stage == 'audit' else stage + ' checked\n'
            kwargs['stdout'].write(output.encode())
            if drift and stage == 'audit':
                (checkout / 'Ptx/New.lean').write_text('unrecorded checking change\n')
            return subprocess.CompletedProcess(args, 1 if stage == fail else 0)
        return run

    def replay(self, **fake_options):
        with patch.object(r.subprocess, 'run', side_effect=self.fake_build(**fake_options)):
            return r.replay(self.attempt, self.repo, self.destination, ['Ptx.New'],
                            [self.driver], ['Ptx.New.result'])

    def assert_failure_record(self, record, message):
        self.assertEqual(record['mechanical'], 'fail')
        self.assertIn(message, record['error'])
        self.assertTrue(record['finished_at'])
        self.assertEqual(r.read_json(self.destination / 'result.json'), record)
        self.assertEqual(record['semantic_review'], 'not_performed')
        self.assertEqual(record['integration'], 'not_performed')

    def test_reconstructs_new_file_without_worker_files_or_cache(self):
        original = (self.worker / 'Ptx/New.lean').read_bytes()
        (self.worker / '.lake').mkdir()
        (self.worker / '.lake/stale.olean').write_text('polluted original build')
        (self.worker / 'Ptx/New.lean').write_text('edited after recorded submission')
        driver = self.driver.read_bytes()
        record = self.replay()
        self.assertEqual(record['mechanical'], 'pass')
        self.assertEqual(self.stages, ['baseline', 'modules', 'driver', 'audit'])
        self.assertEqual((self.destination / 'worktree/Ptx/New.lean').read_bytes(), original)
        self.assertFalse((self.destination / 'worktree/.lake/stale.olean').exists())
        self.assertEqual((self.destination / 'driver-0.lean').read_bytes(), driver)
        self.assertEqual(record['drivers'][0]['sha256'], r.sha(driver))
        self.assertEqual(record['boundary']['changed_paths'], ['Ptx/New.lean'])
        self.assertTrue(record['boundary']['eligible_for_review'])
        self.assertFalse((self.repo / 'Ptx/New.lean').exists())
        self.assertEqual(record['semantic_review'], 'not_performed')
        self.assertEqual(record['integration'], 'not_performed')

    def test_patch_hash_tampering_rejected_before_checkout(self):
        (self.attempt / 'candidate.patch').write_bytes(b'tampered')
        with self.assertRaisesRegex(ValueError, 'patch hash'):
            self.replay()
        self.assertFalse(self.destination.exists())

    def test_task_hash_and_base_tampering_rejected(self):
        task = dict(self.task, prompt='different obligations')
        r.atomic_json(self.attempt / 'task.json', task)
        with self.assertRaisesRegex(ValueError, 'task hash'):
            self.replay()
        r.atomic_json(self.attempt / 'task.json', self.task)
        self.receipt['base_commit'] = '0' * 40
        r.atomic_json(self.attempt / 'receipt.json', self.receipt)
        with self.assertRaisesRegex(ValueError, 'base differs'):
            self.replay()
        self.assertFalse(self.destination.exists())

    def test_unresolved_and_ineligible_receipts_rejected(self):
        for state, eligible, expected in [('started', True, 'unresolved'),
                                          ('completed', False, 'review boundary')]:
            with self.subTest(state=state, eligible=eligible):
                self.receipt.update(state=state, boundary={'eligible_for_review': eligible})
                r.atomic_json(self.attempt / 'receipt.json', self.receipt)
                with self.assertRaisesRegex(ValueError, expected):
                    self.replay()
        self.assertFalse(self.destination.exists())

    def test_reconstructed_edit_boundary_is_checked_independently(self):
        (self.worker / 'outside.txt').write_text('outside assigned paths')
        self.replace_candidate('theorem result : True := True.intro\n')
        self.receipt['boundary']['eligible_for_review'] = True
        r.atomic_json(self.attempt / 'receipt.json', self.receipt)
        record = self.replay()
        self.assert_failure_record(record, 'recorded allowed patch')
        self.assertEqual(self.stages, [])

    def test_every_build_gate_failure_is_recorded_and_stops_later_gates(self):
        order = ['baseline', 'modules', 'driver', 'audit']
        for index, stage in enumerate(order):
            with self.subTest(stage=stage):
                self.destination = self.home / ('replay-' + stage)
                self.stages = []
                record = self.replay(fail=stage)
                self.assert_failure_record(record, 'failed with exit code 1')
                self.assertEqual(self.stages, order[:index + 1])
                self.assertEqual(record['commands'][-1]['exit_code'], 1)
                self.assertTrue((self.destination / record['commands'][-1]['log']).exists())

    def test_bad_dependency_reports_fail_after_successful_audit_process(self):
        reports = [('', 'Missing'),
                   ("'Ptx.New.other' does not depend on any axioms\n", 'unexpected'),
                   ("'Ptx.New.result' does not depend on any axioms\n" * 2, 'duplicate'),
                   ("'Ptx.New.result' depends on axioms: [customOracle]\n", 'Disallowed')]
        for index, (log, expected) in enumerate(reports):
            with self.subTest(log=log):
                self.destination = self.home / ('audit-' + str(index))
                record = self.replay(audit=log)
                self.assert_failure_record(record, expected)
                self.assertEqual(record['commands'][-1]['exit_code'], 0)

    def test_no_axioms_report_is_accepted(self):
        record = self.replay(audit="'Ptx.New.result' does not depend on any axioms\n")
        self.assertEqual(record['mechanical'], 'pass')

    def test_checking_induced_source_drift_fails(self):
        record = self.replay(drift=True)
        self.assert_failure_record(record, 'recorded allowed patch')
        self.assertEqual(self.stages[-1], 'audit')

    def test_forbidden_proof_declaration_stops_before_builds(self):
        self.replace_candidate('axiom fabricated : False\n')
        record = self.replay()
        self.assert_failure_record(record, 'Forbidden proof token')
        self.assertEqual(self.stages, [])

    def test_command_launch_failure_has_command_level_record(self):
        record = self.replay(fail='modules', launch_error=True)
        self.assert_failure_record(record, 'fake missing executable')
        command = record['commands'][-1]
        self.assertTrue(command.get('finished_at'))
        self.assertEqual(command.get('log'), 'modules.log')
        self.assertIn('FileNotFoundError', command.get('error', ''))
        self.assertTrue((self.destination / command['log']).exists())

    def test_invalid_patch_has_recorded_apply_failure(self):
        data = b'not a Git patch\n'
        (self.attempt / 'candidate.patch').write_bytes(data)
        self.receipt['patch_sha256'] = r.sha(data)
        r.atomic_json(self.attempt / 'receipt.json', self.receipt)
        record = self.replay()
        self.assert_failure_record(record, 'apply failed')
        self.assertEqual(self.stages, [])
        self.assertNotEqual(record['commands'][0]['exit_code'], 0)
        self.assertTrue((self.destination / 'apply.log').exists())

    def test_source_hash_mismatch_rejected_before_checkout(self):
        self.task['sources'][0]['sha256'] = '0' * 64
        r.atomic_json(self.attempt / 'task.json', self.task)
        self.receipt['task_sha256'] = r.sha(json.dumps(self.task, sort_keys=True).encode())
        r.atomic_json(self.attempt / 'receipt.json', self.receipt)
        with self.assertRaisesRegex(ValueError, 'Source hash mismatch'):
            self.replay()
        self.assertFalse(self.destination.exists())

    def test_allowed_lean_files_outside_ptx_are_scanned(self):
        self.task['allowed_paths'].append('Extra.lean')
        r.atomic_json(self.attempt / 'task.json', self.task)
        self.receipt['task_sha256'] = r.sha(json.dumps(self.task, sort_keys=True).encode())
        (self.worker / 'Extra.lean').write_text('axiom unusedOracle : False\n')
        self.replace_candidate('namespace Ptx.New\ntheorem result : True := True.intro\nend Ptx.New\n')
        record = self.replay()
        self.assert_failure_record(record, 'Forbidden proof token')
        self.assertEqual(self.stages, [])

    def test_independent_driver_is_scanned_and_preserved_on_failure(self):
        self.driver.write_text('import Ptx.New\naxiom leakedAssumption : False\n')
        record = self.replay()
        self.assert_failure_record(record, 'Forbidden proof token')
        self.assertEqual(self.stages, ['baseline', 'modules'])
        self.assertEqual((self.destination/'driver-0.lean').read_bytes(), self.driver.read_bytes())
        self.assertEqual(record['drivers'][0]['sha256'], r.sha(self.driver.read_bytes()))


    def test_allowed_symlink_output_is_rejected_before_build(self):
        target = self.home / 'external.lean'
        target.write_text('theorem externallyMutable : True := True.intro\n')
        output = self.worker / 'Ptx/New.lean'
        output.unlink()
        output.symlink_to(target)
        candidate, boundary = r.patch_and_boundary(self.worker, self.base, self.task['allowed_paths'])
        (self.attempt / 'candidate.patch').write_bytes(candidate)
        self.receipt.update(patch_sha256=r.sha(candidate), boundary=boundary)
        r.atomic_json(self.attempt / 'receipt.json', self.receipt)
        record = self.replay()
        self.assert_failure_record(record, 'symbolic-link targets')
        self.assertEqual(self.stages, [])
        self.assertTrue((self.destination / 'worktree/Ptx/New.lean').is_symlink())


if __name__ == '__main__':
    unittest.main()
