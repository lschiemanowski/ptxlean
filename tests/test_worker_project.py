"""Pinned subproject replay: actual Git reconstruction and fake Lean commands."""
import json
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_worker_replay as replay_tests
r = replay_tests.r


class ProjectReplayTests(replay_tests.ReplayTests):
    # Keep the reusable fixture helpers, without rerunning its root-only test methods.
    def setUp(self):
        super().setUp()
        self.project = 'integration/torchlean'
        self.project_dir = self.repo / self.project
        self.project_dir.mkdir(parents=True)
        for directory in [self.repo, self.project_dir]:
            (directory / 'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
            (directory / 'lakefile.toml').write_text('name = "fixture"\n')
            r.atomic_json(directory / 'lake-manifest.json', {'packagesDir': '.lake/packages', 'lakeDir': '.lake', 'packages': []})
        self.task['replay_project'] = self.project
        self.task['allowed_paths'] = [self.project + '/New.lean']
        self.commit_config()

    def commit_config(self):
        r.git(self.repo, 'add', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', self.project)
        r.git(self.repo, 'commit', '-qm', 'pinned project')
        self.base = r.git(self.repo, 'rev-parse', 'HEAD').decode().strip()
        self.task['base_commit'] = self.base
        self.task['sources'] = [{'path': 'source.txt', 'sha256': r.sha(b'pinned PTX semantics\n')}]
        for directory in ['', self.project + '/']:
            for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
                path = directory + name
                self.task['sources'].append({'path': path, 'sha256': r.sha((self.repo/path).read_bytes())})
        r.git(self.worker, 'reset', '--hard', self.base)
        old = self.worker/'Ptx/New.lean'
        if old.exists():
            old.unlink()
        (self.worker/self.project/'New.lean').write_text('namespace Ptx.New\ntheorem result : True := True.intro\nend Ptx.New\n')
        self.save_task()

    def save_task(self):
        r.atomic_json(self.attempt/'task.json', self.task)
        self.receipt.update(base_commit=self.task['base_commit'], task_sha256=r.sha(json.dumps(self.task, sort_keys=True).encode()))
        candidate, boundary = r.patch_and_boundary(self.worker, self.base, self.task['allowed_paths'], self.project)
        (self.attempt/'candidate.patch').write_bytes(candidate)
        self.receipt.update(patch_sha256=r.sha(candidate), boundary=boundary)
        r.atomic_json(self.attempt/'receipt.json', self.receipt)

    def fake_project_build(self, drift=False, fail_ledger=False, dependency_drift=False, cache_failure=False):
        def run(args, **kwargs):
            if args[0] == 'git':
                return self.real_run(args, **kwargs)
            cwd = Path(kwargs['cwd'])
            stage = ('base-form-ledger' if args[0] == 'python3' else 'baseline' if args[0] == 'bash'
                     else 'modules' if args[1] == 'build' else 'cache' if args[1] == 'exe'
                     else 'audit' if Path(args[-1]).name == 'audit.lean' else 'driver')
            self.stages.append(stage)
            self.assertEqual(cwd, self.destination/'worktree' if stage in ['baseline','base-form-ledger']
                             else self.destination/'worktree'/self.project)
            if stage == 'base-form-ledger':
                self.assertFalse((cwd/self.project/'New.lean').exists())
            elif stage == 'baseline':
                if (cwd/'coverage/implemented-forms.json').exists():
                    self.assertEqual(args[-1], '--defer-form-ledger')
                (cwd/'.lake').mkdir()
            elif stage == 'modules':
                (cwd/'.lake').mkdir(exist_ok=True)
                (cwd/'.lake/cache').write_text('fresh subproject build')
            elif stage == 'audit':
                if drift:
                    (cwd/'New.lean').write_text('unrecorded source drift\n')
                if dependency_drift:
                    (cwd/'.lake/packages/mathlib/Proof.lean').write_text('changed dependency\n')
            output = "'Ptx.New.result' does not depend on any axioms\n" if stage == 'audit' else stage+'\n'
            kwargs['stdout'].write(output.encode())
            failed = stage == 'base-form-ledger' and fail_ledger or stage == 'cache' and cache_failure
            return subprocess.CompletedProcess(args, 1 if failed else 0)
        return run

    def project_replay(self, **options):
        with patch.object(r.subprocess, 'run', side_effect=self.fake_project_build(**options)):
            return r.replay(self.attempt, self.repo, self.destination, ['Ptx.New'], [self.driver], ['Ptx.New.result'])

    def add_local_dependency(self):
        source = self.home/'dependency'
        source.mkdir()
        subprocess.run(['git', 'init', '-q', str(source)], check=True)
        r.git(source, 'config', 'user.name', 'test'); r.git(source, 'config', 'user.email', 'test@example.invalid')
        (source/'Proof.lean').write_text('def fromPinnedSource := 1\n')
        r.git(source,'add','.'); r.git(source,'commit','-qm','dependency')
        revision = r.git(source,'rev-parse','HEAD').decode().strip()
        manifest = r.read_json(self.project_dir/'lake-manifest.json')
        manifest['packages'] = [{'type':'git','name':'mathlib','url':'https://example.invalid/mathlib', 'rev':revision,'subDir':None}]
        r.atomic_json(self.project_dir/'lake-manifest.json',manifest)
        self.commit_config()
        target=self.project_dir/'.lake/packages/mathlib'
        target.parent.mkdir(parents=True)
        # A read-only source symlink is permitted; the replay checkout must be independent.
        target.symlink_to(source,target_is_directory=True)
        (source/'Proof.lean').write_text('dirty source must not be copied\n')
        (source/'.lake').mkdir(); (source/'.lake/stale.olean').write_text('bad cache')
        return source, revision

    def test_project_cwds_and_nested_cache_boundary(self):
        record = self.project_replay()
        self.assertEqual(record['mechanical'],'pass')
        self.assertEqual(record['replay_project'],self.project)
        self.assertEqual(self.stages,['baseline','modules','driver','audit'])
        self.assertEqual(record['boundary']['changed_paths'],self.task['allowed_paths'])
        self.assertTrue(all('cwd' in c for c in record['commands']))

    def test_bad_project_paths(self):
        for value in ['/tmp/x','../outside','integration/../torchlean','integration/.lake/x', '', None]:
            with self.subTest(value=value):
                self.task['replay_project']=value;self.save_task()
                with self.assertRaises(ValueError):
                    self.project_replay()
        self.assertFalse(self.destination.exists())

    def test_missing_manifest_pin(self):
        self.task['sources']=[s for s in self.task['sources'] if s['path'] != self.project+'/lake-manifest.json']
        self.save_task()
        with self.assertRaisesRegex(ValueError,'immutable task source'):
            self.project_replay()

    def test_unpinned_dependency_revision(self):
        manifest=r.read_json(self.project_dir/'lake-manifest.json')
        manifest['packages']=[{'name':'mathlib','type':'git','rev':'main'}]
        r.atomic_json(self.project_dir/'lake-manifest.json',manifest);self.commit_config()
        with self.assertRaisesRegex(ValueError,'exact commit'):
            self.project_replay()

    def test_external_path_dependency(self):
        manifest=r.read_json(self.project_dir/'lake-manifest.json')
        manifest['packages']=[{'name':'external','type':'path','dir':'../../../external','configFile':'lakefile.toml'}]
        r.atomic_json(self.project_dir/'lake-manifest.json',manifest);self.commit_config()
        with self.assertRaisesRegex(ValueError,'repository root'):
            self.project_replay()

    def test_toolchain_mismatch(self):
        (self.project_dir/'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n');self.commit_config()
        with self.assertRaisesRegex(ValueError,'toolchains differ'):
            self.project_replay()

    def test_project_source_drift(self):
        self.assert_failure_record(self.project_replay(drift=True),'recorded allowed patch')

    def test_unselected_nested_lake_is_not_exempt(self):
        outside=self.worker/'other/.lake/cache';outside.parent.mkdir(parents=True);outside.write_text('not selected')
        self.save_task()
        self.assertFalse(self.receipt['boundary']['eligible_for_review'])

    def test_independent_dependency_checkout_and_official_cache(self):
        original, revision=self.add_local_dependency()
        record=self.project_replay(cache_failure=True)
        self.assertEqual(record['mechanical'],'pass')
        target=self.destination/'worktree'/self.project/'.lake/packages/mathlib'
        self.assertFalse(target.is_symlink())
        self.assertEqual((target/'Proof.lean').read_text(),'def fromPinnedSource := 1\n')
        self.assertFalse((target/'.lake/stale.olean').exists())
        self.assertEqual((original/'Proof.lean').read_text(),'dirty source must not be copied\n')
        self.assertEqual(record['official_cache']['source_revision'],revision)
        self.assertEqual(record['official_cache']['exit_code'],1)
        self.assertIn('cache',self.stages)

    def test_changed_dependency_fails(self):
        self.add_local_dependency()
        self.assert_failure_record(self.project_replay(dependency_drift=True),'Dependency tracked sources changed')

    def test_missing_local_dependency_has_failed_receipt(self):
        original,_=self.add_local_dependency()
        (self.project_dir/'.lake/packages/mathlib').unlink()
        self.assert_failure_record(self.project_replay(),'Missing local dependency prerequisite')
        self.assertEqual(self.stages,['baseline'])

    def ledger_fixture(self):
        (self.repo/'coverage').mkdir();(self.repo/'coverage/implemented-forms.json').write_text('{}')
        r.git(self.repo,'add','coverage');self.commit_config()

    def test_pristine_ledger_precedes_patch_and_deferral_visible(self):
        self.ledger_fixture()
        record=self.project_replay()
        self.assertEqual(record['mechanical'],'pass')
        self.assertEqual(self.stages[0],'base-form-ledger')
        self.assertEqual(record['form_ledger']['pristine_base'],'pass')
        self.assertEqual(record['form_ledger']['candidate'],'deferred_to_coordinator')
        self.assertEqual(record['form_ledger']['regression_fixture_revision'],self.base)

    def test_pristine_ledger_failure_blocks_patch_and_builds(self):
        self.ledger_fixture()
        record=self.project_replay(fail_ledger=True)
        self.assert_failure_record(record,'base-form-ledger failed')
        self.assertEqual(self.stages,['base-form-ledger'])
        self.assertFalse((self.destination/'worktree'/self.project/'New.lean').exists())

# Root-only tests remain in test_worker_replay.py, not inherited into this suite.
for name in list(replay_tests.ReplayTests.__dict__):
    if name.startswith('test_') and name not in ProjectReplayTests.__dict__:
        setattr(ProjectReplayTests,name,None)
