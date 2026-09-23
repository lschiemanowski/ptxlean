"""Behavior checks for the selected-form ledger, using actual retained evidence."""
import copy
import hashlib
import json
import os
import subprocess
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import check_implemented_forms as checker


def fixture_bytes(root, path, revision=None):
    if revision:
        return subprocess.check_output(['git', '-C', str(root), 'show', f'{revision}:{path}'])
    return (root / path).read_bytes()


class FixtureRevisionTests(unittest.TestCase):
    def test_requested_revision_uses_git_bytes_not_working_tree(self):
        with patch.object(subprocess, 'check_output', return_value=b'committed bytes') as command:
            self.assertEqual(fixture_bytes(ROOT, checker.LEDGER, 'HEAD'), b'committed bytes')
            command.assert_called_once_with(['git', '-C', str(ROOT), 'show', f'HEAD:{checker.LEDGER}'])

    def test_missing_requested_revision_does_not_fall_back(self):
        error = subprocess.CalledProcessError(128, ['git', 'show'])
        with patch.object(subprocess, 'check_output', side_effect=error):
            with self.assertRaises(subprocess.CalledProcessError):
                fixture_bytes(ROOT, checker.LEDGER, 'missing')


class ImplementedFormTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.template = tempfile.TemporaryDirectory()
        cls.base = Path(cls.template.name)
        revision = os.environ.get('PTXLEAN_LEDGER_FIXTURE_REV')
        def read(path):
            return fixture_bytes(ROOT, path, revision)
        cls.data = json.loads(read(checker.LEDGER))
        paths = {ref['path'] for ref in cls.data['files'].values()}
        for trial in cls.data['trials'].values():
            path = Path(cls.data['files'][trial['evidence']]['path'])
            manifest = json.loads(read(path))
            paths.add(str(path.parent / manifest['archive']))
        for path in paths:
            destination = cls.base / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(read(path))

    @classmethod
    def tearDownClass(cls):
        cls.template.cleanup()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        shutil.copytree(self.base, self.root, dirs_exist_ok=True)
        self.data = copy.deepcopy(type(self).data)

    def check(self):
        path = self.root / checker.LEDGER
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(self.data))
        return checker.verify(self.root)

    def test_current_selected_forms_pass(self):
        self.assertEqual(self.check(), 4)

    def test_wrong_source_rejected_even_if_file_hash_refreshed(self):
        ref = self.data['files']['manual']
        path = self.root / ref['path']
        raw = path.read_bytes() + b'\n'
        path.write_bytes(raw)
        ref['sha256'] = hashlib.sha256(raw).hexdigest()
        with self.assertRaisesRegex(ValueError, 'pinned source mismatch'):
            self.check()

    def test_missing_proof_site_rejected(self):
        self.data['forms'][0]['proofs'][0]['name'] = 'missing_proof'
        with self.assertRaisesRegex(ValueError, 'missing or ambiguous declaration'):
            self.check()

    def test_duplicate_accepted_form_rejected(self):
        self.data['forms'].append(copy.deepcopy(self.data['forms'][0]))
        with self.assertRaisesRegex(ValueError, 'duplicate form'):
            self.check()

    def test_accepted_form_cannot_also_be_uncovered(self):
        self.data['uncovered_siblings'][0]['spellings'].append('min.u32')
        with self.assertRaisesRegex(ValueError, 'duplicate form'):
            self.check()

    def test_wrong_source_anchor_rejected(self):
        self.data['source']['sections']['missing-source-section'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'missing source anchor'):
            self.check()

    def test_source_section_hash_rejected(self):
        anchor = self.data['forms'][0]['source_anchor']
        self.data['source']['sections'][anchor] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'section hash mismatch'):
            self.check()

    def test_stale_definition_reference_rejected(self):
        path = self.root / self.data['files']['scalar']['path']
        path.write_bytes(path.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'file hash mismatch: scalar'):
            self.check()

    def test_missing_proof_file_rejected(self):
        (self.root / self.data['files']['minmax']['path']).unlink()
        with self.assertRaises(FileNotFoundError):
            self.check()

    def test_wrong_namespace_rejected(self):
        self.data['forms'][0]['proofs'][0]['namespace'] = 'Unrelated'
        with self.assertRaisesRegex(ValueError, 'namespace/site mismatch'):
            self.check()

    def test_wrong_patch_identity_rejected(self):
        self.data['trials']['minmax']['patch_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'patch mismatch'):
            self.check()

    def test_target_condition_cannot_drift(self):
        self.data['forms'][2]['target'] = 'all'
        with self.assertRaisesRegex(ValueError, 'target mismatch'):
            self.check()


if __name__ == '__main__':
    unittest.main()
