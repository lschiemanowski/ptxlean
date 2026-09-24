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


class DeclarationSiteTests(unittest.TestCase):
    def test_nested_namespace_and_qualified_declaration_are_distinct(self):
        source = """namespace Ptx.Scalar.Binary32
namespace Text
theorem decode_encode : True := by trivial
end Text
def Text.decode := 1
end Ptx.Scalar.Binary32
"""
        self.assertEqual(checker.locate_declaration(source, 'Ptx.Scalar.Binary32.Text',
                                                   'decode_encode', proof=True),
                         'Ptx.Scalar.Binary32.Text.decode_encode')
        self.assertEqual(checker.locate_declaration(source, 'Ptx.Scalar.Binary32', 'Text.decode'),
                         'Ptx.Scalar.Binary32.Text.decode')
        with self.assertRaisesRegex(ValueError, 'missing or ambiguous'):
            checker.locate_declaration(source, 'Ptx.Scalar.Binary32', 'decode_encode')

    def test_sections_do_not_change_namespace_and_end_restores_parent(self):
        source = """namespace A
section Parameters
namespace B
noncomputable section
@[simp] theorem inside : True := by trivial
end
end B
end Parameters
section
def outside := 1
end
end A
"""
        self.assertEqual([site[0] for site in checker.declaration_sites(source)],
                         ['A.B.inside', 'A.outside'])

    def test_qualified_names_are_relative_unless_root_qualified(self):
        source = """namespace A
def B.value := 1
def A.value := 2
def _root_.Outside.value := 3
end A
"""
        self.assertEqual([site[0] for site in checker.declaration_sites(source)],
                         ['A.B.value', 'A.A.value', 'Outside.value'])
        self.assertEqual(checker.locate_declaration(source, 'Outside', 'value'), 'Outside.value')

    def test_comments_and_strings_cannot_supply_names_or_scopes(self):
        source = '''namespace A
/- namespace Fake
/- theorem answer : True := by trivial -/
end Fake -/
-- theorem answer : True := by trivial
def text := "namespace Fake\\n theorem answer : True := by trivial"
@[simp] theorem answer : True := by trivial -- end Wrong
end A
'''
        self.assertEqual(checker.locate_declaration(source, 'A', 'answer', proof=True), 'A.answer')
        with self.assertRaisesRegex(ValueError, 'missing or ambiguous'):
            checker.locate_declaration(source, 'Fake', 'answer', proof=True)

    def test_commented_declaration_is_missing(self):
        source = 'namespace A\n/- theorem answer : True := by trivial -/\nend A\n'
        with self.assertRaisesRegex(ValueError, 'missing or ambiguous'):
            checker.locate_declaration(source, 'A', 'answer', proof=True)

    def test_duplicate_qualified_sites_are_ambiguous(self):
        source = """namespace A
namespace B
theorem answer : True := by trivial
end B
def B.answer := 1
end A
"""
        with self.assertRaisesRegex(ValueError, 'missing or ambiguous'):
            checker.locate_declaration(source, 'A.B', 'answer', proof=True)

    def test_identical_short_names_in_different_namespaces_are_not_ambiguous(self):
        source = """namespace A
theorem answer : True := by trivial
end A
namespace B
theorem answer : True := by trivial
end B
"""
        self.assertEqual(checker.locate_declaration(source, 'B', 'answer', proof=True), 'B.answer')

    def test_definition_cannot_supply_proof_site(self):
        source = 'namespace A\ndef answer := True\nend A\n'
        with self.assertRaisesRegex(ValueError, 'not a theorem'):
            checker.locate_declaration(source, 'A', 'answer', proof=True)

    def test_private_site_is_not_public(self):
        source = 'namespace A\nprivate theorem answer : True := by trivial\nend A\n'
        with self.assertRaisesRegex(ValueError, 'missing or ambiguous'):
            checker.locate_declaration(source, 'A', 'answer', proof=True)

    def test_unbalanced_and_unsupported_scopes_fail_closed(self):
        for source in ['end A', 'namespace A', 'namespace A\nend B',
                       'namespace «A»\nend «A»', 'namespace A; section', 'namespace']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                checker.declaration_sites(source)

    def test_unsupported_declaration_name_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unsupported declaration header'):
            checker.declaration_sites('namespace A\ntheorem «answer» : True := by trivial\nend A')

    def test_modifiers_and_attributes_retain_public_name(self):
        source = """namespace A
noncomputable def realValue := 1
@[simp] protected theorem eq' : True := by trivial
end A
"""
        self.assertEqual(checker.locate_declaration(source, 'A', "eq'", proof=True), "A.eq'")
        self.assertEqual(checker.locate_declaration(source, 'A', 'realValue'), 'A.realValue')


class ImplementedFormTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.template = tempfile.TemporaryDirectory()
        cls.base = Path(cls.template.name)
        revision = os.environ.get('PTXLEAN_LEDGER_FIXTURE_REV')
        def read(path):
            # Vendor input is intentionally absent from every new commit. The
            # revision's ledger still pins its exact digest; never substitute a
            # mutable website version when constructing a replay fixture.
            if str(path) == '.ptx-source/9.4/index.html':
                raw = (ROOT / path).read_bytes()
                if hashlib.sha256(raw).hexdigest() != cls.data['files']['manual']['sha256']:
                    raise ValueError('Local fixture source differs from revision pin')
                return raw
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
        expected = 4 + (2 if 'binary32' in self.data['trials'] else 0)
        expected += 1 if 'select32' in self.data['trials'] else 0
        expected += 2 if 'signed_minmax32' in self.data['trials'] else 0
        expected += 3 if 'bitwise32' in self.data['trials'] else 0
        expected += 2 if 'unary_bits32' in self.data['trials'] else 0
        expected += 3 if 'shift32' in self.data['trials'] else 0
        expected += 1 if 'brev32' in self.data['trials'] else 0
        expected += 2 if 'mulhi32' in self.data['trials'] else 0
        expected += 2 if 'bfe32' in self.data['trials'] else 0
        expected += 1 if 'bfi32' in self.data['trials'] else 0
        expected += 1 if 'lop3' in self.data['trials'] else 0
        expected += 1 if 'prmt' in self.data['trials'] else 0
        self.assertEqual(self.check(), expected)

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
        with self.assertRaisesRegex(ValueError, 'missing or ambiguous declaration'):
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
