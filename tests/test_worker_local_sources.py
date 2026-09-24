"""Source acquisition is explicit; untrusted or drifting bytes never become input."""
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
import check_sources as source
import check_distribution as distribution


class AcquisitionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.body = b'<p>Synthetic test documentation, not a vendor source.</p>'
        self.pin = {'isa_version':'9.4','artifact':'index.html','bytes':len(self.body),
                    'sha256':hashlib.sha256(self.body).hexdigest(),'url':'https://example.invalid/manual'}
        path=self.root/source.MANIFEST;path.parent.mkdir(parents=True);path.write_text(json.dumps(self.pin))

    def test_missing_source_never_downloads_implicitly(self):
        with patch.object(source,'urlopen',side_effect=AssertionError('implicit network')):
            with self.assertRaisesRegex(ValueError,'not bundled'):source.acquire(self.root)

    def test_explicit_fetch_verifies_and_installs_only_data(self):
        with patch.object(source,'urlopen',return_value=io.BytesIO(self.body)) as fetch:
            self.assertEqual(source.acquire(self.root,fetch=True),self.body)
            fetch.assert_called_once_with(self.pin['url'],timeout=60)
        self.assertEqual((self.root/source.SOURCE).read_bytes(),self.body)

    def test_wrong_download_is_not_installed(self):
        with patch.object(source,'urlopen',return_value=io.BytesIO(b'new publisher version')):
            with self.assertRaisesRegex(ValueError,'differs'):source.acquire(self.root,fetch=True)
        self.assertFalse((self.root/source.SOURCE).exists())

    def test_valid_cache_is_checked_without_network(self):
        p=self.root/source.SOURCE;p.parent.mkdir(parents=True);p.write_bytes(self.body)
        with patch.object(source,'urlopen',side_effect=AssertionError('unnecessary fetch')):
            self.assertEqual(source.acquire(self.root,fetch=True),self.body)

    def test_changed_cache_is_not_silently_overwritten(self):
        p=self.root/source.SOURCE;p.parent.mkdir(parents=True);p.write_bytes(b'changed')
        with patch.object(source,'urlopen',side_effect=AssertionError('replacement fetch')):
            with self.assertRaisesRegex(ValueError,'differs'):source.acquire(self.root,fetch=True)
        self.assertEqual(p.read_bytes(),b'changed')

    def test_existing_copy_still_requires_pinned_hash(self):
        p=self.root/'download.html';p.write_bytes(self.body)
        self.assertEqual(source.acquire(self.root,source_file=p),self.body)

    def test_distribution_guard_rejects_renamed_full_copy_and_raw_transcript(self):
        for name,body in [('notes.txt',self.body),('attempts/x/events.jsonl',b'{}'),
                          ('references/nvidia/a.html',b'x'),('.ptx-source/x',b'x')]:
            with self.subTest(name=name),self.assertRaisesRegex(ValueError,'Non-distributable'):
                distribution.check_payload(name,body,self.pin['sha256'])
        distribution.check_payload('review.txt',b'Our own explanation.',self.pin['sha256'])


class HistoryDistributionTests(unittest.TestCase):
    def setUp(self):
        import subprocess
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git = lambda *args: subprocess.check_output(['git', *args], cwd=self.root,
                                                       stderr=subprocess.DEVNULL)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Distribution test')
        self.git('config', 'user.email', 'test@example.invalid')
        self.manual = b'Synthetic manual bytes for a history test.'
        self.digest = hashlib.sha256(self.manual).hexdigest()

    def commit(self, name, body):
        path = self.root/name; path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(body)
        self.git('add', '--', name)
        self.git('commit', '-qm', 'fixture')
        return self.git('rev-parse', 'HEAD').decode().strip()

    def test_deleted_renamed_manual_remains_rejected_in_history(self):
        self.commit('renamed.txt', self.manual)
        self.git('rm', 'renamed.txt'); self.git('commit', '-qm', 'remove')
        with self.assertRaisesRegex(ValueError, 'Non-distributable'):
            distribution.check_history(self.root, 'HEAD', self.digest)

    def test_historical_archive_transcript_is_rejected(self):
        import tarfile
        body = io.BytesIO()
        with tarfile.open(fileobj=body, mode='w:gz') as stream:
            member = tarfile.TarInfo('attempts/one/events.jsonl')
            member.size = 2; stream.addfile(member, io.BytesIO(b'{}'))
        self.commit('evidence.tar.gz', body.getvalue())
        self.git('rm', 'evidence.tar.gz'); self.git('commit', '-qm', 'remove')
        with self.assertRaisesRegex(ValueError, 'Non-distributable'):
            distribution.check_history(self.root, 'HEAD', self.digest)

    def test_only_selected_history_is_scanned_not_private_other_refs(self):
        clean = self.commit('README.md', b'Project-authored description.')
        self.commit('private-source.txt', self.manual)
        self.assertEqual(distribution.check_history(self.root, clean, self.digest), (1, 1))
        with self.assertRaisesRegex(ValueError, 'Non-distributable'):
            distribution.check_history(self.root, 'HEAD', self.digest)
