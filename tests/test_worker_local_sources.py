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
