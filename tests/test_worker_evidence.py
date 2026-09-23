"""Multi-trial archive discovery must not silently skip a failing second trial."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest import mock

MODULE = Path(__file__).resolve().parents[1] / "scripts/check_worker_evidence.py"
spec = importlib.util.spec_from_file_location("worker_evidence", MODULE)
evidence = importlib.util.module_from_spec(spec)
spec.loader.exec_module(evidence)


class MultiTrialEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def trial(self, name):
        directory = self.root / "formalization/results" / name
        directory.mkdir(parents=True)
        payload = b"preserved attempt receipt\n"
        archive = directory / "worker-evidence.tar.gz"
        with tarfile.open(archive, "w:gz") as stream:
            member = tarfile.TarInfo("attempts/example/receipt.json")
            member.size = len(payload)
            stream.addfile(member, io.BytesIO(payload))
        sha = lambda data: hashlib.sha256(data).hexdigest()
        manifest = directory / "evidence-manifest.json"
        manifest.write_text(json.dumps({
            "archive": archive.name, "archive_sha256": sha(archive.read_bytes()),
            "members": {"attempts/example/receipt.json": {
                "bytes": len(payload), "sha256": sha(payload)}}}))
        return manifest

    def test_discovers_and_verifies_both_trials(self):
        second = self.trial("second")
        first = self.trial("first")
        self.assertEqual(evidence.default_manifests(self.root), [first, second])
        with mock.patch.object(evidence, "default_manifests", return_value=[first, second]), \
             mock.patch("sys.argv", ["check_worker_evidence.py"]), \
             mock.patch("sys.stdout", new_callable=io.StringIO) as output:
            evidence.main()
        self.assertIn("2 archived files across 2 archives", output.getvalue())

    def test_default_run_rejects_corrupt_second_trial(self):
        first, second = self.trial("first"), self.trial("second")
        second.with_name("worker-evidence.tar.gz").write_bytes(b"changed archive")
        with mock.patch.object(evidence, "default_manifests", return_value=[first, second]), \
             mock.patch("sys.argv", ["check_worker_evidence.py"]):
            with self.assertRaisesRegex(ValueError, "archive hash mismatch"):
                evidence.main()

    def test_explicit_selection_does_not_discover_unselected_trial(self):
        selected = self.trial("selected")
        with mock.patch.object(evidence, "default_manifests", side_effect=AssertionError("must not discover")), \
             mock.patch("sys.argv", ["check_worker_evidence.py", str(selected)]), \
             mock.patch("sys.stdout", new_callable=io.StringIO):
            evidence.main()

    def test_no_archived_trials_is_not_vacuous_success(self):
        with self.assertRaisesRegex(ValueError, "No archived"):
            evidence.default_manifests(self.root)


if __name__ == "__main__":
    unittest.main()
