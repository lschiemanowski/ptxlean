import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from validate_dense import saved, sha, replay, module


class ArtifactTests(unittest.TestCase):
    def test_replay_rejects_tampered_inputs_before_cuda(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp)
            (d/'cases.json').write_text('[]')
            (d/'exports.json').write_text('[]')
            receipt=dict(status='pass',cases=[],input_sha256=sha(d/'cases.json'),export_sha256=sha(d/'exports.json'))
            (d/'report.json').write_text(json.dumps(receipt))
            self.assertEqual(saved(d),receipt)
            (d/'cases.json').write_text('[{}]')
            with patch('validate_dense.Cuda') as cuda:
                with self.assertRaisesRegex(ValueError,'hash mismatch'):
                    replay(d)
                cuda.assert_not_called()

    def test_replay_rejects_tampered_binary(self):
        with tempfile.TemporaryDirectory() as tmp:
            d=Path(tmp)
            for name in ('cases.json','exports.json','x.ptx','x.cubin'):
                (d/name).write_text('[]')
            receipt=dict(status='pass',input_sha256=sha(d/'cases.json'),export_sha256=sha(d/'exports.json'),
                         cases=[dict(ptx='x.ptx',ptx_sha256=sha(d/'x.ptx'),cubin='x.cubin',cubin_sha256=sha(d/'x.cubin'))])
            (d/'report.json').write_text(json.dumps(receipt))
            (d/'x.cubin').write_text('changed')
            with self.assertRaisesRegex(ValueError,'hash mismatch'): saved(d)

    def test_version_does_not_silently_fall_back(self):
        e=dict(width=1,depth=0,shared_words=1,program=[])
        self.assertTrue(module(e,'9.4','sm_120').startswith('.version 9.4'))
        self.assertTrue(module(e,'9.2','sm_120').startswith('.version 9.2'))
        with self.assertRaises(ValueError): module(e,'9.1','sm_120')


if __name__ == '__main__':
    unittest.main()
