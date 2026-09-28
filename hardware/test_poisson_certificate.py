"""Behavioral checks for binding the exact residual request to saved GPU words."""
import json
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch

from certify_poisson import request, certify
from poisson_kernels import Layout, module

REFERENCE = Path(__file__).resolve().parents[1] / 'examples/poisson/reference.json'


class CertificateBinding(unittest.TestCase):
    def test_saved_arena_words_and_solution_are_exact(self):
        ref = json.loads(REFERENCE.read_text())['outputs'][1]
        layout = Layout(ref, {})
        module(layout, '9.2')
        with tempfile.TemporaryDirectory() as name:
            folder = Path(name)
            (folder/'layout.json').write_text(json.dumps(layout.manifest()))
            (folder/'arena.bin').write_bytes(layout.data)
            (folder/'observed.json').write_text(json.dumps({
                'solution': ref['solution'], 'true_residual_norm': -1000,
                'tolerance': 1000000}))
            value = request(folder)
            expected = lambda x: struct.unpack('<Q', struct.pack('<d', x))[0]
            self.assertEqual(value['B'], list(map(expected, ref['B'])))
            self.assertEqual(value['solution'], list(map(expected, ref['solution'])))
            self.assertEqual(value['W'], [expected(a*b) for a in ref['weights'] for b in ref['weights']])
            self.assertEqual(value['rtol'], expected(1e-10))
            self.assertNotIn('true_residual_norm', value)
            self.assertNotIn('tolerance', value)

    def test_corrupt_archive_is_rejected_before_building_or_checking(self):
        with tempfile.TemporaryDirectory() as name:
            folder = Path(name)
            (folder/'arena.bin').write_bytes(b'changed')
            (folder/'report.json').write_text(json.dumps({
                'numerical_status': 'pass', 'artifacts': {'arena.bin': '0'*64}, 'cases': []}))
            with patch('certify_poisson.build', side_effect=AssertionError('must not build')):
                with self.assertRaisesRegex(ValueError, 'artifact hash mismatch'):
                    certify(folder, folder/'certificate')
            self.assertEqual(json.loads((folder/'certificate/certification.json').read_text())['status'], 'fail')


if __name__ == '__main__':
    unittest.main()
