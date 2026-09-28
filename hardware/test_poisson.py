"""Input/provenance rejection tests; GPU behavior is exercised by validate_poisson."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from poisson_kernels import Layout,module
from validate_poisson import replay

REFERENCE=Path(__file__).resolve().parents[1]/'examples/poisson/reference.json'


class PoissonInputs(unittest.TestCase):
    def setUp(self):self.ref=json.loads(REFERENCE.read_text())['outputs'][4]

    def test_reject_wrong_geometry_and_shape(self):
        for field,value in [('cells',[[0]]),('boundary',[0]),('degree',0),('n',0),('B',[])]:
            with self.subTest(field=field):
                ref=copy.deepcopy(self.ref);ref[field]=value
                with self.assertRaises(ValueError):Layout(ref,{})

    def test_reject_nonfinite_and_invalid_diagonal(self):
        for field in ('load','probe','diagonal'):
            ref=copy.deepcopy(self.ref);ref[field][4]=float('nan')
            with self.assertRaises(ValueError):Layout(ref,{})
        ref=copy.deepcopy(self.ref);ref['diagonal'][ref['interior'][0]]=0
        with self.assertRaises(ValueError):Layout(ref,{})

    def test_reject_solver_options_and_version_fallback(self):
        for options in ({'rtol':-1},{'rtol':0},{'atol':float('inf')},{'check_every':0},{'maxiter':True}):
            with self.assertRaises(ValueError):Layout(self.ref,options)
        with self.assertRaises(ValueError):module(Layout(self.ref,{}),'9.1')
        with self.assertRaises(ValueError):module(Layout(self.ref,{}),'9.2','sm_90')
        self.assertTrue(module(Layout(self.ref,{})).startswith('.version 9.4\n'))

    def test_replay_rejects_tampering_before_cuda(self):
        with tempfile.TemporaryDirectory() as d:
            path=Path(d);(path/'kernel.cubin').write_bytes(b'changed')
            (path/'report.json').write_text(json.dumps({'numerical_status':'pass','cases':[],
                'artifacts':{'kernel.cubin':'0'*64}}))
            with patch('validate_poisson.Session',side_effect=AssertionError('CUDA must not be reached')):
                with self.assertRaisesRegex(ValueError,'hash mismatch'):replay(path)

if __name__=='__main__':unittest.main()
