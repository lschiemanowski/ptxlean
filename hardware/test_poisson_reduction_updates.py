"""Frontend mutation tests; the saved-run checker uses Lean's renderer."""
import json
from pathlib import Path
import unittest
from check_poisson_reduction_updates import STRIDES, verify_updates
from poisson_kernels import Layout, module


class ReductionUpdateBinding(unittest.TestCase):
    def setUp(self):
        ref = json.loads((Path(__file__).resolve().parents[1]/'examples/poisson/reference.json').read_text())['outputs'][4]
        self.ptx = module(Layout(ref, {}), '9.2')
        self.expected = [[
            'mul.wide.u32 %off, %lane, 8;', 'add.u64 %addr, %shared, %off;',
            'ld.shared.f64 %a, [%addr];', f'ld.shared.f64 %b, [%addr+{stride*8}];',
            'add.rn.f64 %acc, %a, %b;', 'st.shared.f64 [%addr], %acc;'] for stride in STRIDES]

    def test_all_updates(self):
        self.assertEqual(len(verify_updates(self.ptx, self.expected)), 48)
        self.assertEqual(len(verify_updates(self.ptx.replace('.version 9.2', '.version 9.4'), self.expected)), 48)

    def test_reject_altered_stage(self):
        start = self.ptx.index('.visible .entry dot_rhs(')
        end = self.ptx.index('\n}', start)+2
        body = self.ptx[start:end]
        for old, new in [
            ('ld.shared.f64 %b, [%addr+1024];', 'ld.shared.f64 %b, [%addr+1032];'),
            ('add.rn.f64 %acc, %a, %b;', 'add.rz.f64 %acc, %a, %b;'),
            ('st.shared.f64 [%addr], %acc;\nnext_128:', 'st.shared.f64 [%addr], %a;\nnext_128:'),
            ('@%p0 bra next_128;', '@!%p0 bra next_128;'),
            ('next_128:\nbar.sync 0;', 'next_128:'),
            ('next_128:\nbar.sync 0;', 'next_128:\nbar.sync 0;\nmov.u32 %lane, 0;'),
            ('setp.ge.u32 %p0, %lane, 128;', 'setp.ge.u32 %p0, %lane, 129;'),
            ('.reqntid 256, 1, 1', '.reqntid 128, 1, 1'),
            ('.shared .align 8 .b8 scratch[2048];', '.shared .align 8 .b8 scratch[1024];')]:
            with self.subTest(new=new):
                self.assertIn(old, body)
                altered = self.ptx[:start]+body.replace(old, new, 1)+self.ptx[end:]
                with self.assertRaises(ValueError): verify_updates(altered, self.expected)

    def test_reject_missing_duplicate_or_comment(self):
        for changed in [self.ptx.replace('next_128:', 'next_128:\nnext_128:', 1),
                        self.ptx.replace('.entry dot_rhs(', '.entry missing(', 1),
                        self.ptx+'\n// comment']:
            with self.assertRaises(ValueError): verify_updates(changed, self.expected)


if __name__ == '__main__':
    unittest.main()
