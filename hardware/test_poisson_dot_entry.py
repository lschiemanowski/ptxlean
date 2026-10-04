"""Adversarial checks of complete dot-entry instruction and layout bindings."""
import copy
import re
import unittest

from check_poisson_dot_entry import parameters, verify_entry
import test_poisson_dot_input as input_tests
import test_poisson_reduction_tree as tree_tests


class DotEntryBinding(unittest.TestCase):
    def setUp(self):
        inputs = input_tests.DotInputBinding()
        inputs.setUp()
        tree = tree_tests.ReductionTreeBinding()
        tree.setUp()
        self.ptx, self.layout = inputs.ptx, inputs.layout
        translated = [re.sub(r'#(\d+)', lambda match: '#'+str(int(match[1])+20), line)
                      for line in tree.expected]
        self.expected = {}
        for entry, (_, _, _, out) in parameters(self.layout.manifest()).items():
            self.expected[entry] = inputs.expected[entry]+translated+[
                'setp.ne.u32 %p0, %lane, 0;', '@%p0 ret;', 'ld.shared.f64 %acc, [%shared];',
                'mul.wide.u32 %off, 0, 8;', 'add.u64 %addr, %base, %off;',
                f'add.u64 %addr, %addr, {out};', 'st.global.f64 [%addr], %acc;', 'ret;']

    def test_valid_complete_programs(self):
        for version in ('9.2', '9.4'):
            checked = verify_entry(self.ptx.replace('.version 9.2', '.version '+version), self.expected)
            self.assertEqual(len(checked), 6)
            self.assertTrue(all(item['instructions'] == 104 for item in checked))

    def test_reject_changed_epilogue_and_control(self):
        start = self.ptx.index('.visible .entry dot_rhs(')
        end = self.ptx.index('\n}', start)+2
        body = self.ptx[start:end]
        for old, new in [
            ('@%p0 ret;', '@!%p0 ret;'),
            ('ld.shared.f64 %acc, [%shared];', 'ld.shared.f64 %acc, [%addr];'),
            ('mul.wide.u32 %off, 0, 8;', 'mul.wide.u32 %off, %lane, 8;'),
            ('st.global.f64 [%addr], %acc;', 'st.global.f64 [%addr], %a;'),
            ('ret;\n}', 'bra loop;\n}'),
            ('next_1:\nbar.sync 0;', 'next_1:'),
            ('@%p0 bra finish;', '@%p0 bra next_128;'),
            ('loop:', 'loop:\nloop:'),
        ]:
            with self.subTest(new=new):
                self.assertIn(old, body)
                altered = self.ptx[:start]+body.replace(old, new, 1)+self.ptx[end:]
                with self.assertRaises(ValueError):
                    verify_entry(altered, self.expected)

    def test_reject_layout_overlap_and_bad_output(self):
        for field, value in [('offset', self.layout.fields['rhs']['offset']),
                             ('offset', 1), ('count', 2), ('kind', 'I')]:
            manifest = copy.deepcopy(self.layout.manifest())
            manifest['fields']['rhs_square'][field] = value
            with self.assertRaises(ValueError):
                parameters(manifest)

    def test_reject_missing_extra_or_partial_entry(self):
        for altered in [self.ptx.replace('.entry dot_rhs(', '.entry absent(', 1),
                        self.ptx+'\n// unreviewed syntax']:
            with self.assertRaises(ValueError):
                verify_entry(altered, self.expected)
        for expected in [dict(self.expected, extra=self.expected['dot_rhs']),
                         dict(self.expected, dot_rhs=self.expected['dot_rhs'][:-1])]:
            with self.assertRaises(ValueError):
                verify_entry(self.ptx, expected)


if __name__ == '__main__':
    unittest.main()
