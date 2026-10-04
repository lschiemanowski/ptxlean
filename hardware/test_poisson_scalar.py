"""Mutation checks for the complete norm and restart-flag scalar entries."""
import copy
import unittest

from check_poisson_scalar import parameters, verify_entry
import test_poisson_dot_input as inputs


class ScalarBinding(unittest.TestCase):
    def setUp(self):
        fixture = inputs.DotInputBinding()
        fixture.setUp()
        self.ptx, self.layout = fixture.ptx, fixture.layout.manifest()
        source, output, active = parameters(self.layout)
        header = ['ld.param.u64 %base, [arena];', 'mov.u32 %lane, %tid.x;', 'mov.u32 %cell, %ctaid.x;']
        def address(offset, width):
            return [f'mul.wide.u32 %off, 0, {width};', 'add.u64 %addr, %base, %off;', f'add.u64 %addr, %addr, {offset};']
        self.expected = {
            'residual_norm': header+address(source, 8)+['ld.global.f64 %a, [%addr];', 'sqrt.rn.f64 %a, %a;']+
                             address(output, 8)+['st.global.f64 [%addr], %a;', 'ret;'],
            'restart_flag': header+address(active, 4)+['st.global.u32 [%addr], 1;', 'ret;'],
        }

    def test_valid(self):
        for version in ('9.2', '9.4'):
            for entry, code in self.expected.items():
                answer = verify_entry(self.ptx.replace('.version 9.2', '.version '+version), code, self.layout, entry)
                self.assertEqual(answer['instructions'], len(code))

    def test_reject_arithmetic_width_and_operand_changes(self):
        for entry, changes in {
            'residual_norm': [('sqrt.rn', 'sqrt.rz'), ('sqrt.rn.f64 %a, %a;', 'sqrt.rn.f64 %a, %b;'),
                              ('st.global.f64 [%addr], %a;', 'st.global.f64 [%addr], %b;')],
            'restart_flag': [('st.global.u32 [%addr], 1;', 'st.global.u32 [%addr], 0;'),
                             ('mul.wide.u32 %off, 0, 4;', 'mul.wide.u32 %off, 0, 8;'),
                             ('st.global.u32', 'st.global.u64')],
        }.items():
            start = self.ptx.index('.visible .entry '+entry+'(')
            end = self.ptx.index('\n}', start)+2
            body = self.ptx[start:end]
            for old, new in changes:
                with self.subTest(entry=entry, new=new), self.assertRaises(ValueError):
                    verify_entry(self.ptx[:start]+body.replace(old, new, 1)+self.ptx[end:], self.expected[entry], self.layout, entry)

    def test_reject_bad_layouts(self):
        for field, key, value in [('active', 'kind', 'd'), ('active', 'count', 2), ('residual', 'offset', 1),
                                   ('active', 'offset', self.layout['bytes']),
                                   ('residual', 'offset', self.layout['fields']['true_square']['offset'])]:
            layout = copy.deepcopy(self.layout)
            layout['fields'][field][key] = value
            with self.assertRaises(ValueError):
                parameters(layout)

    def test_reject_launch(self):
        for entry in self.expected:
            for key, value in [('threads', 2), ('groups', 2), ('shared_bytes', 4)]:
                layout = copy.deepcopy(self.layout)
                layout['launches'][entry][key] = value
                with self.assertRaises(ValueError):
                    parameters(layout)

    def test_reject_partial_missing_duplicate(self):
        for entry, code in self.expected.items():
            for ptx, expected in [(self.ptx, code[:-1]), (self.ptx+self.ptx, code),
                                  (self.ptx.replace('.entry '+entry+'(', '.entry absent('), code)]:
                with self.assertRaises(ValueError):
                    verify_entry(ptx, expected, self.layout, entry)


if __name__ == '__main__':
    unittest.main()
