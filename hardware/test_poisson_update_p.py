"""Mutations of the actual PCG direction-update body and its launch layout."""
import copy
import unittest

from check_poisson_update_p import parameters, verify_entry
import test_poisson_dot_input as inputs


class DirectionUpdateBinding(unittest.TestCase):
    def setUp(self):
        fixture = inputs.DotInputBinding()
        fixture.setUp()
        self.ptx, self.layout = fixture.ptx, fixture.layout.manifest()
        count, beta, p, z = parameters(self.layout)
        self.expected = ['ld.param.u64 %base, [arena];', 'mov.u32 %lane, %tid.x;',
                         'mov.u32 %cell, %ctaid.x;', 'mad.lo.u32 %global, %cell, 256, %lane;',
                         f'setp.ge.u32 %p0, %global, {count};', '@%p0 ret;']
        for register, index, offset in [('%a', '0', beta), ('%b', '%global', p), ('%c', '%global', z)]:
            self.expected += [f'mul.wide.u32 %off, {index}, 8;', 'add.u64 %addr, %base, %off;',
                              f'add.u64 %addr, %addr, {offset};', f'ld.global.f64 {register}, [%addr];']
        self.expected += ['mul.rn.f64 %prod, %a, %b;', 'add.rn.f64 %c, %c, %prod;',
                          'mul.wide.u32 %off, %global, 8;', 'add.u64 %addr, %base, %off;',
                          f'add.u64 %addr, %addr, {p};', 'st.global.f64 [%addr], %c;', 'ret;']

    def test_valid(self):
        for version in ('9.2', '9.4'):
            result = verify_entry(self.ptx.replace('.version 9.2', '.version '+version), self.expected, self.layout)
            self.assertEqual(result['instructions'], 25)

    def test_reject_arithmetic_and_control_mutations(self):
        start = self.ptx.index('.visible .entry update_p(')
        end = self.ptx.index('\n}', start)+2
        body = self.ptx[start:end]
        for old, new in [('@%p0 ret;', '@!%p0 ret;'),
                         ('mul.rn.f64 %prod, %a, %b;', 'mul.rz.f64 %prod, %a, %b;'),
                         ('add.rn.f64 %c, %c, %prod;', 'add.rn.f64 %c, %prod, %c;'),
                         ('st.global.f64 [%addr], %c;', 'st.global.f64 [%addr], %a;'),
                         ('mul.wide.u32 %off, 0, 8;', 'mul.wide.u32 %off, %global, 8;'),
                         ('ret;\n}', '}')]:
            with self.subTest(new=new), self.assertRaises(ValueError):
                altered = self.ptx[:start]+body.replace(old, new, 1)+self.ptx[end:]
                verify_entry(altered, self.expected, self.layout)

    def test_reject_bad_fields_and_overlap(self):
        for name, key, value in [('beta', 'count', 2), ('p', 'offset', 1), ('z', 'kind', 'I'),
                                 ('p', 'offset', self.layout['bytes']),
                                 ('z', 'offset', self.layout['fields']['p']['offset'])]:
            layout = copy.deepcopy(self.layout)
            layout['fields'][name][key] = value
            with self.subTest(name=name, key=key), self.assertRaises(ValueError):
                parameters(layout)

    def test_reject_launch(self):
        for key, value in [('threads', 128), ('groups', 0), ('shared_bytes', 8)]:
            layout = copy.deepcopy(self.layout)
            layout['launches']['update_p'][key] = value
            with self.assertRaises(ValueError):
                parameters(layout)

    def test_reject_missing_duplicate_and_partial(self):
        for ptx, expected in [(self.ptx.replace('.entry update_p(', '.entry absent('), self.expected),
                              (self.ptx+self.ptx, self.expected), (self.ptx, self.expected[:-1]),
                              (self.ptx+'\n// extra', self.expected)]:
            with self.assertRaises(ValueError):
                verify_entry(ptx, expected, self.layout)


if __name__ == '__main__':
    unittest.main()
