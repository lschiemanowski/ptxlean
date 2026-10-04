"""Adversarial text/layout checks for the PCG restart."""
import copy
import unittest

from check_poisson_restart import parameters, verify_entry
import test_poisson_dot_input as inputs


class RestartBinding(unittest.TestCase):
    def setUp(self):
        fixture = inputs.DotInputBinding()
        fixture.setUp()
        self.ptx, self.layout = fixture.ptx, fixture.layout.manifest()
        count, source, r, diagonal, boundary, z, p = parameters(self.layout)
        self.expected = ['ld.param.u64 %base, [arena];', 'mov.u32 %lane, %tid.x;',
                         'mov.u32 %cell, %ctaid.x;', 'mad.lo.u32 %global, %cell, 256, %lane;',
                         f'setp.ge.u32 %p0, %global, {count};', '@%p0 ret;']

        def address(index, offset, width=8):
            self.expected.extend([f'mul.wide.u32 %off, {index}, {width};',
                                  'add.u64 %addr, %base, %off;', f'add.u64 %addr, %addr, {offset};'])

        def load(register, offset, index='%global', width=8):
            address(index, offset, width)
            self.expected.append(f'ld.global.{"f64" if width == 8 else "u32"} {register}, [%addr];')

        def store(offset, reg='%c'):
            address('%global', offset)
            self.expected.append(f'st.global.f64 [%addr], {reg};')

        load('%a', source)
        store(r, '%a')
        load('%b', diagonal)
        load('%flag', boundary, width=4)
        self.expected.extend(['setp.ne.u32 %p0, %flag, 0;', '@%p0 mov.f64 %b, 0d3ff0000000000000;',
                              'div.rn.f64 %c, %a, %b;'])
        store(z)
        store(p)
        self.expected.append('ret;')

    def test_valid(self):
        for version in ('9.2', '9.4'):
            result = verify_entry(self.ptx.replace('.version 9.2', '.version '+version), self.expected, self.layout)
            self.assertEqual(result['instructions'], 34)

    def test_reject_numerical_control_and_address_mutations(self):
        start = self.ptx.index('.visible .entry restart_vectors(')
        end = self.ptx.index('\n}', start)+2
        body = self.ptx[start:end]
        for old, new in [('@%p0 ret;', '@!%p0 ret;'),
                         ('div.rn.f64 %c, %a, %b;', 'div.rn.f64 %c, %b, %a;'),
                         ('0d3ff0000000000000', '0d0000000000000000'),
                         ('@%p0 mov.f64', '@!%p0 mov.f64'),
                         ('mul.wide.u32 %off, %global, 4;', 'mul.wide.u32 %off, %global, 8;'),
                         ('st.global.f64 [%addr], %c;', 'st.global.f64 [%addr], %a;'),
                         ('ret;\n}', '}')]:
            with self.subTest(new=new), self.assertRaises(ValueError):
                verify_entry(self.ptx[:start]+body.replace(old, new, 1)+self.ptx[end:], self.expected, self.layout)

    def test_reject_bad_fields_and_overlap(self):
        for name, key, value in [('true_r', 'count', 2), ('p', 'offset', 1), ('boundary', 'kind', 'd'),
                                 ('diagonal', 'offset', self.layout['bytes']),
                                 ('r', 'offset', self.layout['fields']['p']['offset']),
                                 ('boundary', 'offset', self.layout['fields']['z']['offset'])]:
            layout = copy.deepcopy(self.layout)
            layout['fields'][name][key] = value
            with self.subTest(name=name, key=key), self.assertRaises(ValueError):
                parameters(layout)

    def test_reject_launch(self):
        for key, value in [('threads', 128), ('groups', 0), ('shared_bytes', 8)]:
            layout = copy.deepcopy(self.layout)
            layout['launches']['restart_vectors'][key] = value
            with self.assertRaises(ValueError):
                parameters(layout)

    def test_reject_missing_duplicate_and_partial(self):
        for ptx, expected in [(self.ptx.replace('.entry restart_vectors(', '.entry absent('), self.expected),
                              (self.ptx+self.ptx, self.expected), (self.ptx, self.expected[:-1]),
                              (self.ptx+'\n// extra', self.expected)]:
            with self.assertRaises(ValueError):
                verify_entry(ptx, expected, self.layout)


if __name__ == '__main__':
    unittest.main()
