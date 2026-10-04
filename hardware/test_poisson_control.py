"""Reject changed scalar arithmetic, guards, layouts, and incomplete bindings."""
import copy
import unittest

from check_poisson_control import ENTRIES, parameters, verify_entry
import test_poisson_dot_input as inputs


class ControlBinding(unittest.TestCase):
    def setUp(self):
        fixture = inputs.DotInputBinding()
        fixture.setUp()
        self.ptx, self.layout = fixture.ptx, fixture.layout.manifest()
        parameters(self.layout)
        header = ['ld.param.u64 %base, [arena];', 'mov.u32 %lane, %tid.x;', 'mov.u32 %cell, %ctaid.x;']
        def transfer(name, reg, store=False):
            field = self.layout['fields'][name]
            width = 4 if field['kind'] == 'I' else 8
            kind = 'u32' if width == 4 else 'f64'
            instruction = f'st.global.{kind} [%addr], {reg};' if store else f'ld.global.{kind} {reg}, [%addr];'
            return [f'mul.wide.u32 %off, 0, {width};', 'add.u64 %addr, %base, %off;',
                    f"add.u64 %addr, %addr, {field['offset']};", instruction]
        def finite(reg, p):
            return [f'abs.f64 %value, {reg};', f'setp.le.f64 %p{p}, %value, 0d7fefffffffffffff;']
        def initial(name):
            return header+transfer(name, '%a')+transfer('rho', '%b')+transfer('active', '%flag')+transfer('broken', '%flag2')
        self.expected = {
            'start': header+transfer('rhs_square', '%a')+['sqrt.rn.f64 %a, %a;']+
                transfer('rhs_norm', '%a', True)+transfer('residual', '%a', True)+
                transfer('rtol', '%b')+transfer('atol', '%c')+['mul.rn.f64 %b, %b, %a;', 'max.f64 %b, %b, %c;']+
                transfer('tolerance', '%b', True)+transfer('active', '1', True)+transfer('broken', '0', True)+['ret;'],
            'coefficient_alpha': initial('denominator')+finite('%a', 0)+finite('%b', 1)+[
                'setp.gt.f64 %p2, %a, 0d0000000000000000;', 'setp.gt.f64 %p3, %b, 0d0000000000000000;',
                'and.pred %p0, %p0, %p1;', 'and.pred %p0, %p0, %p2;', 'and.pred %p0, %p0, %p3;',
                'setp.ne.u32 %p1, %flag, 0;', 'not.pred %p2, %p0;', 'and.pred %p2, %p2, %p1;',
                '@%p2 mov.u32 %flag2, 1;', 'and.pred %p0, %p0, %p1;', 'selp.u32 %flag, 1, 0, %p0;']+
                transfer('broken', '%flag2', True)+transfer('use_step', '%flag', True)+[
                'mov.f64 %c, 0d0000000000000000;', '@%p0 div.rn.f64 %c, %b, %a;']+
                transfer('alpha', '%c', True)+['ret;'],
            'coefficient_beta': initial('rho_next')+finite('%a', 0)+[
                'not.pred %p0, %p0;', 'setp.ne.u32 %p1, %flag, 0;', 'and.pred %p0, %p0, %p1;', '@%p0 mov.u32 %flag2, 1;']+
                transfer('broken', '%flag2', True)+transfer('use_step', '%flag')+[
                'setp.ne.u32 %p0, %flag, 0;', 'mov.f64 %c, 0d0000000000000000;', '@%p0 div.rn.f64 %c, %a, %b;']+
                transfer('beta', '%c', True)+transfer('rho', '%a', True)+transfer('rr', '%a')+transfer('tolerance', '%b')+[
                'mul.rn.f64 %b, %b, %b;', 'setp.gt.f64 %p1, %a, %b;', 'setp.eq.u32 %p2, %flag2, 0;',
                'and.pred %p0, %p0, %p1;', 'and.pred %p0, %p0, %p2;', 'selp.u32 %flag, 1, 0, %p0;']+
                transfer('active', '%flag', True)+['ret;'],
        }

    def test_valid(self):
        for version in ('9.2', '9.4'):
            for entry, code in self.expected.items():
                self.assertEqual(verify_entry(self.ptx.replace('.version 9.2', '.version '+version), code, self.layout, entry)['instructions'], ENTRIES[entry])

    def test_reject_changed_guards_rounding_operands(self):
        changes = {
            'start': [('sqrt.rn', 'sqrt.rz'), ('max.f64 %b, %b, %c;', 'max.f64 %b, %b, %a;'), ('st.global.u32 [%addr], 1;', 'st.global.u32 [%addr], 0;')],
            'coefficient_alpha': [('setp.gt.f64', 'setp.ge.f64'), ('@%p0 div.rn', '@!%p0 div.rn'), ('%c, %b, %a;', '%c, %a, %b;')],
            'coefficient_beta': [('setp.eq.u32', 'setp.ne.u32'), ('mul.rn.f64 %b, %b, %b;', 'mul.rn.f64 %b, %b, %a;'), ('@%p0 div.rn', 'div.rn')],
        }
        for entry, mutations in changes.items():
            start = self.ptx.index('.visible .entry '+entry+'(')
            end = self.ptx.index('\n}', start)+2
            body = self.ptx[start:end]
            for old, new in mutations:
                self.assertIn(old, body)
                with self.subTest(entry=entry, new=new), self.assertRaises(ValueError):
                    verify_entry(self.ptx[:start]+body.replace(old, new, 1)+self.ptx[end:], self.expected[entry], self.layout, entry)

    def test_reject_bad_layouts(self):
        for field, key, value in [('use_step', 'kind', 'd'), ('rho', 'count', 2), ('tolerance', 'offset', 1),
                                   ('broken', 'offset', self.layout['bytes']), ('alpha', 'offset', self.layout['fields']['rho']['offset'])]:
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
