"""Reject mutations that invalidate the fetched input-loop correspondence."""
import copy
import json
from pathlib import Path
import unittest
from check_poisson_dot_input import parameters, verify_input
from poisson_kernels import Layout, module


class DotInputBinding(unittest.TestCase):
    def setUp(self):
        ref = json.loads((Path(__file__).resolve().parents[1]/'examples/poisson/reference.json').read_text())['outputs'][4]
        self.layout = Layout(ref, {})
        self.ptx = module(self.layout, '9.2')
        self.expected = {}
        for name, (count, left, right) in parameters(self.layout.manifest()).items():
            code = ['mov.u64 %shared, scratch;', 'ld.param.u64 %base, [arena];',
                    'mov.u32 %lane, %tid.x;', 'mov.u32 %cell, %ctaid.x;',
                    'mov.u32 %global, %lane;', 'mov.f64 %acc, 0d0000000000000000;',
                    f'setp.ge.u32 %p0, %global, {count};', '@%p0 bra #20;']
            for reg, off in [('%a', left), ('%b', right)]:
                code += ['mul.wide.u32 %off, %global, 8;', 'add.u64 %addr, %base, %off;',
                         f'add.u64 %addr, %addr, {off};', f'ld.global.f64 {reg}, [%addr];']
            code += ['mul.rn.f64 %prod, %a, %b;', 'add.rn.f64 %acc, %acc, %prod;',
                     'add.u32 %global, %global, 256;', 'bra #6;']
            self.expected[name] = code

    def test_valid(self):
        for version in ('9.2', '9.4'):
            self.assertEqual(len(verify_input(self.ptx.replace('.version 9.2', '.version '+version), self.expected)), 6)

    def test_semantic_mutations(self):
        start = self.ptx.index('.visible .entry dot_rhs(')
        end = self.ptx.index('\n}', start)+2
        body = self.ptx[start:end]
        changes = [
            ('mov.u32 %global, %lane;', 'mov.u32 %global, 0;'),
            ('add.u32 %global, %global, 256;', 'add.u32 %global, %global, 255;'),
            ('add.rn.f64 %acc, %acc, %prod;', 'add.rz.f64 %acc, %acc, %prod;'),
            ('@%p0 bra finish;', '@!%p0 bra finish;'),
            ('mul.wide.u32 %off, %global, 8;', 'mul.wide.u32 %off, %global, 4;'),
            ('loop:\n', 'loop:\nloop:\n'),
            ('finish:\n', 'finish:\nbra loop;\n'),
            ('mov.f64 %acc, 0d0000000000000000;', 'mov.f64 %acc, 0d8000000000000000;'),
            (f'setp.ge.u32 %p0, %global, {self.layout.size};',
             f'setp.gt.u32 %p0, %global, {self.layout.size};')]
        for old, new in changes:
            with self.subTest(new=new):
                self.assertIn(old, body)
                altered = self.ptx[:start]+body.replace(old, new, 1)+self.ptx[end:]
                with self.assertRaises(ValueError): verify_input(altered, self.expected)

    def test_layout_rejections(self):
        manifest = self.layout.manifest()
        for key, value in [('offset', 1), ('count', self.layout.size+1), ('kind', 'I')]:
            altered = copy.deepcopy(manifest)
            altered['fields']['rhs'][key] = value
            with self.assertRaises(ValueError): parameters(altered)
        altered = copy.deepcopy(manifest)
        altered['launches']['dot_rhs']['groups'] = 2
        with self.assertRaises(ValueError): parameters(altered)


if __name__ == '__main__':
    unittest.main()
