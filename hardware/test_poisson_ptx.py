"""Rejections for the restricted instruction binding, without CUDA or Lean.
The full receipt compares generated PTX with the actual compiled Lean renderer.
"""
import copy
import json
import hashlib
import tempfile
from pathlib import Path
import unittest

from check_poisson_ptx import parameters, verify_entry, read_artifact
from poisson_kernels import Layout, module


class InstructionBinding(unittest.TestCase):
    def setUp(self):
        reference = Path(__file__).resolve().parents[1]/'examples/poisson/reference.json'
        ref = json.loads(reference.read_text())['outputs'][4]
        obj = Layout(ref, {})
        self.ptx = module(obj, '9.2')
        self.layout = dict(n=obj.n, degree=obj.p, bytes=len(obj.data), fields=obj.fields, launches=obj.launches)
        p = parameters(self.layout)
        self.expected = ['ld.param.u64 %base, [arena];', 'mov.u32 %lane, %tid.x;',
                         'mov.u32 %cell, %ctaid.x;', 'mad.lo.u32 %global, %cell, 256, %lane;',
                         f'setp.ge.u32 %p0, %global, {p["count"]};', '@%p0 ret;']
        for field, register in [('rhs', '%a'), ('ap', '%b')]:
            self.expected.extend(['mul.wide.u32 %off, %global, 8;', 'add.u64 %addr, %base, %off;',
                                  f'add.u64 %addr, %addr, {p[field]};', f'ld.global.f64 {register}, [%addr];'])
        self.expected.extend(['sub.rn.f64 %c, %a, %b;', 'mul.wide.u32 %off, %global, 8;',
                              'add.u64 %addr, %base, %off;', f'add.u64 %addr, %addr, {p["output"]};',
                              'st.global.f64 [%addr], %c;', 'ret;'])

    def test_current_frontend(self):
        result = verify_entry(self.ptx, self.expected, self.layout)
        self.assertEqual(result['instruction_count'], 20)

    def test_instruction_and_control_mutations(self):
        marker = '.visible .entry true_residual'
        start = self.ptx.index(marker)
        for old, new in [('sub.rn.f64 %c, %a, %b;', 'sub.rn.f64 %c, %b, %a;'),
                         ('sub.rn.f64', 'sub.rz.f64'),
                         ('@%p0 ret;', '@!%p0 ret;'),
                         ('mul.wide.u32 %off, %global, 8;', 'mul.wide.u32 %off, %global, 4;'),
                         ('.reqntid 256, 1, 1', '.reqntid 128, 1, 1')]:
            with self.subTest(new=new):
                changed = self.ptx[:start]+self.ptx[start:].replace(old, new, 1)
                with self.assertRaises(ValueError): verify_entry(changed, self.expected, self.layout)

    def test_comments_and_duplicate_entry_rejected(self):
        start = self.ptx.index('.visible .entry true_residual')
        end = self.ptx.index('}', start)+1
        for changed in (self.ptx+self.ptx[start:end], self.ptx[:start]+'/*'+self.ptx[start:end]+'*/'+self.ptx[end:]):
            with self.assertRaises(ValueError): verify_entry(changed, self.expected, self.layout)

    def test_every_consumed_artifact_needs_its_hash(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root/'layout.json').write_text('{}')
            report = {'artifacts': {}}
            with self.assertRaisesRegex(ValueError, 'missing from manifest'):
                read_artifact(root, report, 'layout.json')
            report['artifacts']['layout.json'] = hashlib.sha256(b'{}').hexdigest()
            self.assertEqual(read_artifact(root, report, 'layout.json'), b'{}')
            (root/'layout.json').write_text('{"changed":true}')
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                read_artifact(root, report, 'layout.json')
            with self.assertRaises(ValueError): read_artifact(root, report, '../escape')

    def test_layout_and_launch_rejected(self):
        for field, value in [('offset', -8), ('offset', 1), ('offset', 2**64), ('kind', 'I'), ('count', 1)]:
            layout = copy.deepcopy(self.layout)
            layout['fields']['rhs'][field] = value
            with self.assertRaises(ValueError): parameters(layout)
        layout = copy.deepcopy(self.layout)
        layout['launches']['true_residual']['threads'] = 128
        with self.assertRaises(ValueError): parameters(layout)


if __name__ == '__main__': unittest.main()
