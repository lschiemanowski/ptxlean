"""Binding rejections only; the receipt uses Lean's actual renderer separately."""
import copy
import json
from pathlib import Path
import unittest
from check_poisson_contractions import parameters, verify_blocks
from poisson_kernels import Layout, module, PTX


class ContractionBinding(unittest.TestCase):
    def setUp(self):
        ref = json.loads((Path(__file__).resolve().parents[1]/'examples/poisson/reference.json').read_text())['outputs'][4]
        self.obj = Layout(ref, {})
        self.ptx = module(self.obj, '9.2')
        self.layout = self.obj.manifest()
        g = PTX(self.obj)
        specs = [('bu', ('B','%i','k'), (0,'k','%j'), '%acc'),
                 ('du', ('D','%i','k'), (0,'k','%j'), '%acc'),
                 ('dx', (1,'%i','k'), ('D','%j','k'), '%acc'),
                 ('dy', (2,'%i','k'), ('B','%j','k'), '%acc'),
                 ('bl', ('B','k','%i'), (3,'k','%j'), '%acc'),
                 ('dl', ('D','k','%i'), (4,'k','%j'), '%acc'),
                 ('x', (5,'%i','k'), ('D','k','%j'), '%acc'),
                 ('y', (6,'%i','k'), ('B','k','%j'), '%acc2')]
        self.expected = [(name, g.dot(a,b,acc).splitlines()) for name,a,b,acc in specs]

    def test_structure(self):
        self.assertEqual(len(verify_blocks(self.ptx, self.expected, self.layout)), 24)

    def test_instruction_mutations(self):
        for old,new in [('mul.rn.f64 %prod, %a, %b;', 'mul.rz.f64 %prod, %a, %b;'),
                        ('add.rn.f64 %acc, %acc, %prod;', 'add.rn.f64 %acc, %prod, %prod;'),
                        ('ld.shared.f64 %b, [%addr+0];', 'ld.shared.f64 %b, [%addr+8];'),
                        ('add.u32 %idx, %idx, %j;', 'add.u32 %idx, %idx, %i;'),
                        ('mov.f64 %acc, 0d0000000000000000;', 'mov.f64 %acc, 0d3ff0000000000000;')]:
            with self.subTest(new=new):
                self.assertIn(old, self.ptx)
                with self.assertRaises(ValueError):
                    verify_blocks(self.ptx.replace(old,new,1), self.expected, self.layout)

    def test_layout_rejection(self):
        for key,value in [('offset',1), ('count',1), ('kind','I'), ('offset',self.layout['bytes'])]:
            layout=copy.deepcopy(self.layout);layout['fields']['B'][key]=value
            with self.assertRaises(ValueError): parameters(layout)

    def test_missing_and_extra_blocks(self):
        for expected in (self.expected[:-1], self.expected+[self.expected[0]], self.expected[::-1]):
            with self.assertRaises(ValueError): verify_blocks(self.ptx, expected, self.layout)


if __name__ == '__main__': unittest.main()
