"""Binding rejections only; the receipt uses Lean's actual renderer separately."""
import copy
import json
from pathlib import Path
import unittest
from check_poisson_contractions import parameters, verify_blocks, verify_stores, verify_control, verify_middle, verify_final
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

    def test_stores(self):
        g = PTX(self.obj)
        stores = [(plane, g.shared_store(plane, '%value' if plane == 0 else '%acc').splitlines())
                  for plane in range(7)]
        self.assertEqual(len(verify_stores(self.ptx, stores, self.layout, self.expected)), 21)
        for old, new in [('st.shared.f64 [%addr+0], %value;', 'st.shared.f64 [%addr+8], %value;'),
                         ('mul.wide.u32 %off, %lane, 8;', 'mul.wide.u32 %off, %lane, 4;'),
                         ('st.shared.f64 [%addr+0], %value;', 'st.shared.f64 [%addr+0], %acc;')]:
            with self.subTest(new=new):
                self.assertIn(old, self.ptx)
                with self.assertRaises(ValueError):
                    verify_stores(self.ptx.replace(old,new), stores, self.layout, self.expected)
        block = '\n'.join(self.expected[0][1])
        mutated = self.ptx.replace(block, block+'\nadd.rn.f64 %acc, %acc, %acc;', 1)
        with self.assertRaises(ValueError):
            verify_stores(mutated, stores, self.layout, self.expected)
        for plans in (stores[:-1], stores[::-1], stores+[stores[0]]):
            with self.assertRaises(ValueError): verify_stores(self.ptx, plans, self.layout, self.expected)
        with self.assertRaises(ValueError):
            verify_stores(self.ptx.replace('st.shared.f64 [%addr+0], %value;', ''), stores, self.layout, self.expected)

    def test_barrier_control(self):
        self.assertEqual(len(verify_control(self.ptx, self.layout)), 3)
        for old, new in [('.reqntid 32, 1, 1', '.reqntid 16, 1, 1'),
                         ('bar.sync 0;', 'bar.sync 1;'),
                         ('bar.sync 0;', '@%live bar.sync 0;'),
                         ('bar.sync 0;', ''),
                         ('@!%live bra stage_0_done;', '@!%live bra stage_1_done;'),
                         ('stage_0_done:\nbar.sync 0;', 'bar.sync 0;\nstage_0_done:'),
                         ('stage_1_done:', 'ret;\nstage_1_done:')]:
            with self.subTest(new=new):
                self.assertIn(old, self.ptx)
                with self.assertRaises(ValueError):
                    verify_control(self.ptx.replace(old,new,1), self.layout)

    def test_complete_middle_bodies(self):
        # This is a mutation test. The separate receipt obtains expected text
        # from Lean's renderer, not from this Python extraction.
        lines = self.ptx.splitlines()
        expected = [lines[lines.index(f'@!%live bra stage_{p}_done;')+1:
                          lines.index(f'stage_{p}_done:')] for p in (1, 2, 3)]
        self.assertEqual(len(verify_middle(self.ptx, expected, self.layout)), 3)
        for old, new in [('mul.rn.f64 %acc, %acc, %c;', 'mul.rn.f64 %acc, %acc, %b;'),
                         ('ld.global.f64 %c, [%addr];', 'ld.global.f64 %c, [%addr+8];'),
                         ('stage_2_done:', 'mov.b64 %shared, 0;\nstage_2_done:')]:
            with self.subTest(new=new):
                self.assertIn(old, self.ptx)
                with self.assertRaises(ValueError):
                    verify_middle(self.ptx.replace(old, new, 1), expected, self.layout)
        changed_layout = copy.deepcopy(self.layout)
        changed_layout['fields']['W']['offset'] += 8
        with self.assertRaises(ValueError):
            verify_middle(self.ptx, expected, changed_layout)
        for bodies in (expected[:-1], expected[::-1], expected+[expected[0]]):
            with self.assertRaises(ValueError):
                verify_middle(self.ptx, bodies, self.layout)

    def test_final_body(self):
        lines = self.ptx.splitlines()
        expected = lines[lines.index('@!%live bra stage_4_done;')+1:
                         lines.index('stage_4_done:')]+['ret;']
        self.assertEqual(len(verify_final(self.ptx, expected, self.layout)), 3)
        for old, new in [('add.rn.f64 %value, %acc, %acc2;', 'sub.rn.f64 %value, %acc, %acc2;'),
                         ('st.global.f64 [%addr], %value;', 'st.global.f64 [%addr], %acc;'),
                         ('stage_4_done:', 'add.u32 %idx, %idx, 1;\nstage_4_done:')]:
            with self.subTest(new=new):
                self.assertIn(old, self.ptx)
                with self.assertRaises(ValueError):
                    verify_final(self.ptx.replace(old, new), expected, self.layout)
        for code in (expected[:-1], expected+['ret;'], list(reversed(expected))):
            with self.assertRaises(ValueError): verify_final(self.ptx, code, self.layout)
        for key, value in [('offset', 1), ('count', 1), ('count', 2**32), ('kind', 'I')]:
            layout = copy.deepcopy(self.layout)
            layout['fields']['element'][key] = value
            with self.assertRaises(ValueError): parameters(layout)

    def test_output_coefficient_separation(self):
        width = self.layout['degree']+1
        end = max(self.layout['fields'][name]['offset']+width*width*8 for name in ('B', 'D', 'W'))
        for offset in (self.layout['fields']['B']['offset'],
                       self.layout['fields']['D']['offset'], end-8):
            with self.subTest(offset=offset):
                layout = copy.deepcopy(self.layout)
                layout['fields']['element']['offset'] = offset
                with self.assertRaisesRegex(ValueError, 'overlaps coefficient'):
                    parameters(layout)
        adjacent = copy.deepcopy(self.layout)
        adjacent['fields']['element']['offset'] = end
        self.assertEqual(parameters(adjacent)['output'], end)

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
