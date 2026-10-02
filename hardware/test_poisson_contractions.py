"""Binding rejections only; the receipt uses Lean's actual renderer separately."""
import copy
import json
from pathlib import Path
import unittest
from check_poisson_contractions import parameters, verify_blocks, verify_stores, verify_control, verify_middle, verify_final, verify_prologue, verify_gather, verify_entry, verify_whole, verify_assembly_loop, verify_assembly_entries
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

    def test_complete_assembly(self):
        import re
        expected = []
        for entry in ('assemble_probe','assemble_ap'):
            body = re.search(r'\.visible \.entry '+entry+r'\(.*?\n}', self.ptx, re.S)[0].splitlines()
            code = body[body.index('ld.param.u64 %base, [arena];'):-1]
            expected.append(dict(code=code,shape=[len(code)-2,[[17,29],[28,16]]]))
        self.assertEqual(len(verify_assembly_entries(self.ptx, expected, self.layout)),2)
        begin = self.ptx.index('.visible .entry assemble_probe')
        end = self.ptx.index('\n}',begin)+2
        chunk = self.ptx[begin:end]
        for old,new in [
                ('add.u32 %idx, %global, 1;', 'add.u32 %idx, %global, 2;'),
                ('mov.f64 %acc, 0d0000000000000000;', 'mov.f64 %acc, 0d3ff0000000000000;'),
                ('bra loop;', 'bra done;'),
                ('st.global.f64 [%addr], %acc;', 'st.global.f64 [%addr], %a;'),
                ('.reqntid 256, 1, 1', '.reqntid 128, 1, 1'),
                ('.reg .u32 %lane', '.reg .s32 %lane'),
                ('@%p0 ret;', '@!%p0 ret;')]:
            with self.subTest(new=new):
                self.assertIn(old,chunk)
                altered=self.ptx[:begin]+chunk.replace(old,new,1)+self.ptx[end:]
                with self.assertRaises(ValueError): verify_assembly_entries(altered,expected,self.layout)
        altered=self.ptx.replace('@%p0 mov.f64 %acc, 0d0000000000000000;', '@!%p0 mov.f64 %acc, 0d0000000000000000;',1)
        with self.assertRaises(ValueError): verify_assembly_entries(altered,expected,self.layout)
        bad=copy.deepcopy(expected);bad[0]['shape'][1][0][1]=30
        with self.assertRaises(ValueError): verify_assembly_entries(self.ptx,bad,self.layout)
        bad=copy.deepcopy(self.layout);bad['launches']['assemble_probe']['threads']=128
        with self.assertRaises(ValueError): verify_assembly_entries(self.ptx,expected,bad)

    def test_complete_prologue(self):
        lines = self.ptx.splitlines()
        start = lines.index('mov.u64 %shared, scratch;')
        expected = lines[start:start+7]
        self.assertEqual(len(verify_prologue(self.ptx, expected, self.layout)), 3)
        width = self.layout['degree']+1
        for old, new in [
                ('mov.u32 %lane, %tid.x;', 'mov.u32 %lane, %ctaid.x;'),
                ('mov.u64 %shared, scratch;', 'mov.u64 %shared, 0;'),
                ('ld.param.u64 %base, [arena];', ''),
                (f'div.u32 %i, %lane, {width};', f'rem.u32 %i, %lane, {width};'),
                (f'rem.u32 %j, %lane, {width};', 'rem.u32 %j, %lane, 0;'),
                (f'setp.lt.u32 %live, %lane, {width*width};',
                 f'setp.le.u32 %live, %lane, {width*width};'),
                ('@!%live bra stage_0_done;', 'mov.u32 %i, 0;\n@!%live bra stage_0_done;'),
                ('.reg .u32 %lane', '.reg .s32 %lane'),
                ('.shared .align 8', '.shared .align 4')]:
            with self.subTest(new=new):
                self.assertIn(old, self.ptx)
                with self.assertRaises(ValueError):
                    verify_prologue(self.ptx.replace(old, new, 1), expected, self.layout)
        for expected_bad in (expected[:-1], expected[::-1], expected+[expected[0]]):
            with self.assertRaises(ValueError):
                verify_prologue(self.ptx, expected_bad, self.layout)

    def test_complete_entry(self):
        import re
        expected = []
        for entry in ('element_probe', 'element_p', 'element_x'):
            body = re.search(r'\.visible \.entry '+entry+r'\(.*?\n}', self.ptx, re.S)[0].splitlines()
            first = next(i for i, line in enumerate(body) if line.startswith('.shared '))+1
            expected.append(body[first:body.index('@!%live bra stage_1_done;')])
        self.assertEqual(len(verify_entry(self.ptx, expected, self.layout)), 3)
        for old, new in [('@!%live bra stage_0_done;', '@%live bra stage_0_done;'),
                         ('stage_0_done:\nbar.sync 0;', 'stage_0_done:\nbar.sync 1;'),
                         ('stage_0_done:\nbar.sync 0;', 'bar.sync 0;\nstage_0_done:'),
                         ('@!%live bra stage_1_done;', 'mov.u32 %i, 0;\n@!%live bra stage_1_done;')]:
            with self.subTest(new=new):
                self.assertIn(old, self.ptx)
                with self.assertRaises(ValueError):
                    verify_entry(self.ptx.replace(old,new,1), expected, self.layout)

    def test_complete_gather(self):
        import re
        expected = []
        for entry in ('element_probe', 'element_p', 'element_x'):
            body = re.search(r'\.visible \.entry '+entry+r'\(.*?\n}', self.ptx, re.S)[0].splitlines()
            expected.append(body[body.index('@!%live bra stage_0_done;')+1:body.index('stage_0_done:')])
        self.assertEqual(len(verify_gather(self.ptx, expected, self.layout)), 3)
        for old, new in [('ld.global.u32 %node, [%addr];', 'ld.global.u64 %node, [%addr];'),
                         ('mul.wide.u32 %off, %idx, 4;', 'mul.wide.u32 %off, %idx, 8;'),
                         ('mul.wide.u32 %off, %node, 8;', 'mul.wide.u32 %off, %lane, 8;'),
                         ('st.shared.f64 [%addr+0], %value;', 'st.shared.f64 [%addr+8], %value;'),
                         ('stage_0_done:', 'mov.u32 %i, 0;\nstage_0_done:')]:
            with self.subTest(new=new):
                self.assertIn(old, self.ptx)
                with self.assertRaises(ValueError):
                    verify_gather(self.ptx.replace(old,new,1), expected, self.layout)
        with self.assertRaises(ValueError): verify_gather(self.ptx, expected[::-1], self.layout)
        bad = copy.deepcopy(self.layout)
        bad['fields']['cells']['kind'] = 'd'
        with self.assertRaises(ValueError): parameters(bad)

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

    def test_whole_native_counters(self):
        # Mutation evidence only; production expected shapes come from Lean.
        import re
        lines = re.search(r'\.visible \.entry element_probe\(.*?\n}', self.ptx, re.S)[0].splitlines()
        begin = next(i for i,line in enumerate(lines) if line.startswith('.shared '))+1
        body = lines[begin:-1]
        instructions = [line for line in body if not line.endswith(':')]
        labels = {}
        pc = 0
        for line in body:
            if line.endswith(':'): labels[line[:-1]] = pc
            else: pc += 1
        branches = [[pc, labels[re.fullmatch(r'@!%live bra (\w+);', line)[1]]]
                    for pc,line in enumerate(instructions) if line.startswith('@')]
        entries = []
        for entry in ('element_probe', 'element_p', 'element_x'):
            section = re.search(r'\.visible \.entry '+entry+r'\(.*?\n}', self.ptx, re.S)[0].splitlines()
            first = next(i for i,line in enumerate(section) if line.startswith('.shared '))+1
            entries.append(section[first:section.index('@!%live bra stage_1_done;')])
        code = dict(prologue=body[:7], entries=entries,
                    middle=[body[body.index(f'@!%live bra stage_{p}_done;')+1:body.index(f'stage_{p}_done:')] for p in (1,2,3)],
                    final=body[body.index('@!%live bra stage_4_done;')+1:body.index('stage_4_done:')]+['ret;'],
                    shape=[len(instructions), [[pc for pc,line in enumerate(instructions) if line=='bar.sync 0;'], branches]])
        self.assertEqual(len(verify_whole(self.ptx, code, self.layout)), 3)
        for modify in ('count', 'barrier', 'branch'):
            changed = copy.deepcopy(code)
            if modify=='count': changed['shape'][0] += 1
            elif modify=='barrier': changed['shape'][1][0][1] -= 21
            else: changed['shape'][1][1][-1][1] -= 5
            with self.subTest(modify=modify), self.assertRaisesRegex(ValueError, 'absolute instruction counters'):
                verify_whole(self.ptx, changed, self.layout)
        for mutated in (self.ptx.replace('bar.sync 0;', 'mov.u32 %i, 0;\nbar.sync 0;', 1),
                        self.ptx.replace('stage_4_done:', 'ret;\nstage_4_done:', 1)):
            with self.assertRaises(ValueError): verify_whole(mutated, code, self.layout)

    def test_assembly_loop(self):
        import re
        lines = re.search(r'\.visible \.entry assemble_probe\(.*?\n}', self.ptx, re.S)[0].splitlines()
        expected = lines[lines.index('loop:'):lines.index('done:')+1]
        self.assertEqual(len(verify_assembly_loop(self.ptx, expected, self.layout)), 2)
        for old,new in [('setp.ge.u32 %p0, %cursor, %end;', 'setp.gt.u32 %p0, %cursor, %end;'),
                        ('add.rn.f64 %acc, %acc, %a;', 'add.rn.f64 %acc, %acc, %b;'),
                        ('add.u32 %cursor, %cursor, 1;', 'add.u32 %cursor, %cursor, 2;'),
                        ('bra loop;', 'ret;'), ('@%p0 bra done;', '@!%p0 bra done;')]:
            with self.subTest(new=new), self.assertRaises(ValueError):
                verify_assembly_loop(self.ptx.replace(old,new,1), expected, self.layout)

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
