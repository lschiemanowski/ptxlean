#!/usr/bin/env python3
"""Extraction boundary and committed-source regressions; no third-party packages."""

import hashlib
import json
import re
import sys
import unittest

sys.dont_write_bytecode = True
from coverage_inventory import ROOT, SOURCE, OUTPUT, SectionParser, classify, inventory, render


def manifest_for(raw):
    return {'isa_version': '9.4', 'artifact': 'index.html',
            'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw),
            'url': 'https://example.invalid/pinned'}


def document(children):
    return ('<section id="instructions"><h2>9.7. Instructions</h2>' + children + '</section>').encode()


def section(anchor, number, heading, body=''):
    return f'<section id="{anchor}"><h3>{number}. {heading}</h3>{body}</section>'


class ExtractionTests(unittest.TestCase):
    def test_unicode_byte_span_and_nested_hashes(self):
        raw = ('前言\n<section id="instructions"><h2>9.7. Instructions'
               '<a class="headerlink" href="#instructions"></a></h2>\n' +
               section('add', '9.7.1', 'Integer Instructions: <code>add</code>', 'é') +
               '</section>\n終').encode()
        rows = inventory(raw, manifest_for(raw))['sections']
        self.assertEqual(rows[0]['heading'], '9.7. Instructions')
        self.assertEqual(rows[0]['source_line'], 2)
        for row in rows:
            fragment = raw[row['start_byte']:row['end_byte_exclusive']]
            self.assertTrue(fragment.startswith(f'<section id="{row["id"]}"'.encode()))
            self.assertTrue(fragment.endswith(b'</section>'))
            self.assertEqual(hashlib.sha256(fragment).hexdigest(), row['sha256'])
        self.assertEqual(rows[1]['mnemonics_in_heading'], ['add'])
        self.assertEqual(rows[1]['form_coverage'], 'not_elaborated')
        self.assertEqual(rows[1]['implementation_coverage'], 'not_assessed')

    def test_groups_concepts_and_syntax_are_not_instructions(self):
        for heading, children, expected in [
            ('9.7.1. Instructions: Bulk copy', True, 'group'),
            ('9.7.1. Instructions: mbarrier', True, 'group'),
            ('9.7.1. Instruction descriptor', False, 'context'),
            ('9.7.1. Matrix Fragments for mma.m8n8k4', False, 'context'),
            ('9.7.1. Instructions: {}', False, 'language_construct'),
            ('9.7.2. Instructions: @', False, 'language_construct'),
        ]:
            with self.subTest(heading=heading):
                self.assertEqual(classify(heading, children)[0], expected)
        self.assertEqual(classify('9.7.1. Instructions: cp.async.wait_group / cp.async.wait_all', False)[2],
                         ['cp.async.wait_group', 'cp.async.wait_all'])
        self.assertEqual(classify('9.7.1. Instruction: mma.sp / mma.sp::ordered_metadata', False)[0], 'instruction')
        self.assertEqual(classify('9.7.1. Instructions: vote (deprecated)', False)[2], ['vote'])
        with self.assertRaisesRegex(ValueError, 'unrecognized instruction-heading'):
            classify('9.7.1. Instructions: Unexpected new convention', False)

    def test_repeated_mnemonic_is_not_deduplicated(self):
        raw = document(section('mov', '9.7.1', 'Instructions: mov') +
                       section('mov-vector', '9.7.2', 'Instructions: mov'))
        data = inventory(raw, manifest_for(raw))
        self.assertEqual(data['counts']['instruction'], 2)
        self.assertEqual([r['id'] for r in data['sections']], ['instructions', 'mov', 'mov-vector'])

    def test_missing_and_duplicate_structure_rejected(self):
        cases = [
            (document(section('x', '9.7.1', 'Instructions: add') * 2), 'duplicate section id'),
            (document('<section id="x">No heading</section>'), 'missing heading'),
            (document('<section><h3>9.7.1. Missing anchor</h3></section>'), 'section without id'),
            (document(section('a', '9.7.1', 'Context') + section('b', '9.7.1', 'Context')), 'duplicate section number'),
            (document(section('x', '9.7.1.1', 'Context')), 'number/nesting mismatch'),
            (document(section('x', '9.8.1', 'Context')), 'out-of-chapter'),
            (b'<section id="instructions"><h2>9.7. Instructions</h2>', 'unclosed section'),
            (b'<section id="other"><h2>1. Other</h2></section>', 'missing Instructions chapter'),
        ]
        for raw, message in cases:
            with self.subTest(message=message):
                with self.assertRaisesRegex(ValueError, message):
                    inventory(raw, manifest_for(raw))

    def test_source_tampering_rejected(self):
        raw = document('')
        m = manifest_for(raw)
        with self.assertRaisesRegex(ValueError, 'SHA-256 mismatch'):
            inventory(raw + b' ', m)
        with self.assertRaisesRegex(ValueError, 'byte count mismatch'):
            inventory(raw, {**m, 'bytes': len(raw) + 1})
        with self.assertRaisesRegex(ValueError, 'wrong source ISA'):
            inventory(raw, {**m, 'isa_version': '9.3'})


class PinnedSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = (ROOT / SOURCE).read_bytes()
        cls.data = inventory(cls.raw, json.loads((ROOT / SOURCE.parent / 'manifest.json').read_text()))

    def test_committed_inventory_and_partition(self):
        self.assertEqual((ROOT / OUTPUT).read_text(), render(self.data))
        self.assertEqual(self.data['counts'], {'all_sections': 451, 'instruction': 219,
                         'group': 81, 'context': 149, 'language_construct': 2})
        rows = self.data['sections']
        chapter = rows[0]
        # Independent direct-tag enumeration checks that parsing has dropped no section.
        source_ids = re.findall(rb'<section id="([^"]+)"',
                               self.raw[chapter['start_byte']:chapter['end_byte_exclusive']])
        self.assertEqual([s.decode() for s in source_ids], [s['id'] for s in rows])
        for row in rows:
            self.assertEqual(hashlib.sha256(self.raw[row['start_byte']:row['end_byte_exclusive']]).hexdigest(), row['sha256'])

    def test_important_boundaries_in_actual_manual(self):
        rows = self.data['sections']
        # Both mov headings matter; these are distinct sections, not a unique name count.
        mov = [r for r in rows if r['mnemonics_in_heading'] == ['mov']]
        self.assertEqual([r['number'] for r in mov], ['9.7.10.3', '9.7.10.4'])
        kinds = {r['number']: r['kind'] for r in rows}
        self.assertEqual(kinds['9.7.15.16'], 'group')  # mbarrier is an object plus instruction family.
        self.assertEqual(kinds['9.7.15.16.12'], 'instruction')  # mbarrier.init
        self.assertEqual(kinds['9.7.18.4.2'], 'group')  # Instruction descriptor, not an instruction.
        self.assertEqual(kinds['9.7.14.1'], 'language_construct')  # {}
        self.assertEqual(kinds['9.7.14.2'], 'language_construct')  # @
        self.assertTrue(all(r['implementation_coverage'] == 'not_assessed' for r in rows))


if __name__ == '__main__':
    unittest.main(verbosity=2)
