#!/usr/bin/env python3
"""Reproduce the instruction-section inventory from the pinned PTX HTML.

This deliberately extracts section provenance, not instruction forms or support.
Only Python's standard library is needed. No network or model calls are made.
"""

import argparse
from collections import Counter
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
from check_sources import SOURCE, MANIFEST
OUTPUT = Path('coverage/ptx-isa-9.4-sections.json')
CHAPTER = 'instructions'
KINDS = ('instruction', 'group', 'context', 'language_construct')


def require(condition, message):
    if not condition:
        raise ValueError(message)


class SectionParser(HTMLParser):
    """Track section nesting and byte spans without confusing the navigation TOC.

    Offsets use the original UTF-8 bytes, including the opening and closing section
    tags. Parent spans include children. Heading permalink icons are excluded.
    """

    def __init__(self, raw):
        super().__init__(convert_charrefs=True)
        self.raw = raw
        self.text = raw.decode('utf-8')
        self.lines = self.text.splitlines(keepends=True)
        self.line_offsets = [0]
        for line in self.lines:
            self.line_offsets.append(self.line_offsets[-1] + len(line.encode('utf-8')))
        self.sections = []
        self.stack = []
        self.ids = set()
        self.heading = None
        self.heading_parts = []
        self.skip_permalink = False

    def byte_offset(self):
        line, col = self.getpos()
        return self.line_offsets[line - 1] + len(self.lines[line - 1][:col].encode('utf-8'))

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'section':
            anchor = attrs.get('id')
            if anchor:
                require(anchor not in self.ids, f'duplicate section id: {anchor}')
                self.ids.add(anchor)
                named_parents = [s for s in self.stack if s is not None]
                section = {'id': anchor,
                           'parent_id': named_parents[-1]['id'] if named_parents else None,
                           'source_line': self.getpos()[0],
                           'start_byte': self.byte_offset()}
                self.sections.append(section)
                self.stack.append(section)
            else:
                require(not any(s and s['id'] == CHAPTER for s in self.stack),
                        'section without id inside Instructions chapter')
                self.stack.append(None)  # The document includes an unnumbered UI wrapper.
        if re.fullmatch(r'h[1-9][0-9]*', tag) and self.stack and self.stack[-1] is not None:
            require(self.heading is None, 'nested section heading')
            require('heading' not in self.stack[-1], f'multiple headings: {self.stack[-1]["id"]}')
            self.heading = tag
            self.heading_parts = []
        if self.heading and tag == 'a' and 'headerlink' in attrs.get('class', '').split():
            self.skip_permalink = True

    def handle_data(self, text):
        if self.heading and not self.skip_permalink:
            self.heading_parts.append(text)

    def handle_endtag(self, tag):
        if tag == self.heading:
            heading = ' '.join(''.join(self.heading_parts).split())
            require(bool(heading), 'empty section heading')
            self.stack[-1]['heading'] = heading
            self.heading = None
        if tag == 'a':
            self.skip_permalink = False
        if tag == 'section':
            require(bool(self.stack), 'unmatched closing section')
            section = self.stack.pop()
            if section is not None:
                start = self.byte_offset()
                end = self.raw.find(b'>', start)
                require(end >= 0, 'unterminated section closing tag')
                section['end_byte_exclusive'] = end + 1
                section['end_line'] = self.getpos()[0]
                section['sha256'] = hashlib.sha256(
                    self.raw[section['start_byte']:end + 1]).hexdigest()

    def parse(self):
        self.feed(self.text)
        self.close()
        require(not self.stack, 'unclosed section')
        require(self.heading is None, 'unclosed heading')
        return self.sections


def classify(heading, has_children):
    """Classify the pinned manual's heading convention, never infer supportedness.

    A spelling-like suffix after Instruction(s): marks an instruction section.
    The enclosing mbarrier section and async copy headings are groups, not forms.
    Unknown leaf headings remain visible as context, with explicit reasons.
    """
    match = re.search(r'\bInstructions?:\s*(.+)$', heading, re.IGNORECASE)
    if match:
        suffix = match.group(1)
        if suffix in ('{}', '@'):
            return 'language_construct', 'Block syntax or predication, not a standalone instruction.', []
        if not has_children:
            spelling = re.sub(r'\s*\(deprecated\)$', '', suffix)
            names = re.split(r'\s*[,/]\s*', spelling)
            if all(re.fullmatch(r'[a-z][a-z0-9_.]*(?:::[a-z0-9_]+)?', n) for n in names):
                return 'instruction', 'Instruction heading with explicit mnemonic spelling(s).', names
            raise ValueError(f'unrecognized instruction-heading suffix: {suffix}')
    if has_children:
        return 'group', 'Organizes nested sections; excluded from instruction-section counts.', []
    return 'context', 'Explanatory material; excluded from instruction-section counts.', []


def inventory(raw, manifest):
    require(manifest['isa_version'] == '9.4', 'wrong source ISA version')
    require(manifest['artifact'] == 'index.html', 'unexpected source artifact')
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == manifest['sha256'], 'source SHA-256 mismatch')
    require(len(raw) == manifest['bytes'], 'source byte count mismatch')
    sections = SectionParser(raw).parse()
    by_id = {s['id']: s for s in sections}
    require(CHAPTER in by_id, 'missing Instructions chapter')
    chapter = by_id[CHAPTER]
    require(chapter.get('heading') == '9.7. Instructions', 'unexpected Instructions chapter heading')
    selected = [s for s in sections if chapter['start_byte'] <= s['start_byte'] < chapter['end_byte_exclusive']]
    children = {s['parent_id'] for s in selected}
    selected_ids = {s['id'] for s in selected}
    require(bool(selected), 'empty inventory')
    seen_numbers = set()
    for section in selected:
        require('heading' in section, f'missing heading: {section["id"]}')
        match = re.fullmatch(r'(9\.7(?:\.[0-9]+)*)\. (.+)', section['heading'])
        require(match is not None, f'unnumbered or out-of-chapter heading: {section["id"]}')
        number = match.group(1)
        require(number not in seen_numbers, f'duplicate section number: {number}')
        seen_numbers.add(number)
        section['number'] = number
        if section['id'] != CHAPTER:
            require(section['parent_id'] in selected_ids, 'parent outside selected chapter')
            parent = by_id[section['parent_id']]
            require(number.rsplit('.', 1)[0] == parent['number'], f'number/nesting mismatch: {number}')
        kind, reason, names = classify(section['heading'], section['id'] in children)
        section['kind'] = kind
        section['classification_reason'] = reason
        section['mnemonics_in_heading'] = names
        section['form_coverage'] = 'not_elaborated' if kind == 'instruction' else 'not_an_instruction_section'
        section['implementation_coverage'] = 'not_assessed'
        section['local_reference'] = f'{SOURCE}#{section["id"]}'
        section['source_url'] = manifest['url'] + '#' + section['id']
    counts = Counter(s['kind'] for s in selected)
    return {
        'schema_version': 1,
        'scope': 'Every section in PTX ISA 9.4 section 9.7, Instructions, including its root.',
        'denominator_warning': 'Instruction sections are not unique mnemonics or complete instruction forms. No supportedness or semantic-fidelity claims are inferred.',
        'classification_policy': 'Headings and nesting; instruction leaf headings require explicit mnemonic spelling(s). Group headings, context, and language constructs are excluded from instruction-section counts.',
        'source': {'path': str(SOURCE), 'isa_version': manifest['isa_version'],
                   'sha256': digest, 'bytes': len(raw), 'url': manifest['url'],
                   'section_hash_scope': 'Exact UTF-8 bytes from opening section tag through closing tag, inclusive of nested sections.'},
        'counts': {'all_sections': len(selected), **{kind: counts[kind] for kind in KINDS}},
        'sections': selected,
    }


def render(data):
    return json.dumps(data, indent=2, ensure_ascii=False) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Regenerate the committed inventory; default verifies it.')
    args = parser.parse_args()
    manifest = json.loads((ROOT / MANIFEST).read_text())
    data = inventory((ROOT / SOURCE).read_bytes(), manifest)
    expected = render(data)
    destination = ROOT / OUTPUT
    if args.write:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(expected, encoding='utf-8')
    else:
        require(destination.read_text(encoding='utf-8') == expected, 'inventory differs; review source/classification changes before regenerating')
    print(f'PTX 9.4 instruction-section inventory: {data["counts"]}; no form-coverage claim.')


if __name__ == '__main__':
    main()
