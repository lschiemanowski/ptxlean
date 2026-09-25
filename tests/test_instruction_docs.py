"""Behavior checks for portable documentation, coverage, and source provenance."""
from html.parser import HTMLParser
from pathlib import Path, PurePosixPath
import json
import posixpath
import shutil
import sys
import tempfile
import unittest
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from build_instruction_docs import render


class Links(HTMLParser):
    def __init__(self, body):
        super().__init__()
        self.ids, self.targets, self.rows, self.assets = set(), [], [], []
        self.feed(body)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.add(attrs['id'])
        if tag == 'tr' and 'data-status' in attrs:
            self.rows.append(attrs)
        if tag in ('a', 'link') and 'href' in attrs:
            self.targets.append(attrs['href'])
        if tag in ('script', 'img', 'iframe') and 'src' in attrs:
            self.targets.append(attrs['src'])
            self.assets.append(attrs['src'])
        if tag == 'link':
            self.assets.append(attrs['href'])


class InstructionDocsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pages = render()
        cls.parsed = {n: Links(b) for n, b in cls.pages.items() if n.endswith('.html')}

    def test_all_instruction_sections_present_without_coverage_inflation(self):
        sections = json.loads((ROOT / 'coverage/ptx-isa-9.4-sections.json').read_text())['sections']
        rows = self.parsed['index.html'].rows
        self.assertEqual({r['id'] for r in rows}, {s['id'] for s in sections if s['kind'] == 'instruction'})
        self.assertEqual(len(rows), len({r['id'] for r in rows}))
        by_id = {r['id']: r for r in rows}
        self.assertEqual(by_id['integer-arithmetic-instructions-add']['data-status'], 'restricted')
        self.assertEqual(by_id['floating-point-instructions-add']['data-status'], 'reviewed')
        self.assertEqual(by_id['half-precision-floating-point-instructions-add']['data-status'], 'none')
        forms = json.loads((ROOT / 'coverage/implemented-forms.json').read_text())['forms']
        for form in forms:
            self.assertIn('forms/' + form['spelling'] + '.html', self.pages)

    def test_every_local_link_and_anchor_resolves(self):
        for name, parsed in self.parsed.items():
            for href in parsed.targets:
                url = urlsplit(href)
                if url.scheme:
                    self.assertEqual(url.scheme, 'https')
                    continue
                target = posixpath.normpath(str(PurePosixPath(name).parent / url.path)) if url.path else name
                self.assertIn(target, self.pages, (name, href))
                if url.fragment:
                    self.assertIn(url.fragment, self.parsed[target].ids, (name, href))
            self.assertTrue(all(not urlsplit(a).scheme for a in parsed.assets))

    def test_regeneration_is_exact(self):
        self.assertEqual(self.pages, render())
        for name, body in self.pages.items():
            self.assertEqual((ROOT / 'docs/instructions' / name).read_text(), body)

    def test_no_vendor_source_needed_and_stale_source_rejected(self):
        ledger = json.loads((ROOT / 'coverage/implemented-forms.json').read_text())
        restricted = json.loads((ROOT / 'docs/reference/restricted-models.json').read_text())
        paths = {r['path'] for k, r in ledger['files'].items() if k != ledger['source']['file']}
        paths.update(r['path'] for e in restricted['entries'] for r in e['code'])
        paths.update(['coverage/implemented-forms.json', 'coverage/ptx-isa-9.4-sections.json',
                      'docs/reference/restricted-models.json', 'docs/reference/explanations.json', 'scripts/instruction_docs.css', 'scripts/instruction_docs.js'])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in paths:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / name, root / name)
            self.assertFalse((root / '.ptx-source').exists())
            self.assertEqual(render(root), self.pages)
            path = root / 'Ptx/Shf32.lean'
            path.write_text(path.read_text() + '\n-- changed\n')
            with self.assertRaisesRegex(AssertionError, 'Stale ledger input'):
                render(root)


if __name__ == '__main__':
    unittest.main()
