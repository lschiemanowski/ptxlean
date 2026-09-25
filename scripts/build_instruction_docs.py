#!/usr/bin/env python3
"""Build/check the portable instruction reference using project-owned inputs only.

No manual HTML, network access, models, or third-party Python packages are needed.
This checks documentation freshness and mapped source integrity, not Lean validity.
"""
import argparse
from collections import defaultdict
import hashlib
from html import escape
import json
from pathlib import Path
import re

from check_implemented_forms import declaration_sites

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = Path('docs/instructions')


LEAN_KEYWORDS = set('''import namespace end section open scoped variable variables
 def abbrev theorem lemma example instance structure inductive class where deriving
 private protected noncomputable opaque axiom constant universe universes attribute
 set_option in if then else match with let have show from fun forall exists do return
 by at as calc suffices obtain constructor cases induction intro intros exact apply
 refine simp simpa only rw rfl decide native_decide omega aesop trivial assumption
 rcases rintro use unfold dsimp change subst contradiction linarith ring norm_num
 repeat first all_goals sorry termination_by decreasing_by mutual Prop Type Sort
 true false'''.split())
LEAN_TOKEN = re.compile(
    r'(?P<string>"(?:\\.|[^"\\])*")'
    r"|(?P<string_char>'(?:\\.|[^'\\\n])')"
    r'|(?P<number>\b(?:0[xX][0-9a-fA-F]+|0[bB][01]+|[0-9]+(?:\.[0-9]+)?))'
    r"|(?P<name>[^\W\d][\w'.!?]*)"
    r'|(?P<operator>[:=<>+*/|&^~!@#$%\-→←↔⇒∀∃∧∨¬λ⟨⟩≤≥≠∈∉⊆∪∩]+)', re.UNICODE)


def highlight_lean(body):
    """Return escaped, independently balanced HTML lines; never rewrite source.

    This is lexical coloring, not a Lean parser. Scan the complete source before
    splitting lines so nested block comments and multiline strings retain color.
    """
    lines = ['']

    def emit(text, kind=None):
        for i, part in enumerate(text.split('\n')):
            if i:
                lines.append('')
            if part:
                safe = escape(part)
                lines[-1] += f'<span class="syntax-{kind}">{safe}</span>' if kind else safe

    pos = 0
    while pos < len(body):
        if body.startswith('--', pos):
            stop = body.find('\n', pos)
            stop = len(body) if stop < 0 else stop
            emit(body[pos:stop], 'comment')
        elif body.startswith('/-', pos):
            stop, depth = pos + 2, 1
            while stop < len(body) and depth:
                if body.startswith('/-', stop):
                    depth += 1
                    stop += 2
                elif body.startswith('-/', stop):
                    depth -= 1
                    stop += 2
                else:
                    stop += 1
            emit(body[pos:stop], 'comment')
        else:
            token = LEAN_TOKEN.match(body, pos)
            stop = token.end() if token else pos + 1
            kind = token.lastgroup if token else None
            word = body[pos:stop]
            if kind == 'name':
                kind = 'keyword' if word in LEAN_KEYWORDS else None
            elif kind == 'string_char':
                kind = 'string'
            emit(word, kind)
        pos = stop
    return lines


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def slug(name):
    if not re.fullmatch(r'[a-zA-Z0-9_.-]+', name):
        raise ValueError('Unsafe page name: ' + name)
    return name + '.html'


def page(title, content, prefix='', source=False):
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{escape(title)} · PTXLean</title><link rel="stylesheet" href="{prefix}style.css">
<script src="{prefix}search.js" defer></script></head>
<body{' class="code-source"' if source else ''}><header><a href="{prefix}index.html"><strong>PTXLEAN</strong> / Instruction reference</a><span>PTX ISA 9.4 · Lean 4.34.0</span></header>
<main>{content}<footer>Project-authored explanations and project Lean source. Lean proof validity, interpretation of PTX, and hardware conformance are separate claims. No vendor manual prose is embedded.</footer></main></body></html>
'''


def render(root=ROOT):
    root = Path(root)
    inventory = json.loads((root / 'coverage/ptx-isa-9.4-sections.json').read_text())
    ledger = json.loads((root / 'coverage/implemented-forms.json').read_text())
    restricted = json.loads((root / 'docs/reference/restricted-models.json').read_text())['entries']
    pin = json.loads((root / 'references/nvidia/ptx-isa-9.4/manifest.json').read_text())
    assert inventory['source']['sha256'] == pin['sha256'], 'Inventory source pin differs'
    sections = {s['id']: s for s in inventory['sections']}
    assert len(sections) == len(inventory['sections']), 'Duplicate inventory section'
    instructions = [s for s in inventory['sections'] if s['kind'] == 'instruction']
    forms = ledger['forms']
    explanations = json.loads((root / 'docs/reference/explanations.json').read_text())
    assert set(explanations) == {f['spelling'] for f in forms}, 'Missing or obsolete explanation'
    assert all(paragraphs and all(isinstance(p, str) and p.strip() for p in paragraphs)
               for paragraphs in explanations.values()), 'Empty explanation'
    assert len({f['spelling'] for f in forms + restricted}) == len(forms + restricted), 'Duplicate form'
    # Check public ledger inputs by their exact hashes. Do not open the local manual.
    for key, ref in ledger['files'].items():
        if key == ledger['source']['file']:
            continue
        path = Path(ref['path'])
        assert not path.is_absolute() and '..' not in path.parts, 'Non-local ledger input'
        assert digest((root / path).read_bytes()) == ref['sha256'], 'Stale ledger input: ' + str(path)
    for trial in ledger['trials'].values():
        acceptance = json.loads((root / ledger['files'][trial['acceptance']]['path']).read_text())
        assert all(acceptance[k] == 'pass' for k in
                   ['mechanical', 'independent_source_review', 'independent_proof_review']), 'Unaccepted trial'
    for f in forms:
        assert f['status'] == 'accepted'
        assert sections[f['source_anchor']]['sha256'] == ledger['source']['sections'][f['source_anchor']]
    # The typed scalar frontend must not acquire undocumented spellings silently.
    scalar_text = (root / 'Ptx/ScalarText.lean').read_text()
    selected = scalar_text.split('def supportedMnemonic', 1)[1].split('def decodeOp', 1)[0]
    scalar_spellings = set(re.findall(r'"([a-z][a-z0-9_.]*)"', selected))
    assert scalar_spellings <= {f['spelling'] for f in forms + restricted}, 'Unmapped scalar spelling'

    output = {'style.css': (root / 'scripts/instruction_docs.css').read_text(),
              'search.js': (root / 'scripts/instruction_docs.js').read_text()}
    source_files = {}

    def source(path):
        p = Path(path)
        assert p.suffix == '.lean' and p.parts[0] in ('Ptx', 'integration'), 'Not project Lean source'
        assert (root / p).resolve().is_relative_to(root.resolve()), 'Escaping source path'
        if path not in source_files:
            body = (root / p).read_text()
            # The ledger indexer intentionally handles a smaller name grammar.
            # Normalize a trailing '?' only for indexing; displayed source stays exact.
            indexed = re.sub(r'^(\s*(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem)\s+[A-Za-z_][A-Za-z_0-9.\']*)\?', r'\1___question', body, flags=re.M)
            sites = {n.replace('___question', '?'): (k, line)
                     for n, k, line in declaration_sites(indexed)}
            source_files[path] = body, sites
        return source_files[path]

    def code_name(path):
        return path.replace('/', '__') + '.html'

    def code_link(path, declaration):
        _, sites = source(path)
        assert declaration in sites, f'Missing declaration: {path}: {declaration}'
        line = sites[declaration][1]
        return f'<a href="../code/{escape(code_name(path))}#L{line}"><code>{escape(declaration)}</code></a>'

    def snippet(path, declaration):
        body, sites = source(path)
        line = sites[declaration][1]
        lines = body.splitlines()
        # A small exact opening excerpt, explicitly labeled when it continues.
        # Full source and proof bodies always remain available through line links.
        stop = min(line + 17, len(lines))
        later = [n - 1 for _, n in sites.values() if n > line]
        if later:
            stop = min(stop, min(later))
        code = '\n'.join(highlight_lean(body)[line - 1:stop]).rstrip()
        return f'<p>{code_link(path, declaration)} <small>· opening excerpt; follow the link for full source</small></p><pre><code>{code}</code></pre>'

    def refs(form, key):
        return [(ledger['files'][r['file']]['path'], r['namespace'] + '.' + r['name'])
                for r in form[key]]

    indexed = defaultdict(list)
    for form, status in [(f, 'reviewed') for f in forms] + [(f, 'restricted') for f in restricted]:
        section = sections[form['source_anchor']]
        assert section['kind'] == 'instruction', 'Form mapped to non-instruction section'
        indexed[section['id']].append((form, status))
        name = form['spelling']
        all_refs = (refs(form, 'semantics') + refs(form, 'frontend') + refs(form, 'proofs')
                    if status == 'reviewed' else [(r['path'], r['declaration']) for r in form['code']])
        for path, declaration in all_refs:
            code_link(path, declaration)
        content = f'<p class="back"><a href="../index.html#{escape(section["id"])}">← All instruction entries</a></p>'
        content += f'<div class="eyebrow">{escape(section["number"])} · {"Reviewed form" if status == "reviewed" else "Restricted core model"}</div><h1>{escape(name)}</h1>'
        paragraphs = explanations[name] if status == 'reviewed' else [form['meaning']]
        content += ''.join(f'<p class="intro">{escape(p)}</p>' for p in paragraphs)
        content += f'<details><summary>Model restrictions</summary><p>{escape(form["boundary"])}</p></details>'
        if status == 'reviewed':
            content += '<h2>Operands and execution</h2><dl>'
            operands = form['operands']
            for label, value in [('Destination', operands['destination']), ('Sources', '; '.join(operands['sources'])),
                                 ('Overlap', operands['aliasing']), ('Guard', form['guard']),
                                 ('Version', 'Introduced in PTX ' + form['ptx_minimum'] + ('; selected ISA ' + form['selected_isa'] if 'selected_isa' in form else '; this decoder does not enforce version/target eligibility')),
                                 ('Target', form['target'])]:
                content += f'<dt>{escape(label)}</dt><dd>{escape(value)}</dd>'
            content += '</dl><p class="muted">A word is a fixed-size sequence of bits. Signed and unsigned interpretations use the same bits but assign different numbers. A guard is a true-or-false condition deciding whether to execute. Immediate operands are values supplied directly. Typed operands have already been classified; this does not parse or validate a complete PTX module.</p>'
        else:
            content += '<p class="muted">This page documents an existing bounded formalization. It is not promoted to the independently accepted instruction-form ledger. Read its module comments and proof hypotheses for the precise execution restrictions.</p>'
        content += '<h2>Lean definitions</h2>' + snippet(*all_refs[0])
        content += '<h2>Definitions and proofs</h2><ul class="proofs">' + ''.join(
            '<li>' + code_link(path, decl) + '</li>' for path, decl in dict.fromkeys(all_refs)) + '</ul>'
        paths = list(dict.fromkeys(path for path, _ in all_refs))
        content += '<h2>Complete Lean source</h2><p>Browse the actual modules, including all proof bodies and shared execution rules.</p><ul>'
        for path in paths:
            content += f'<li><a href="../code/{escape(code_name(path))}">{escape(path)}</a></li>'
        content += '</ul><h2>Source provenance</h2>'
        content += f'<p><a href="{escape(section["source_url"])}">NVIDIA instruction reference</a> · section {escape(section["number"])}. The online manual may change; the project reviewed the pinned ISA 9.4 source.</p><p><small>Reviewed section SHA-256: <code>{escape(section["sha256"])}</code></small></p>'
        if status == 'reviewed':
            content += f'<p class="muted">Acceptance record: <code>{escape(ledger["files"][ledger["trials"][form["trial"]]["acceptance"]]["path"])}</code>. Proofs establish the formal contract; source review is separate and neither establishes hardware conformance.</p>'
        output['forms/' + slug(name)] = page(name, content, '../')

    for path, (body, sites) in source_files.items():
        content = f'<p class="back"><a href="../index.html">← Instruction index</a></p><div class="eyebrow">Project Lean source · full file</div><h1>{escape(path)}</h1><p><small>SHA-256 <code>{digest(body.encode())}</code></small></p>'
        colored = highlight_lean(body)[:len(body.splitlines())]
        content += '<pre><code>' + '\n'.join(f'<span class="code-line" id="L{i}"><a class="line-number" href="#L{i}">{i}</a>{line}</span>' for i, line in enumerate(colored, 1)) + '</code></pre>'
        output['code/' + code_name(path)] = page(path, content, '../', True)

    def category(section):
        current = section
        while current['parent_id'] in sections:
            parent = sections[current['parent_id']]
            if parent['kind'] == 'group':
                return re.sub(r'^\d+(?:\.\d+)*\.?\s*', '', parent['heading'])
            current = parent
        return 'Instructions'

    content = '<div class="eyebrow">An annotated map of the ISA</div><h1>PTX instruction reference</h1>'
    content += '<p class="intro">Find an instruction, read what its formal model means, and follow the Lean definitions and proofs. Explanations are written for this project; NVIDIA’s manual is linked separately.</p>'
    content += f'<div class="stats"><div><strong>{len(instructions)}</strong><span>instruction entries</span></div><div><strong>{len(forms)}</strong><span>reviewed forms</span></div><div><strong>{len(restricted)}</strong><span>restricted model pages</span></div></div>'
    content += '<p class="note">Entries follow the pinned PTX 9.4 instruction sections. A name can appear in several categories, and one entry can contain several names. A <strong>form</strong> specifies types and options, such as <code>add.rn.f32</code>. Linked forms do not imply complete coverage of that instruction. “No mapped model” means none is documented in this catalog, not an exhaustive claim that no related code exists.</p>'
    content += '<div class="controls"><label for="search">Find an instruction<input id="search" type="search" placeholder="Name, form or category…"></label><label for="status">Show<select id="status"><option value="all">All entries</option><option value="reviewed">With reviewed forms</option><option value="restricted">With restricted models</option><option value="none">No mapped model</option></select></label><p id="result-count" aria-live="polite"></p></div><div class="table-wrap"><table><caption class="muted">Instruction entries and exact documented forms</caption><thead><tr><th scope="col">Instruction</th><th scope="col">Category</th><th scope="col">Formalization</th><th scope="col">Source</th></tr></thead><tbody>'
    for section in instructions:
        mapped = indexed[section['id']]
        names = ', '.join(section['mnemonics_in_heading'])
        cat = category(section)
        statuses = ' '.join(sorted({s for _, s in mapped})) or 'none'
        terms = ' '.join([names, cat, *(f['spelling'] for f, _ in mapped)]).lower()
        content += f'<tr id="{escape(section["id"])}" data-status="{statuses}" data-search="{escape(terms)}"><td><code>{escape(names)}</code></td><td>{escape(cat)}</td><td>'
        for status, label in [('reviewed', 'Reviewed forms'), ('restricted', 'Restricted models')]:
            selected = [f for f, s in mapped if s == status]
            if selected:
                content += f'<span class="badge {status}">{label}</span><div class="form-links">' + ''.join(f'<a href="forms/{slug(f["spelling"])}"><code>{escape(f["spelling"])}</code></a>' for f in selected) + '</div>'
        if not mapped:
            content += '<span class="badge none">No mapped model</span>'
        content += f'</td><td><a href="{escape(section["source_url"])}">§{escape(section["number"])}</a></td></tr>'
    content += '</tbody></table><p id="empty" hidden>No matching instruction entries. Try a shorter name or another status.</p></div>'
    content += '<p class="muted">Open this file directly in a browser; no server, network, or JavaScript is required to read every entry and its code. Search and filtering use only a local script. Rebuild with <code>python3 scripts/build_instruction_docs.py</code>.</p>'
    output['index.html'] = page('Instruction reference', content)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='fail on stale or missing generated files')
    args = parser.parse_args()
    outputs = render()
    destination = ROOT / OUTPUT
    existing = {p.relative_to(destination).as_posix() for p in destination.rglob('*') if p.is_file()}
    stale = sorted(existing - outputs.keys())
    changed = sorted(name for name, body in outputs.items()
                     if not (destination / name).is_file() or (destination / name).read_text() != body)
    if args.check:
        if stale or changed:
            raise SystemExit('Stale instruction documentation: ' + ', '.join(stale + changed))
        print(f'Instruction documentation: {len(outputs)} generated files are current.')
    else:
        # Only our known static output types are replaced or removed.
        assert all(Path(name).suffix in ('.html', '.css', '.js') for name in stale), 'Unexpected output file'
        for name in stale:
            (destination / name).unlink()
        for name, body in outputs.items():
            path = destination / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(body)
        print(f'Built {len(outputs)} static instruction-reference files in {OUTPUT}.')


if __name__ == '__main__':
    main()
