#!/usr/bin/env python3
"""Verify selected form provenance; never infer complete PTX coverage."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile

from coverage_inventory import SectionParser, require
from check_worker_evidence import verify as verify_archive

ROOT = Path(__file__).resolve().parents[1]
LEDGER = Path('coverage/implemented-forms.json')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def verify(root=ROOT, ledger=LEDGER):
    data = json.loads((root / ledger).read_text())
    require(data['schema_version'] == 1, 'unsupported ledger schema')
    require(data['scope'] == 'selected_accepted_forms', 'not a full coverage ledger')
    files = data['files']
    contents = {}
    for key, ref in files.items():
        path = Path(ref['path'])
        require(not path.is_absolute() and '..' not in path.parts, 'non-local file reference')
        require((root / path).resolve().is_relative_to(root.resolve()), 'file outside repository')
        raw = (root / path).read_bytes()
        require(sha(raw) == ref['sha256'], f'file hash mismatch: {key}')
        contents[key] = raw

    def text(key):
        require(key in contents, f'missing file reference: {key}')
        return contents[key].decode('utf-8')

    source = data['source']
    raw = contents[source['file']]
    pin = json.loads(text(source['manifest']))
    require(pin['isa_version'] == '9.4' and pin['artifact'] == 'index.html', 'wrong pinned source')
    require(sha(raw) == pin['sha256'] and len(raw) == pin['bytes'], 'pinned source mismatch')
    sections = {s['id']: s for s in SectionParser(raw).parse()}
    for anchor, digest in source['sections'].items():
        require(anchor in sections, f'missing source anchor: {anchor}')
        require(sections[anchor]['sha256'] == digest, f'section hash mismatch: {anchor}')

    def section(anchor):
        require(anchor in source['sections'], f'unpinned source anchor: {anchor}')

    for anchor in source['common_operand_guard_anchors']:
        section(anchor)

    trials = {}
    for key, trial in data['trials'].items():
        acceptance = json.loads(text(trial['acceptance']))
        manifest_path = root / files[trial['evidence']]['path']
        verify_archive(manifest_path)
        manifest = json.loads(text(trial['evidence']))
        archive = manifest_path.parent / manifest['archive']
        with tarfile.open(archive, 'r:gz') as stream:
            def member(name):
                require(name in manifest['members'], f'unrecorded evidence member: {name}')
                return stream.extractfile(name).read()
            patch = member(trial['patch_member'])
            replay = json.loads(member(trial['replay_member']))
        require(sha(patch) == trial['patch_sha256'] == acceptance['accepted_patch_sha256'] ==
                replay['patch_sha256'], f'patch mismatch: {key}')
        require(trial['replay_member'] == acceptance['mechanical_replay'], 'wrong accepted replay')
        require(trial['patch_member'] == f"attempts/{acceptance['worker_attempt']}/candidate.patch",
                'wrong accepted attempt patch')
        require(replay['attempt'] == acceptance['worker_attempt'] and
                replay['task'] == acceptance['task'] and replay['base_commit'] == acceptance['base_commit'],
                'replay identity mismatch')
        require(replay['mechanical'] == 'pass' and replay['boundary']['eligible_for_review'] is True,
                'replay did not pass')
        require(all(acceptance[k] == 'pass' for k in
                    ('mechanical', 'independent_source_review', 'independent_proof_review')),
                'acceptance is incomplete')
        require(acceptance['source_conditions']['manual_sha256'] == sha(raw), 'acceptance source mismatch')
        text(trial['source_review'])
        trials[key] = acceptance, replay

    def declaration(ref, proof=False):
        content = text(ref['file'])
        # A deliberately small locator for the current single-namespace modules.
        # It checks sites, not Lean syntax or theorem validity; the build does that.
        namespaces = re.findall(r'^namespace ([\w.]+)\s*$', content, re.M)
        require(namespaces == [ref['namespace']], f'namespace/site mismatch: {ref["name"]}')
        kind = 'theorem' if proof else r'(?:def|inductive|structure|theorem)'
        pattern = rf'^{kind} {re.escape(ref["name"])}(?=[\s:({{])'
        require(len(re.findall(pattern, content, re.M)) == 1,
                f'missing or ambiguous declaration: {ref["name"]}')
        return ref['namespace'] + '.' + ref['name']

    seen = set()
    trial_forms = {key: set() for key in trials}
    for form in data['forms']:
        spelling = form['spelling']
        require(spelling not in seen, f'duplicate form: {spelling}')
        seen.add(spelling)
        require(form['status'] == 'accepted', 'unexpected form status')
        section(form['source_anchor'])
        acceptance, replay = trials[form['trial']]
        trial_forms[form['trial']].add(spelling)
        require(spelling in acceptance['selected_forms'], 'form absent from acceptance')
        conditions = acceptance['source_conditions']
        require(form['source_anchor'] in conditions['sections'], 'form source disagrees with acceptance')
        require(form['ptx_minimum'] == conditions['ptx_minimum'], 'version mismatch')
        require(form['target'] == conditions.get('target_minimum', conditions.get('targets')), 'target mismatch')
        for field in ('operands', 'guard', 'meaning', 'boundary'):
            require(bool(form[field]), f'missing {field}')
        for category in ('semantics', 'frontend', 'proofs'):
            require(bool(form[category]), f'missing {category}')
            for ref in form[category]:
                name = declaration(ref, proof=category == 'proofs')
                if category == 'proofs':
                    require(name in replay['declarations'], f'proof not in accepted replay audit: {name}')
    require(bool(seen), 'empty accepted ledger')
    for key, (acceptance, _) in trials.items():
        require(trial_forms[key] == set(acceptance['selected_forms']), 'trial forms incomplete')
    for group in data['uncovered_siblings']:
        section(group['source_anchor'])
        require(group['status'] == 'unimplemented' and group['reason'], 'missing uncovered boundary')
        require(bool(group['spellings']), 'empty sibling group')
        for spelling in group['spellings']:
            require(spelling not in seen, f'duplicate form: {spelling}')
            seen.add(spelling)
    return len(data['forms'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('ledger', nargs='?', type=Path, default=LEDGER)
    args = parser.parse_args()
    count = verify(ledger=args.ledger)
    print(f'Implemented-form ledger: {count} selected accepted forms verified; no section-coverage claim.')


if __name__ == '__main__':
    main()
