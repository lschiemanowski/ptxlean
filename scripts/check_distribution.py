#!/usr/bin/env python3
"""Guard release files or selected Git history against known vendor artifacts.

This checks known artifact types, not copyright law or every possible quotation.
Private local caches, recovery bundles and other refs are not publication inputs.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def check_payload(name, body, manual_sha):
    if (name == 'events.jsonl' or name.endswith('/events.jsonl')
            or name.startswith('.ptx-source/')
            or ('references/nvidia/' in name and name.endswith('.html'))
            or hashlib.sha256(body).hexdigest() == manual_sha):
        raise ValueError('Non-distributable vendor source/transcript: ' + name)


def check_file(name, body, manual_sha):
    check_payload(name, body, manual_sha)
    if name.endswith('.tar.gz'):
        with tarfile.open(fileobj=io.BytesIO(body), mode='r:gz') as stream:
            for member in stream:
                check_payload(member.name, b'', manual_sha)
                if member.isfile():
                    check_payload(member.name, stream.extractfile(member).read(), manual_sha)


def check_history(root, revision, manual_sha):
    """Check every reachable tree, including deleted files and archive members."""
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=root)

    # Resolve once, reject option-like input, and use only the resolved commit below.
    commit = git('rev-parse', '--verify', '--end-of-options',
                 revision + '^{commit}').decode().strip()
    commits = git('rev-list', commit).decode().splitlines()
    entries = set()
    for rev in commits:
        for entry in git('ls-tree', '-r', '-z', rev).split(b'\0'):
            if not entry:
                continue
            metadata, name = entry.split(b'\t', 1)
            mode, kind, oid = metadata.decode().split()
            if kind == 'blob':
                entries.add((name.decode(), oid))
    checked = set()
    for name, oid in sorted(entries):
        check_payload(name, b'', manual_sha)
        # The same content can occur under different paths. Names are always checked;
        # archive interpretation also depends on the suffix.
        key = (oid, name.endswith('.tar.gz'))
        if key not in checked:
            check_file(name, git('cat-file', 'blob', oid), manual_sha)
            checked.add(key)
    return len(commits), len(checked)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--history', metavar='REVISION',
                        help='check every commit reachable from this publication revision')
    args = parser.parse_args()
    pin = json.loads((ROOT/'references/nvidia/ptx-isa-9.4/manifest.json').read_text())
    if args.history:
        commits, blobs = check_history(ROOT, args.history, pin['sha256'])
        print(f'Distribution guard: {commits} reachable commits and {blobs} distinct '
              'file contents contain no known manual artifact or raw model event transcript.')
        return
    names = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    for name in filter(None, names):
        path = ROOT/name
        if path.is_file():  # Proposed deletions are absent from the release tree.
            check_file(name, path.read_bytes(), pin['sha256'])
    print('Distribution guard: current tracked files contain no manual artifact or raw model event transcript; Git history is separate.')


if __name__ == '__main__':
    main()
