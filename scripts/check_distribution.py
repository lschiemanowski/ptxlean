#!/usr/bin/env python3
"""Guard the current release files against bundled manuals and raw transcripts.

This checks known artifact types, not copyright law or every possible quotation.
It does not certify Git history; historical copies require separate removal.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def check_payload(name, body, manual_sha):
    if (name.endswith('/events.jsonl') or name.startswith('.ptx-source/')
            or ('references/nvidia/' in name and name.endswith('.html'))
            or hashlib.sha256(body).hexdigest() == manual_sha):
        raise ValueError('Non-distributable vendor source/transcript: ' + name)


def main():
    pin = json.loads((ROOT/'references/nvidia/ptx-isa-9.4/manifest.json').read_text())
    names = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    for name in filter(None, names):
        path = ROOT/name
        if not path.is_file():
            continue  # Proposed deletions are absent from the release tree.
        check_payload(name, path.read_bytes(), pin['sha256'])
        if name.endswith('.tar.gz'):
            with tarfile.open(path) as stream:
                for member in stream:
                    if member.isfile():
                        check_payload(member.name, stream.extractfile(member).read(), pin['sha256'])
    print('Distribution guard: current tracked files contain no manual artifact or raw model event transcript; Git history is separate.')


if __name__ == '__main__':
    main()
