#!/usr/bin/env python3
"""Acquire an optional local PTX source, then verify its exact pinned provenance.

Downloads are explicit (--fetch), never executed, and checked before installation.
The project distributes its manifest and locators, not NVIDIA's document.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path('references/nvidia/ptx-isa-9.4/manifest.json')
SOURCE = Path('.ptx-source/9.4/index.html')


def verify_bytes(body, manifest):
    if manifest['isa_version'] != '9.4' or manifest['artifact'] != 'index.html':
        raise ValueError('Unexpected PTX source identity')
    if len(body) != manifest['bytes'] or hashlib.sha256(body).hexdigest() != manifest['sha256']:
        raise ValueError('PTX source differs from the reviewed SHA-256/byte count; no file was installed')
    return body


def acquire(root=ROOT, fetch=False, source_file=None):
    manifest = json.loads((root / MANIFEST).read_text())
    destination = root / SOURCE
    if destination.exists():
        # A failed check never overwrites a previously installed document.
        return verify_bytes(destination.read_bytes(), manifest)
    if source_file is not None:
        body = Path(source_file).read_bytes()
    elif fetch:
        with urlopen(manifest['url'], timeout=60) as response:
            body = response.read(manifest['bytes'] + 1)
    else:
        raise ValueError('PTX manual is not bundled. Run python3 scripts/check_sources.py --fetch '
                         'or --from-file PATH for an exact publisher-supplied copy.')
    verify_bytes(body, manifest)
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(body)
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return body


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--fetch', action='store_true', help='Download from the recorded NVIDIA URL if absent')
    mode.add_argument('--from-file', type=Path, help='Verify and install an already acquired exact source')
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError('Source checks require Python assertions; unset PYTHONOPTIMIZE')
    manifest = json.loads((ROOT / MANIFEST).read_text())
    body = acquire(fetch=args.fetch, source_file=args.from_file)
    digest = hashlib.sha256(body).hexdigest()
    assert (ROOT / MANIFEST.parent / 'SHA256SUMS').read_text().split() == [digest, 'index.html'], 'SHA256SUMS mismatch'
    lines = body.decode('utf-8').splitlines()
    seen = set()
    for section in manifest['sections']:
        anchor = section['anchor']
        assert anchor not in seen, f'Duplicate anchor: {anchor}'
        seen.add(anchor)
        line = section['source_line']
        assert 0 < line <= len(lines), f'Invalid source line: {anchor}'
        assert f'id="{anchor}"' in lines[line - 1], f'Anchor/line mismatch: {anchor}'
        assert section['local_reference'] == f'index.html#{anchor}', f'Local reference mismatch: {anchor}'
        assert section['url'] == manifest['url'] + '#' + anchor, f'Source URL mismatch: {anchor}'
    assert seen, 'Empty section manifest'
    print(f'PTX 9.4 local source: SHA-256, {len(body)} bytes, {len(seen)} anchors verified.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
