#!/usr/bin/env python3
"""Check the pinned source artifact and the manifest's exact anchor locations."""

import hashlib
import json
from pathlib import Path


def main():
    if not __debug__:
        raise RuntimeError("Source checks require Python assertions; unset PYTHONOPTIMIZE")
    root = Path(__file__).resolve().parents[1]
    source = root / "references/nvidia/ptx-isa-9.4"
    manifest = json.loads((source / "manifest.json").read_text())
    assert manifest["isa_version"] == "9.4", "Wrong PTX ISA version"
    assert manifest["artifact"] == "index.html", "Unexpected source artifact"
    body = (source / manifest["artifact"]).read_bytes()
    digest = hashlib.sha256(body).hexdigest()
    assert digest == manifest["sha256"], "Manifest SHA-256 mismatch"
    assert len(body) == manifest["bytes"], "Manifest byte count mismatch"
    assert (source / "SHA256SUMS").read_text().split() == [digest, "index.html"], \
        "SHA256SUMS mismatch"
    lines = body.decode("utf-8").splitlines()
    seen = set()
    for section in manifest["sections"]:
        anchor = section["anchor"]
        assert anchor not in seen, f"Duplicate anchor: {anchor}"
        seen.add(anchor)
        line = section["source_line"]
        assert 0 < line <= len(lines), f"Invalid source line: {anchor}"
        assert f'id="{anchor}"' in lines[line - 1], f"Anchor/line mismatch: {anchor}"
        assert section["local_reference"] == f"index.html#{anchor}", \
            f"Local reference mismatch: {anchor}"
        assert section["url"] == manifest["url"] + "#" + anchor, \
            f"Source URL mismatch: {anchor}"
    assert seen, "Empty section manifest"
    print(f"PTX 9.4 source: SHA-256, {len(body)} bytes, {len(seen)} anchors verified.")


if __name__ == "__main__":
    main()
