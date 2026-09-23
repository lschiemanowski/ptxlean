#!/usr/bin/env python3
"""Verify the frozen first campaign archive without extracting or executing it."""
import argparse
import hashlib
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def verify(path):
    manifest = json.loads(path.read_text())
    archive = path.parent / manifest["archive"]
    sha = lambda data: hashlib.sha256(data).hexdigest()
    if sha(archive.read_bytes()) != manifest["archive_sha256"]:
        raise ValueError("Worker evidence archive hash mismatch")
    with tarfile.open(archive, "r:gz") as stream:
        members = stream.getmembers()
        if len(members) != len(manifest["members"]) or {m.name for m in members} != set(manifest["members"]):
            raise ValueError("Missing, duplicate or unexpected evidence member")
        for member in members:
            if not member.isfile():
                raise ValueError("Only regular evidence files are allowed")
            data = stream.extractfile(member).read()
            expected = manifest["members"][member.name]
            if len(data) != expected["bytes"] or sha(data) != expected["sha256"]:
                raise ValueError("Evidence member mismatch: " + member.name)
    return len(members)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", nargs="?", type=Path,
                        default=ROOT / "formalization/results/minmax-u32/evidence-manifest.json")
    args = parser.parse_args()
    print(f"Worker evidence: {verify(args.manifest)} archived files verified.")


if __name__ == "__main__":
    main()
