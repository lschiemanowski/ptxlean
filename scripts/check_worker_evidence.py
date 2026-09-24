#!/usr/bin/env python3
"""Verify archived worker and synthetic replay evidence without extracting or executing their contents."""
import argparse
import hashlib
import json
import re
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def verify(path):
    manifest = json.loads(path.read_text())
    distribution = manifest.get("distribution")
    if distribution is not None:
        if (distribution.get("policy") != "omit-raw-model-transcripts"
                or not re.fullmatch(r"[0-9a-f]{64}", distribution.get("original_archive_sha256", ""))
                or not distribution.get("reason") or not distribution.get("omitted_members")):
            raise ValueError("Invalid evidence distribution record")
        for name, original in distribution["omitted_members"].items():
            if (not name.endswith("/events.jsonl") or name in manifest["members"]
                    or not isinstance(original.get("bytes"), int) or original["bytes"] < 0
                    or not re.fullmatch(r"[0-9a-f]{64}", original.get("sha256", ""))):
                raise ValueError("Invalid evidence omission record")
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


def default_manifests(root=ROOT):
    """Each evidence archive owns one independently verified manifest."""
    manifests = sorted((root / "formalization/results").glob("*/evidence-manifest.json"))
    if not manifests:
        raise ValueError("No archived worker evidence manifests found")
    return manifests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", nargs="*", type=Path,
                        help="Explicit manifests; default: every evidence archive")
    args = parser.parse_args()
    manifests = args.manifest or default_manifests()
    total = sum(verify(path) for path in manifests)
    print(f"Worker evidence: {total} archived files across {len(manifests)} archives verified.")


if __name__ == "__main__":
    main()
