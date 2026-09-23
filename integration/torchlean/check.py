#!/usr/bin/env python3
"""Check the pinned integration sources and exact public dependency endpoints.

No dependency update, clone, cache download, or external model invocation.
This source guard and proof audit do not establish semantic fidelity.
"""
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_proofs import FORBIDDEN, code_only
from worker_replay import audit_dependencies

COUNTS = {"PtxTorchLean": 7, "PtxTorchLean.TensorBridge": 15,
          "Ptx.Binary32": 25, "Ptx.Binary32.Examples": 16,
          "Ptx.Binary32.Bounds": 12, "Ptx.Binary32.Error": 10}
TARGETS = {"PtxTorchLean", "PtxTensorBridge", "PtxBinary32",
           "PtxBinary32Examples", "PtxBinary32Bounds", "PtxBinary32Error"}


def git(directory, *args):
    return subprocess.check_output(["git", "-C", str(directory), *args], text=True).strip()


def dependencies():
    manifest = json.loads((HERE / "lake-manifest.json").read_text())
    checked = 0
    for package in manifest["packages"]:
        if package["type"] == "path":
            if package["name"] != "ptxlean" or (HERE / package["dir"]).resolve() != ROOT:
                raise ValueError(f"Unexpected local dependency: {package['name']}")
            continue
        if package["type"] != "git":
            raise ValueError(f"Unsupported dependency kind: {package['type']}")
        name = package["name"].removeprefix("«").removesuffix("»")
        directory = HERE / manifest["packagesDir"] / name
        if not (directory / ".git").exists():
            raise ValueError(f"Missing pinned dependency {name}; provision it before checking")
        if git(directory, "rev-parse", "HEAD") != package["rev"]:
            raise ValueError(f"Dependency HEAD differs from manifest: {name}")
        if git(directory, "status", "--porcelain", "--untracked-files=no"):
            raise ValueError(f"Tracked dependency files modified: {name}")
        checked += 1
    return checked


def sources():
    paths = []
    for directory, subdirs, files in os.walk(HERE):
        subdirs[:] = [d for d in subdirs if d not in {".lake", ".git", "__pycache__"}]
        paths.extend(Path(directory) / f for f in files if f.endswith(".lean"))
    return sorted(paths)


def snapshot():
    paths = [*sources(), ROOT / "Ptx.lean", *sorted((ROOT / "Ptx").rglob("*.lean")),
             HERE / "check.py", HERE / "check.sh",
             ROOT / "scripts/check_proofs.py", ROOT / "scripts/worker_replay.py",
             ROOT / "scripts/worker_run.py"]
    for directory in (HERE, ROOT):
        paths += [directory / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    if len(sys.argv) != 1:
        raise ValueError("Usage: integration/torchlean/check.sh (no arguments)")
    config = tomllib.loads((HERE / "lakefile.toml").read_text())
    if set(config["defaultTargets"]) != TARGETS:
        raise ValueError("Default integration targets changed; update the explicit audit coverage")
    if (HERE / "lean-toolchain").read_bytes() != (ROOT / "lean-toolchain").read_bytes():
        raise ValueError("Integration and root toolchain pins differ")
    count = dependencies()
    paths = sources()
    for path in paths:
        match = FORBIDDEN.search(code_only(path.read_text()))
        if match:
            raise ValueError(f"{path.relative_to(HERE)}: forbidden proof token {match.group()}")
    driver = HERE / "PtxIntegrationAudit.lean"
    names = re.findall(r"^#print axioms (\S+)\s*$", code_only(driver.read_text()), re.MULTILINE)
    if len(set(names)) != len(names) or Counter(n.rsplit('.', 1)[0] for n in names) != Counter(COUNTS):
        raise ValueError("Missing, duplicate, or unexpected audit endpoint count")
    before = snapshot()
    print(f"Pinned dependencies: {count}; integration Lean source guard: {len(paths)} files.", flush=True)
    try:
        pin = (HERE / "lean-toolchain").read_text().strip()
        prefix = "leanprover/lean4:v"
        if not pin.startswith(prefix):
            raise ValueError(f"Unsupported toolchain pin: {pin}")
        version = subprocess.check_output(
            ["lake", "--no-cache", "env", "lean", "--version"], cwd=HERE, text=True).strip()
        if not version.startswith(f"Lean (version {pin.removeprefix(prefix)},"):
            raise ValueError(f"Actual Lean differs from pin {pin}: {version}")
        print(version, flush=True)
        subprocess.run(["lake", "--no-cache", "build"], cwd=HERE, check=True)
        audit = subprocess.run(["lake", "--no-cache", "env", "lean", driver.name],
                               cwd=HERE, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(audit.stdout, end="", flush=True)
        audit.check_returncode()
        audit_dependencies(audit.stdout, names)
    finally:
        dependencies()
        if snapshot() != before:
            raise ValueError("Checked sources, pins, configuration, or checker changed during verification")
    print(f"Integration check passed: {len(names)} exact dependency reports, only standard Lean axioms.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, subprocess.CalledProcessError) as error:
        sys.exit(f"Integration check failed: {error}")
