#!/usr/bin/env python3
"""Replay a recorded patch without inference; mechanical checking is not acceptance."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess

from check_proofs import ALLOWED_AXIOMS, FORBIDDEN, code_only
from worker_run import (atomic_json, changed_sources, git, now, patch_and_boundary,
                        read_json, sha, validate_task)


def validate_attempt(attempt, root):
    task = read_json(attempt / "task.json")
    receipt = read_json(attempt / "receipt.json")
    patch = (attempt / "candidate.patch").read_bytes()
    validate_task(task, root)
    if receipt.get("task_sha256") != sha(json.dumps(task, sort_keys=True).encode()):
        raise ValueError("Recorded task hash differs")
    if receipt.get("base_commit") != task["base_commit"]:
        raise ValueError("Recorded base differs")
    if receipt.get("patch_sha256") != sha(patch):
        raise ValueError("Recorded patch hash differs")
    if not receipt.get("finished_at") or receipt.get("state") not in {"completed", "failed", "interrupted"}:
        raise ValueError("Attempt is unresolved")
    if not receipt.get("boundary", {}).get("eligible_for_review"):
        raise ValueError("Attempt is outside the review boundary")
    return task, receipt, patch


def audit_dependencies(log, declarations):
    reports = re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", log)
    if Counter(n for n, _ in reports) != Counter(declarations):
        raise ValueError("Missing, duplicate or unexpected dependency report")
    for name, dependencies in reports:
        used = {d.strip() for d in dependencies.split(",") if d.strip()}
        if used - ALLOWED_AXIOMS:
            raise ValueError(f"Disallowed dependencies for {name}: {sorted(used - ALLOWED_AXIOMS)}")


def scan(paths):
    for path in paths:
        match = FORBIDDEN.search(code_only(path.read_text()))
        if match:
            raise ValueError(f"Forbidden proof token in {path}: {match.group()}")


def replay(attempt, root, destination, modules, checks, declarations):
    attempt, root, destination = (Path(p).resolve() for p in (attempt, root, destination))
    task, receipt, patch = validate_attempt(attempt, root)
    identifier = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
    if not modules or not declarations or len(set(declarations)) != len(declarations):
        raise ValueError("Provide modules and distinct audited declarations")
    if any(not re.fullmatch(identifier, s) for s in [*modules, *declarations]):
        raise ValueError("Invalid Lean module or declaration name")
    # Read coordinator-owned checks before starting, and preserve those exact bytes.
    drivers = [(Path(p).resolve(), Path(p).read_bytes()) for p in checks]
    if not drivers:
        raise ValueError("At least one independent acceptance driver is required")
    destination.mkdir(parents=True, exist_ok=False)
    record = {"schema_version": 1, "attempt": receipt["attempt"],
              "task": task["id"], "base_commit": task["base_commit"],
              "patch_sha256": sha(patch), "receipt_sha256": sha((attempt / "receipt.json").read_bytes()),
              "checker_sha256": sha(Path(__file__).read_bytes()), "started_at": now(),
              "commands": [], "drivers": [], "declarations": declarations,
              "mechanical": "running", "semantic_review": "not_performed",
              "integration": "not_performed"}
    worktree = destination / "worktree"
    atomic_json(destination / "task.json", task)
    (destination / "candidate.patch").write_bytes(patch)
    atomic_json(destination / "result.json", record)

    def command(args, stem):
        entry = {"argv": [str(a) for a in args], "started_at": now(),
                 "log": stem + ".log", "exit_code": None, "state": "running"}
        record["commands"].append(entry)
        atomic_json(destination / "result.json", record)
        try:
            with (destination / entry["log"]).open("wb") as log:
                result = subprocess.run(entry["argv"], cwd=worktree, stdout=log, stderr=subprocess.STDOUT)
            entry.update(exit_code=result.returncode, state="completed")
        except BaseException as error:
            entry.update(state="interrupted" if isinstance(error, KeyboardInterrupt) else "launch_failed",
                         error=f"{type(error).__name__}: {error}")
            raise
        finally:
            entry["finished_at"] = now()
            atomic_json(destination / "result.json", record)
        if result.returncode:
            raise ValueError(f"{stem} failed with exit code {result.returncode}")
        return (destination / (stem + ".log")).read_text()

    def unchanged():
        actual, boundary = patch_and_boundary(worktree, task["base_commit"], task["allowed_paths"])
        for name in boundary["changed_paths"]:
            path = worktree / name
            if any(p.is_symlink() for p in [path, *path.parents] if p != worktree and worktree in p.parents):
                raise ValueError("Replayed outputs cannot depend on symbolic-link targets")
        if actual != patch or not boundary["eligible_for_review"] or changed_sources(worktree, task):
            raise ValueError("Replayed source differs from the recorded allowed patch")
        return boundary

    try:
        git(root, "worktree", "add", "--detach", str(worktree), task["base_commit"])
        command(["git", "apply", "--", destination / "candidate.patch"], "apply")
        record["boundary"] = unchanged()
        lean_sources = {worktree / "Ptx.lean", *(worktree / "Ptx").rglob("*.lean")}
        lean_sources.update(worktree / p for p in task["allowed_paths"]
                            if p.endswith(".lean") and (worktree / p).is_file())
        scan(sorted(lean_sources))
        # This is the pinned base project's checker, never the worker's build cache.
        command(["bash", "scripts/check.sh", "--clean"], "baseline")
        command(["lake", "build", *modules], "modules")
        for index, (source, data) in enumerate(drivers):
            driver = destination / f"driver-{index}.lean"
            driver.write_bytes(data)
            record["drivers"].append({"source": str(source), "copy": driver.name, "sha256": sha(data)})
            scan([driver])
            command(["lake", "env", "lean", driver], f"driver-{index}")
        audit = destination / "audit.lean"
        audit.write_text("".join(f"import {m}\n" for m in modules) +
                         "".join(f"#print axioms {d}\n" for d in declarations))
        log = command(["lake", "env", "lean", audit], "audit")
        audit_dependencies(log, declarations)
        record["boundary"] = unchanged()
        record["mechanical"] = "pass"
    except Exception as error:
        record.update(mechanical="fail", error=f"{type(error).__name__}: {error}")
    finally:
        if record["mechanical"] == "running":
            record["mechanical"] = "interrupted"
        record["finished_at"] = now()
        atomic_json(destination / "result.json", record)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("attempt", type=Path)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--module", action="append", required=True)
    parser.add_argument("--check", action="append", type=Path, required=True)
    parser.add_argument("--audit", action="append", required=True)
    args = parser.parse_args()
    result = replay(args.attempt, args.root, args.destination, args.module, args.check, args.audit)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["mechanical"] == "pass" else 1)


if __name__ == "__main__":
    main()
