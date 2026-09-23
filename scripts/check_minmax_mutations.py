#!/usr/bin/env python3
"""Offline, proof-preserving seeded-defect checks for a recorded min/max candidate.

No model invocation, automatic integration, or checkout cleanup is performed.
A nonzero build or an unrelated acceptance failure never counts as detection.
"""
import argparse
import datetime
import difflib
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def save_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"Expected exactly one mutation anchor: {old!r}")
    return text.replace(old, new, 1)


def remove_supported_max(files):
    text = files["Ptx/ScalarText.lean"]
    start = text.index("def supportedMnemonic")
    end = text.index("def decodeOp", start)
    section = replace_once(text[start:end], '"min.u32", "max.u32",', '"min.u32",')
    return {"Ptx/ScalarText.lean": text[:start] + section + text[end:]}


def swap_text_meanings(files):
    text = files["Ptx/ScalarText.lean"]
    text = replace_once(text, '| .minU => "min.u32"', '| .minU => "max.u32"')
    text = replace_once(text, '| .maxU => "max.u32"', '| .maxU => "min.u32"')
    text = replace_once(text,
        '| "min.u32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .minU d a b)',
        '| "min.u32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .maxU d a b)')
    text = replace_once(text,
        '| "max.u32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .maxU d a b)',
        '| "max.u32", [.word (.reg d), .word a, .word b] => .ok (.bin32 .minU d a b)')
    own = files["Ptx/IntegerMinMax.lean"]
    # Alter only the two worker-authored decoder assertions. Arithmetic and
    # execution theorems, required numerical signatures and all other examples stay.
    pattern = re.compile(r'(example : decodeOp "(min|max)\.u32"[^\n]*\n\s*\.ok \(\.bin32 \.)'
        r'(minU|maxU)([^\n]*\n)')
    matches = list(pattern.finditer(own))
    if len(matches) != 2 or {m[2] for m in matches} != {"min", "max"}:
        raise ValueError("Expected the worker's two direct decoder examples")
    own = pattern.sub(lambda m: m[1] + {"minU": "maxU", "maxU": "minU"}[m[3]] + m[4], own)
    return {"Ptx/ScalarText.lean": text, "Ptx/IntegerMinMax.lean": own}


REGIONS = {
    "remove-supported-max": [
        ('max-invalid-category', 'example : decodeOp "max.u32" [.word (.reg 0), .address (.reg 1), .word (.imm 7)] ='),
        ('max-invalid-arity', 'example : decodeOp "max.u32" [.word (.reg 0), .word (.reg 1), .word (.imm 7), .word (.imm 8)] ='),
    ],
    "swap-text-meanings": [
        ('decode-min', 'example : decode ⟨.pred 1 false, "min.u32",'),
        ('decode-max', 'example : decodeOp "max.u32" [.word (.reg 0), .word (.imm 0xffffffff),'),
        ('encode-min', 'example : encode (.plain (.bin32 .minU'),
        ('encode-max', 'example : encode (.plain (.bin32 .maxU'),
    ],
}


def regions(driver, mutation):
    lines = driver.splitlines()
    result = []
    for identifier, prefix in REGIONS[mutation]:
        indexes = [i for i, line in enumerate(lines) if line.startswith(prefix)]
        if len(indexes) != 1:
            raise ValueError(f"Missing or ambiguous independent check: {identifier}")
        start = indexes[0]
        end = start
        while end + 1 < len(lines) and lines[end + 1].strip() and not lines[end + 1].startswith("example :"):
            end += 1
        result.append({"id": identifier, "start_line": start + 1, "end_line": end + 1})
    return result


def expected_rejection(output, driver_path, expected):
    pattern = re.compile(re.escape(str(driver_path)) + r":(\d+):(\d+): error:([^\n]*)")
    matches = list(pattern.finditer(output))
    errors = []
    detected = set()
    valid = bool(matches)
    # All error diagnostics, including ones in unexpected files, must be explained.
    if len(re.findall(r":\d+:\d+: error:", output)) != len(matches):
        valid = False
    for i, match in enumerate(matches):
        line = int(match[1])
        end = matches[i + 1].start() if i + 1 < len(matches) else len(output)
        diagnostic = output[match.end():end]
        checks = [r["id"] for r in expected if r["start_line"] <= line <= r["end_line"]]
        # Compilation/proof-consistency failures and unrelated elaboration errors
        # do not satisfy this deliberately narrow rejection criterion.
        false_decision = "decide" in (match[3] + diagnostic) and "false" in (match[3] + diagnostic)
        valid = valid and len(checks) == 1 and false_decision
        detected.update(checks)
        errors.append({"line": line, "column": int(match[2]), "checks": checks,
                       "header": match[3].strip(), "false_decision": false_decision})
    required = {r["id"] for r in expected}
    return valid and detected == required, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--task", type=Path, required=True)
    parser.add_argument("--patch", type=Path, required=True)
    parser.add_argument("--driver", type=Path, default=Path("formalization/checks/minmax-u32.lean"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--worktree", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    task_path, patch_path, driver_path = [p.resolve() for p in (args.task, args.patch, args.driver)]
    output = args.output.resolve()
    worktree = args.worktree.resolve() if args.worktree else root / ".formalization-runs/review-probes" / output.name
    if output.exists() or worktree.exists():
        parser.error("Output and worktree must be fresh; prior evidence is never overwritten")
    task = json.loads(task_path.read_text())
    base = task["base_commit"]
    if not re.fullmatch(r"[0-9a-f]{40}", base):
        parser.error("Task must pin a complete base commit")
    output.mkdir(parents=True)
    shutil.copyfile(task_path, output / "task.json")
    shutil.copyfile(patch_path, output / "candidate.patch")
    shutil.copyfile(driver_path, output / "acceptance.lean")
    shutil.copyfile(Path(__file__), output / "harness.py")
    driver = output / "acceptance.lean"
    report = {"schema": "ptxlean.minmax-review-probes/v1", "started_at": now(),
              "base_commit": base, "worktree": str(worktree), "model_calls": 0,
              "invocation": [sys.executable, *sys.argv], "invocation_cwd": str(Path.cwd()),
              "script_sha256": sha(Path(__file__).read_bytes()),
              "candidate_patch_sha256": sha(patch_path.read_bytes()),
              "task_sha256": sha(task_path.read_bytes()), "driver_sha256": sha(driver.read_bytes()),
              "sources": task["sources"], "commands": [], "cases": [], "outcome": "incomplete",
              "limits": "Two hand-designed defects in one candidate; no general detection-rate or semantic-completeness claim."}

    def command(name, argv, cwd):
        start = now()
        result = subprocess.run(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (output / (name + ".stdout.log")).write_bytes(result.stdout)
        (output / (name + ".stderr.log")).write_bytes(result.stderr)
        record = {"name": name, "argv": [str(a) for a in argv], "cwd": str(cwd),
                  "started_at": start, "finished_at": now(), "returncode": result.returncode,
                  "stdout": name + ".stdout.log", "stderr": name + ".stderr.log"}
        report["commands"].append(record)
        save_json(output / "report.json", report)
        return result

    try:
        for source in task["sources"]:
            got = subprocess.run(["git", "show", f"{base}:{source['path']}"], cwd=root,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
            if sha(got) != source["sha256"]:
                raise ValueError(f"Pinned source mismatch: {source['path']}")
        created = command("setup-worktree", ["git", "worktree", "add", "--detach", str(worktree), base], root)
        if created.returncode:
            raise RuntimeError("Could not create isolated checkout")
        report["lean_toolchain"] = (worktree / "lean-toolchain").read_text().strip()
        version = command("setup-lean-version", ["lake", "env", "lean", "--version"], worktree)
        if version.returncode:
            raise RuntimeError("Could not inspect pinned Lean environment")
        applied = command("setup-apply", ["git", "apply", str(output / "candidate.patch")], worktree)
        if applied.returncode:
            raise RuntimeError("Recorded patch could not be applied")
        for source in task["sources"]:
            if sha((worktree / source["path"]).read_bytes()) != source["sha256"]:
                raise ValueError(f"Candidate changed pinned source: {source['path']}")
        originals = {name: (worktree / name).read_text() for name in
                     ["Ptx/Scalar.lean", "Ptx/ScalarText.lean", "Ptx/IntegerMinMax.lean"]}
        report["candidate_files"] = {name: sha(text.encode()) for name, text in originals.items()}
        for name, mutate in [("control", None), ("remove-supported-max", remove_supported_max),
                             ("swap-text-meanings", swap_text_meanings)]:
            changes = mutate(originals) if mutate else {}
            for path, content in originals.items():
                (worktree / path).write_text(changes.get(path, content))
            patch = "".join("".join(difflib.unified_diff(originals[p].splitlines(True), content.splitlines(True),
                       fromfile="a/" + p, tofile="b/" + p)) for p, content in changes.items())
            (output / (name + ".mutation.patch")).write_text(patch)
            case = {"id": name, "mutation_patch": name + ".mutation.patch", "mutation_sha256": sha(patch.encode()),
                    "changed_files": {p: {"before": sha(originals[p].encode()), "after": sha(s.encode())}
                                      for p, s in changes.items()}, "outcome": "inconclusive"}
            report["cases"].append(case)
            build = command(name + "-build", ["lake", "build", "Ptx.IntegerMinMax"], worktree)
            case["module_build_returncode"] = build.returncode
            if build.returncode:
                raise RuntimeError(f"{name}: own module/proofs did not build; not a semantic detection")
            checked = command(name + "-acceptance", ["lake", "env", "lean", str(driver)], worktree)
            case["acceptance_returncode"] = checked.returncode
            if mutate is None:
                if checked.returncode:
                    raise RuntimeError("Unchanged positive control failed independent checks")
                case["outcome"] = "pass"
            else:
                expected = regions(driver.read_text(), name)
                detected, diagnostics = expected_rejection(
                    (checked.stdout + checked.stderr).decode(errors="replace"), driver, expected)
                case.update(expected_checks=expected, diagnostics=diagnostics)
                if checked.returncode != 1 or not detected:
                    raise RuntimeError(f"{name}: missing expected false-proposition rejection or unexpected errors")
                case["outcome"] = "detected"
        report["outcome"] = "pass"
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        report["outcome"] = "fail"
        report["error"] = str(error)
    finally:
        report["finished_at"] = now()
        report["artifacts"] = {p.name: sha(p.read_bytes()) for p in sorted(output.iterdir())
                               if p.is_file() and p.name != "report.json"}
        save_json(output / "report.json", report)
    print(json.dumps({"outcome": report["outcome"], "report": str(output / "report.json"),
                      "cases": [{"id": c["id"], "outcome": c["outcome"]} for c in report["cases"]]}, indent=2))
    return 0 if report["outcome"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
