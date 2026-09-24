#!/usr/bin/env python3
"""Prepare pinned worker prerequisites, then revalidate and dispatch one recorded call."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import uuid

import worker_run as runner
from worker_project import provision_dependencies, verify_dependencies, plain_destination


def digest(path):
    return runner.sha(Path(path).read_bytes())


def helper_hashes():
    return {name: digest(Path(__file__).with_name(name)) for name in
            ["worker_provision.py", "worker_project.py", "worker_run.py"]}


def attempt_path(campaign, attempt):
    if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", attempt):
        raise ValueError("Invalid attempt identifier")
    return Path(campaign).resolve() / "attempts" / attempt


def snapshot(worktree, task):
    patch, boundary = runner.patch_and_boundary(worktree, task["base_commit"],
                                               task["allowed_paths"], runner.replay_project(task),
                                               runner.local_source_paths(task))
    if not boundary["eligible_for_review"] or runner.changed_sources(worktree, task):
        raise ValueError("Worktree violates immutable source or edit boundary")
    return patch


def artifact_hashes(worktree, project, dependencies):
    """Hash generated prerequisite bytes, including dependency build artifacts.

    Source revisions are checked separately. No build artifact is interpreted as
    candidate proof acceptance, and fresh replay never reuses these caches.
    """
    roots = {worktree, worktree / project, *(Path(d["destination"]) for d in dependencies)}
    files = set()
    for root in roots:
        directory = root / ".lake/build"
        plain_destination(directory, worktree)
        if directory.exists():
            files.update(p for p in directory.rglob("*") if p.is_file() or p.is_symlink())
        lake = root / ".lake"
        if lake.exists():
            files.update(p for p in lake.iterdir() if p.is_file() or p.is_symlink())
    result = {}
    for path in sorted(files):
        plain_destination(path, worktree)
        if not path.is_file():
            raise ValueError(f"Nonregular prerequisite artifact: {path}")
        result[str(path.relative_to(worktree))] = digest(path)
    return result


def command_recorder(directory, record, phase, worktree, filename):
    def save():
        runner.atomic_json(directory / filename, record)

    def command(args, stem, cwd=None, allow_failure=False):
        entry = {"argv": [str(a) for a in args], "cwd": str(cwd or worktree),
                 "state": "running", "started_at": runner.now(), "exit_code": None,
                 "log": f"phase-{phase}-{len(record['commands']):03d}-{stem}.log"}
        record["commands"].append(entry)
        save()
        try:
            with (directory / entry["log"]).open("wb") as log:
                result = subprocess.run(entry["argv"], cwd=entry["cwd"], stdout=log,
                                        stderr=subprocess.STDOUT)
            entry.update(state="completed", exit_code=result.returncode)
        except BaseException as error:
            entry.update(state="interrupted" if isinstance(error, KeyboardInterrupt) else "failed",
                         error=f"{type(error).__name__}: {error}")
            raise
        finally:
            entry["finished_at"] = runner.now()
            entry["log_sha256"] = digest(directory / entry["log"])
            save()
        if result.returncode and not allow_failure:
            raise ValueError(f"{stem} failed with exit code {result.returncode}")
        return (directory / entry["log"]).read_text()
    return command, save


def validate_plan(directory, root):
    plan = runner.read_json(directory / "plan.json")
    record = runner.read_json(directory / "preparation.json")
    if record["plan_sha256"] != digest(directory / "plan.json"):
        raise ValueError("Provisioning plan changed")
    if plan["helpers"] != helper_hashes():
        raise ValueError("Provisioning helper version changed; prepare a new attempt")
    for name, expected in plan["helpers"].items():
        if digest(directory / "provisioner" / name) != expected:
            raise ValueError("Saved provisioning helper changed")
    task = runner.read_json(directory / "task.json")
    runner.validate_task(task, root)
    if digest(directory / "task.json") != plan["task_sha256"]:
        raise ValueError("Prepared task changed")
    if digest(directory / "prompt.md") != plan["prompt_sha256"]:
        raise ValueError("Prepared prompt changed")
    info = runner.project_inputs(task, root, require_root=True)
    if info != plan["project_inputs"]:
        raise ValueError("Pinned project inputs changed")
    worktree = Path(plan["worktree"])
    if worktree.resolve() != worktree:
        raise ValueError("Prepared worktree path changed")
    for name, expected in plan.get("parent_records", {}).items():
        if digest(Path(plan["campaign"]) / "attempts" / plan["resume_from"] / name) != expected:
            raise ValueError("Prepared repair parent record changed")
    if plan.get("resume_from"):
        if digest(directory / "feedback.md") != plan["context"]["feedback_sha256"]:
            raise ValueError("Prepared feedback changed")
        checked_task, checked_tree, prompt, _, context = runner.resume_preflight(
            root, Path(plan["campaign"]), plan["resume_from"], directory / "feedback.md")
        if (checked_task, checked_tree, prompt, context) != (task, worktree,
                (directory / "prompt.md").read_text(), plan["context"]):
            raise ValueError("Prepared repair parent changed")
    return plan, record, task, worktree


def prepare(task_file, root, campaign, attempt, modules=(), resume_from=None, feedback_file=None):
    root, campaign = Path(root).resolve(), Path(campaign).resolve()
    if resume_from:
        if task_file is not None or feedback_file is None:
            raise ValueError("Repair preparation needs feedback and inherits its task")
        worktree = runner.resume_worktree(campaign, resume_from)
    else:
        if task_file is None or feedback_file is not None:
            raise ValueError("Fresh preparation requires a task, without repair feedback")
        worktree = attempt_path(campaign, attempt) / "worktree"
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", m)
           for m in modules):
        raise ValueError("Invalid prerequisite module name")
    with runner.worktree_locked(campaign, worktree):
        if resume_from:
            task, checked_tree, prompt, feedback, context = runner.resume_preflight(
                root, campaign, resume_from, feedback_file)
            if checked_tree != worktree:
                raise ValueError("Repair worktree changed")
        else:
            task = runner.read_json(task_file)
            runner.validate_task(task, root)
            prompt, feedback, context = runner.task_prompt(task), None, {}
        info = runner.project_inputs(task, root, require_root=True)
        directory = runner.new_attempt(campaign, attempt, task, prompt)
        if feedback is not None:
            (directory / "feedback.md").write_text(feedback)
        helpers = helper_hashes()
        (directory / "provisioner").mkdir()
        for name in helpers:
            (directory / "provisioner" / name).write_bytes(Path(__file__).with_name(name).read_bytes())
        plan = {"schema_version": 1, "attempt": attempt, "campaign": str(campaign),
                "worktree": str(worktree), "base_commit": task["base_commit"],
                "task_sha256": digest(directory / "task.json"),
                "prompt_sha256": digest(directory / "prompt.md"), "helpers": helpers,
                "project_inputs": info, "modules": list(modules),
                "resume_from": resume_from, "context": context, "created_at": runner.now(),
                "parent_records": {name: digest(campaign / "attempts" / resume_from / name)
                    for name in ["receipt.json", "task.json", "candidate.patch", "events.jsonl"]}
                    if resume_from else {}}
        runner.atomic_json(directory / "plan.json", plan)
        runner.atomic_json(directory / "preparation.json", {
            "schema_version": 1, "plan_sha256": digest(directory / "plan.json"),
            "state": "pending", "commands": [], "phases": []})
        return _prepare(directory, root)


def retry(root, campaign, attempt):
    directory = attempt_path(campaign, attempt)
    plan = runner.read_json(directory / "plan.json")
    with runner.worktree_locked(Path(campaign).resolve(), Path(plan["worktree"])):
        return _prepare(directory, Path(root).resolve())


def _prepare(directory, root):
    plan, record, task, worktree = validate_plan(directory, root)
    if record["state"] == "ready" or (directory / "receipt.json").exists():
        raise ValueError("Preparation already ready or attempt dispatched")
    phase = len(record["phases"]) + 1
    record["phases"].append({"phase": phase, "started_at": runner.now(), "state": "running",
                             "previous_state": record["state"]})
    record["state"] = "preparing"
    record.pop("error", None)
    command, save = command_recorder(directory, record, phase, worktree, "preparation.json")
    save()
    try:
        if not worktree.exists():
            command(["git", "worktree", "add", "--detach", str(worktree), task["base_commit"]],
                    "worktree", cwd=root)
        runner.install_local_sources(root, worktree, task)
        current = snapshot(worktree, task)
        prior = directory / "prepared.patch"
        if prior.exists():
            if record.get("prepared_patch_sha256") != digest(prior):
                raise ValueError("Preparation patch record changed")
            if prior.read_bytes() != current:
                raise ValueError("Prepared candidate patch changed")
        else:
            if not plan["resume_from"] and current:
                raise ValueError("Fresh checkout unexpectedly has candidate changes")
            prior.write_bytes(current)
            record["prepared_patch_sha256"] = digest(prior)
            save()
        project = plan["project_inputs"]["path"]
        info = plan["project_inputs"]
        versions = {tool: command([tool, "--version"], tool + "-version", cwd=worktree / project)
                    for tool in ["lake", "lean"]}
        expected = info["toolchain"].split(":v", 1)[1]
        if not all(re.search(r"(?<![0-9.])" + re.escape(expected) + r"(?![0-9.])", v)
                   for v in versions.values()):
            raise ValueError("Installed tool version does not match pinned toolchain")
        provision_dependencies(root, worktree, project, info, record, command, save, reuse=True)
        command(["lake", "build", *plan["modules"]], "prerequisites", cwd=worktree / project)
        verify_dependencies(record["dependency_checkouts"], worktree)
        if snapshot(worktree, task) != current:
            raise ValueError("Provisioning changed the prepared source or candidate patch")
        artifacts = artifact_hashes(worktree, project, record["dependency_checkouts"])
        record["phases"][-1].update(state="ready", finished_at=runner.now())
        ready = {"schema_version": 1, "plan_sha256": digest(directory / "plan.json"),
                 "patch_sha256": digest(prior), "versions": versions,
                 "dependency_checkouts": record["dependency_checkouts"], "artifacts": artifacts,
                 "commands": record["commands"], "phases": record["phases"], "ready_at": runner.now()}
        runner.atomic_json(directory / "ready.json", ready)
        record.update(state="ready", ready_sha256=digest(directory / "ready.json"))
    except BaseException as error:
        state = "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"
        record.update(state=state, error=f"{type(error).__name__}: {error}")
        record["phases"][-1].update(state=state, error=record["error"], finished_at=runner.now())
        if not isinstance(error, Exception):
            raise
    finally:
        save()
    return record


def _run(root, campaign, attempt, executable="codex"):
    root, campaign = Path(root).resolve(), Path(campaign).resolve()
    directory = attempt_path(campaign, attempt)
    initial = runner.read_json(directory / "plan.json")
    with runner.worktree_locked(campaign, Path(initial["worktree"])):
        plan, preparation, task, worktree = validate_plan(directory, root)
        if worktree != Path(initial["worktree"]):
            raise ValueError("Prepared checkout lock target changed")
        if plan["campaign"] != str(campaign) or plan["attempt"] != attempt:
            raise ValueError("Prepared attempt location changed")
        if preparation["state"] != "ready":
            raise ValueError("Preparation is not ready")
        if (directory / "run.json").exists() or (directory / "receipt.json").exists():
            raise ValueError("Dispatch already recorded; inspect it, never repeat it")
        if digest(directory / "ready.json") != preparation["ready_sha256"]:
            raise ValueError("Ready manifest changed")
        ready = runner.read_json(directory / "ready.json")
        if ready["plan_sha256"] != digest(directory / "plan.json"):
            raise ValueError("Ready manifest belongs to another plan")
        if ready["patch_sha256"] != digest(directory / "prepared.patch") or \
                runner.sha(snapshot(worktree, task)) != ready["patch_sha256"]:
            raise ValueError("Prepared candidate patch changed")
        verify_dependencies(ready["dependency_checkouts"], worktree)
        project = plan["project_inputs"]["path"]
        if artifact_hashes(worktree, project, ready["dependency_checkouts"]) != ready["artifacts"]:
            raise ValueError("Prerequisite build artifacts changed")
        for entry in ready["commands"]:
            if digest(directory / entry["log"]) != entry["log_sha256"]:
                raise ValueError("Preparation command log changed")
        for tool, expected in ready["versions"].items():
            actual = subprocess.check_output([tool, "--version"], cwd=worktree / project,
                                              stderr=subprocess.STDOUT).decode()
            if actual != expected:
                raise ValueError("Prepared tool version changed")
        # Tool-version probes are processes too: recheck after they return.
        if runner.sha(snapshot(worktree, task)) != ready["patch_sha256"]:
            raise ValueError("Prepared candidate changed during tool verification")
        verify_dependencies(ready["dependency_checkouts"], worktree)
        if artifact_hashes(worktree, project, ready["dependency_checkouts"]) != ready["artifacts"]:
            raise ValueError("Prerequisite artifacts changed during tool verification")
        state = {"state": "dispatching", "started_at": runner.now(),
                 "ready_sha256": preparation["ready_sha256"]}
        runner.atomic_json(directory / "run.json", state)
        try:
            command = runner.headless_command(executable, worktree, directory,
                                               plan["context"].get("resumed_session_id"))
            try:
                receipt = runner.dispatch(task, campaign, attempt, directory, worktree,
                    (directory / "prompt.md").read_text(), command,
                    provisioning_sha256=preparation["ready_sha256"], **plan["context"])
            finally:
                # Even an interrupted/failed process can have modified prerequisites.
                if (directory / "receipt.json").exists():
                    receipt = runner.read_json(directory / "receipt.json")
                    try:
                        verify_dependencies(ready["dependency_checkouts"], worktree)
                    except Exception as error:
                        receipt["provisioning_drift"] = str(error)
                        receipt.setdefault("boundary", {})["eligible_for_review"] = False
                        runner.atomic_json(directory / "receipt.json", receipt)
            state.update(state=receipt["state"], finished_at=runner.now())
            return receipt
        except BaseException as error:
            state.update(state="interrupted" if isinstance(error, KeyboardInterrupt) else "failed",
                         error=f"{type(error).__name__}: {error}", finished_at=runner.now())
            raise
        finally:
            runner.atomic_json(directory / "run.json", state)


def run(root, campaign, attempt, executable="codex"):
    """Preserve rejected preflight attempts too, without reserving a model call."""
    directory = attempt_path(campaign, attempt)
    if not directory.is_dir():
        raise ValueError("No prepared attempt exists")
    path = directory / ("run-check-" + uuid.uuid4().hex + ".json")
    record = {"state": "validating", "started_at": runner.now(), "attempt": attempt}
    runner.atomic_json(path, record)
    try:
        receipt = _run(root, campaign, attempt, executable)
        record.update(state="dispatched", receipt_sha256=digest(directory / "receipt.json"))
        return receipt
    except BaseException as error:
        record.update(state="interrupted" if isinstance(error, KeyboardInterrupt) else "rejected_or_failed",
                      error=f"{type(error).__name__}: {error}")
        raise
    finally:
        record["finished_at"] = runner.now()
        runner.atomic_json(path, record)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ["prepare", "retry", "run"]:
        command = sub.add_parser(name)
        command.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
        command.add_argument("--campaign", type=Path, required=True)
        command.add_argument("--attempt", required=True)
        if name == "prepare":
            command.add_argument("task", type=Path, nargs="?")
            command.add_argument("--resume-from")
            command.add_argument("--feedback", type=Path)
            command.add_argument("--module", action="append", default=[])
        if name == "run":
            command.add_argument("--codex", default="codex")
    args = parser.parse_args()
    if args.command == "prepare":
        result = prepare(args.task, args.root, args.campaign, args.attempt,
                         args.module, args.resume_from, args.feedback)
    elif args.command == "retry":
        result = retry(args.root, args.campaign, args.attempt)
    else:
        result = run(args.root, args.campaign, args.attempt, args.codex)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["state"] in {"ready", "completed"} else 1)


if __name__ == "__main__":
    main()
