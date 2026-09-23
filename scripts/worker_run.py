#!/usr/bin/env python3
"""Recorded Codex headless attempts; no automatic patch integration or acceptance.

Standard library only. A campaign invocation is reserved durably before process
launch. Worktrees isolate changes, not credentials or hostile code. The edit
boundary is a post-run review gate, not a security sandbox.
"""
import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile

CHECKPOINT = 200
MODEL = "gpt-6-luna"


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as f:
        json.dump(value, f, indent=2, ensure_ascii=False)
        f.write("\n")
        f.flush()
        os.fsync(f.fileno())
        temporary = f.name
    os.replace(temporary, path)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.PIPE)


def relative_path(value):
    path = PurePosixPath(value)
    if not isinstance(value, str) or path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError(f"Unsafe task path: {value!r}")
    if path.parts[0] in {".git", ".lake", ".formalization-runs"}:
        raise ValueError(f"Internal task path: {value!r}")
    if str(path) != value:
        raise ValueError(f"Task path must be canonical: {value!r}")
    return str(path)


def validate_task(task, root):
    if task.get("schema_version") != 1:
        raise ValueError("Unsupported task schema")
    for field in ["id", "prompt", "base_commit", "allowed_paths", "sources"]:
        if not task.get(field):
            raise ValueError(f"Missing task field: {field}")
    if not re.fullmatch(r"[0-9a-f]{40}", task["base_commit"]):
        raise ValueError("Task base must be an exact 40-character commit")
    if git(root, "rev-parse", task["base_commit"] + "^{commit}").decode().strip() != task["base_commit"]:
        raise ValueError("Unresolved base commit")
    allowed = [relative_path(p) for p in task["allowed_paths"]]
    if len(set(allowed)) != len(allowed):
        raise ValueError("Duplicate allowed path")
    # Source bytes come from the pinned commit, not uncommitted caller files.
    for source in task["sources"]:
        path = relative_path(source["path"])
        if path in allowed:
            raise ValueError(f"Pinned source cannot be an allowed output: {path}")
        data = git(root, "show", task["base_commit"] + ":" + path)
        if sha(data) != source["sha256"]:
            raise ValueError(f"Source hash mismatch: {path}")
    if task.get("model", MODEL) != MODEL:
        raise ValueError("This campaign explicitly selects gpt-6-luna")


@contextmanager
def locked(campaign):
    campaign = Path(campaign)
    campaign.mkdir(parents=True, exist_ok=True)
    with (campaign / "ledger.lock").open("a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        yield


def reserve(campaign, attempt, task, **context):
    if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", attempt):
        raise ValueError("Attempt identifier must contain lowercase letters, numbers, - or _")
    campaign = Path(campaign)
    with locked(campaign):
        path = campaign / "ledger.json"
        ledger = read_json(path) if path.exists() else {"schema_version": 1, "checkpoint": CHECKPOINT, "calls": []}
        if ledger["checkpoint"] != CHECKPOINT:
            raise ValueError("Campaign checkpoint changed; explicit review required")
        if any(c["attempt"] == attempt for c in ledger["calls"]):
            raise ValueError("Attempt already reserved; inspect it or use a new attempt identifier")
        if len(ledger["calls"]) >= CHECKPOINT:
            raise ValueError("200 calls reserved: check back with the user before call 201")
        entry = {"call": len(ledger["calls"]) + 1, "attempt": attempt,
                 "task": task["id"], "task_sha256": sha(json.dumps(task, sort_keys=True).encode()),
                 "base_commit": task["base_commit"], "reserved_at": now(), "state": "reserved", **context}
        ledger["calls"].append(entry)
        atomic_json(path, ledger)
        return entry


def update_call(campaign, attempt, **fields):
    with locked(campaign):
        path = Path(campaign) / "ledger.json"
        ledger = read_json(path)
        entry = next(c for c in ledger["calls"] if c["attempt"] == attempt)
        entry.update(fields)
        atomic_json(path, ledger)


def patch_and_boundary(worktree, base, allowed):
    changed = set(filter(None, git(worktree, "diff", "--name-only", "-z", base).decode().split("\0")))
    new = list(filter(None, git(worktree, "ls-files", "--others", "-z").decode().split("\0")))
    # Named generated-artifact exemptions, not arbitrary .gitignore rules.
    new = [p for p in new if not p.startswith(".lake/") and "__pycache__" not in PurePosixPath(p).parts]
    changed.update(new)
    patch = git(worktree, "diff", "--binary", base)
    # Include ordinary new files without staging or altering the worker checkout.
    for name in new:
        result = subprocess.run(["git", "diff", "--no-index", "--binary", "--", "/dev/null", name], cwd=worktree, capture_output=True)
        if result.returncode not in (0, 1):
            raise RuntimeError(result.stderr.decode())
        patch += result.stdout
    head = git(worktree, "rev-parse", "HEAD").decode().strip()
    return patch, {"changed_paths": sorted(changed), "outside_allowed": sorted(changed - set(allowed)),
                   "head_unchanged": head == base, "head": head,
                   "eligible_for_review": not (changed - set(allowed)) and head == base}


def event_summary(path):
    events, errors, usage, models, sessions = 0, 0, [], set(), set()
    for line in Path(path).read_text(errors="replace").splitlines():
        try:
            event = json.loads(line)
        except ValueError:
            errors += 1
            continue
        if not isinstance(event, dict):
            errors += 1
            continue
        events += 1
        if event.get("type") == "thread.started" and isinstance(event.get("thread_id"), str):
            sessions.add(event["thread_id"])
        if event.get("usage") is not None:
            usage.append(event["usage"])
        if isinstance(event.get("model"), str):
            models.add(event["model"])
    return {"event_count": events, "non_json_lines": errors, "reported_usage": usage,
            "reported_models": sorted(models), "reported_session_ids": sorted(sessions)}


def changed_sources(worktree, task):
    return [s["path"] for s in task["sources"]
            if not (worktree / s["path"]).is_file() or
            sha((worktree / s["path"]).read_bytes()) != s["sha256"]]


@contextmanager
def worktree_locked(campaign, worktree):
    directory = Path(campaign) / "worktree-locks"
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / (sha(str(worktree.resolve()).encode()) + ".lock")).open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError("Worktree is already in use by another invocation") from None
        yield


def task_prompt(task):
    return ("Work on the following bounded PTXLean task. Do not commit, prepare Stratic reviews, "
            "or modify files outside the task's allowed paths; the coordinator handles integration. "
            "Do not change theorem obligations or shared semantics to make a proof pass. "
            "If a prerequisite is missing, report it explicitly. No external model calls.\n\n" +
            task["prompt"] + "\n\nAllowed paths:\n" + "\n".join(task["allowed_paths"]) +
            "\n\nPinned source inputs:\n" + "\n".join(s["path"] for s in task["sources"]) + "\n")


def new_attempt(campaign, attempt, task, prompt):
    if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", attempt):
        raise ValueError("Invalid attempt identifier")
    directory = campaign / "attempts" / attempt
    if directory.exists():
        raise ValueError("Attempt directory already exists; never overwrite a previous run")
    directory.mkdir(parents=True)
    atomic_json(directory / "task.json", task)
    (directory / "prompt.md").write_text(prompt)
    return directory


def dispatch(task, campaign, attempt, directory, worktree, prompt, command, **context):
    entry = reserve(campaign, attempt, task, worktree=str(worktree), **context)
    runner_bytes = Path(__file__).read_bytes()
    (directory / "runner.py").write_bytes(runner_bytes)
    receipt = {**entry, "requested_model": MODEL, "command": command, "worktree": str(worktree),
               "prompt_sha256": sha(prompt.encode()), "runner_sha256": sha(runner_bytes),
               "started_at": now(), "state": "started", **context}
    atomic_json(directory / "receipt.json", receipt)
    update_call(campaign, attempt, state="started", started_at=receipt["started_at"])
    environment = dict(os.environ)
    for key in ["OPENAI_API_KEY", "CODEX_API_KEY"]:
        environment.pop(key, None)
    try:
        with (directory / "events.jsonl").open("wb") as stdout, (directory / "stderr.log").open("wb") as stderr:
            result = subprocess.run(command, input=prompt.encode(), stdout=stdout, stderr=stderr, env=environment, cwd=worktree)
        receipt.update(exit_code=result.returncode, state="completed" if result.returncode == 0 else "failed")
    except BaseException as error:
        receipt.update(state="interrupted" if isinstance(error, KeyboardInterrupt) else "failed", error=f"{type(error).__name__}: {error}")
        raise
    finally:
        receipt["finished_at"] = now()
        if (directory / "events.jsonl").exists():
            try:
                receipt.update(event_summary(directory / "events.jsonl"))
            except Exception as error:
                receipt["event_capture_error"] = str(error)
        try:
            patch, boundary = patch_and_boundary(worktree, task["base_commit"], task["allowed_paths"])
            (directory / "candidate.patch").write_bytes(patch)
            altered_sources = changed_sources(worktree, task)
            boundary["altered_sources"] = altered_sources
            boundary["eligible_for_review"] = boundary["eligible_for_review"] and not altered_sources
            expected_session = context.get("resumed_session_id")
            if expected_session and receipt.get("reported_session_ids"):
                matches = receipt["reported_session_ids"] == [expected_session]
                receipt["session_matches_requested"] = matches
                boundary["eligible_for_review"] = boundary["eligible_for_review"] and matches
            receipt.update(boundary=boundary, patch_sha256=sha(patch))
        except Exception as error:
            receipt["capture_error"] = str(error)
        receipt["acceptance"] = "not_reviewed"
        atomic_json(directory / "receipt.json", receipt)
        update_call(campaign, attempt, state=receipt["state"], finished_at=receipt["finished_at"])
    return receipt



def execute(task_file, root, campaign, attempt, executable="codex"):
    root, campaign = Path(root).resolve(), Path(campaign).resolve()
    task = read_json(task_file)
    validate_task(task, root)
    prompt = task_prompt(task)
    directory = new_attempt(campaign, attempt, task, prompt)
    worktree = directory / "worktree"
    git(root, "worktree", "add", "--detach", str(worktree), task["base_commit"])
    command = [executable, "exec", "--ignore-user-config", "--model", MODEL,
               "--approve-for-me", "--json", "--cd", str(worktree),
               "--output-last-message", str(directory / "final.md"), "-"]
    with worktree_locked(campaign, worktree):
        return dispatch(task, campaign, attempt, directory, worktree, prompt, command)


def resume(root, campaign, attempt, resume_from, feedback_file, executable="codex"):
    root, campaign = Path(root).resolve(), Path(campaign).resolve()
    if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", resume_from):
        raise ValueError("Invalid prior attempt identifier")
    previous_dir = campaign / "attempts" / resume_from
    previous = read_json(previous_dir / "receipt.json")
    task = read_json(previous_dir / "task.json")
    validate_task(task, root)
    if previous.get("task_sha256") != sha(json.dumps(task, sort_keys=True).encode()):
        raise ValueError("Prior task record changed")
    if previous.get("state") not in {"completed", "failed", "interrupted"} or not previous.get("finished_at"):
        raise ValueError("Prior invocation is unresolved; inspect it before resuming")
    worktree = Path(previous["worktree"]).resolve()
    feedback = Path(feedback_file).read_text()
    if not feedback.strip():
        raise ValueError("Resume feedback must not be empty")
    with worktree_locked(campaign, worktree):
        # The same checkout has one linear invocation history. Reject a stale parent
        # even if a later run happened to leave identical file contents.
        with locked(campaign):
            calls = read_json(campaign / "ledger.json")["calls"]
            related = []
            for call in calls:
                recorded_worktree = call.get("worktree")
                if recorded_worktree is None:
                    old_receipt = campaign / "attempts" / call["attempt"] / "receipt.json"
                    if old_receipt.exists():
                        recorded_worktree = read_json(old_receipt).get("worktree")
                if recorded_worktree and Path(recorded_worktree).resolve() == worktree:
                    related.append(call)
            if not related or related[-1]["attempt"] != resume_from:
                raise ValueError("Resume must select the latest recorded invocation for this worktree")
            if related[-1]["state"] not in {"completed", "failed", "interrupted"}:
                raise ValueError("Prior ledger entry is unresolved; inspect it before resuming")
        saved_patch = (previous_dir / "candidate.patch").read_bytes()
        if sha(saved_patch) != previous.get("patch_sha256"):
            raise ValueError("Prior patch record changed")
        actual_patch, boundary = patch_and_boundary(worktree, task["base_commit"], task["allowed_paths"])
        if actual_patch != saved_patch or not boundary["head_unchanged"]:
            raise ValueError("Worktree does not match the prior recorded patch and commit")
        if not boundary["eligible_for_review"] or changed_sources(worktree, task):
            raise ValueError("Prior worktree violates its edit or pinned-source boundary")
        sessions = event_summary(previous_dir / "events.jsonl")["reported_session_ids"]
        if len(sessions) != 1:
            raise ValueError("Prior output must identify exactly one Codex session")
        session = sessions[0]
        prompt = (task_prompt(task) + "\nContinue the recorded attempt " + resume_from +
                  ". Preserve its task obligations and finish the requested repair.\n\nFeedback:\n" + feedback)
        directory = new_attempt(campaign, attempt, task, prompt)
        (directory / "feedback.md").write_text(feedback)
        command = [executable, "exec", "--approve-for-me", "--cd", str(worktree), "resume",
                   "--ignore-user-config", "--model", MODEL, "--json",
                   "--output-last-message", str(directory / "final.md"), session, "-"]
        return dispatch(task, campaign, attempt, directory, worktree, prompt, command,
                        resume_from=resume_from, resumed_session_id=session,
                        previous_patch_sha256=sha(saved_patch), feedback_sha256=sha(feedback.encode()))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    run = sub.add_parser("run")
    run.add_argument("task", type=Path, nargs="?")
    run.add_argument("--resume-from", help="Resume this campaign attempt with its original task and worktree")
    run.add_argument("--feedback", type=Path, help="Feedback file required with --resume-from")
    run.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    run.add_argument("--campaign", type=Path, required=True)
    run.add_argument("--attempt", required=True)
    status = sub.add_parser("status")
    status.add_argument("--campaign", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "status":
        path = args.campaign / "ledger.json"
        print(json.dumps(read_json(path) if path.exists() else {"calls": []}, indent=2))
    else:
        if args.resume_from:
            if args.task is not None or args.feedback is None:
                parser.error("--resume-from requires --feedback and does not accept a new task file")
            result = resume(args.root, args.campaign, args.attempt, args.resume_from, args.feedback)
        else:
            if args.task is None or args.feedback is not None:
                parser.error("A task file is required for a fresh run; --feedback requires --resume-from")
            result = execute(args.task, args.root, args.campaign, args.attempt)
        print(json.dumps(result, indent=2))
        if result.get("exit_code") != 0:
            sys.exit(1)


if __name__ == "__main__":
    main()
