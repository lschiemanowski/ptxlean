"""Shared exact-revision dependency setup for worker preparation and fresh replay."""
from pathlib import Path, PurePosixPath
import subprocess

from worker_run import git


def plain_destination(path, worktree):
    path, worktree = Path(path), Path(worktree)
    if not path.is_relative_to(worktree):
        raise ValueError("Dependency destination escaped worktree")
    if any(p.is_symlink() for p in [path, *path.parents]
           if p != worktree and worktree in p.parents):
        raise ValueError("Dependency destination cannot use symbolic links")


def verify_dependencies(dependencies, worktree):
    for dependency in dependencies:
        target = Path(dependency["destination"])
        plain_destination(target, worktree)
        metadata = target / ".git"
        if not metadata.is_dir() or metadata.is_symlink():
            raise ValueError("Dependency must have independent Git metadata")
        common = Path(git(target, "rev-parse", "--git-common-dir").decode().strip())
        if not common.is_absolute():
            common = target / common
        if common.resolve() != metadata.resolve():
            raise ValueError("Dependency Git metadata is shared")
        if git(target, "rev-parse", "HEAD").decode().strip() != dependency["revision"]:
            raise ValueError(f"Dependency HEAD changed: {dependency['name']}")
        if git(target, "remote", "get-url", "origin").decode().strip() != dependency["url"]:
            raise ValueError(f"Dependency origin changed: {dependency['name']}")
        if git(target, "status", "--porcelain", "--untracked-files=no").strip():
            raise ValueError(f"Dependency tracked sources changed: {dependency['name']}")
        untracked = git(target, "ls-files", "--others", "-z").decode().split("\0")
        extra = [p for p in untracked if p and not p.startswith(".lake/")
                 and "__pycache__" not in PurePosixPath(p).parts]
        if extra:
            raise ValueError(f"Dependency untracked sources changed: {dependency['name']}: {extra}")


def provision_dependencies(root, worktree, project, project_info, record, command, save,
                           reuse=False):
    """Copy only Git objects; never copy a coordinator/worker compiled cache.

    command records argv/cwd/status before execution. Reuse only accepts exact,
    clean recorded-revision source trees; incomplete clones are not reset.
    """
    project_cwd = worktree / project
    record["dependency_checkouts"] = []
    for dependency in project_info["dependencies"]:
        name, revision = dependency["name"], dependency["revision"]
        source = root / project / ".lake/packages" / name
        if not source.is_dir():
            raise ValueError(f"Missing local dependency prerequisite: {source} at {revision}")
        try:
            resolved = git(source, "rev-parse", revision + "^{commit}").decode().strip()
        except subprocess.CalledProcessError as error:
            raise ValueError(f"Missing local dependency revision: {source} at {revision}") from error
        if resolved != revision:
            raise ValueError(f"Dependency revision does not resolve exactly: {name}")
        target = project_cwd / ".lake/packages" / name
        plain_destination(target, worktree)
        entry = {**dependency, "source_repository": str(source), "destination": str(target)}
        if target.exists():
            if not reuse:
                raise ValueError(f"Dependency destination already exists: {target}")
            verify_dependencies([entry], worktree)
            if git(target, "rev-parse", "--show-toplevel").decode().strip() != str(target):
                raise ValueError("Dependency destination is not an independent checkout")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            command(["git", "clone", "--no-hardlinks", "--no-checkout", "--dissociate", "--", source, target],
                    "dependency-" + name + "-clone")
            command(["git", "-C", target, "checkout", "--detach", revision],
                    "dependency-" + name + "-checkout")
            command(["git", "-C", target, "remote", "set-url", "origin", dependency["url"]],
                    "dependency-" + name + "-remote")
        record["dependency_checkouts"].append(entry)
        save()
    verify_dependencies(record["dependency_checkouts"], worktree)
    mathlib = next((d for d in project_info["dependencies"] if d["name"] == "mathlib"), None)
    if mathlib:
        record["official_cache"] = {
            "package": "mathlib", "source_revision": mathlib["revision"],
            "policy": "official Lake cache command; failure permits source build"}
        command(["lake", "exe", "cache", "get"], "mathlib-cache", cwd=project_cwd, allow_failure=True)
        record["official_cache"]["exit_code"] = record["commands"][-1]["exit_code"]
        save()
        verify_dependencies(record["dependency_checkouts"], worktree)
