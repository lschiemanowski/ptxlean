#!/usr/bin/env python3
"""Reject proof placeholders and nonstandard dependencies of audited theorems.

The source scan is a small lexical guard, not a Lean parser or security boundary.
Lean's compiled dependency reports are the authoritative audited-proof check.
"""

import argparse
from collections import Counter
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide|sorryAx)\b")


def code_only(text):
    """Blank comments (including nesting) and strings, preserving source lines."""
    output = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                output.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                output.extend("  ")
                i += 2
            else:
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                output.extend("\n" if c == "\n" else " " for c in text[i:i + 2])
                i += 2
            else:
                in_string = text[i] != '"'
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            output.extend(" " * (end - i))
            i = end
        elif text.startswith("/-", i):
            depth = 1
            output.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            output.append(" ")
            i += 1
        else:
            output.append(text[i])
            i += 1
    if depth or in_string:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(output)


def scan_sources():
    paths = [ROOT / "Ptx.lean", *sorted((ROOT / "Ptx").rglob("*.lean"))]
    for path in paths:
        code = code_only(path.read_text())
        match = FORBIDDEN.search(code)
        if match:
            line = code.count("\n", 0, match.start()) + 1
            raise ValueError(f"{path.relative_to(ROOT)}:{line}: forbidden token {match[0]}")
    print(f"Lean source guard: {len(paths)} files checked.")


def check_audit(log):
    audit = code_only((ROOT / "Ptx/Audit.lean").read_text())
    expected = re.findall(r"^#print axioms (\S+)\s*$", audit, re.MULTILINE)
    if not expected or len(set(expected)) != len(expected):
        raise ValueError("Audit must contain a nonempty list of distinct declarations")
    pattern = re.compile(
        r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
        re.MULTILINE,
    )
    reports = pattern.findall(log)
    if Counter(name for name, _ in reports) != Counter(expected):
        raise ValueError("Missing, duplicate, or unexpected theorem dependency report")
    for name, dependencies in reports:
        axioms = {item.strip() for item in dependencies.split(",") if item.strip()}
        rejected = axioms - ALLOWED_AXIOMS
        if rejected:
            raise ValueError(f"{name}: disallowed axioms {sorted(rejected)}")
    print(f"Axiom audit: {len(reports)} declarations; only standard Lean axioms permitted.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--scan", action="store_true")
    mode.add_argument("--audit", type=Path)
    args = parser.parse_args()
    if args.scan:
        scan_sources()
    else:
        check_audit(args.audit.read_text())


if __name__ == "__main__":
    main()
