#!/usr/bin/env python3
"""Reject proof placeholders and nonstandard axiom shortcuts in Lean source.

Challenge.lean is the statement-only surface and must contain exactly one
deliberate `sorry`. The final axiom audit and Comparator remain authoritative.
"""

from pathlib import Path
import os
import re

ROOT = Path(__file__).resolve().parents[1]
TOKEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide)\b")


def remove_comments_and_strings(text: str) -> str:
    result = list(text)
    i = 0
    depth = 0
    line_comment = False
    in_string = False
    escaped = False
    while i < len(text):
        pair = text[i:i + 2]
        if line_comment:
            if text[i] == "\n":
                line_comment = False
            else:
                result[i] = " "
            i += 1
        elif depth:
            if pair == "/-":
                depth += 1
                result[i:i + 2] = "  "
                i += 2
            elif pair == "-/":
                depth -= 1
                result[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    result[i] = " "
                i += 1
        elif in_string:
            character = text[i]
            if character != "\n":
                result[i] = " "
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            i += 1
        elif pair == "--":
            line_comment = True
            result[i:i + 2] = "  "
            i += 2
        elif pair == "/-":
            depth = 1
            result[i:i + 2] = "  "
            i += 2
        elif text[i] == '"':
            in_string = True
            result[i] = " "
            i += 1
        else:
            i += 1
    if depth or in_string:
        raise ValueError("unterminated comment or string")
    return "".join(result)


failures = []
paths = []
for directory, subdirectories, names in os.walk(ROOT, followlinks=False):
    subdirectories[:] = [name for name in subdirectories if name not in {".git", ".lake"}]
    paths.extend(Path(directory) / name for name in names if name.endswith(".lean"))
for path in sorted(paths):
    source = path.read_text(encoding="utf-8")
    try:
        code = remove_comments_and_strings(source)
    except ValueError as error:
        failures.append(f"{path.relative_to(ROOT)}: {error}")
        continue
    found = list(TOKEN.finditer(code))
    if path == ROOT / "Challenge.lean" and [m.group() for m in found] == ["sorry"]:
        continue
    for match in found:
        line = code.count("\n", 0, match.start()) + 1
        failures.append(f"{path.relative_to(ROOT)}:{line}: {match.group()}")

if failures:
    print("\n".join(failures))
    raise SystemExit(1)
print("Proof source has no placeholders, custom axioms, or native_decide.")
