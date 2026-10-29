#!/usr/bin/env python3
"""Require complete axiom output for main_result and every semantic theorem."""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    expected = set(re.findall(
        r"^#print axioms ([A-Za-z0-9_.]+)$",
        (ROOT / "verification/Audit.lean").read_text(encoding="utf-8"), re.M,
    ))
    semantic_names = {
        "ThreeOmittedValues.SemanticCorrespondence." + name
        for name in re.findall(
            r"^theorem ([A-Za-z0-9_]+)",
            (ROOT / "Theorem12Proof/SemanticCorrespondence.lean").read_text(encoding="utf-8"), re.M,
        )
    }
    if expected != semantic_names | {"PalomarTheorem12.main_result"}:
        raise SystemExit("Axiom audit must include every semantic theorem and main_result.")
    output = Path(sys.argv[1]).read_text(encoding="utf-8-sig")
    results = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.M)
    if len(results) != len(expected) or {name for name, _ in results} != expected:
        raise SystemExit("Axiom audit output is missing, duplicated, or names unexpected targets.")
    for name, axioms in results:
        used = {item.strip() for item in axioms.split(",") if item.strip()}
        if not used <= ALLOWED:
            raise SystemExit(f"{name}: disallowed axioms: {sorted(used - ALLOWED)}")
    print(f"All {len(expected)} audited theorems use only permitted standard axioms.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
