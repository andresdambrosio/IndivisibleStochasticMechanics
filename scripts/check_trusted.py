#!/usr/bin/env python3
"""Check that the trusted layer in TRUSTED.md matches the Lean sources.

Every definition (`def`, `structure`, `abbrev`, `class`, `inductive`, `instance`) must be
listed in TRUSTED.md, because definitions are where physical meaning enters and Lean cannot
check meaning. Theorems are free: Lean checks them. Every declaration listed in TRUSTED.md
(including the main theorems chosen by humans) must exist in the sources.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "IndivisibleStochasticMechanics"
TRUSTED = ROOT / "TRUSTED.md"

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(def|structure|abbrev|class|inductive|instance|theorem|lemma)\s+([^\s:({\[]+)"
)
NAMESPACE = re.compile(r"^namespace\s+(\S+)")
SECTION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$"
)
END = re.compile(r"^end(?:\s+(\S+))?\s*$")
DEFINITION_KINDS = {"def", "structure", "abbrev", "class", "inductive", "instance"}


def declarations():
    """Yield (kind, full name, location) for every declaration in the library."""
    for path in sorted(SRC.rglob("*.lean")):
        # Each scope is (kind, name parts); sections do not change the namespace.
        scopes = []
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            stack = [p for kind, parts in scopes if kind == "namespace" for p in parts]
            if m := NAMESPACE.match(line):
                scopes.append(("namespace", m.group(1).split(".")))
            elif m := SECTION.match(line):
                scopes.append(("section", []))
            elif m := END.match(line):
                if scopes:
                    scopes.pop()
            elif m := DECL.match(line):
                kind, name = m.groups()
                full = ".".join(stack + [name])
                yield kind, full, f"{path.relative_to(ROOT)}:{lineno}"


def main():
    listed = set(re.findall(r"^\|\s*`([^`]+)`", TRUSTED.read_text(), re.MULTILINE))
    decls = list(declarations())
    names = {full for _, full, _ in decls}
    errors = []
    for kind, full, loc in decls:
        if kind in DEFINITION_KINDS and full not in listed:
            errors.append(f"{loc}: `{full}` ({kind}) is not listed in TRUSTED.md")
    for name in sorted(listed - names):
        errors.append(f"TRUSTED.md: `{name}` does not exist in the Lean sources")
    for e in errors:
        print(e)
    if errors:
        print(f"\n{len(errors)} problem(s). See CONTRIBUTING.md, section 'The trusted layer'.")
        sys.exit(1)
    print(f"OK: {len(listed)} trusted declarations, all definitions accounted for.")


if __name__ == "__main__":
    main()
