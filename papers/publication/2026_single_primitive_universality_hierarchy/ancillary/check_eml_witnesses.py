#!/usr/bin/env python3
"""Check the finite EML witness certificate printed in Section 5.

The script is deliberately small: it parses the straight-line table in
``sections/sec05_hierarchy_strictness.tex``, verifies that every register is
acyclic and uses only earlier registers, expands the three named witnesses to
pure grammar strings, and compares those expansions with the locked ancillary
catalogue.
"""

from __future__ import annotations

import hashlib
import re
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SECTION = ROOT / "sections" / "sec05_hierarchy_strictness.tex"
CATALOGUE = ROOT / "ancillary" / "eml_witness_catalogue.txt"

REGISTER_RE = re.compile(
    r"U_(?:\{(?P<braced>\d+)\}|(?P<plain>\d+))&="
    r"(?P<body>1|x|\\mathsf E\(U_\{?(?P<a>\d+)\}?,U_\{?(?P<b>\d+)\}?\))"
)
CATALOGUE_RE = re.compile(r"^(W_(?:PI|SIN|SQRT)_EML(?:_X)?) = (EML\[.*\])$", re.M)

ROOTS = {
    "W_PI_EML": 47,
    "W_SIN_EML_X": 111,
    "W_SQRT_EML_X": 126,
}


def parse_registers() -> dict[int, tuple[str, int | None, int | None]]:
    text = SECTION.read_text(encoding="utf-8")
    registers: dict[int, tuple[str, int | None, int | None]] = {}
    for match in REGISTER_RE.finditer(text):
        index = int(match.group("braced") or match.group("plain"))
        body = match.group("body")
        if body in {"1", "x"}:
            registers[index] = (body, None, None)
        else:
            left = int(match.group("a"))
            right = int(match.group("b"))
            if left >= index or right >= index:
                raise ValueError(f"U_{index} is not acyclic: uses U_{left}, U_{right}")
            registers[index] = ("EML", left, right)

    expected = set(range(127))
    actual = set(registers)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        raise ValueError(f"register mismatch: missing={missing}, extra={extra}")
    return registers


def parse_catalogue() -> dict[str, str]:
    text = CATALOGUE.read_text(encoding="utf-8")
    entries = dict(CATALOGUE_RE.findall(text))
    if set(entries) != set(ROOTS):
        raise ValueError(f"catalogue keys mismatch: {sorted(entries)}")
    return entries


def main() -> None:
    registers = parse_registers()
    catalogue = parse_catalogue()

    @lru_cache(maxsize=None)
    def expand(index: int) -> str:
        kind, left, right = registers[index]
        if kind in {"1", "x"}:
            return kind
        assert left is not None and right is not None
        return f"EML[{expand(left)},{expand(right)}]"

    @lru_cache(maxsize=None)
    def stats(index: int) -> tuple[int, int]:
        kind, left, right = registers[index]
        if kind in {"1", "x"}:
            return (0, 0)
        assert left is not None and right is not None
        left_nodes, left_depth = stats(left)
        right_nodes, right_depth = stats(right)
        return (1 + left_nodes + right_nodes, 1 + max(left_depth, right_depth))

    catalogue_bytes = CATALOGUE.read_bytes()
    print(f"catalogue_sha256={hashlib.sha256(catalogue_bytes).hexdigest()}")
    print(f"registers={len(registers)}")
    for name, root in ROOTS.items():
        expansion = expand(root)
        if expansion != catalogue[name]:
            raise ValueError(f"{name} expansion differs from catalogue")
        nodes, depth = stats(root)
        digest = hashlib.sha256(expansion.encode("utf-8")).hexdigest()
        print(f"{name}: root=U_{root} eml_nodes={nodes} depth={depth} sha256={digest}")

    print("certificate_ok")


if __name__ == "__main__":
    main()
