#!/usr/bin/env python3
"""Syntax audit for the optional printed-root EML catalogue.

This script intentionally proves no real-domain identities.  It only checks that
the ancillary catalogue contains finite strings in the grammar

    S -> 1 | x | EML[S,S].

The manuscript treats the semantic assertions for the named roots as the
external hypothesis (H_W); the unconditional Richardson theorem uses arbitrary
replacement triples whose three identities have already been proved.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CATALOGUE = ROOT / "ancillary" / "eml_witness_catalogue.txt"
EXPECTED = {"W_PI_EML", "W_SIN_EML_X", "W_SQRT_EML_X"}


@dataclass(frozen=True)
class Stats:
    eml_nodes: int
    depth: int


def parse_term(text: str, position: int = 0) -> tuple[Stats, int]:
    if position >= len(text):
        raise ValueError("unexpected end of term")
    if text[position] in {"1", "x"}:
        return Stats(0, 0), position + 1
    marker = "EML["
    if not text.startswith(marker, position):
        raise ValueError(f"expected grammar atom at offset {position}")
    left, position = parse_term(text, position + len(marker))
    if position >= len(text) or text[position] != ",":
        raise ValueError(f"expected comma at offset {position}")
    right, position = parse_term(text, position + 1)
    if position >= len(text) or text[position] != "]":
        raise ValueError(f"expected closing bracket at offset {position}")
    stats = Stats(1 + left.eml_nodes + right.eml_nodes, 1 + max(left.depth, right.depth))
    return stats, position + 1


def main() -> None:
    catalogue_bytes = CATALOGUE.read_bytes()
    text = catalogue_bytes.decode("utf-8-sig")
    entries: dict[str, str] = {}
    for line in text.splitlines():
        if " = EML[" not in line:
            continue
        name, term = line.split(" = ", 1)
        if name in EXPECTED:
            entries[name] = term
    if set(entries) != EXPECTED:
        missing = sorted(EXPECTED - set(entries))
        extra = sorted(set(entries) - EXPECTED)
        raise ValueError(f"catalogue keys mismatch: missing={missing}, extra={extra}")

    print(f"catalogue_sha256={hashlib.sha256(catalogue_bytes).hexdigest()}")
    for name in sorted(entries):
        stats, end = parse_term(entries[name])
        if end != len(entries[name]):
            raise ValueError(f"trailing text in {name} at offset {end}")
        digest = hashlib.sha256(entries[name].encode("utf-8")).hexdigest()
        print(f"{name}: eml_nodes={stats.eml_nodes} depth={stats.depth} sha256={digest}")
    print("syntax_certificate_ok")
    print("semantic_status=external_hypothesis_H_W_not_proved_by_this_script")


if __name__ == "__main__":
    main()
