#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Minimal normalizer for the projection-word fragment PW_{Z,E}.

We normalize words built from:
  - PZ    (the idempotent normalization projection P_Z)
  - E[m]  (conditional expectation E_m, with the tower rule)

Rewrite rules:
  (R_Z)  PZ ∘ PZ  => PZ
  (R_E)  E[m1] ∘ E[m2] => E[m1]  if m2 >= m1

This script is a reproducible, executable witness for the termination/confluence
normal form theorem in the paper (thm:pom-rewrite-termination-confluence).

Input format:
  Tokens are given left-to-right in composition order, e.g.
    python3 scripts/exp_pom_projword_ze_normalizer.py PZ E5 E12 PZ PZ E3

Output:
  Prints the normalized token list and a compact string.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from typing import List, Optional


@dataclass(frozen=True)
class Tok:
    kind: str  # "PZ" or "E"
    m: Optional[int] = None

    def __str__(self) -> str:
        if self.kind == "PZ":
            return "PZ"
        assert self.kind == "E" and self.m is not None
        return f"E{self.m}"


_E_RE = re.compile(r"^E\[?(\d+)\]?$")


def parse_tokens(raw: List[str]) -> List[Tok]:
    out: List[Tok] = []
    for s in raw:
        if s == "PZ":
            out.append(Tok("PZ"))
            continue
        m = _E_RE.match(s)
        if m:
            out.append(Tok("E", int(m.group(1))))
            continue
        raise SystemExit(f"Bad token: {s}. Use PZ or E[m]/Em.")
    return out


def normalize(tokens: List[Tok]) -> List[Tok]:
    # Single left-to-right pass with a stack, using only local rewrites.
    st: List[Tok] = []
    for t in tokens:
        if not st:
            st.append(t)
            continue
        prev = st[-1]

        # (R_Z): PZ PZ -> PZ
        if prev.kind == "PZ" and t.kind == "PZ":
            continue

        # (R_E): E[m1] E[m2] -> E[min(m1,m2)] with the tower direction
        if prev.kind == "E" and t.kind == "E":
            assert prev.m is not None and t.m is not None
            if t.m >= prev.m:
                # E[m1] ∘ E[m2] => E[m1]
                continue
            # Else keep the smaller index (equivalently swap by collapsing to Emin)
            st[-1] = Tok("E", t.m)
            continue

        st.append(t)
    return st


def main() -> None:
    parser = argparse.ArgumentParser(description="Normalize PW_{Z,E} words (PZ and E[m]).")
    parser.add_argument("tokens", nargs="+", help="Tokens: PZ, E[m] or Em.")
    args = parser.parse_args()

    toks = parse_tokens(args.tokens)
    norm = normalize(toks)
    print("[ze-normalizer] in:  ", " ".join(str(t) for t in toks), flush=True)
    print("[ze-normalizer] out: ", " ".join(str(t) for t in norm), flush=True)


if __name__ == "__main__":
    main()

