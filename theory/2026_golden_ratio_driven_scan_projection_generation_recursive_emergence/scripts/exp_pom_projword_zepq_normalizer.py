#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Normalizer for a slightly extended projection-word fragment PW_{Z,E,P,Q}.

We extend the minimal PW_{Z,E} normalizer by adding the split-epi pair:
  - P[m] : pushforward (Fold_m)_*  (stable readout)
  - Q[m] : uniform lift           (fiber-uniform section)

and the induced fiber reflector:
  - K[m] := Q[m] ∘ P[m]   (idempotent)

Rewrite rules (local):
  (R_Z)    PZ ∘ PZ        => PZ
  (R_E)    E[m1] ∘ E[m2]  => E[m1]        if m2 >= m1

  (R_PQ)   P[m] ∘ Q[m]    => Id           (split-epi)
  (R_QP)   Q[m] ∘ P[m]    => K[m]
  (R_KK)   K[m] ∘ K[m]    => K[m]
  (R_PK)   P[m] ∘ K[m]    => P[m]
  (R_KQ)   K[m] ∘ Q[m]    => Q[m]

This script is intended as an executable witness for the paper's rewrite fragment
that combines the expectation-tower calculus with the split-epi calculus.

Input format:
  Tokens are given left-to-right in composition order, e.g.
    python3 scripts/exp_pom_projword_zepq_normalizer.py PZ E5 Q5 P5 Q5 P5

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from typing import List, Optional


@dataclass(frozen=True)
class Tok:
    kind: str  # "PZ", "E", "P", "Q", "K"
    m: Optional[int] = None

    def __str__(self) -> str:
        if self.kind == "PZ":
            return "PZ"
        assert self.m is not None
        return f"{self.kind}{self.m}"


_E_RE = re.compile(r"^E\[?(\d+)\]?$")
_P_RE = re.compile(r"^P\[?(\d+)\]?$")
_Q_RE = re.compile(r"^Q\[?(\d+)\]?$")
_K_RE = re.compile(r"^K\[?(\d+)\]?$")


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
        m = _P_RE.match(s)
        if m:
            out.append(Tok("P", int(m.group(1))))
            continue
        m = _Q_RE.match(s)
        if m:
            out.append(Tok("Q", int(m.group(1))))
            continue
        m = _K_RE.match(s)
        if m:
            out.append(Tok("K", int(m.group(1))))
            continue
        raise SystemExit(f"Bad token: {s}. Use PZ, E[m], P[m], Q[m], K[m].")
    return out


def _same_m(a: Tok, b: Tok) -> bool:
    return a.m is not None and b.m is not None and a.m == b.m


def normalize(tokens: List[Tok]) -> List[Tok]:
    # Greedy left-to-right stack reduction with local rewrites.
    st: List[Tok] = []
    for t in tokens:
        st.append(t)
        changed = True
        while changed and len(st) >= 2:
            changed = False
            b = st[-1]
            a = st[-2]

            # (R_Z): PZ PZ -> PZ
            if a.kind == "PZ" and b.kind == "PZ":
                st.pop()
                changed = True
                continue

            # (R_E): E[m1] E[m2] -> E[min(m1,m2)] with tower direction.
            if a.kind == "E" and b.kind == "E":
                assert a.m is not None and b.m is not None
                if b.m >= a.m:
                    st.pop()
                else:
                    st[-2] = Tok("E", b.m)
                    st.pop()
                changed = True
                continue

            # (R_PQ): P[m] Q[m] -> Id
            if a.kind == "P" and b.kind == "Q" and _same_m(a, b):
                st.pop()
                st.pop()
                changed = True
                continue

            # (R_QP): Q[m] P[m] -> K[m]
            if a.kind == "Q" and b.kind == "P" and _same_m(a, b):
                mm = a.m
                st.pop()
                st.pop()
                st.append(Tok("K", mm))
                changed = True
                continue

            # (R_KK): K[m] K[m] -> K[m]
            if a.kind == "K" and b.kind == "K" and _same_m(a, b):
                st.pop()
                changed = True
                continue

            # (R_PK): P[m] K[m] -> P[m]
            if a.kind == "P" and b.kind == "K" and _same_m(a, b):
                st.pop()
                changed = True
                continue

            # (R_KQ): K[m] Q[m] -> Q[m]
            if a.kind == "K" and b.kind == "Q" and _same_m(a, b):
                st[-2] = Tok("Q", b.m)
                st.pop()
                changed = True
                continue

    return st


def main() -> None:
    parser = argparse.ArgumentParser(description="Normalize PW_{Z,E,P,Q} words.")
    parser.add_argument("tokens", nargs="+", help="Tokens: PZ, E[m], P[m], Q[m], K[m].")
    args = parser.parse_args()

    toks = parse_tokens(args.tokens)
    norm = normalize(toks)
    print("[zepq-normalizer] in:  ", " ".join(str(t) for t in toks), flush=True)
    print("[zepq-normalizer] out: ", " ".join(str(t) for t in norm), flush=True)


if __name__ == "__main__":
    main()

