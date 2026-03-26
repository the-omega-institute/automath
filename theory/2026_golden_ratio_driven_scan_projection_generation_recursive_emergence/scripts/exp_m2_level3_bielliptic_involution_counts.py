#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Enumerate involution orbits on level-3 fibers over the bielliptic divisor Xi.

English-only by repository convention.

We work over F_3 with the standard symplectic form on V=F_3^4. We choose an
involution s in Sp(4,F_3) with eigen-decomposition V=V_+ ⊕ V_- into two
orthogonal symplectic 2-planes, acting by +1 on V_+ and -1 on V_-.

We enumerate s-orbits on:
  - Points: P(V) (1-dim subspaces), size 40; fixed size 8; remaining are 16 transpositions.
  - Lagrangians: maximal isotropic 2-planes, size 40; fixed size 16; remaining are 12 transpositions.
  - Flags: (line ⊂ lagrangian), size 160; fixed size 32; remaining are 64 transpositions.

Outputs:
  - artifacts/export/m2_level3_bielliptic_involution_counts.json
  - sections/generated/eq_m2_level3_bielliptic_involution_counts.tex
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, List, Sequence, Set, Tuple

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


F = 3


def _mod(x: int) -> int:
    return x % F


Vec = Tuple[int, int, int, int]
Line = Vec
Plane = FrozenSet[Vec]
Flag = Tuple[Line, Plane]


def dot_symplectic(x: Vec, y: Vec) -> int:
    # Standard form with matrix J = [[0,I],[-I,0]] on (x1,x2,x3,x4).
    x1, x2, x3, x4 = x
    y1, y2, y3, y4 = y
    return _mod(x1 * y3 + x2 * y4 - x3 * y1 - x4 * y2)


def add(x: Vec, y: Vec) -> Vec:
    return (_mod(x[0] + y[0]), _mod(x[1] + y[1]), _mod(x[2] + y[2]), _mod(x[3] + y[3]))


def smul(a: int, x: Vec) -> Vec:
    return (_mod(a * x[0]), _mod(a * x[1]), _mod(a * x[2]), _mod(a * x[3]))


def all_nonzero_vectors() -> List[Vec]:
    out: List[Vec] = []
    for a in range(F):
        for b in range(F):
            for c in range(F):
                for d in range(F):
                    if a == 0 and b == 0 and c == 0 and d == 0:
                        continue
                    out.append((a, b, c, d))
    return out


def normalize_line(v: Vec) -> Vec:
    # Choose a canonical representative: first nonzero coordinate becomes 1.
    for vi in v:
        if vi % F != 0:
            inv = 1 if vi % F == 1 else 2  # inverse in F_3: 1->1, 2->2
            return smul(inv, v)
    raise ValueError("zero vector")


def all_lines() -> List[Line]:
    seen: Set[Line] = set()
    out: List[Line] = []
    for v in all_nonzero_vectors():
        rep = normalize_line(v)
        if rep not in seen:
            seen.add(rep)
            out.append(rep)
    out.sort()
    return out


def span2(a: Vec, b: Vec) -> Set[Vec]:
    s: Set[Vec] = set()
    for i in range(F):
        for j in range(F):
            s.add(add(smul(i, a), smul(j, b)))
    return s


def is_lagrangian(plane_vectors: Set[Vec]) -> bool:
    # In dimension 4, a Lagrangian is exactly a 2-dim isotropic plane.
    if len(plane_vectors) != 9:
        return False
    basis: List[Vec] = [v for v in plane_vectors if v != (0, 0, 0, 0)]
    for i in range(len(basis)):
        for j in range(i + 1, len(basis)):
            if dot_symplectic(basis[i], basis[j]) != 0:
                return False
    return True


def all_lagrangians() -> List[Plane]:
    planes: Set[Plane] = set()
    vecs = all_nonzero_vectors()
    for a in vecs:
        for b in vecs:
            if a == b:
                continue
            sp = span2(a, b)
            if is_lagrangian(sp):
                planes.add(frozenset(sp))
    out = list(planes)
    out.sort(key=lambda p: sorted(p))
    return out


def lines_in_plane(plane: Plane) -> List[Line]:
    reps: Set[Line] = set()
    for v in plane:
        if v == (0, 0, 0, 0):
            continue
        reps.add(normalize_line(v))
    out = list(reps)
    out.sort()
    return out


def all_flags(lagrangians: Sequence[Plane]) -> List[Flag]:
    out: List[Flag] = []
    for pl in lagrangians:
        for ln in lines_in_plane(pl):
            out.append((ln, pl))
    out.sort(key=lambda f: (f[0], sorted(f[1])))
    return out


def involution_s(x: Vec) -> Vec:
    # Symplectic involution with +1 on span(e1,e3) and -1 on span(e2,e4).
    x1, x2, x3, x4 = x
    return (_mod(x1), _mod(-x2), _mod(x3), _mod(-x4))


def act_on_line(ln: Line) -> Line:
    return normalize_line(involution_s(ln))


def act_on_plane(pl: Plane) -> Plane:
    return frozenset(involution_s(v) for v in pl)


def act_on_flag(flag: Flag) -> Flag:
    ln, pl = flag
    return (act_on_line(ln), act_on_plane(pl))


def orbit_decomposition(elements: Sequence[object], action) -> Tuple[int, int]:
    # Returns (fixed_count, transposition_count) under an involution.
    seen: Set[object] = set()
    fixed = 0
    transpositions = 0
    for x in elements:
        if x in seen:
            continue
        y = action(x)
        seen.add(x)
        if y == x:
            fixed += 1
        else:
            seen.add(y)
            transpositions += 1
    return fixed, transpositions


@dataclass(frozen=True)
class Payload:
    field: int
    sizes: Dict[str, int]
    fixed: Dict[str, int]
    transpositions: Dict[str, int]
    cycle_types: Dict[str, str]


def main() -> None:
    lines = all_lines()
    lags = all_lagrangians()
    flags = all_flags(lags)

    fixed_lines, trans_lines = orbit_decomposition(lines, act_on_line)
    fixed_lags, trans_lags = orbit_decomposition(lags, act_on_plane)
    fixed_flags, trans_flags = orbit_decomposition(flags, act_on_flag)

    payload = Payload(
        field=F,
        sizes={"points": len(lines), "lagrangians": len(lags), "flags": len(flags)},
        fixed={"points": fixed_lines, "lagrangians": fixed_lags, "flags": fixed_flags},
        transpositions={"points": trans_lines, "lagrangians": trans_lags, "flags": trans_flags},
        cycle_types={
            "points": f"1^{fixed_lines},2^{trans_lines}",
            "lagrangians": f"1^{fixed_lags},2^{trans_lags}",
            "flags": f"1^{fixed_flags},2^{trans_flags}",
        },
    )

    _write_json(export_dir() / "m2_level3_bielliptic_involution_counts.json", asdict(payload))

    tex: List[str] = [
        "% Auto-generated by scripts/exp_m2_level3_bielliptic_involution_counts.py",
        r"\[",
        r"|\PP^3(\FF_3)|=40,\qquad |\mathrm{Lag}(\FF_3^4)|=40,\qquad |\mathrm{Flag}|=160.",
        r"\]",
        r"\[",
        rf"\#\mathrm{{Fix}}_{{\PP(V)}}(\sigma)={fixed_lines},\qquad (40-{fixed_lines})/2={trans_lines}.",
        r"\]",
        r"\[",
        rf"\#\mathrm{{Fix}}_{{\mathrm{{Lag}}(V)}}(\sigma)={fixed_lags},\qquad (40-{fixed_lags})/2={trans_lags}.",
        r"\]",
        r"\[",
        rf"\#\mathrm{{Fix}}_{{\mathrm{{Flag}}(V)}}(\sigma)={fixed_flags},\qquad (160-{fixed_flags})/2={trans_flags}.",
        r"\]",
    ]
    _write_text(generated_dir() / "eq_m2_level3_bielliptic_involution_counts.tex", "\n".join(tex) + "\n")


if __name__ == "__main__":
    main()

