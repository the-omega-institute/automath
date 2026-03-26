#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Enumerate transvection orbits on level-3 fibers over Delta_0.

English-only by repository convention.

We work over F_3 with the standard symplectic form on V=F_3^4, choose a nonzero v,
and consider the symplectic transvection
  tau_v(x) = x + <x,v> v.
It has order 3. We enumerate:
  - Points: P(V) (1-dim subspaces), size 40; fixed points size 13; remaining are 9 cycles of length 3.
  - Lagrangians: maximal isotropic 2-planes, size 40; fixed size 4; remaining are 12 cycles of length 3.
  - Flags: (line ⊂ lagrangian), size 160; fixed size 16; remaining are 48 cycles of length 3.
  - Refined splitting for the forgetful map Flag -> P(V) over the fixed locus.

Outputs:
  - artifacts/export/m2_level3_boundary_transvection_counts.json
  - sections/generated/eq_m2_level3_boundary_transvection_counts.tex
"""

from __future__ import annotations

import argparse
import json
import os
import time
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


def dot_symplectic(x: Vec, y: Vec) -> int:
    # Standard form with matrix J = [[0,I],[-I,0]] on (x1,x2,x3,x4).
    x1, x2, x3, x4 = x
    y1, y2, y3, y4 = y
    return _mod(x1 * y3 + x2 * y4 - x3 * y1 - x4 * y2)


def add(x: Vec, y: Vec) -> Vec:
    return (_mod(x[0] + y[0]), _mod(x[1] + y[1]), _mod(x[2] + y[2]), _mod(x[3] + y[3]))


def smul(a: int, x: Vec) -> Vec:
    return (_mod(a * x[0]), _mod(a * x[1]), _mod(a * x[2]), _mod(a * x[3]))


def tau(v: Vec, x: Vec) -> Vec:
    return add(x, smul(dot_symplectic(x, v), v))


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
    for i, vi in enumerate(v):
        if vi % F != 0:
            inv = 1 if vi % F == 1 else 2  # inverse in F_3: 1->1, 2->2
            return smul(inv, v)
    raise ValueError("zero vector")


Line = Vec  # canonical rep of a 1-dim subspace


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


Plane = FrozenSet[Vec]  # set of 4 vectors: a 2-dim subspace has 3^2=9 vectors; but store basis? better store canonical basis.


def span2(a: Vec, b: Vec) -> Set[Vec]:
    s: Set[Vec] = set()
    for i in range(F):
        for j in range(F):
            s.add(add(smul(i, a), smul(j, b)))
    return s


def rank2(a: Vec, b: Vec) -> bool:
    return len(span2(a, b)) == F * F


def canonical_plane_basis(a: Vec, b: Vec) -> Tuple[Vec, Vec]:
    # Return a canonical ordered basis by scanning all nonzero combinations.
    # This is sufficient at this small size.
    S = sorted([normalize_line(v) for v in span2(a, b) if v != (0, 0, 0, 0)])
    e1 = S[0]
    # pick e2 not in span(e1)
    span_e1 = {smul(t, e1) for t in range(F)}
    for v in S[1:]:
        if v not in span_e1:
            e2 = v
            return e1, e2
    raise RuntimeError("failed to find basis")


def plane_key(a: Vec, b: Vec) -> Tuple[Vec, Vec]:
    e1, e2 = canonical_plane_basis(a, b)
    return (e1, e2)


def is_isotropic_plane(a: Vec, b: Vec) -> bool:
    if not rank2(a, b):
        return False
    return dot_symplectic(a, b) == 0


def all_lagrangian_planes() -> List[Tuple[Vec, Vec]]:
    # Enumerate 2-dim isotropic subspaces by basis, deduplicate by canonical key.
    vecs = all_nonzero_vectors()
    seen: Set[Tuple[Vec, Vec]] = set()
    out: List[Tuple[Vec, Vec]] = []
    n = len(vecs)
    for i in range(n):
        for j in range(i + 1, n):
            a, b = vecs[i], vecs[j]
            if not is_isotropic_plane(a, b):
                continue
            key = plane_key(a, b)
            if key in seen:
                continue
            seen.add(key)
            out.append(key)
    out.sort()
    return out


def plane_contains_vector(plane: Tuple[Vec, Vec], v: Vec) -> bool:
    a, b = plane
    return v in span2(a, b)


def plane_contains_line(plane: Tuple[Vec, Vec], ell: Line) -> bool:
    return plane_contains_vector(plane, ell)


def tau_on_line(v: Vec, ell: Line) -> Line:
    return normalize_line(tau(v, ell))


def tau_on_plane(v: Vec, plane: Tuple[Vec, Vec]) -> Tuple[Vec, Vec]:
    a, b = plane
    return plane_key(tau(v, a), tau(v, b))


Flag = Tuple[Line, Tuple[Vec, Vec]]


def all_flags(lines: Sequence[Line], lags: Sequence[Tuple[Vec, Vec]]) -> List[Flag]:
    out: List[Flag] = []
    for L in lags:
        # all lines in plane L: there are 4.
        S = sorted({normalize_line(x) for x in span2(L[0], L[1]) if x != (0, 0, 0, 0)})
        # dedupe to 4 projective lines
        lines_in_L = sorted(set(S))
        # sanity: should be 4
        # In F_3^2, there are (3^2-1)/(3-1)=4 lines.
        for ell in lines_in_L:
            out.append((ell, L))
    out.sort()
    return out


def orbit_decomposition(
    items: Sequence[object], action, max_cycle: int = 3
) -> Tuple[int, Dict[int, int]]:
    # Return number of fixed points and counts of cycles by length.
    idx: Dict[object, int] = {x: i for i, x in enumerate(items)}
    seen: Set[object] = set()
    cycles: Dict[int, int] = {}
    fixed = 0
    for x in items:
        if x in seen:
            continue
        # follow orbit
        cur = x
        orb: List[object] = []
        while cur not in seen:
            seen.add(cur)
            orb.append(cur)
            cur = action(cur)
        L = len(orb)
        if L == 1:
            fixed += 1
        cycles[L] = cycles.get(L, 0) + 1
        if L > max_cycle:
            raise RuntimeError(f"unexpected orbit length {L}")
    return fixed, cycles


@dataclass(frozen=True)
class Payload:
    v: List[int]
    points_total: int
    points_fixed: int
    points_cycles: Dict[str, int]
    lag_total: int
    lag_fixed: int
    lag_cycles: Dict[str, int]
    flags_total: int
    flags_fixed: int
    flags_cycles: Dict[str, int]
    refined_fixed_line_all_four_fixed: bool
    refined_other_fixed_line_structure_ok: bool
    refined_nonfixed_line_no_fixed_flags: bool


def main() -> None:
    parser = argparse.ArgumentParser(description="Enumerate transvection orbit counts over F_3.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    os.environ.setdefault("TZ", "Asia/Singapore")
    t0 = time.time()
    print("[m2-level3-delta0-transvection] start", flush=True)

    v = (1, 0, 0, 0)

    lines = all_lines()
    lags = all_lagrangian_planes()
    flags = all_flags(lines, lags)

    points_fixed, points_cycles = orbit_decomposition(lines, lambda x: tau_on_line(v, x))
    lag_fixed, lag_cycles = orbit_decomposition(lags, lambda x: tau_on_plane(v, x))
    flags_fixed, flags_cycles = orbit_decomposition(flags, lambda x: (tau_on_line(v, x[0]), tau_on_plane(v, x[1])))

    # Refined splitting checks on fixed locus in P(V):
    # fixed lines are exactly lines in v^perp; among them, the special line is <v>.
    v_line = normalize_line(v)

    def fixed_lines() -> List[Line]:
        out: List[Line] = []
        for ell in lines:
            if tau_on_line(v, ell) == ell:
                out.append(ell)
        return out

    fixed_ells = fixed_lines()

    def lag_planes_containing_line(ell: Line) -> List[Tuple[Vec, Vec]]:
        return [L for L in lags if plane_contains_line(L, ell)]

    # Special fixed line: ell=<v> should have 4 lag planes, all fixed.
    special_lags = lag_planes_containing_line(v_line)
    refined_special_ok = len(special_lags) == 4 and all(tau_on_plane(v, L) == L for L in special_lags)

    # Other fixed lines: exactly one containing v is fixed, other 3 should permute as a 3-cycle.
    refined_other_ok = True
    for ell in fixed_ells:
        if ell == v_line:
            continue
        Ls = lag_planes_containing_line(ell)
        if len(Ls) != 4:
            refined_other_ok = False
            break
        fixed_Ls = [L for L in Ls if tau_on_plane(v, L) == L]
        if len(fixed_Ls) != 1:
            refined_other_ok = False
            break
        # the other three must form one 3-cycle
        other = [L for L in Ls if L not in fixed_Ls]
        # follow orbit inside the set
        start = other[0]
        o1 = tau_on_plane(v, start)
        o2 = tau_on_plane(v, o1)
        if not (o1 in other and o2 in other and tau_on_plane(v, o2) == start):
            refined_other_ok = False
            break

    # Nonfixed lines: no fixed flags above them.
    refined_nonfixed_ok = True
    fixed_flag_set = {fl for fl in flags if (tau_on_line(v, fl[0]), tau_on_plane(v, fl[1])) == fl}
    for ell in lines:
        if tau_on_line(v, ell) == ell:
            continue
        Ls = lag_planes_containing_line(ell)
        for L in Ls:
            if (ell, L) in fixed_flag_set:
                refined_nonfixed_ok = False
                break
        if not refined_nonfixed_ok:
            break

    payload = Payload(
        v=list(v),
        points_total=len(lines),
        points_fixed=points_fixed,
        points_cycles={str(k): int(vv) for k, vv in sorted(points_cycles.items())},
        lag_total=len(lags),
        lag_fixed=lag_fixed,
        lag_cycles={str(k): int(vv) for k, vv in sorted(lag_cycles.items())},
        flags_total=len(flags),
        flags_fixed=flags_fixed,
        flags_cycles={str(k): int(vv) for k, vv in sorted(flags_cycles.items())},
        refined_fixed_line_all_four_fixed=bool(refined_special_ok),
        refined_other_fixed_line_structure_ok=bool(refined_other_ok),
        refined_nonfixed_line_no_fixed_flags=bool(refined_nonfixed_ok),
    )

    if not args.no_output:
        _write_json(export_dir() / "m2_level3_boundary_transvection_counts.json", asdict(payload))

        tex = [
            "% Auto-generated by scripts/exp_m2_level3_boundary_transvection_counts.py",
            r"\[",
            r"|\PP^3(\FF_3)|=40,\qquad |\mathrm{Lag}(\FF_3^4)|=40,\qquad |\mathrm{Flag}|=160.",
            r"\]",
            r"\[",
            rf"\#\mathrm{{Fix}}_{{\PP(V)}}(\tau_v)={points_fixed},\qquad (40-{points_fixed})/3={(40-points_fixed)//3}.",
            r"\]",
            r"\[",
            rf"\#\mathrm{{Fix}}_{{\mathrm{{Lag}}(V)}}(\tau_v)={lag_fixed},\qquad (40-{lag_fixed})/3={(40-lag_fixed)//3}.",
            r"\]",
            r"\[",
            rf"\#\mathrm{{Fix}}_{{\mathrm{{Flag}}(V)}}(\tau_v)={flags_fixed},\qquad (160-{flags_fixed})/3={(160-flags_fixed)//3}.",
            r"\]",
        ]
        _write_text(generated_dir() / "eq_m2_level3_boundary_transvection_counts.tex", "\n".join(tex) + "\n")

    dt = time.time() - t0
    ok = (
        payload.points_total == 40
        and payload.points_fixed == 13
        and payload.lag_total == 40
        and payload.lag_fixed == 4
        and payload.flags_total == 160
        and payload.flags_fixed == 16
        and payload.refined_fixed_line_all_four_fixed
        and payload.refined_other_fixed_line_structure_ok
        and payload.refined_nonfixed_line_no_fixed_flags
    )
    print(
        "[m2-level3-delta0-transvection] done"
        f" ok={ok} fixed(P, Lag, Flag)=({points_fixed},{lag_fixed},{flags_fixed})"
        f" seconds={dt:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()

