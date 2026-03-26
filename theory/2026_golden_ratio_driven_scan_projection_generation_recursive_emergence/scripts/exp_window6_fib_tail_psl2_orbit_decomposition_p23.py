#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Window-6 Fibonacci-tail PSL2(P^1(F_p)) orbit decomposition certificate (p=23).

All code is English-only by repository convention.

We consider the Fibonacci-tail matrix
  G_m = [[F_{m+3}, F_{m+2}],
         [F_{m+4}, F_{m+3}]]
at m=6, reduce mod p=23, and study its Möbius action on P^1(F_23).

Outputs:
  - artifacts/export/window6_fib_tail_psl2_orbit_decomposition_p23.json
  - sections/generated/eq_window6_fib_tail_p23_p1_orbit_decomposition.tex
  - sections/generated/tab_window6_fib_tail_p23_p1_orbits.tex
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

from common_paths import export_dir, generated_dir


Point = Optional[int]  # None denotes infinity on P^1(F_p)


def fib_upto(n: int) -> List[int]:
    """Return [F_0, F_1, ..., F_n] with F_0=0, F_1=1."""
    if n < 0:
        raise ValueError("n must be non-negative")
    f = [0] * (n + 1)
    if n >= 0:
        f[0] = 0
    if n >= 1:
        f[1] = 1
    for k in range(2, n + 1):
        f[k] = f[k - 1] + f[k - 2]
    return f


def G_m(m: int) -> Tuple[int, int, int, int]:
    """Return integer matrix entries (a,b,c,d) for G_m."""
    if m < 2:
        raise ValueError("m must be >= 2")
    F = fib_upto(m + 4)
    a = F[m + 3]
    b = F[m + 2]
    c = F[m + 4]
    d = F[m + 3]
    return a, b, c, d


def _inv_mod(x: int, p: int) -> int:
    x %= p
    if x == 0:
        raise ZeroDivisionError("no inverse mod p")
    return pow(x, p - 2, p)


def mobius_apply(M: Tuple[int, int, int, int], x: Point, p: int) -> Point:
    """Apply Möbius transform induced by M on P^1(F_p)."""
    a, b, c, d = (M[0] % p, M[1] % p, M[2] % p, M[3] % p)
    if x is None:
        if c % p == 0:
            return None
        return (a * _inv_mod(c, p)) % p
    denom = (c * (x % p) + d) % p
    if denom == 0:
        return None
    num = (a * (x % p) + b) % p
    return (num * _inv_mod(denom, p)) % p


def _point_key(x: Point) -> Tuple[int, int]:
    # Sort finite points first, infinity last.
    if x is None:
        return (1, 0)
    return (0, int(x))


def _point_tex(x: Point) -> str:
    if x is None:
        return r"\infty"
    return str(int(x))


@dataclass(frozen=True)
class Orbit:
    rep: Point
    cycle: List[Point]  # in forward-iteration order, starting at rep

    @property
    def size(self) -> int:
        return len(self.cycle)


def orbit_decomposition(M: Tuple[int, int, int, int], p: int) -> List[Orbit]:
    pts: List[Point] = list(range(p)) + [None]
    unseen = set(pts)
    out: List[Orbit] = []
    while unseen:
        rep = min(unseen, key=_point_key)
        cyc: List[Point] = []
        seen_local = set()
        x = rep
        while True:
            if x in seen_local:
                raise AssertionError("cycle repetition before returning to representative")
            seen_local.add(x)
            cyc.append(x)
            x = mobius_apply(M, x, p)
            if x == rep:
                break
        unseen -= set(cyc)
        out.append(Orbit(rep=rep, cycle=cyc))
    out.sort(key=lambda o: _point_key(o.rep))
    return out


def write_outputs(*, json_out: Path, tex_eq: Path, tex_tab: Path) -> None:
    m = 6
    p = 23

    a, b, c, d = G_m(m)
    M = (a % p, b % p, c % p, d % p)

    # Basic sanity checks: determinant in SL2, and order-3 in PSL2 at p=23 by direct powering.
    det = (M[0] * M[3] - M[1] * M[2]) % p
    if det != 1:
        raise AssertionError(f"Unexpected det mod p: det={det} (expected 1)")

    def mat_mul(X: Tuple[int, int, int, int], Y: Tuple[int, int, int, int]) -> Tuple[int, int, int, int]:
        (a1, b1, c1, d1) = X
        (a2, b2, c2, d2) = Y
        return (
            (a1 * a2 + b1 * c2) % p,
            (a1 * b2 + b1 * d2) % p,
            (c1 * a2 + d1 * c2) % p,
            (c1 * b2 + d1 * d2) % p,
        )

    I = (1 % p, 0, 0, 1 % p)
    M2 = mat_mul(M, M)
    M3 = mat_mul(M2, M)
    if M3 != I:
        raise AssertionError(f"Unexpected M^3 mod p: M3={M3} (expected identity)")
    if M == I:
        raise AssertionError("Unexpected: M is identity mod p")

    orbits = orbit_decomposition(M, p)
    sizes = [o.size for o in orbits]
    if sorted(sizes) != [3] * 8:
        raise AssertionError(f"Unexpected orbit sizes on P1(F_{p}): {sorted(sizes)}")

    payload: Dict[str, object] = {
        "m": m,
        "p": p,
        "Gm_Z": {"a": a, "b": b, "c": c, "d": d},
        "Gm_mod_p": {"a": M[0], "b": M[1], "c": M[2], "d": M[3]},
        "det_mod_p": det,
        "orbits": [
            {
                "rep": ("inf" if o.rep is None else int(o.rep)),
                "cycle": [("inf" if x is None else int(x)) for x in o.cycle],
            }
            for o in orbits
        ],
    }

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_eq.parent.mkdir(parents=True, exist_ok=True)
    tex_eq.write_text(
        "\n".join(
            [
                "% AUTO-GENERATED by scripts/exp_window6_fib_tail_psl2_orbit_decomposition_p23.py",
                r"\begin{equation}\label{eq:window6_fib_tail_p23_p1_orbit_decomposition}",
                r"\begin{aligned}",
                rf"|\mathbb{{P}}^1(\mathbb{{F}}_{{{p}}})|&={p+1},\\",
                rf"\mathbb{{P}}^1(\mathbb{{F}}_{{{p}}})&=\bigsqcup_{{j=1}}^{{{len(orbits)}}}\mathcal{{O}}_j,"
                rf"\qquad (|\mathcal{{O}}_j|)_{{j=1}}^{{{len(orbits)}}}=({','.join(['3']*len(orbits))}).",
                r"\end{aligned}",
                r"\end{equation}",
                "",
            ]
        ),
        encoding="utf-8",
    )

    rows: List[str] = []
    for j, o in enumerate(orbits, start=1):
        cyc_tex = "(" + ",\\ ".join(_point_tex(x) for x in o.cycle) + ")"
        rep_tex = _point_tex(o.rep)
        rows.append(rf"{j} & ${rep_tex}$ & ${cyc_tex}$\\")

    tex_tab.parent.mkdir(parents=True, exist_ok=True)
    tex_tab.write_text(
        "\n".join(
            [
                "% AUTO-GENERATED by scripts/exp_window6_fib_tail_psl2_orbit_decomposition_p23.py",
                r"\begin{table}[H]",
                r"\centering",
                r"\small",
                r"\setlength{\tabcolsep}{10pt}",
                r"\renewcommand{\arraystretch}{1.10}",
                r"\caption{Orbit decomposition of $\mathbb{P}^1(\mathbb{F}_{23})$ under the Möbius action of the Fibonacci-tail matrix $G_6$ modulo $23$. Each orbit is shown as a $3$-cycle in forward-iteration order, starting at the representative.}",
                r"\label{tab:window6_fib_tail_p23_p1_orbits}",
                r"\begin{tabular}{r r l}",
                r"\toprule",
                r"$\#$ & rep & cycle\\",
                r"\midrule",
                *rows,
                r"\bottomrule",
                r"\end{tabular}",
                r"\end{table}",
                "",
            ]
        ),
        encoding="utf-8",
    )


def main() -> None:
    json_out = export_dir() / "window6_fib_tail_psl2_orbit_decomposition_p23.json"
    tex_eq = generated_dir() / "eq_window6_fib_tail_p23_p1_orbit_decomposition.tex"
    tex_tab = generated_dir() / "tab_window6_fib_tail_p23_p1_orbits.tex"
    write_outputs(json_out=json_out, tex_eq=tex_eq, tex_tab=tex_tab)
    print(f"[ok] wrote {json_out}", flush=True)
    print(f"[ok] wrote {tex_eq}", flush=True)
    print(f"[ok] wrote {tex_tab}", flush=True)


if __name__ == "__main__":
    main()

