#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Primitive Artin split for the real-input 40-state kernel.

We report a refined decomposition:
  p_n(M) = p_n(in) + p_n(-F) + b_n,
where
  - in := the input-skeleton channel (A = F ⊗ F),
  - -F := the twist channel (golden factor with sign),
  - b_n is a boundary short-cycle term supported only at n=1,2.

We use the determinant factorization:
  det(I-zM) = det(I-zA) * det_vert(z),
where
  det(I-zA) = (1+z)^2(1-3z+z^2),
  det_vert(z)= (1-z)^2(1+z)(1+z-z^2),
so
  zeta_M = zeta_in * zeta_vert.

At the primitive level, the Möbius--log transform is additive:
  P_M(z) = P_in(z) + P_vert(z),
so coefficients satisfy p_n(M)=p_n(in)+q_n with q_n := [z^n] P_vert(z).
Moreover, for this kernel q_n splits as q_n = p_n(-F) + b_n.

We compute:
  - p_n(M) from artifacts/export/sync_kernel_real_input_40.json (already audited from M),
  - p_n(in) from the closed-form trace of A via its characteristic polynomial,
  - the twist contribution p_n(-F) from Lucas traces (Tr(F^n)),
  - b_n explicitly (only n=1,2),
  - q_n by subtraction and by checking q_n = p_n(-F)+b_n.

Outputs:
  - artifacts/export/real_input_40_primitive_artin_split.json
  - sections/generated/tab_real_input_40_primitive_artin_split.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

from common_paths import export_dir, generated_dir


def mobius(n: int) -> int:
    if n == 1:
        return 1
    mu = 1
    p = 2
    nn = n
    while p * p <= nn:
        if nn % p == 0:
            nn //= p
            if nn % p == 0:
                return 0
            mu = -mu
        p += 1
    if nn > 1:
        mu = -mu
    return mu


def s_n_quadratic_sum(n_max: int) -> List[int]:
    """Return s_n = (phi^2)^n + (phi^{-2})^n as integers, for n=0..n_max."""
    if n_max < 0:
        return []
    s = [0] * (n_max + 1)
    s[0] = 2
    if n_max >= 1:
        s[1] = 3
    for n in range(2, n_max + 1):
        s[n] = 3 * s[n - 1] - s[n - 2]
    return s


def traces_in(n_max: int) -> List[int]:
    """a_n(in) = Tr(A^n) for det(I-zA)=(1+z)^2(1-3z+z^2)."""
    # Eigenvalues: -1 (mult 2) and roots of t^2-3t+1 (phi^2, phi^{-2}).
    s = s_n_quadratic_sum(n_max)
    out = []
    for n in range(1, n_max + 1):
        out.append((2 * ((-1) ** n)) + s[n])
    return out


def lucas(n_max: int) -> List[int]:
    """Return Lucas numbers L_n = Tr(F^n) for n=0..n_max (integers)."""
    if n_max < 0:
        return []
    L = [0] * (n_max + 1)
    L[0] = 2
    if n_max >= 1:
        L[1] = 1
    for n in range(2, n_max + 1):
        L[n] = L[n - 1] + L[n - 2]
    return L


def traces_twist(n_max: int) -> List[int]:
    """a_n(twist) = Tr((-F)^n) = (-1)^n Tr(F^n) = (-1)^n L_n for n=1..n_max."""
    L = lucas(n_max)
    return [(((-1) ** n) * L[n]) for n in range(1, n_max + 1)]


def primitives_from_traces(a: List[int]) -> List[int]:
    """Given a_n for n=1..N, return p_n for n=1..N."""
    N = len(a)
    p: List[int] = []
    for n in range(1, N + 1):
        acc = 0
        for d in range(1, n + 1):
            if n % d == 0:
                acc += mobius(d) * a[n // d - 1]
        if acc % n != 0:
            raise ValueError(f"p_n not integer at n={n}")
        p.append(acc // n)
    return p


@dataclass(frozen=True)
class Row:
    n: int
    p_in: int
    p_twist: int
    p_bdry: int
    q_vert: int
    p_M: int


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        "\\caption{Primitive split for the real-input $40$-state kernel. "
        "We report the space/twist/boundary decomposition "
        "$p_n(M)=p_n(\\mathrm{in})+p_n(-F)+b_n$, where "
        "$q_n:=p_n(M)-p_n(\\mathrm{in})=p_n(-F)+b_n$ is the signed vertical contribution and "
        "$b_n$ is supported only at $n=1,2$.}"
    )
    lines.append("\\label{tab:real_input_40_primitive_artin_split}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$n$ & $p_n(\\mathrm{in})$ & $p_n(-F)$ (signed) & $b_n$ & $q_n$ (signed) & $p_n(M)$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(f"{r.n} & {r.p_in} & {r.p_twist} & {r.p_bdry} & {r.q_vert} & {r.p_M}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Primitive Artin split for real-input 40-state kernel.")
    parser.add_argument("--max-n", type=int, default=10)
    parser.add_argument(
        "--in-json",
        type=str,
        default=str(export_dir() / "sync_kernel_real_input_40.json"),
        help="Input JSON path containing p_n(M).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_primitive_artin_split.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_primitive_artin_split.tex"),
    )
    args = parser.parse_args()

    payload = json.loads(Path(args.in_json).read_text(encoding="utf-8"))
    p_M = [int(x) for x in payload["p_n"][: int(args.max_n)]]
    N = len(p_M)

    a_in = traces_in(N)
    p_in = primitives_from_traces(a_in)
    q = [pm - pin for pm, pin in zip(p_M, p_in, strict=True)]

    # Twist block: -F, where Tr(F^n)=Lucas number L_n and Tr((-F)^n)=(-1)^n L_n.
    a_tw = traces_twist(N)
    p_tw = primitives_from_traces(a_tw)

    # Boundary short-cycle term: (1-z)^{-2}(1+z)^{-1} contributes b_1=b_2=1, else 0.
    p_bdry = [1 if (i + 1) in (1, 2) else 0 for i in range(N)]

    # Audit the refined split: q_n = p_n(-F) + b_n.
    q_refined = [pt + pb for pt, pb in zip(p_tw, p_bdry, strict=True)]
    if q_refined != q:
        raise ValueError(f"refined split mismatch: q != p_twist + b at max_n={N}")

    rows = [
        Row(
            n=i + 1,
            p_in=p_in[i],
            p_twist=p_tw[i],
            p_bdry=p_bdry[i],
            q_vert=q[i],
            p_M=p_M[i],
        )
        for i in range(N)
    ]

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps(
            {
                "max_n": int(args.max_n),
                "p_M": p_M,
                "p_in": p_in,
                "p_twist": p_tw,
                "p_boundary": p_bdry,
                "q_vert": q,
                "rows": [asdict(r) for r in rows],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"[real-input-40-prim-artin] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[real-input-40-prim-artin] wrote {tout}", flush=True)
    print("[real-input-40-prim-artin] done", flush=True)


if __name__ == "__main__":
    main()

