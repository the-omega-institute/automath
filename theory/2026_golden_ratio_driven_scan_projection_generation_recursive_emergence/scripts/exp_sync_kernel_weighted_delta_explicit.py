#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Export an explicit closed form for Delta(z,u)=det(I - z B(u)) for the weighted sync-kernel.

We start from the paper's 6th-degree polynomial (the Perron branch equation):
  F(λ,u)=λ^6-(1+u)λ^5-5uλ^4+3u(1+u)λ^3
        -u(u^2-3u+1)λ^2+u(u^3-3u^2-3u+1)λ+u^2(u^2+u+1).

For this kernel, det(I - z B(u)) has degree 6 in z (four eigenvalues are 0 for all u),
and we have the exact identity
  Delta(z,u) = z^6 * F(1/z, u).

This script:
  - writes a LaTeX snippet for Delta(z,u),
  - numerically checks Delta(z,u) against det(I - z B(u)) on random samples,
  - checks the self-duality identity Delta(z,u)=Delta(uz,1/u) symbolically.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import random
from pathlib import Path
from typing import List, Tuple

import numpy as np
import sympy as sp

from common_paths import generated_dir
from exp_sync_kernel_weighted_pressure import STATES, build_edges


def _F(lam: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    return (
        lam**6
        - (1 + u) * lam**5
        - 5 * u * lam**4
        + 3 * u * (1 + u) * lam**3
        - u * (u**2 - 3 * u + 1) * lam**2
        + u * (u**3 - 3 * u**2 - 3 * u + 1) * lam
        + u**2 * (u**2 + u + 1)
    )


def _build_numeric_B(u0: complex) -> np.ndarray:
    n = len(STATES)
    idx = {s: i for i, s in enumerate(STATES)}
    B = np.zeros((n, n), dtype=np.complex128)
    for edge in build_edges():
        i = idx[edge.src]
        j = idx[edge.dst]
        B[i, j] += 1.0 if edge.e == 0 else complex(u0)
    return B


def _samples(seed: int, count: int) -> List[Tuple[complex, float]]:
    rng = random.Random(seed)
    out: List[Tuple[complex, float]] = []
    for _ in range(count):
        # Keep u away from 0 and away from the unit circle's singular substitution u->1/u issues.
        ur = rng.choice([0.25, 0.5, 0.8, 1.3, 2.0, 3.0])
        ui = rng.choice([0.0, 0.1, -0.2])
        u0 = complex(ur, ui)
        z0 = rng.choice([0.03, 0.05, 0.08, 0.1])
        out.append((u0, float(z0)))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Export explicit Delta(z,u) for weighted sync-kernel.")
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_weighted_delta_explicit.tex"),
        help="Output LaTeX snippet path.",
    )
    parser.add_argument("--check-count", type=int, default=12, help="Number of random numeric checks.")
    parser.add_argument("--seed", type=int, default=12345, help="RNG seed for checks.")
    args = parser.parse_args()

    z, u, lam = sp.symbols("z u lam")
    F = _F(lam, u)
    Delta = sp.expand(z**6 * F.subs(lam, 1 / z))

    # Symbolic self-duality check: Delta(z,u)=Delta(uz,1/u)
    print("[delta-explicit] checking self-duality symbolically...", flush=True)
    chk = sp.simplify(Delta - sp.expand(Delta.subs({z: u * z, u: 1 / u})))
    if chk != 0:
        raise RuntimeError(f"Self-duality check failed: Delta(z,u)-Delta(uz,1/u) = {chk}")

    # Numeric determinant check against the 10x10 B(u) definition.
    print("[delta-explicit] checking against det(I - z B(u)) numerically...", flush=True)
    for (u0, z0) in _samples(args.seed, args.check_count):
        B = _build_numeric_B(u0)
        det_num = np.linalg.det(np.eye(B.shape[0], dtype=np.complex128) - z0 * B)
        det_poly = complex(sp.N(Delta.subs({u: u0, z: z0}), 80))
        err = abs(det_num - det_poly)
        if err > 1e-8 * max(1.0, abs(det_num), abs(det_poly)):
            raise RuntimeError(
                f"Numeric check failed at u={u0}, z={z0}: |det - poly|={err}, "
                f"det={det_num}, poly={det_poly}"
            )

    # Write LaTeX.
    tex_path = Path(args.tex_out)
    tex_path.parent.mkdir(parents=True, exist_ok=True)
    Delta_latex = sp.latex(Delta)

    def _latex_multiline(tex: str, *, max_line_len: int = 95) -> List[str]:
        """Greedy split of a TeX polynomial string into multiple lines."""
        s = tex.strip()
        s = s.replace(" - ", " + - ")
        raw = [p.strip() for p in s.split(" + ") if p.strip()]
        if not raw:
            return ["0"]

        terms: List[str] = []
        for i, p in enumerate(raw):
            if i == 0:
                terms.append(p)
                continue
            if p.startswith("-"):
                terms.append("- " + p[1:].lstrip())
            else:
                terms.append("+ " + p)

        out_lines: List[str] = []
        cur = terms[0]
        for t in terms[1:]:
            if len(cur) + 1 + len(t) > max_line_len:
                out_lines.append(cur)
                cur = t
            else:
                cur = cur + " " + t
        out_lines.append(cur)
        return out_lines

    poly_lines = _latex_multiline(Delta_latex, max_line_len=85)
    lines: List[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append("\\begin{equation}\\label{eq:sync-kernel-weighted-delta-explicit}")
    lines.append("\\boxed{")
    lines.append("\\begin{aligned}")
    if len(poly_lines) == 1:
        lines.append("\\Delta(z,u)&=" + poly_lines[0])
    else:
        lines.append("\\Delta(z,u)&=" + poly_lines[0] + "\\\\")
        for ln in poly_lines[1:-1]:
            lines.append("&" + ln + "\\\\")
        lines.append("&" + poly_lines[-1])
    lines.append("\\end{aligned}")
    lines.append("}")
    lines.append("\\end{equation}")
    tex_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[delta-explicit] wrote {tex_path}", flush=True)
    print("[delta-explicit] done", flush=True)


if __name__ == "__main__":
    main()

