#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Export the completed polynomial \\hat\\Delta(w,s) for the weighted sync-kernel.

Completion coordinates:
  u = r^2,
  s = r + r^{-1},
  w = z r = z sqrt(u).

The self-duality Delta(z,u)=Delta(uz,1/u) implies that, after completion,
Delta depends only on (w,s) and becomes an integer polynomial \\hat\\Delta(w,s) in Z[w,s]:
  Delta(z,u) = \\hat\\Delta(z sqrt(u), sqrt(u) + 1/sqrt(u)).

This script:
  - constructs Delta(z,u) from the verified 6th-degree Perron-branch polynomial,
  - constructs \\hat\\Delta(w,s) by symbolic substitution and elimination,
  - checks the identity Delta(z,u)=\\hat\\Delta(z sqrt(u), sqrt(u)+1/sqrt(u)) symbolically,
  - writes a LaTeX snippet with the explicit \\hat\\Delta(w,s).

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import List

import sympy as sp

from common_paths import generated_dir
from exp_sync_kernel_weighted_delta_explicit import _F


def main() -> None:
    parser = argparse.ArgumentParser(description="Export completed \\hat\\Delta(w,s) for weighted sync-kernel.")
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_weighted_delta_completed.tex"),
        help="Output LaTeX snippet path.",
    )
    args = parser.parse_args()

    z, u, lam = sp.symbols("z u lam")
    r, w, s = sp.symbols("r w s")

    # Delta(z,u) = z^6 F(1/z, u)
    F = _F(lam, u)
    Delta_zu = sp.expand(z**6 * F.subs(lam, 1 / z))

    # Completion substitution: u=r^2, w=z r.
    # We compute Delta as a Laurent polynomial in r with parameter w, then rewrite it in Z[w,s]
    # using the invariant ring Z[r,r^{-1}]^{r->1/r} = Z[s].
    Delta_wr_laurent = sp.expand(Delta_zu.subs({u: r**2, z: w / r}))

    # Collect coefficients of r^e and combine symmetric pairs into C_e(s)=r^e+r^{-e}.
    coeffs = {}
    for term in sp.Add.make_args(Delta_wr_laurent):
        c, e = term.as_coeff_exponent(r)
        if not e.is_Integer:
            raise RuntimeError(f"Non-integer r-exponent in term: {term}")
        ei = int(e)
        coeffs[ei] = coeffs.get(ei, 0) + c

    def C(k: int) -> sp.Expr:
        # C_k(s)=r^k+r^{-k}, with C_0=2, C_1=s, C_{k+1}=s C_k - C_{k-1}
        if k == 0:
            return sp.Integer(2)
        if k == 1:
            return s
        c0, c1 = sp.Integer(2), s
        for _ in range(2, k + 1):
            c0, c1 = c1, sp.expand(s * c1 - c0)
        return c1

    hat = sp.Integer(0)
    used = set()
    for e in sorted(coeffs.keys(), key=lambda x: abs(x)):
        if e in used:
            continue
        if e == 0:
            hat += coeffs[e]
            used.add(0)
            continue
        if sp.simplify(coeffs.get(e, 0) - coeffs.get(-e, 0)) != 0:
            raise RuntimeError(f"Not invariant under r->1/r at exponent {e}")
        hat += coeffs[e] * C(abs(e))
        used.add(e)
        used.add(-e)
    hat_ws = sp.expand(hat)

    # Check the defining identity by substituting w=z r, s=r+1/r back.
    chk = sp.simplify(Delta_zu.subs({u: r**2}) - hat_ws.subs({w: z * r, s: r + 1 / r}))
    if chk != 0:
        raise RuntimeError(f"Completion identity failed: Delta - hatDelta = {chk}")

    tex_path = Path(args.tex_out)
    tex_path.parent.mkdir(parents=True, exist_ok=True)
    hat_latex = sp.latex(hat_ws)
    lines: List[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append("\\begin{equation}\\label{eq:sync-kernel-weighted-delta-completed}")
    lines.append("\\boxed{")
    lines.append("\\widehat{\\Delta}(w,s)=" + hat_latex)
    lines.append("}")
    lines.append("\\end{equation}")
    tex_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[delta-completed] wrote {tex_path}", flush=True)


if __name__ == "__main__":
    main()

