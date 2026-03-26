#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit squarefreeness / coprimality for A_{32}(y), B_{66}(y) and separation from
the Lee--Yang branch locus y(y-1)P_LY(y).

Outputs:
  artifacts/export/xi_weight_tripling_index_squarefree_audit.json
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp

from common_paths import paper_root


def _extract_tex_poly(src: str, name: str) -> str:
    # Match lines like: A_{32}(y)= ... .
    # The generated file uses display math blocks; we capture inside the equality.
    m = re.search(rf"{re.escape(name)}\(y\)\s*=\s*([^.\n]+)\.", src)
    if not m:
        raise ValueError(f"Could not find polynomial assignment for {name}(y)")
    return m.group(1).strip()


def _tex_to_sympy(expr: str, y: sp.Symbol) -> sp.Poly:
    # Convert "729 y^{32} - 11664 y^{31} + ..." to sympy Poly over QQ.
    s = expr
    s = s.replace("{", "").replace("}", "")
    s = re.sub(r"\by\^(\d+)", r"y**\1", s)  # after brace stripping, y^{n} -> y^n
    s = re.sub(r"\by\*\*(\d+)", r"y**\1", s)
    s = re.sub(r"\by\s*\*\*\s*(\d+)", r"y**\1", s)
    s = re.sub(r"\by\s*\^\s*(\d+)", r"y**\1", s)
    s = re.sub(r"\by\s*\*\*\s*(\d+)", r"y**\1", s)
    s = re.sub(r"\by\s*\*\s*\*\s*(\d+)", r"y**\1", s)
    s = re.sub(r"\by\s*\*\s*", "y*", s)
    s = re.sub(r"\s+", " ", s).strip()
    # Insert explicit multiplication where needed.
    # - "729 y**32" -> "729*y**32"
    # - "256y**3" -> "256*y**3"
    # - ")y" -> ")*y"
    s = re.sub(r"(\d)\s+y", r"\1*y", s)
    s = re.sub(r"(\d)y", r"\1*y", s)
    s = re.sub(r"\)y", r")*y", s)
    s = re.sub(r"y\s+(\d)", r"y*\1", s)
    # Sympy parse
    f = sp.sympify(s, locals={"y": y})
    return sp.Poly(f, y, domain=sp.QQ)


def _gcd_deg(a: sp.Poly, b: sp.Poly) -> int:
    g = sp.gcd(a, b)
    if g.is_zero:
        return -1
    return int(g.degree())

def _is_squarefree(p: sp.Poly) -> bool:
    return _gcd_deg(p, p.diff()) == 0


def main() -> None:
    root = paper_root()
    tex_path = root / "sections" / "generated" / "eq_fold_zm_elliptic_weight_tripling_discriminant.tex"
    src = tex_path.read_text(encoding="utf-8")

    y = sp.Symbol("y")

    PLY_expr = _extract_tex_poly(src, "P_{\\mathrm{LY}}")
    A32_expr = _extract_tex_poly(src, "A_{32}")
    B66_expr = _extract_tex_poly(src, "B_{66}")

    PLY = _tex_to_sympy(PLY_expr, y)
    A32 = _tex_to_sympy(A32_expr, y)
    B66 = _tex_to_sympy(B66_expr, y)

    branch = sp.Poly(y * (y - 1), y, domain=sp.QQ) * PLY
    idx = A32 * B66

    out: Dict[str, object] = {
        "degrees": {"PLY": int(PLY.degree()), "A32": int(A32.degree()), "B66": int(B66.degree())},
        "gcd_degrees": {
            "gcd(A32, A32')": _gcd_deg(A32, A32.diff()),
            "gcd(B66, B66')": _gcd_deg(B66, B66.diff()),
            "gcd(A32, B66)": _gcd_deg(A32, B66),
            "gcd(A32*B66, y(y-1)PLY)": _gcd_deg(idx, branch),
        },
        "squarefree": {
            "A32": _is_squarefree(A32),
            "B66": _is_squarefree(B66),
            "A32*B66": _is_squarefree(idx),
        },
    }

    out_path = root / "artifacts" / "export" / "xi_weight_tripling_index_squarefree_audit.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

