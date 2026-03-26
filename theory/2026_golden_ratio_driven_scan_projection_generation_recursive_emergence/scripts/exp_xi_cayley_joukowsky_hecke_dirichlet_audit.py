#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit Cayley–Joukowsky / dilation conjugacy / zeta-multiplier identities.

This script audits identities stated in:
  sections/body/zeta_finite_part/xi/subsubsec__xi-cayley-joukowsky-singular-circle-hecke-dirichlet.tex

Outputs:
- artifacts/export/xi_cayley_joukowsky_hecke_dirichlet_audit.json
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Dict

import sympy as sp

from common_paths import export_dir


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool


def _simp(expr: sp.Expr) -> sp.Expr:
    return sp.simplify(sp.together(sp.factor(expr)))


def main() -> None:
    x, theta = sp.symbols("x theta", real=True)
    m = sp.symbols("m", positive=True, real=True)
    L = sp.symbols("L", positive=True, real=True)
    w = sp.symbols("w")
    I = sp.I

    checks = []

    # (1) Cayley angle derivative: theta = 2 arctan x => dtheta/(2pi) = dx/(pi(1+x^2))
    theta_of_x = 2 * sp.atan(x)
    dtheta_dx = sp.diff(theta_of_x, x)
    checks.append(Check("cayley_pushforward_density", _simp(dtheta_dx - 2 / (1 + x**2)) == 0))

    # (2) Joukowsky ellipse speed |dS/dtheta|^2 = a^2 sin^2 + b^2 cos^2
    a = sp.sqrt(L) + 1 / sp.sqrt(L)
    b = sp.sqrt(L) - 1 / sp.sqrt(L)
    S = sp.sqrt(L) * sp.exp(I * theta) + (1 / sp.sqrt(L)) * sp.exp(-I * theta)
    dS = sp.diff(S, theta)
    speed_sq = _simp(dS * sp.conjugate(dS))
    target_speed_sq = _simp(a**2 * sp.sin(theta) ** 2 + b**2 * sp.cos(theta) ** 2)
    checks.append(Check("joukowsky_speed_identity", _simp(speed_sq - target_speed_sq) == 0))

    # (3) Dilation conjugacy on circle: phi_m(w) closed form and semigroup law.
    C = lambda t: (1 + I * t) / (1 - I * t)  # noqa: E731
    Cinv = lambda ww: -I * (ww - 1) / (ww + 1)  # noqa: E731
    phi = _simp(C(m * Cinv(w)))
    phi_closed = _simp(((1 - m) + (1 + m) * w) / ((1 + m) + (1 - m) * w))
    checks.append(Check("dilation_conjugacy_closed_form", _simp(phi - phi_closed) == 0))

    n = sp.symbols("n", positive=True, real=True)
    phi_m = lambda ww: _simp(((1 - m) + (1 + m) * ww) / ((1 + m) + (1 - m) * ww))  # noqa: E731
    phi_n = lambda ww: _simp(((1 - n) + (1 + n) * ww) / ((1 + n) + (1 - n) * ww))  # noqa: E731
    left = _simp(phi_m(phi_n(w)))
    right = _simp(((1 - m * n) + (1 + m * n) * w) / ((1 + m * n) + (1 - m * n) * w))
    checks.append(Check("dilation_conjugacy_semigroup", _simp(left - right) == 0))

    # (4) Unitary weight identity for U_m at the level of measure-change algebra.
    u = sp.symbols("u", real=True)
    x_sub = m * u
    lhs_density = _simp((m * (1 + x**2) / (m**2 + x**2)) * (1 / (1 + x**2)))
    lhs_after = _simp(lhs_density.subs({x: x_sub}) * m)  # dx = m du
    rhs_density = _simp(1 / (1 + u**2))
    checks.append(Check("U_m_unitarity_weight_change", _simp(lhs_after - rhs_density) == 0))

    # (5) Linearization weight identity used in WU_m translation.
    y = sp.symbols("y", real=True)
    expr = sp.sqrt(m * (1 + sp.exp(2 * y)) / (m**2 + sp.exp(2 * y))) * sp.sqrt(
        sp.exp(y) / (1 + sp.exp(2 * y))
    )
    target = sp.sqrt(sp.exp(y - sp.log(m)) / (1 + sp.exp(2 * (y - sp.log(m)))))
    checks.append(Check("W_linearizes_translation_weight", _simp(expr - target) == 0))

    assert all(c.ok for c in checks), "One or more audits failed"

    out: Dict[str, object] = {
        "checks": [{"name": c.name, "ok": c.ok} for c in checks],
        "notes": {
            "file": "subsubsec__xi-cayley-joukowsky-singular-circle-hecke-dirichlet.tex",
            "sympy": sp.__version__,
        },
    }

    p = export_dir() / "xi_cayley_joukowsky_hecke_dirichlet_audit.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {p.relative_to(export_dir().parent)}", flush=True)


if __name__ == "__main__":
    main()

