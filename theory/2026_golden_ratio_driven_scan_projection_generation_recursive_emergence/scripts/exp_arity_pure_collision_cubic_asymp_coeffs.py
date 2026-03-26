#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute closed-form Taylor coefficients for the pure-collision cubic pressure.

We work with the 4x4 input-skeleton matrix:
  A_xi(u) = D(u) (F ⊗ F),  D(u)=diag(1,1,1,u),
whose characteristic polynomial factors as:
  det(λI - A_xi(u)) = (λ+1)(λ^3 - 2λ^2 - (u+1)λ + u).

Define u = exp(z) and the principal Perron branch ρ(z) solving the cubic
with ρ(0)=φ^2, then define the pressure:
  P_xi(z) = log ρ(z).

This script computes exact closed forms for P_xi^{(k)}(0) for k=2,4,6,8,
exports a small LaTeX table, and writes a JSON artifact.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Coeffs:
    P2: str
    P4: str
    P6: str
    P8: str
    kappa_inf: str
    beta: str
    gamma6: str
    gamma8: str


def _ns_qsqrt5(expr: sp.Expr, dps: int = 80) -> sp.Expr:
    """Fast exactification into Q(sqrt(5)) via nsimplify."""
    s5 = sp.sqrt(5)
    return sp.nsimplify(sp.N(expr, dps), [s5])


def _implicit_derivatives_at_zero(max_order: int = 8) -> tuple[sp.Expr, List[sp.Expr]]:
    """
    Compute rho(0) and rho^{(k)}(0) for k=1..max_order exactly by implicit differentiation.

    Cubic: F(r,u) = r^3 - 2 r^2 - (u+1) r + u = 0,  with u=exp(z).
    We differentiate w.r.t. z at z=0 on the Perron branch r(0)=phi^2.
    """
    z = sp.Symbol("z")
    u = sp.exp(z)
    phi = (1 + sp.sqrt(5)) / 2
    r0 = sp.simplify(phi**2)

    if max_order < 1 or max_order > 12:
        raise ValueError("max_order must be in [1,12].")

    # Symbols for derivatives at 0.
    rs = sp.symbols(" ".join([f"r{i}" for i in range(1, max_order + 1)]))

    # Build truncated Taylor r(z)=r0 + Σ r_n z^n/n!
    r = r0
    for n, sym in enumerate(rs, start=1):
        r += sym * z**n / sp.factorial(n)
    F = sp.expand(r**3 - 2 * r**2 - (u + 1) * r + u)
    S = sp.series(F, z, 0, max_order + 1).removeO()

    subs: dict[sp.Symbol, sp.Expr] = {}
    out: List[sp.Expr] = []
    for n, sym in enumerate(rs, start=1):
        eqn = sp.expand(S).coeff(z, n).subs(subs)
        print(f"[pure-collision-asymp] solving rho^{n}(0)...", flush=True)
        sol = sp.solve(sp.Eq(eqn, 0), sym)
        if not sol:
            raise RuntimeError(f"Failed to solve for derivative order {n}.")
        val = sp.simplify(sol[0])
        subs[sym] = val
        out.append(val)
    return r0, out


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute closed-form P_xi''(0), P_xi^{(4)}(0) for pure-collision cubic.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_pure_collision_cubic_asymp_coeffs.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_arity_pure_collision_cubic_asymp_coeffs.tex"),
    )
    args = parser.parse_args()

    r0, ders = _implicit_derivatives_at_zero(max_order=8)
    r1, r2, r3, r4, r5, r6, r7, r8 = ders
    print("[pure-collision-asymp] converting to pressure derivatives...", flush=True)

    # P(z)=log r(z). We compute its Taylor coefficients up to z^8 via
    # formal power series arithmetic, to avoid heavy symbolic expansion.
    order = 8
    rs = [sp.Integer(0)] * (order + 1)
    rs[0] = r0
    derivs = [None, r1, r2, r3, r4, r5, r6, r7, r8]
    for n in range(1, order + 1):
        rs[n] = sp.simplify(derivs[n] / sp.factorial(n))

    # s(z) := (r(z)-r0)/r0, so log r(z) = log r0 + log(1+s(z)).
    s = [sp.Integer(0)] * (order + 1)
    for n in range(1, order + 1):
        s[n] = sp.simplify(rs[n] / r0)

    def mul(a: List[sp.Expr], b: List[sp.Expr]) -> List[sp.Expr]:
        out = [sp.Integer(0)] * (order + 1)
        for i in range(0, order + 1):
            if a[i] == 0:
                continue
            for j in range(0, order + 1 - i):
                if b[j] == 0:
                    continue
                out[i + j] += a[i] * b[j]
        return out

    log1p = [sp.Integer(0)] * (order + 1)
    power = s[:]  # s^1
    for m in range(1, order + 1):
        coef = sp.Rational(1, m) if (m % 2 == 1) else -sp.Rational(1, m)
        for n in range(1, order + 1):
            if power[n] != 0:
                log1p[n] += coef * power[n]
        power = mul(power, s)

    # Derivatives: P^{(n)}(0)=n!*coeff[z^n] log r(z).
    P2 = sp.simplify(sp.factorial(2) * log1p[2])
    P4 = sp.simplify(sp.factorial(4) * log1p[4])
    P6 = sp.simplify(sp.factorial(6) * log1p[6])
    P8 = sp.simplify(sp.factorial(8) * log1p[8])

    kappa_inf = sp.simplify(P2 / 2)
    beta = sp.simplify(P4 / 24)
    gamma6 = sp.simplify(-P6 / sp.factorial(6))  # coefficient for alpha^6 in Re P(i alpha)
    gamma8 = sp.simplify(P8 / sp.factorial(8))   # coefficient for alpha^8 in Re P(i alpha)

    coeffs = Coeffs(
        P2=sp.latex(P2),
        P4=sp.latex(P4),
        P6=sp.latex(P6),
        P8=sp.latex(P8),
        kappa_inf=sp.latex(kappa_inf),
        beta=sp.latex(beta),
        gamma6=sp.latex(gamma6),
        gamma8=sp.latex(gamma8),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"coeffs": asdict(coeffs)}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[pure-collision-asymp] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Closed-form Taylor data for the pure-collision cubic pressure "
        "$P_\\xi(z)=\\log\\rho(A_\\xi(e^{z}))$ at $z=0$ (Perron branch).}"
    )
    lines.append("\\label{tab:arity_pure_collision_cubic_asymp_coeffs}")
    lines.append("\\begin{tabular}{l l}")
    lines.append("\\toprule")
    lines.append("$P_\\xi''(0)$ & $" + coeffs.P2 + "$\\\\")
    lines.append("$P_\\xi^{(4)}(0)$ & $" + coeffs.P4 + "$\\\\")
    lines.append("$P_\\xi^{(6)}(0)$ & $" + coeffs.P6 + "$\\\\")
    lines.append("$P_\\xi^{(8)}(0)$ & $" + coeffs.P8 + "$\\\\")
    lines.append("$\\kappa_\\infty=P_\\xi''(0)/2$ & $" + coeffs.kappa_inf + "$\\\\")
    lines.append("$\\beta=P_\\xi^{(4)}(0)/24$ & $" + coeffs.beta + "$\\\\")
    lines.append("$\\gamma_6=-P_\\xi^{(6)}(0)/6!$ & $" + coeffs.gamma6 + "$\\\\")
    lines.append("$\\gamma_8=P_\\xi^{(8)}(0)/8!$ & $" + coeffs.gamma8 + "$\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[pure-collision-asymp] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

