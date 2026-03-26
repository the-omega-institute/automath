#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Edge-weight RH threshold for the 4th-collision kernel A_4(t).

We replace the single multi-edge weight "7" in A_4 by a continuous parameter t>0:

  A_4(t) =
    [[0,1,0,0,0],
     [0,0,t,0,1],
     [0,1,2,0,0],
     [1,0,1,0,0],
     [0,0,0,1,0]].

Its characteristic polynomial is linear in t:

  p_t(x) = det(xI - A_4(t)) = x^5 - 2x^4 - t x^3 - 2x + 2.

Let r(t)=rho(A_4(t)) be the Perron root and Λ(t) the sub-spectral radius.
The kernel-RH / Ramanujan condition is Λ(t) <= sqrt(r(t)).

Empirically (and consistent with the manuscript's "negative real mode" axis),
the RH boundary is triggered by a negative real eigenvalue μ_-(t) crossing the
square-root circle:

  |μ_-(t)| = sqrt(r(t))  <=>  r(t) = (-μ_-(t))^2.

Write μ_-(t)=-b (b>0). At an RH-sharp point we must have:

  p_t(-b)=0  and  p_t(b^2)=0.

Eliminating b via a resultant gives:

  Res_b(p_t(-b), p_t(b^2)) = (t+1)^2 * P_4(t),

where P_4 is an integer degree-8 polynomial. Its unique positive real root t_*
is the edge-weight threshold:

  t < t_*  => Λ(t) < sqrt(r(t))  (kernel-RH holds),
  t = t_*  => Λ(t) = sqrt(r(t))  (RH-sharp),
  t > t_*  => Λ(t) > sqrt(r(t))  (kernel-RH breaks).

Outputs:
  - artifacts/export/collision_kernel_A4_edge_weight_threshold.json
  - sections/generated/eq_collision_kernel_A4_edge_weight_threshold.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


def _fmt(x: mp.mpf, nd: int = 16) -> str:
    return mp.nstr(x, nd)


def _poly_P4() -> sp.Poly:
    t = sp.Symbol("t")
    P4 = t**8 - 10 * t**7 + 72 * t**6 - 24 * t**5 - 1924 * t**4 - 2904 * t**3 + 1312 * t**2 + 1464 * t - 1412
    return sp.Poly(sp.expand(P4), t)


def _resultant_factorization_P4() -> Tuple[sp.Symbol, sp.Poly, sp.Poly]:
    """Return (t, Res(t), P4(t)) where Res is the b-resultant and P4 is the degree-8 factor."""
    t = sp.Symbol("t")
    b = sp.Symbol("b")

    # p_t(x)=x^5-2x^4-tx^3-2x+2
    def p(x: sp.Expr) -> sp.Expr:
        return sp.expand(x**5 - 2 * x**4 - t * x**3 - 2 * x + 2)

    Res = sp.resultant(p(-b), p(b**2), b)
    fac = sp.factor_list(Res, t)

    P4 = None
    for f, e in fac[1]:
        if e == 1 and sp.Poly(f, t).degree() == 8:
            P4 = sp.Poly(f, t)
            break
    if P4 is None:
        raise RuntimeError("Failed to extract degree-8 factor P_4(t) from resultant.")

    return t, sp.Poly(Res, t), P4


def _roots_real_positive(poly: sp.Poly, *, dps: int) -> List[sp.Expr]:
    roots = poly.nroots(n=dps, maxsteps=200)
    imag_eps = sp.Float(10) ** (-(dps // 2))
    out: List[sp.Expr] = []
    for r in roots:
        rr = sp.re(r).evalf(dps)
        ii = sp.im(r).evalf(dps)
        if abs(ii) <= imag_eps and rr > 0:
            out.append(rr)
    out = sorted(out, key=lambda x: float(x))
    return out


def _p_roots_numeric(t_val: mp.mpf) -> List[mp.mpc]:
    """Return numerical roots of p_t(x)=0 as mpmath complex numbers."""
    # x^5 - 2x^4 - t x^3 + 0*x^2 - 2x + 2
    coeffs = [mp.mpf(1), mp.mpf(-2), -t_val, mp.mpf(0), mp.mpf(-2), mp.mpf(2)]
    return list(mp.polyroots(coeffs, maxsteps=200))


def _rhk_diagnostic(t_val: mp.mpf) -> Tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    """Return (r, Lam, ratio, mu_minus) at t>0."""
    roots = _p_roots_numeric(t_val)
    perron = max(roots, key=lambda z: abs(z))
    r = mp.re(perron)

    neg_reals = [mp.re(r0) for r0 in roots if abs(mp.im(r0)) < mp.mpf("1e-50") and mp.re(r0) < 0]
    if not neg_reals:
        raise RuntimeError("Expected at least one negative real root for t>0.")
    neg_reals.sort()
    mu_minus = neg_reals[0]

    others = [r0 for r0 in roots if r0 != perron]
    Lam = max(abs(r0) for r0 in others)
    ratio = Lam / mp.sqrt(r)
    return r, Lam, ratio, mu_minus


@dataclass(frozen=True)
class Payload:
    dps: int
    # polynomial certificates
    resultant_degree: int
    P4_degree: int
    # critical values
    t_star: str
    u_star: str
    gap_7_minus_t_star: str
    # spectral data at t_star
    r_star: str
    mu_star: str
    z_star: str
    Lambda_star: str
    ratio_star: str
    check_r_minus_mu2: str


def _write_tex(path: Path, *, t_star: mp.mpf, r: mp.mpf, Lam: mp.mpf, ratio: mp.mpf, mu_minus: mp.mpf, check: mp.mpf) -> None:
    nd = 16
    nd_ratio = 12
    nd_check = 24

    u_star = t_star / mp.mpf(7)
    gap = mp.mpf(7) - t_star
    # mpmath mpf does not support fixed-point __format__; use float for a stable
    # fixed-decimal display (12 d.p. is well within float precision here).
    ratio_fixed = f"{float(ratio):.{nd_ratio}f}"
    z_star = -mu_minus

    # TeX for P4(t)
    # (degree 8 is short enough to print in one line; keep it explicit as a certificate)
    P4_tex = (
        r"t^{8}-10t^{7}+72t^{6}-24t^{5}-1924t^{4}-2904t^{3}+1312t^{2}+1464t-1412"
    )

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_collision_kernel_A4_edge_weight_threshold.py")
    lines.append(r"\begin{equation}\label{eq:collision_kernel_A4_edge_weight_threshold}")
    lines.append(r"\begin{aligned}")
    lines.append(rf"P_4(t)&:={P4_tex},\\")
    lines.append(rf"P_4(t_\star)&=0,\qquad t_\star\approx {_fmt(t_star, nd)},\\")
    lines.append(rf"u_\star:=t_\star/7&\approx {_fmt(u_star, nd)},\qquad 7-t_\star\approx {_fmt(gap, nd)},\\")
    lines.append(rf"r_\star=\rho(A_4(t_\star))&\approx {_fmt(r, nd)},\qquad \mu_\star\approx {_fmt(mu_minus, nd)},\\")
    lines.append(rf"z_\star:=-\mu_\star&\approx {_fmt(z_star, nd)},\qquad r_\star=z_\star^2,\\")
    lines.append(rf"\Lambda(t_\star)/\sqrt{{r_\star}}&\approx {ratio_fixed},\qquad r_\star-\mu_\star^2\approx {_fmt(check, nd_check)}.")
    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute the A4(t) edge-weight RH threshold via resultant elimination.")
    parser.add_argument("--dps", type=int, default=120, help="Working decimal precision (sympy nroots + mpmath).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_edge_weight_threshold.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_collision_kernel_A4_edge_weight_threshold.tex"),
    )
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 60:
        raise SystemExit("Require --dps >= 60 for stable t_* output.")
    mp.mp.dps = dps

    t_sym, Res_t, P4 = _resultant_factorization_P4()
    roots_pos = _roots_real_positive(P4, dps=dps)
    if len(roots_pos) != 1:
        raise RuntimeError(f"Expected a unique positive real root of P_4(t), got {len(roots_pos)}.")

    t_star = mp.mpf(str(sp.N(roots_pos[0], dps)))
    r, Lam, ratio, mu_minus = _rhk_diagnostic(t_star)
    check = r - (mu_minus**2)

    payload = Payload(
        dps=dps,
        resultant_degree=int(Res_t.degree()),
        P4_degree=int(P4.degree()),
        t_star=_fmt(t_star, 40),
        u_star=_fmt(t_star / mp.mpf(7), 40),
        gap_7_minus_t_star=_fmt(mp.mpf(7) - t_star, 40),
        r_star=_fmt(r, 40),
        mu_star=_fmt(mu_minus, 40),
        z_star=_fmt(-mu_minus, 40),
        Lambda_star=_fmt(Lam, 40),
        ratio_star=_fmt(ratio, 24),
        check_r_minus_mu2=_fmt(check, 40),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[A4-edge-weight-threshold] wrote {jout}", flush=True)

    _write_tex(Path(args.tex_out), t_star=t_star, r=r, Lam=Lam, ratio=ratio, mu_minus=mu_minus, check=check)
    print(f"[A4-edge-weight-threshold] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

