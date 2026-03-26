#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Pole quadratic resonance for the A4(t) Newman criticality, and cyclotomic (ADE-adjacency)
injection points on the same one-parameter family.

Context (paper-local):
  - A_4(t) is the 5x5 collision-kernel family in the manuscript.
  - D_t(z) := det(I - z A_4(t)) is the spectral determinant (pole polynomial).
  - The Newman/RH-sharp threshold t_* is already certified by the degree-8 integer polynomial
    P_4(t) in sections/generated/eq_collision_kernel_A4_edge_weight_threshold.tex.

This script produces two additional, auditable certificates:

  (I) Newman criticality as a strict quadratic resonance in the z-plane:
      the RH-sharp point is equivalent to the existence of v in (0,1) such that
        D_t(v^2)=0 and D_t(-v)=0,
      i.e. the Perron pole and the dominant negative-real pole satisfy z_+ = z_-^2.
      Eliminating t yields an irreducible octic equation in v, and t_* admits two
      equivalent closed forms under this constraint.

  (II) Cyclotomic adjacency injection:
      for any integer h>=4, let c_h := 2 cos(pi/h) and v_h := 1/c_h. Define
        t_h^{adj} := c_h^2 + 2 c_h - 2/c_h^2 - 2/c_h^3.
      Then D_{t_h^{adj}}(-v_h)=0, hence -c_h is an eigenvalue of A_4(t_h^{adj}).
      We compute primitive integer minimal polynomials for h=12,18,30 and provide
      numerical values and a strict ordering chain relative to t_* and the ADE index
      intersection points t_{E6}, t_{E7}, t_{E8} already used in the manuscript.

Outputs:
  - artifacts/export/collision_kernel_A4_pole_quadratic_resonance_and_cyclotomic_adjacency_injection.json
  - sections/generated/eq_collision_kernel_A4_newman_pole_quadratic_resonance.tex
  - sections/generated/eq_collision_kernel_A4_cyclotomic_adjacency_injection.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


def _fmt(x: mp.mpf, nd: int = 16) -> str:
    return mp.nstr(x, nd)


def _poly_primitive_integer(expr: sp.Expr, var: sp.Symbol) -> sp.Poly:
    """
    Given a polynomial expression over QQ, clear denominators and return a primitive Poly over ZZ
    with positive leading coefficient.
    """
    pQQ = sp.Poly(sp.expand(expr), var, domain=sp.QQ)
    den_lcm = sp.ilcm(*[sp.denom(c) for c in pQQ.all_coeffs()]) if pQQ.degree() >= 0 else sp.Integer(1)
    pZ = sp.Poly(sp.expand(den_lcm * pQQ.as_expr()), var, domain=sp.ZZ)
    content = sp.gcd_list(pZ.all_coeffs()) if pZ.degree() >= 0 else sp.Integer(1)
    pZ = sp.Poly(sp.expand(pZ.as_expr() / content), var, domain=sp.ZZ)
    if pZ.LC() < 0:
        pZ = -pZ
    return pZ


def _factorint_signed(n: sp.Integer) -> Tuple[int, Dict[int, int]]:
    n_int = int(n)
    sign = -1 if n_int < 0 else 1
    fac = sp.factorint(abs(n_int))
    return sign, {int(p): int(e) for p, e in fac.items()}


def _factor_tex(sign: int, fac: Dict[int, int]) -> str:
    parts: List[str] = []
    if sign < 0:
        parts.append("-")
    for p in sorted(fac.keys()):
        e = fac[p]
        if e == 1:
            parts.append(f"{p}")
        else:
            parts.append(f"{p}^{{{e}}}")
    if parts and parts[0] == "-":
        return "-" + r"\cdot ".join(parts[1:]) if len(parts) > 1 else "-"
    return r"\cdot ".join(parts)


def _squarefree_part(fac: Dict[int, int]) -> int:
    sf = 1
    for p, e in fac.items():
        if e % 2 == 1:
            sf *= p
    return int(sf)


def _A4(t: sp.Expr) -> sp.Matrix:
    return sp.Matrix(
        [
            [0, 1, 0, 0, 0],
            [0, 0, t, 0, 1],
            [0, 1, 2, 0, 0],
            [1, 0, 1, 0, 0],
            [0, 0, 0, 1, 0],
        ]
    )


def _Dt_poly() -> Tuple[sp.Symbol, sp.Symbol, sp.Expr]:
    t = sp.Symbol("t")
    z = sp.Symbol("z")
    A = _A4(t)
    Dt = sp.expand((sp.eye(5) - z * A).det())
    return t, z, Dt


def _P4_poly() -> sp.Poly:
    t = sp.Symbol("t")
    P4 = t**8 - 10 * t**7 + 72 * t**6 - 24 * t**5 - 1924 * t**4 - 2904 * t**3 + 1312 * t**2 + 1464 * t - 1412
    return sp.Poly(P4, t, domain=sp.ZZ)


def _roots_real_in_interval(poly: sp.Poly, *, a: float, b: float, dps: int) -> List[sp.Expr]:
    roots = poly.nroots(n=dps, maxsteps=200)
    imag_eps = sp.Float(10) ** (-(dps // 2))
    out: List[sp.Expr] = []
    for r in roots:
        rr = sp.re(r).evalf(dps)
        ii = sp.im(r).evalf(dps)
        if abs(ii) <= imag_eps and float(rr) > a and float(rr) < b:
            out.append(rr)
    out = sorted(out, key=lambda x: float(x))
    return out


def _newman_v_octic() -> sp.Poly:
    v = sp.Symbol("v")
    poly = 2 * v**8 + 2 * v**5 + 2 * v**4 + 2 * v**3 + 2 * v**2 - 1
    return sp.Poly(poly, v, domain=sp.ZZ)


def _t_from_v_via_Dminus(v: sp.Expr) -> sp.Expr:
    # From D_t(-v)=0: 1+2v - t v^2 -2 v^4 -2 v^5=0
    return sp.simplify((1 + 2 * v - 2 * v**4 - 2 * v**5) / (v**2))


def _t_from_v_via_Dplus(v: sp.Expr) -> sp.Expr:
    # From D_t(v^2)=0: 1-2 v^2 - t v^4 -2 v^8 +2 v^10=0
    return sp.simplify((1 - 2 * v**2 - 2 * v**8 + 2 * v**10) / (v**4))


def _t_of_I(I: sp.Expr) -> sp.Expr:
    return sp.simplify((I**5 - 2 * I**4 - 2 * I + 2) / (I**3))


def _Dt_pole_ratio(t_val: mp.mpf) -> mp.mpf:
    """
    Compute the pole-ratio g(t)=z_+(t)/z_-(t)^2 using the real roots of D_t(z)=0,
    where z_+(t) is the smallest positive real root and z_-(t) is the (unique) negative
    real root in (-1,0) (closest to 0 among negative real roots).
    """
    # D_t(z)=2 z^5 -2 z^4 - t z^2 -2 z + 1
    coeffs = [mp.mpf(2), mp.mpf(-2), mp.mpf(0), -mp.mpf(t_val), mp.mpf(-2), mp.mpf(1)]
    roots = mp.polyroots(coeffs, maxsteps=200)
    reals = [mp.re(r) for r in roots if abs(mp.im(r)) < mp.mpf("1e-40")]
    z_plus = min([x for x in reals if x > 0])
    z_minus = max([x for x in reals if x < 0])  # closest to 0 on the negative axis
    return z_plus / (z_minus**2)


def _audit_pole_ratio_monotone(*, t_min: mp.mpf, t_max: mp.mpf, n: int) -> Tuple[bool, mp.mpf]:
    """
    Audit that g(t)=z_+(t)/z_-(t)^2 is strictly increasing on a uniform grid
    of n points in [t_min,t_max]. Returns (ok, min_increment).
    """
    if n < 3:
        raise ValueError("Require n>=3 for a monotonicity grid audit.")
    ts = [t_min + (t_max - t_min) * (mp.mpf(i) / mp.mpf(n - 1)) for i in range(n)]
    gs = [_Dt_pole_ratio(tt) for tt in ts]
    incs = [gs[i + 1] - gs[i] for i in range(n - 1)]
    min_inc = min(incs)
    return (min_inc > 0), min_inc


@dataclass(frozen=True)
class Payload:
    dps: int
    # D_t polynomial certificate
    Dt_z_poly: str
    # Newman pole resonance
    v_star: str
    t_star_from_v: str
    t_star_from_P4: str
    abs_diff_t_star: str
    P4_real_root_count: int
    P4_real_roots: List[str]
    # cyclotomic adjacency injection (selected h)
    t_adj_values: Dict[str, str]
    t_adj_minpolys: Dict[str, List[int]]
    ordering_chain: List[str]
    ordering_ok: bool
    # pole-ratio monotonicity audit (grid)
    pole_ratio_audit_t_min: str
    pole_ratio_audit_t_max: str
    pole_ratio_audit_n: int
    pole_ratio_audit_ok: bool
    pole_ratio_audit_min_increment: str
    # asymptotic coefficients
    t_adj_limit: str
    asymptotic_c2: str
    asymptotic_c4: str


def _write_tex_newman(path: Path, *, Dt_expr: sp.Expr, v_star: mp.mpf, t_star: mp.mpf) -> None:
    # Keep it short; align with manuscript conventions.
    z = sp.Symbol("z")
    t = sp.Symbol("t")
    Dt_poly = sp.Poly(Dt_expr, z, domain=sp.QQ.frac_field(t))
    Dt_tex = sp.latex(Dt_poly.as_expr())

    v = sp.Symbol("v")
    octic_tex = sp.latex(_newman_v_octic().as_expr())

    nd = 16
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_collision_kernel_A4_pole_quadratic_resonance_and_cyclotomic_adjacency_injection.py")
    lines.append(r"\begin{equation}\label{eq:collision_kernel_A4_newman_pole_quadratic_resonance}")
    lines.append(r"\begin{aligned}")
    lines.append(rf"D_t(z)&:={Dt_tex},\\")
    lines.append(rf"{octic_tex}&=0,\qquad v_\star\approx {_fmt(v_star, nd)},\\")
    lines.append(
        rf"t_\star&=-2v_\star^3-2v_\star^2+\frac{{2}}{{v_\star}}+\frac{{1}}{{v_\star^2}}"
        rf"=2v_\star^6-2v_\star^4-\frac{{2}}{{v_\star^2}}+\frac{{1}}{{v_\star^4}}"
        rf"\approx {_fmt(t_star, nd)}."
    )
    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_tex_adj(
    path: Path,
    *,
    minpolys: Dict[int, sp.Poly],
    values: Dict[int, mp.mpf],
    dps: int,
) -> None:
    t = sp.Symbol("t")

    def poly_tex(p: sp.Poly) -> str:
        return sp.latex(sp.Poly(p, t).as_expr())

    # h=12,18,30
    h_list = [12, 18, 30]

    # Asymptotic series (computed in main): keep symbolic coefficients here only.
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_collision_kernel_A4_pole_quadratic_resonance_and_cyclotomic_adjacency_injection.py")
    lines.append(r"\begin{equation}\label{eq:collision_kernel_A4_cyclotomic_adjacency_injection}")
    lines.append(r"\begin{aligned}")
    lines.append(r"c_h&:=2\cos\!\Bigl(\frac{\pi}{h}\Bigr),\qquad v_h:=\frac{1}{c_h},\\")
    lines.append(
        r"t_h^{\mathrm{adj}}&:= -2v_h^2+\frac{1}{v_h^2}-2\Bigl(v_h^3-\frac{1}{v_h}\Bigr)"
        r"=c_h^2+2c_h-\frac{2}{c_h^2}-\frac{2}{c_h^3},\\"
    )
    lines.append(r"D_{t_h^{\mathrm{adj}}}(-v_h)&=0,\qquad -c_h\in\mathrm{spec}\!\bigl(A_4(t_h^{\mathrm{adj}})\bigr).\\")

    for h in h_list:
        p = minpolys[h]
        lines.append(rf"P_{{{h}}}^{{\mathrm{{adj}}}}(t)&:={poly_tex(p)}=0,\\")
    # Numerical localization (for ordering only).
    lines.append(
        r"t_{12}^{\mathrm{adj}}\approx "
        + _fmt(values[12], 15)
        + r",\quad t_{18}^{\mathrm{adj}}\approx "
        + _fmt(values[18], 15)
        + r",\quad t_{30}^{\mathrm{adj}}\approx "
        + _fmt(values[30], 15)
        + r".\\"
    )

    # Asymptotic boundary and coefficients (inserted verbatim; validated in JSON).
    lines.append(r"\lim_{h\to\infty}t_h^{\mathrm{adj}}&=\frac{29}{4},\\")
    lines.append(
        r"t_h^{\mathrm{adj}}&=\frac{29}{4}-\frac{55\pi^2}{8h^2}+\frac{79\pi^4}{96h^4}+O(h^{-6})."
    )

    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="A4(t) Newman pole quadratic resonance + cyclotomic adjacency injection certificates."
    )
    parser.add_argument("--dps", type=int, default=160, help="Working decimal precision (sympy nroots + mpmath).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_pole_quadratic_resonance_and_cyclotomic_adjacency_injection.json"),
    )
    parser.add_argument(
        "--tex-out-newman",
        type=str,
        default=str(generated_dir() / "eq_collision_kernel_A4_newman_pole_quadratic_resonance.tex"),
    )
    parser.add_argument(
        "--tex-out-adj",
        type=str,
        default=str(generated_dir() / "eq_collision_kernel_A4_cyclotomic_adjacency_injection.tex"),
    )
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 80:
        raise SystemExit("Require --dps >= 80 for stable algebraic/numeric output.")
    mp.mp.dps = dps

    # ---- D_t(z) closed form ----
    t_sym, z_sym, Dt_expr = _Dt_poly()
    Dt_expected = sp.expand(1 - 2 * z_sym - t_sym * z_sym**2 - 2 * z_sym**4 + 2 * z_sym**5)
    if sp.expand(Dt_expr - Dt_expected) != 0:
        raise RuntimeError("Unexpected D_t(z) expression; manuscript certificate would be inconsistent.")

    # ---- Newman pole quadratic resonance ----
    v_sym = sp.Symbol("v")
    octic = _newman_v_octic()
    v_roots = _roots_real_in_interval(octic, a=0.0, b=1.0, dps=dps)
    if len(v_roots) != 1:
        raise RuntimeError(f"Expected a unique real root v in (0,1), got {len(v_roots)}.")
    v_star_sym = v_roots[0]
    v_star = mp.mpf(str(sp.N(v_star_sym, dps)))

    t_from_v_1 = sp.N(_t_from_v_via_Dminus(v_star_sym), dps)
    t_from_v_2 = sp.N(_t_from_v_via_Dplus(v_star_sym), dps)
    t_star_from_v = mp.mpf(str(t_from_v_1))
    # Sanity: two closed forms coincide under the octic constraint.
    if mp.fabs(t_star_from_v - mp.mpf(str(t_from_v_2))) > mp.mpf("1e-50"):
        raise RuntimeError("Mismatch between the two t(v) closed forms at v_star.")

    # Compare with P_4(t) certificate.
    P4 = _P4_poly()
    t_roots = _roots_real_in_interval(P4, a=0.0, b=100.0, dps=dps)
    if len(t_roots) != 1:
        raise RuntimeError(f"Expected a unique positive real root of P_4(t), got {len(t_roots)}.")
    t_star_from_P4 = mp.mpf(str(sp.N(t_roots[0], dps)))
    abs_diff = mp.fabs(t_star_from_v - t_star_from_P4)

    # Signature proxy: count real roots of P_4(t).
    # (All embeddings are roots of the irreducible polynomial.)
    P4_real_roots = _roots_real_in_interval(P4, a=-1e9, b=1e9, dps=dps)
    P4_real_roots_s = [_fmt(mp.mpf(str(r)), 30) for r in P4_real_roots]

    # ---- Cyclotomic adjacency injection ----
    def t_adj_of_h(h: int) -> sp.Expr:
        c = sp.simplify(2 * sp.cos(sp.pi / h))
        # t = c^2 + 2c - 2/c^2 - 2/c^3
        return sp.simplify(c**2 + 2 * c - 2 / (c**2) - 2 / (c**3))

    h_list = [12, 18, 30]
    minpolys: Dict[int, sp.Poly] = {}
    values: Dict[int, mp.mpf] = {}
    minpoly_coeffs_desc: Dict[str, List[int]] = {}
    t_adj_values_str: Dict[str, str] = {}

    t = sp.Symbol("t")
    for h in h_list:
        alpha = t_adj_of_h(h)
        p_expr = sp.minimal_polynomial(alpha, t)
        pZ = _poly_primitive_integer(p_expr, t)
        minpolys[h] = pZ
        minpoly_coeffs_desc[str(h)] = [int(c0) for c0 in pZ.all_coeffs()]
        val = mp.mpf(str(sp.N(alpha, dps)))
        values[h] = val
        t_adj_values_str[str(h)] = _fmt(val, 40)

    # ADE index intersection points t_{E6}, t_{E7}, t_{E8} (Perron curve r_4(t)=4 cos^2(pi/h)).
    I_E6 = sp.simplify(4 * sp.cos(sp.pi / 12) ** 2)
    I_E7 = sp.simplify(4 * sp.cos(sp.pi / 18) ** 2)
    I_E8 = sp.simplify(4 * sp.cos(sp.pi / 30) ** 2)
    t_E6 = mp.mpf(str(sp.N(_t_of_I(I_E6), dps)))
    t_E7 = mp.mpf(str(sp.N(_t_of_I(I_E7), dps)))
    t_E8 = mp.mpf(str(sp.N(_t_of_I(I_E8), dps)))

    # Ordering chain (strict, for orientation and later TeX statement).
    chain = [
        ("t_{E_6}", t_E6),
        (r"t_{12}^{\mathrm{adj}}", values[12]),
        ("t_\\star", t_star_from_P4),
        ("7", mp.mpf(7)),
        (r"t_{18}^{\mathrm{adj}}", values[18]),
        (r"t_{30}^{\mathrm{adj}}", values[30]),
        ("t_{E_7}", t_E7),
        ("t_{E_8}", t_E8),
    ]
    ordering_ok = all(chain[i][1] < chain[i + 1][1] for i in range(len(chain) - 1))
    ordering_chain_s = [f"{name}={_fmt(val, 18)}" for name, val in chain]

    # ---- Pole-ratio monotonicity audit (grid; orientation for the geometric criterion) ----
    pole_audit_t_min = t_E6
    pole_audit_t_max = t_E8
    pole_audit_n = 300
    old_dps = mp.mp.dps
    # The grid audit does not require the full algebraic precision; reduce for speed.
    mp.mp.dps = min(old_dps, 90)
    pole_ok, pole_min_inc = _audit_pole_ratio_monotone(t_min=pole_audit_t_min, t_max=pole_audit_t_max, n=pole_audit_n)
    mp.mp.dps = old_dps

    # ---- Asymptotic series ----
    x = sp.Symbol("x")
    c_x = sp.simplify(2 * sp.cos(sp.pi * x))
    t_x = sp.simplify(c_x**2 + 2 * c_x - 2 / (c_x**2) - 2 / (c_x**3))
    # series in x up to x^4 (i.e. h^{-4}).
    ser = sp.series(t_x, x, 0, 6).removeO()
    # Extract coefficients for x^0, x^2, x^4.
    c0 = sp.simplify(sp.expand(ser).coeff(x, 0))
    c2 = sp.simplify(sp.expand(ser).coeff(x, 2))
    c4 = sp.simplify(sp.expand(ser).coeff(x, 4))
    # Expected:
    #   c0 = 29/4
    #   c2 = -55*pi^2/8
    #   c4 = 79*pi^4/96
    if sp.simplify(c0 - sp.Rational(29, 4)) != 0:
        raise RuntimeError("Unexpected h->infty limit coefficient for t_h^{adj}.")
    if sp.simplify(c2 - (-sp.Rational(55, 8) * sp.pi**2)) != 0:
        raise RuntimeError("Unexpected h^{-2} coefficient for t_h^{adj}.")
    if sp.simplify(c4 - (sp.Rational(79, 96) * sp.pi**4)) != 0:
        raise RuntimeError("Unexpected h^{-4} coefficient for t_h^{adj}.")

    # ---- Write TeX ----
    _write_tex_newman(Path(args.tex_out_newman), Dt_expr=Dt_expr, v_star=v_star, t_star=t_star_from_P4)
    _write_tex_adj(Path(args.tex_out_adj), minpolys=minpolys, values=values, dps=dps)

    # ---- JSON payload ----
    payload = Payload(
        dps=dps,
        Dt_z_poly=str(Dt_expected),
        v_star=_fmt(v_star, 50),
        t_star_from_v=_fmt(t_star_from_v, 50),
        t_star_from_P4=_fmt(t_star_from_P4, 50),
        abs_diff_t_star=_fmt(abs_diff, 80),
        P4_real_root_count=len(P4_real_roots),
        P4_real_roots=P4_real_roots_s,
        t_adj_values=t_adj_values_str,
        t_adj_minpolys=minpoly_coeffs_desc,
        ordering_chain=ordering_chain_s,
        ordering_ok=bool(ordering_ok),
        pole_ratio_audit_t_min=_fmt(pole_audit_t_min, 30),
        pole_ratio_audit_t_max=_fmt(pole_audit_t_max, 30),
        pole_ratio_audit_n=int(pole_audit_n),
        pole_ratio_audit_ok=bool(pole_ok),
        pole_ratio_audit_min_increment=_fmt(pole_min_inc, 40),
        t_adj_limit=str(sp.Rational(29, 4)),
        asymptotic_c2=str(c2),
        asymptotic_c4=str(c4),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[A4-pole-resonance+adj-injection] wrote {jout}", flush=True)
    print(f"[A4-pole-resonance+adj-injection] wrote {args.tex_out_newman}", flush=True)
    print(f"[A4-pole-resonance+adj-injection] wrote {args.tex_out_adj}", flush=True)


if __name__ == "__main__":
    main()

