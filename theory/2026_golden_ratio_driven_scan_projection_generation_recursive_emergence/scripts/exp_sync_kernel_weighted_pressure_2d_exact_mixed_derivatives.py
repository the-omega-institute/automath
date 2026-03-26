#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Exact mixed derivatives of the 2D pressure from the explicit Delta(z;u,v).

All code is English-only by repository convention.

We use the explicit integer-coefficient polynomial (Appendix B.0.24):
  Delta(z;u,v) = det(I - z B(u,v))
and define z_*(u,v) as the smallest positive root in z, lambda=1/z_*,
P(theta_e,theta_-)=log lambda(e^{theta_e},e^{theta_-}) = -log z_*(e^{theta_e},e^{theta_-}).

This script computes the Taylor jet of z_*(exp x, exp y) at (x,y)=(0,0)
to total degree <= 4 by implicit power-series solving, with exact rational
arithmetic. It then derives exact mixed partials of P at (0,0), including
the vanishing of cross terms at certain orders.

Artifacts:
- artifacts/export/sync_kernel_weighted_pressure_2d_exact_mixed_derivatives.json
- sections/generated/eq_sync_kernel_weighted_pressure_2d_exact_mixed_derivatives.tex
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Iterable, List, Tuple

from common_paths import export_dir, generated_dir


Index = Tuple[int, int]  # (i, j) for x^i y^j
Series = Dict[Index, Fraction]


def series_zero() -> Series:
    return {}


def series_get(a: Series, i: int, j: int) -> Fraction:
    return a.get((i, j), Fraction(0))


def series_set(a: Series, i: int, j: int, v: Fraction) -> None:
    if v == 0:
        a.pop((i, j), None)
    else:
        a[(i, j)] = v


def series_add(a: Series, b: Series, N: int) -> Series:
    out: Series = dict(a)
    for (i, j), v in b.items():
        if i + j > N:
            continue
        out[(i, j)] = out.get((i, j), Fraction(0)) + v
        if out[(i, j)] == 0:
            del out[(i, j)]
    return out


def series_sub(a: Series, b: Series, N: int) -> Series:
    out: Series = dict(a)
    for (i, j), v in b.items():
        if i + j > N:
            continue
        out[(i, j)] = out.get((i, j), Fraction(0)) - v
        if out[(i, j)] == 0:
            del out[(i, j)]
    return out


def series_scale(a: Series, c: Fraction, N: int) -> Series:
    if c == 0:
        return {}
    out: Series = {}
    for (i, j), v in a.items():
        if i + j <= N:
            out[(i, j)] = v * c
    return out


def series_mul(a: Series, b: Series, N: int) -> Series:
    out: Series = {}
    for (i1, j1), v1 in a.items():
        for (i2, j2), v2 in b.items():
            i = i1 + i2
            j = j1 + j2
            if i + j > N:
                continue
            out[(i, j)] = out.get((i, j), Fraction(0)) + v1 * v2
    out = {k: v for k, v in out.items() if v != 0}
    return out


def series_pow(a: Series, k: int, N: int) -> Series:
    if k < 0:
        raise ValueError("negative power not supported")
    if k == 0:
        return {(0, 0): Fraction(1)}
    if k == 1:
        return dict(a)
    # exponentiation by squaring
    out: Series = {(0, 0): Fraction(1)}
    base: Series = dict(a)
    kk = k
    while kk > 0:
        if kk & 1:
            out = series_mul(out, base, N)
        kk >>= 1
        if kk:
            base = series_mul(base, base, N)
    return out


def series_exp_x(N: int) -> Series:
    # exp(x) = sum_{i=0..N} x^i / i!
    out: Series = {}
    for i in range(0, N + 1):
        out[(i, 0)] = Fraction(1, math.factorial(i))
    return out


def series_exp_y(N: int) -> Series:
    out: Series = {}
    for j in range(0, N + 1):
        out[(0, j)] = Fraction(1, math.factorial(j))
    return out


def series_log_1p(w: Series, N: int) -> Series:
    """log(1+w) truncated, assumes w has zero constant term."""
    if series_get(w, 0, 0) != 0:
        raise ValueError("log1p requires zero constant term")
    out: Series = {}
    # log(1+w)= sum_{n>=1} (-1)^{n+1} w^n / n
    power: Series = dict(w)
    for n in range(1, N + 1):
        coef = Fraction(1 if (n % 2 == 1) else -1, n)
        out = series_add(out, series_scale(power, coef, N), N)
        power = series_mul(power, w, N)
    return out


def delta_series(z: Series, u: Series, v: Series, N: int) -> Series:
    """Delta(z;u,v) expanded as a bivariate series in (x,y) via u=exp x, v=exp y."""
    z2 = series_pow(z, 2, N)
    z3 = series_pow(z, 3, N)
    z4 = series_pow(z, 4, N)
    z5 = series_pow(z, 5, N)
    z6 = series_pow(z, 6, N)

    v2 = series_pow(v, 2, N)
    u2 = series_pow(u, 2, N)
    u3 = series_pow(u, 3, N)
    u4 = series_pow(u, 4, N)

    one = {(0, 0): Fraction(1)}
    two = {(0, 0): Fraction(2)}
    three = {(0, 0): Fraction(3)}
    five = {(0, 0): Fraction(5)}

    # Term-by-term translation of:
    # 1-(u+1)z-u(v^2+2v+2)z^2+uv(uv+2u+v+2)z^3
    # +uv^2(-u^2+3u-1)z^4
    # +(u^4v^2-2u^3v^2-u^3v-2u^2v^2-u^2v+uv^2)z^5
    # +u^2v^2(u^2+u+1)z^6

    term1 = one

    term2 = series_mul(series_add(u, one, N), z, N)  # (u+1) z
    term2 = series_scale(term2, Fraction(-1), N)

    vv = series_add(series_add(v2, series_scale(v, Fraction(2), N), N), two, N)  # v^2+2v+2
    term3 = series_mul(series_mul(u, vv, N), z2, N)
    term3 = series_scale(term3, Fraction(-1), N)

    uv = series_mul(u, v, N)
    inside4 = series_add(series_add(uv, series_scale(u, Fraction(2), N), N), series_add(v, two, N), N)
    term4 = series_mul(series_mul(uv, inside4, N), z3, N)

    inside5 = series_add(series_scale(u2, Fraction(-1), N), series_add(series_scale(u, Fraction(3), N), series_scale(one, Fraction(-1), N), N), N)
    term5 = series_mul(series_mul(series_mul(u, v2, N), inside5, N), z4, N)

    inside6 = series_add(
        series_add(series_mul(u4, v2, N), series_scale(series_mul(u3, v2, N), Fraction(-2), N), N),
        series_add(series_scale(series_mul(u3, v, N), Fraction(-1), N), series_scale(series_mul(u2, v2, N), Fraction(-2), N), N),
        N,
    )
    inside6 = series_add(inside6, series_scale(series_mul(u2, v, N), Fraction(-1), N), N)
    inside6 = series_add(inside6, series_mul(u, v2, N), N)
    term6 = series_mul(inside6, z5, N)

    inside7 = series_add(series_add(u2, u, N), one, N)  # u^2+u+1
    term7 = series_mul(series_mul(series_mul(u2, v2, N), inside7, N), z6, N)

    out = term1
    for t in (term2, term3, term4, term5, term6, term7):
        out = series_add(out, t, N)
    return out


def coeff_pairs_total_degree(t: int) -> Iterable[Index]:
    for i in range(0, t + 1):
        yield (i, t - i)


def solve_z_series(N: int) -> Series:
    # Basepoint z(0,0) = 1/3 (as stated in the appendix: lambda(1,1)=3).
    z: Series = {(0, 0): Fraction(1, 3)}
    u = series_exp_x(N)
    v = series_exp_y(N)

    # Use the implicit recursion: at each (i,j), Delta coefficient must be 0.
    for t in range(1, N + 1):
        for (i, j) in coeff_pairs_total_degree(t):
            # Build F with current z (unknown coeff at (i,j) treated as 0 initially).
            series_set(z, i, j, Fraction(0))
            F0 = delta_series(z, u, v, N)
            b = series_get(F0, i, j)

            # Now set coeff to 1, re-evaluate, get linear coefficient A.
            series_set(z, i, j, Fraction(1))
            F1 = delta_series(z, u, v, N)
            a = series_get(F1, i, j) - b

            if a == 0:
                raise RuntimeError(f"singular recursion at {(i,j)}: Delta depends nonlinearly?")

            # Solve a*c + b = 0
            c = -b / a
            series_set(z, i, j, c)
    return z


def series_for_pressure_from_z(z: Series, N: int) -> Series:
    z0 = series_get(z, 0, 0)
    if z0 == 0:
        raise ValueError("z0 must be nonzero")
    # P = -log z = -log z0 - log(1 + (z-z0)/z0). Drop constant.
    dz = dict(z)
    dz[(0, 0)] = dz.get((0, 0), Fraction(0)) - z0
    w = series_scale(dz, Fraction(1, 1) / z0, N)
    log_part = series_log_1p(w, N)
    return series_scale(log_part, Fraction(-1), N)


def deriv_from_series(P: Series, i: int, j: int) -> Fraction:
    """Return ∂^{i+j} P / ∂x^i ∂y^j at 0 from ordinary power series coefficients."""
    return series_get(P, i, j) * Fraction(math.factorial(i) * math.factorial(j), 1)


def frac_tex(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    sgn = "-" if q < 0 else ""
    q = abs(q)
    return f"{sgn}\\frac{{{q.numerator}}}{{{q.denominator}}}"


@dataclass(frozen=True)
class Derivs:
    P_e: Fraction
    P_n: Fraction
    P_ee: Fraction
    P_nn: Fraction
    P_en: Fraction
    P_een: Fraction
    P_enn: Fraction
    P_eenn: Fraction
    P_ennn: Fraction


def compute_derivatives() -> Tuple[Derivs, Series, Series]:
    N = 4
    z = solve_z_series(N)
    P = series_for_pressure_from_z(z, N)

    derivs = Derivs(
        P_e=deriv_from_series(P, 1, 0),
        P_n=deriv_from_series(P, 0, 1),
        P_ee=deriv_from_series(P, 2, 0),
        P_nn=deriv_from_series(P, 0, 2),
        P_en=deriv_from_series(P, 1, 1),
        P_een=deriv_from_series(P, 2, 1),
        P_enn=deriv_from_series(P, 1, 2),
        P_eenn=deriv_from_series(P, 2, 2),
        P_ennn=deriv_from_series(P, 1, 3),
    )
    return derivs, z, P


def write_tex(derivs: Derivs) -> None:
    lines: List[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append("\\begin{equation}\\label{eq:sync-kernel-weighted-pressure-2d-exact-mixed-derivatives}")
    lines.append("\\boxed{")
    lines.append("\\begin{aligned}")
    lines.append(
        "\\partial_{\\theta_e\\theta_-}^2 P(0,0) &= "
        + frac_tex(derivs.P_en)
        + ",\\\\"
    )
    lines.append(
        "\\partial_{\\theta_e\\theta_e\\theta_-}^3 P(0,0) &= "
        + frac_tex(derivs.P_een)
        + ",\\qquad"
        + "\\partial_{\\theta_e\\theta_-\\theta_-}^3 P(0,0) = "
        + frac_tex(derivs.P_enn)
        + ",\\\\"
    )
    lines.append(
        "\\partial_{\\theta_e\\theta_e\\theta_-\\theta_-}^4 P(0,0) &= "
        + frac_tex(derivs.P_eenn)
        + ",\\qquad"
        + "\\partial_{\\theta_e\\theta_-\\theta_-\\theta_-}^4 P(0,0) = "
        + frac_tex(derivs.P_ennn)
        + "."
    )
    lines.append("\\end{aligned}")
    lines.append("}")
    lines.append("\\end{equation}")
    out = generated_dir() / "eq_sync_kernel_weighted_pressure_2d_exact_mixed_derivatives.tex"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    t0 = time.time()
    derivs, z, P = compute_derivatives()

    export_dir().mkdir(parents=True, exist_ok=True)
    payload = {
        "N_total_degree": 4,
        "z0": str(series_get(z, 0, 0)),
        "P_mixed": {
            "P_e": str(derivs.P_e),
            "P_neg": str(derivs.P_n),
            "P_ee": str(derivs.P_ee),
            "P_nn": str(derivs.P_nn),
            "P_en": str(derivs.P_en),
            "P_een": str(derivs.P_een),
            "P_enn": str(derivs.P_enn),
            "P_eenn": str(derivs.P_eenn),
            "P_ennn": str(derivs.P_ennn),
        },
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "sync_kernel_weighted_pressure_2d_exact_mixed_derivatives.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    write_tex(derivs)

    print(
        "[sync-kernel-2d-exact] "
        f"P_en={derivs.P_en} P_een={derivs.P_een} P_enn={derivs.P_enn} "
        f"P_eenn={derivs.P_eenn} P_ennn={derivs.P_ennn} "
        f"wall={time.time()-t0:.2f}s",
        flush=True,
    )


if __name__ == "__main__":
    main()

