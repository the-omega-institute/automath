#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit two derived consequences of the pure-collision cubic:

1. The positive real branch global coordinate data:
      rho_0 = 1 + sqrt(2),
      u'(rho),
      alpha'(rho),
   together with the endpoint values used in the monotonicity proof.
2. The RH-window collision-frequency endpoint alpha_R, obtained from the
   critical quintic in u and the alpha-resultant quintic.
3. The odd-prime partial product

       P_odd^(<=P) = Π_{3<=p<=P prime} |rho(e^{2π i / p}) / phi^2|,

   together with the two-term Taylor prediction for its logarithm.

Outputs:
  - artifacts/export/real_input_40_collision_frequency_prime_shadow_audit.json
  - sections/generated/eq_real_input_40_collision_frequency_prime_shadow_audit.tex

All code and generated output are English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


ALPHA_QUINTIC = "191*a^5 - 701*a^4 + 1043*a^3 - 748*a^2 + 252*a - 28"
U_QUINTIC = "u^5 + 4*u^4 + 3*u^3 - 96*u^2 - 42*u - 14"


@dataclass(frozen=True)
class Payload:
    dps: int
    p_max: int
    rho_0: str
    uprime_formula: str
    alphaprime_formula: str
    u_at_rho0: str
    alpha_at_rho0: str
    q_at_rho0: str
    p_at_rho0: str
    pprime_at_rho0: str
    alpha_limit_infty: str
    odd_prime_count: int
    u_R: str
    alpha_R_from_uR: str
    alpha_R_from_quintic: str
    alpha_R_match_gap: str
    alpha_quintic_residual: str
    odd_prime_partial_product: str
    odd_prime_partial_log: str
    odd_prime_zeta_2_partial: str
    odd_prime_zeta_4_partial: str
    odd_prime_zeta_6_partial: str
    odd_prime_log_prediction_2term: str
    odd_prime_log_prediction_gap: str
    all_factors_strictly_below_one: bool


def _fmt(x: mp.mpf | mp.mpc, nd: int = 18) -> str:
    if isinstance(x, mp.mpc):
        raise TypeError("Use real-valued formatter only.")
    return mp.nstr(x, nd)


def _sp_str(expr: sp.Expr) -> str:
    return str(sp.simplify(expr))


def _odd_primes_up_to(n: int) -> List[int]:
    if n < 3:
        return []
    sieve = [True] * (n + 1)
    sieve[0] = False
    sieve[1] = False
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            start = p * p
            sieve[start : n + 1 : p] = [False] * (((n - start) // p) + 1)
    return [p for p in range(3, n + 1, 2) if sieve[p]]


def _cubic_roots(u: mp.mpc) -> List[mp.mpc]:
    coeffs = [mp.mpc(1), mp.mpc(-2), -(u + 1), u]
    return list(mp.polyroots(coeffs, maxsteps=200))


def _perron_root_positive_u(u: mp.mpf) -> mp.mpf:
    roots = _cubic_roots(mp.mpc(u))
    real_roots = sorted(mp.re(r) for r in roots)
    return real_roots[-1]


def _u_from_rho(rho: mp.mpf) -> mp.mpf:
    return rho * (rho**2 - 2 * rho - 1) / (rho - 1)


def _alpha_from_rho(rho: mp.mpf) -> mp.mpf:
    num = (rho**2 - 2 * rho - 1) * (rho - 1)
    den = 2 * rho**3 - 5 * rho**2 + 4 * rho + 1
    return num / den


def _compute_u_R(dps: int) -> mp.mpf:
    u = sp.Symbol("u")
    poly = sp.Poly(u**5 + 4 * u**4 + 3 * u**3 - 96 * u**2 - 42 * u - 14, u)
    roots = poly.nroots(n=dps, maxsteps=200)
    cands: List[sp.Expr] = []
    for r in roots:
        rr = sp.re(r).evalf(dps)
        ii = sp.im(r).evalf(dps)
        if abs(float(ii)) < 1e-30 and float(rr) > 0:
            cands.append(rr)
    if len(cands) != 1:
        raise RuntimeError(f"Expected one positive real u_R, got {len(cands)}.")
    return mp.mpf(str(cands[0]))


def _compute_alpha_R_from_quintic(dps: int) -> mp.mpf:
    a = sp.Symbol("a")
    poly = sp.Poly(191 * a**5 - 701 * a**4 + 1043 * a**3 - 748 * a**2 + 252 * a - 28, a)
    roots = poly.nroots(n=dps, maxsteps=200)
    cands: List[sp.Expr] = []
    for r in roots:
        rr = sp.re(r).evalf(dps)
        ii = sp.im(r).evalf(dps)
        rr_f = float(rr)
        if abs(float(ii)) < 1e-30 and 0.0 < rr_f < 0.5:
            cands.append(rr)
    if len(cands) != 1:
        raise RuntimeError(f"Expected one alpha_R root in (0,1/2), got {len(cands)}.")
    return mp.mpf(str(cands[0]))


def _select_branch_roots(primes: Sequence[int]) -> Dict[int, mp.mpc]:
    """
    Follow the analytic Perron branch rho(e^{it}) along t in [0, 2π/3].

    We start at the smallest angle (largest prime) near t=0 and at each next
    sample select the cubic root closest to the previous branch value.
    """
    phi = (1 + mp.sqrt(5)) / 2
    prev = phi**2
    out: Dict[int, mp.mpc] = {}
    for p in sorted(primes, reverse=True):
        t = 2 * mp.pi / p
        roots = _cubic_roots(mp.e ** (mp.j * t))
        root = min(roots, key=lambda z: abs(z - prev))
        out[p] = root
        prev = root
    return out


def _write_tex(
    path: Path,
    *,
    p_max: int,
    alpha_R: mp.mpf,
    alpha_residual: mp.mpf,
    partial_product: mp.mpf,
    partial_log: mp.mpf,
    predicted_log: mp.mpf,
) -> None:
    lines: List[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append(r"\begin{equation}\label{eq:real_input_40_collision_frequency_prime_shadow_audit}")
    lines.append(r"\begin{aligned}")
    lines.append(rf"\alpha_R &\approx {_fmt(alpha_R, 18)},\\")
    lines.append(
        r"191\alpha_R^5-701\alpha_R^4+1043\alpha_R^3-748\alpha_R^2+252\alpha_R-28"
        + rf" &\approx {_fmt(alpha_residual, 8)},\\"
    )
    lines.append(
        r"\mathfrak P_{\mathrm{odd}}^{(\le "
        + str(p_max)
        + r")}"
        + r":=\prod_{\substack{3\le p\le "
        + str(p_max)
        + r"\\ p\ \mathrm{prime}}}\left|\frac{\rho(e^{2\pi i/p})}{\varphi^2}\right|"
        + rf" &\approx {_fmt(partial_product, 18)},\\"
    )
    lines.append(
        r"\log \mathfrak P_{\mathrm{odd}}^{(\le "
        + str(p_max)
        + r")}"
        + rf" &\approx {_fmt(partial_log, 18)},\\"
    )
    lines.append(
        r"-\frac{6\sqrt5-5}{250}(2\pi)^2P_{\mathrm{odd}}^{(\le "
        + str(p_max)
        + r")}(2)"
        + r"+\frac{7+24\sqrt5}{75000}(2\pi)^4P_{\mathrm{odd}}^{(\le "
        + str(p_max)
        + r")}(4)"
        + rf" &\approx {_fmt(predicted_log, 18)}."
    )
    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit alpha_R and odd-prime partial products for the pure-collision cubic."
    )
    parser.add_argument("--dps", type=int, default=80, help="Working decimal precision.")
    parser.add_argument(
        "--p-max",
        type=int,
        default=2000,
        help="Upper prime cutoff P for the odd-prime partial product.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_collision_frequency_prime_shadow_audit.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_collision_frequency_prime_shadow_audit.tex"),
    )
    args = parser.parse_args()

    dps = int(args.dps)
    p_max = int(args.p_max)
    if dps < 50:
        raise SystemExit("Require --dps >= 50 for stable algebraic and prime-shadow output.")
    if p_max < 3:
        raise SystemExit("Require --p-max >= 3.")

    mp.mp.dps = dps
    phi = (1 + mp.sqrt(5)) / 2
    lam = phi**2

    rho = sp.Symbol("rho", positive=True)
    rho0 = 1 + sp.sqrt(2)
    u_expr = rho * (rho**2 - 2 * rho - 1) / (rho - 1)
    alpha_expr = ((rho**2 - 2 * rho - 1) * (rho - 1)) / (2 * rho**3 - 5 * rho**2 + 4 * rho + 1)
    q = 2 * rho**3 - 5 * rho**2 + 4 * rho + 1
    p_poly = rho**4 + 4 * rho**3 - 10 * rho**2 + 4 * rho - 3

    u_R = _compute_u_R(dps)
    rho_R = _perron_root_positive_u(u_R)
    alpha_R_from_uR = _alpha_from_rho(rho_R)
    alpha_R_from_quintic = _compute_alpha_R_from_quintic(dps)
    alpha_gap = abs(alpha_R_from_uR - alpha_R_from_quintic)
    alpha_residual = (
        191 * alpha_R_from_uR**5
        - 701 * alpha_R_from_uR**4
        + 1043 * alpha_R_from_uR**3
        - 748 * alpha_R_from_uR**2
        + 252 * alpha_R_from_uR
        - 28
    )

    odd_primes = _odd_primes_up_to(p_max)
    branch_roots = _select_branch_roots(odd_primes)

    kappa = (6 * mp.sqrt(5) - 5) / 250
    beta = (7 + 24 * mp.sqrt(5)) / 75000

    partial_product = mp.mpf(1)
    partial_log = mp.mpf(0)
    Podd2 = mp.mpf(0)
    Podd4 = mp.mpf(0)
    Podd6 = mp.mpf(0)
    all_lt_one = True

    for p in odd_primes:
        factor = abs(branch_roots[p] / lam)
        if not (factor < 1):
            all_lt_one = False
        partial_product *= factor
        partial_log += mp.log(factor)
        Podd2 += p**-2
        Podd4 += p**-4
        Podd6 += p**-6

    predicted_log = -kappa * (2 * mp.pi) ** 2 * Podd2 + beta * (2 * mp.pi) ** 4 * Podd4
    prediction_gap = partial_log - predicted_log

    payload = Payload(
        dps=dps,
        p_max=p_max,
        rho_0=_sp_str(rho0),
        uprime_formula=_sp_str(sp.factor(sp.diff(u_expr, rho))),
        alphaprime_formula=_sp_str(sp.factor(sp.diff(alpha_expr, rho))),
        u_at_rho0=_sp_str(u_expr.subs(rho, rho0)),
        alpha_at_rho0=_sp_str(alpha_expr.subs(rho, rho0)),
        q_at_rho0=_sp_str(q.subs(rho, rho0)),
        p_at_rho0=_sp_str(p_poly.subs(rho, rho0)),
        pprime_at_rho0=_sp_str(sp.diff(p_poly, rho).subs(rho, rho0)),
        alpha_limit_infty=_sp_str(sp.limit(alpha_expr, rho, sp.oo)),
        odd_prime_count=len(odd_primes),
        u_R=_fmt(u_R, 18),
        alpha_R_from_uR=_fmt(alpha_R_from_uR, 24),
        alpha_R_from_quintic=_fmt(alpha_R_from_quintic, 24),
        alpha_R_match_gap=_fmt(alpha_gap, 8),
        alpha_quintic_residual=_fmt(alpha_residual, 24),
        odd_prime_partial_product=_fmt(partial_product, 24),
        odd_prime_partial_log=_fmt(partial_log, 24),
        odd_prime_zeta_2_partial=_fmt(Podd2, 24),
        odd_prime_zeta_4_partial=_fmt(Podd4, 24),
        odd_prime_zeta_6_partial=_fmt(Podd6, 24),
        odd_prime_log_prediction_2term=_fmt(predicted_log, 24),
        odd_prime_log_prediction_gap=_fmt(prediction_gap, 24),
        all_factors_strictly_below_one=all_lt_one,
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[collision-frequency-prime-shadow] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    _write_tex(
        tout,
        p_max=p_max,
        alpha_R=alpha_R_from_uR,
        alpha_residual=alpha_residual,
        partial_product=partial_product,
        partial_log=partial_log,
        predicted_log=predicted_log,
    )
    print(f"[collision-frequency-prime-shadow] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()
