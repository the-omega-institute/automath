#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Branch points in complex u and analytic radius in theta for the sync-kernel output potential.

We use the explicit degree-6 algebraic curve for the Perron root lambda(u):

  F(lambda,u)=0,  with F in Z[u][lambda],

as stated in `sections/appendix/sync_kernel/weighted/cor__sync-kernel-weighted-unit-root-finite.tex`
(appendix pressure-analytic).
Branch points in the u-plane occur exactly when lambda becomes a multiple root, i.e.
F=0 and dF/dlambda=0, equivalently Disc_lambda(F)(u)=0.

We compute:
  - the discriminant Disc_lambda(F)(u) and its factorization
  - the palindromic degree-20 factor D(u)
  - nearest branch points in theta = Log(u) (min over 2π i Z shifts)
  - an auditable Cauchy remainder certificate for the 8th-order Taylor truncation of P(theta)=log lambda(e^theta)
    using a numerical bound M_r = max_{|theta|=r} |P(theta)| at r=0.99*R_theta.
  - a comparison radius for the phi_minus cubic example (negative-carry potential) from
    `sections/appendix/sync_kernel/app__vector-potential.tex`.

Outputs:
  - artifacts/export/sync_kernel_output_potential_branch_radius_certificate.json
  - sections/generated/eq_sync_kernel_output_potential_branch_radius_certificate.tex
"""

from __future__ import annotations

import argparse
import json
import math
import threading
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


class _Progress:
    def __init__(
        self,
        *,
        enabled: bool,
        every_seconds: float,
        prefix: str = "[sync-branch-radius]",
    ) -> None:
        self._enabled = enabled and every_seconds > 0
        self._every_seconds = float(every_seconds)
        self._prefix = prefix
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._t0 = 0.0

    def start(self, msg: str) -> None:
        if not self._enabled:
            return
        self._t0 = time.time()
        print(f"{self._prefix} {msg}", flush=True)

        def _run() -> None:
            while not self._stop.wait(self._every_seconds):
                dt = time.time() - self._t0
                print(f"{self._prefix} still running... elapsed={dt:.1f}s", flush=True)

        self._thread = threading.Thread(target=_run, name="progress", daemon=True)
        self._thread.start()

    def stop(self, msg: str) -> None:
        if not self._enabled:
            return
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=1.0)
        dt = time.time() - self._t0
        print(f"{self._prefix} {msg} elapsed={dt:.1f}s", flush=True)


def _F(lam: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match `sections/appendix/sync_kernel/weighted/cor__sync-kernel-weighted-unit-root-finite.tex` (app:pressure-analytic).
    return sp.expand(
        lam**6
        - (1 + u) * lam**5
        - 5 * u * lam**4
        + 3 * u * (1 + u) * lam**3
        - u * (u**2 - 3 * u + 1) * lam**2
        + u * (u**3 - 3 * u**2 - 3 * u + 1) * lam
        + u**2 * (u**2 + u + 1)
    )


def _phi_minus_cubic(lam: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match `sections/appendix/sync_kernel/app__vector-potential.tex` (negative-carry example).
    return sp.expand(lam**3 - (u + 2) * lam**2 + (u - 2) * lam + 3 * u)


def _normalize_int_poly_u(expr: sp.Expr, u: sp.Symbol) -> sp.Expr:
    P = sp.Poly(sp.expand(expr), u, domain=sp.ZZ)
    if P.LC() < 0:
        P = sp.Poly(-P.as_expr(), u, domain=sp.ZZ)
    content = int(sp.gcd_list([int(c) for c in P.all_coeffs()])) if P.all_coeffs() else 1
    if content > 1:
        P = sp.Poly(P.as_expr() // content, u, domain=sp.ZZ)
    return sp.expand(P.as_expr())


def _disc_and_D() -> Tuple[sp.Expr, sp.Expr]:
    lam, u = sp.symbols("lam u")
    F = _F(lam, u)
    disc = sp.discriminant(sp.Poly(F, lam), lam)
    disc = sp.expand(disc)
    disc = _normalize_int_poly_u(disc, u)
    # Factor out u^5 (expected) and keep remaining integer polynomial.
    P = sp.Poly(disc, u, domain=sp.ZZ)
    # Poly valuation at u: minimal exponent with nonzero coefficient.
    if P.is_zero:
        raise RuntimeError("discriminant is zero (unexpected)")
    exps = [int(e[0]) for e in P.as_dict().keys()]
    v = min(exps) if exps else 0
    D = sp.expand(disc / (u**v))
    # Normalize sign to match the paper convention Disc = -u^5 D(u) with D(0)>0.
    D0 = int(sp.Poly(D, u, domain=sp.ZZ).eval(0))
    if D0 < 0:
        disc = -disc
        D = -D
    return disc, sp.expand(D)


def _min_theta_distance(u0: complex, max_k: int = 6) -> complex:
    # theta candidates: Log(u0) + 2π i k, choose with minimal |theta|.
    import cmath

    base = cmath.log(u0)
    best = None
    for k in range(-max_k, max_k + 1):
        th = base + 2j * math.pi * k
        if best is None or abs(th) < abs(best):
            best = th
    assert best is not None
    return best


def _newton_root_on_branch(
    *,
    u: complex,
    lam0: complex,
    max_iter: int = 50,
    tol: float = 1e-12,
) -> complex:
    lam_sym, u_sym = sp.symbols("lam u")
    F = _F(lam_sym, u_sym)
    dF = sp.diff(F, lam_sym)
    Ff = sp.lambdify((lam_sym, u_sym), F, "mpmath")
    dFf = sp.lambdify((lam_sym, u_sym), dF, "mpmath")
    import mpmath as mp

    lam = mp.mpc(lam0)
    uu = mp.mpc(u)
    for _ in range(max_iter):
        f = Ff(lam, uu)
        fp = dFf(lam, uu)
        if fp == 0:
            break
        step = f / fp
        lam2 = lam - step
        if abs(lam2 - lam) <= tol * (1 + abs(lam2)):
            lam = lam2
            return complex(lam)
        lam = lam2
    return complex(lam)


def _track_circle_Mr(
    *,
    r: float,
    nphi: int,
    radial_steps: int,
    dps: int,
) -> Tuple[float, float]:
    """
    Track the analytic branch lambda(e^theta) starting from theta=0, lambda=3,
    along the circle |theta|=r (in the theta-plane), and return:
      Mr = max_{|theta|=r} |P(theta)| on the continuous log branch,
      and max |lambda| as a sanity check.
    """
    import cmath
    import mpmath as mp

    mp.mp.dps = int(dps)

    # First reach theta=r (phi=0) along a radial segment.
    lam = 3.0 + 0.0j
    P = math.log(3.0) + 0.0j
    theta_prev = 0.0 + 0.0j
    lam_prev = lam
    for j in range(1, radial_steps + 1):
        theta = (r * j / radial_steps) + 0.0j
        u = cmath.exp(theta)
        lam = _newton_root_on_branch(u=u, lam0=lam_prev, tol=1e-28)
        # continuous log: P += Log(lam/lam_prev) with principal log of ratio (ratio near 1)
        ratio = lam / lam_prev
        P = P + cmath.log(ratio)
        theta_prev = theta
        lam_prev = lam

    # Now traverse the circle.
    Mr = abs(P)
    max_lam = abs(lam_prev)
    for k in range(1, nphi + 1):
        phi = 2.0 * math.pi * k / nphi
        theta = r * complex(math.cos(phi), math.sin(phi))
        u = cmath.exp(theta)
        lam = _newton_root_on_branch(u=u, lam0=lam_prev, tol=1e-26)
        ratio = lam / lam_prev
        P = P + cmath.log(ratio)
        Mr = max(Mr, abs(P))
        max_lam = max(max_lam, abs(lam))
        lam_prev = lam

    return float(Mr), float(max_lam)


@dataclass(frozen=True)
class BranchRadiusPayload:
    disc_u: str
    D_u: str
    D_degree: int
    D_is_palindromic: bool
    D_is_squarefree: bool
    D_inv_x: str
    D_inv_degree: int
    nearest_u: str
    nearest_u_inv: str
    theta_star: str
    R_theta: float
    p_star: int
    arg_theta_star: float
    arg_theta_star_over_pi: float
    near_period_9_delta_rad: float
    near_period_9_k_drift: float
    D_inv_real_roots_in_minus2_2: int
    unit_circle_branch_angles_t: List[float]
    r_used: float
    Mr_bound: float
    remainder_bound_theta_le_0_5: float
    phi_minus_disc_u: str
    phi_minus_nearest_u: str
    phi_minus_theta_star: str
    phi_minus_R_theta: float


def _is_palindromic(P: sp.Poly) -> bool:
    coeffs = [int(c) for c in P.all_coeffs()]
    return coeffs == list(reversed(coeffs))


def _p_star_from_R_theta(R_theta: float, p_max: int = 2000) -> int:
    """
    Smallest integer p>=2 such that 2π/p < R_theta.

    This is the sharp modulus threshold for using the local Taylor/cumulant
    expansion in theta at the p-th root of unity u=exp(2π i/p).
    """
    R = float(R_theta)
    for p in range(2, int(p_max) + 1):
        if (2.0 * math.pi / float(p)) < R:
            return int(p)
    raise RuntimeError(f"Failed to find p_star within p<= {p_max}.")


def _palindromic_invariant_reduction_degree10(Dpoly: sp.Poly) -> sp.Poly:
    """
    Given a palindromic integer polynomial D(u) of degree 20, compute the unique
    D_inv(x) in Z[x] of degree 10 such that:

      D(u) = u^10 * D_inv(u + u^{-1}).

    We use the Chebyshev-type basis U_k(x) = u^k + u^{-k} with recurrence:
      U_0=2, U_1=x, U_{k+1} = x U_k - U_{k-1}.
    """
    u = Dpoly.gens[0]
    deg = int(Dpoly.degree())
    if deg != 20:
        raise ValueError(f"expected deg(D)=20, got {deg}")
    if not _is_palindromic(Dpoly):
        raise ValueError("expected palindromic D(u)")

    n = 10
    x = sp.Symbol("x")

    # Coefficients ascending in u^j.
    coeff_desc = [sp.Integer(c) for c in Dpoly.all_coeffs()]  # u^20..u^0
    d = list(reversed(coeff_desc))  # u^0..u^20

    U: List[sp.Expr] = [sp.Integer(0)] * (n + 1)
    U[0] = sp.Integer(2)
    U[1] = x
    for k in range(1, n):
        U[k + 1] = sp.expand(x * U[k] - U[k - 1])

    Dinv = sp.Integer(d[n])
    for k in range(1, n + 1):
        Dinv = sp.expand(Dinv + sp.Integer(d[n + k]) * U[k])

    Dinv_poly = sp.Poly(Dinv, x, domain=sp.ZZ)

    # Sanity check: u^10 * D_inv(u+u^{-1}) == D(u).
    lhs = sp.expand(Dpoly.as_expr())
    rhs = sp.expand(u**n * Dinv_poly.as_expr().subs(x, u + 1 / u))
    if sp.expand(lhs - rhs) != 0:
        raise RuntimeError("palindromic invariant reduction sanity check failed")
    return Dinv_poly


def _min_theta_from_invariant_root(x0: complex, max_k: int = 8) -> complex:
    """
    Solve 2 cosh(theta) = x0 and return the solution with minimal |theta|
    among the candidates theta = ±acosh(x0/2) + 2π i k.
    """
    import mpmath as mp

    z = mp.mpc(x0) / 2
    base = mp.acosh(z)  # principal
    best: complex | None = None
    for sign in (1, -1):
        for k in range(-max_k, max_k + 1):
            th = sign * base + 2j * mp.pi * k
            th_c = complex(th)
            if best is None or abs(th_c) < abs(best):
                best = th_c
    assert best is not None
    return best


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Branch points, analytic radius in theta, and Taylor remainder certificate for sync-kernel output potential."
    )
    parser.add_argument("--dps", type=int, default=80, help="Decimal digits for root finding/tracking.")
    parser.add_argument("--nphi", type=int, default=1024, help="Number of circle samples for M_r.")
    parser.add_argument(
        "--radial-steps",
        type=int,
        default=160,
        help="Steps for radial continuation from theta=0 to theta=r.",
    )
    parser.add_argument(
        "--radius-factor",
        type=float,
        default=0.99,
        help="Use r = radius_factor * R_theta for Cauchy certificate.",
    )
    parser.add_argument(
        "--progress-seconds",
        type=float,
        default=20.0,
        help="Print a heartbeat progress line every N seconds (0 disables).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_output_potential_branch_radius_certificate.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_output_potential_branch_radius_certificate.tex"),
    )
    args = parser.parse_args()

    prog = _Progress(enabled=(args.progress_seconds > 0), every_seconds=float(args.progress_seconds))
    prog.start("computing discriminant and branch radius")
    try:
        import mpmath as mp

        mp.mp.dps = int(args.dps)

        lam, u = sp.symbols("lam u")
        disc, D = _disc_and_D()
        Dpoly = sp.Poly(D, u, domain=sp.ZZ)
        deg = int(Dpoly.degree())
        pal = _is_palindromic(Dpoly)
        D_squarefree = bool(sp.gcd(Dpoly, Dpoly.diff()).degree() == 0)

        # Palindromic invariant reduction: D(u)=u^10 D_inv(u+u^{-1})
        Dinv_poly = _palindromic_invariant_reduction_degree10(Dpoly)
        x = Dinv_poly.gens[0]
        Dinv_deg = int(Dinv_poly.degree())

        # Unit-circle (theta=it) branch angles: real roots of D_inv(x) in [-2,2].
        # Root count is exact (Sturm sequence), angles are numerical.
        root_count_minus2_2 = int(Dinv_poly.count_roots(-2, 2))

        # Numerical roots of D_inv(x)=0 (degree-10), then map via 2 cosh(theta)=x.
        print("[sync-branch-radius] finding roots of D_inv(x)=0 (degree 10)", flush=True)
        roots_x = sp.nroots(Dinv_poly, n=int(args.dps), maxsteps=250)
        roots_x_c: List[complex] = [complex(sp.N(r, int(args.dps))) for r in roots_x]

        # Choose theta_star that minimizes |theta| over all roots and 2π i Z lifts.
        best_theta = None
        best_x = None
        for xx in roots_x_c:
            th = _min_theta_from_invariant_root(xx, max_k=10)
            if best_theta is None or abs(th) < abs(best_theta):
                best_theta = th
                best_x = xx
        assert best_theta is not None and best_x is not None

        # Presentation conventions: prefer Re(theta)>=0 and Im(theta)>=0 (use symmetries).
        theta_star = best_theta
        if theta_star.real < 0:
            theta_star = -theta_star
        if theta_star.imag < 0:
            theta_star = theta_star.conjugate()

        import cmath

        u_star = cmath.exp(theta_star)
        u_inv = 1.0 / u_star

        R_theta = float(abs(theta_star))
        arg_theta = float(math.atan2(theta_star.imag, theta_star.real))

        # Unit-circle branch angles t in (0,pi]: theta=it => x=2cos t in [-2,2].
        unit_circle_t: List[float] = []
        # Use numerical roots to list angles (count is already exact).
        for rr in roots_x:
            re = float(sp.re(rr))
            im = float(sp.im(rr))
            if abs(im) > 1e-30:
                continue
            if re < -2 - 1e-12 or re > 2 + 1e-12:
                continue
            # t = arccos(x/2) in [0,pi]
            t = float(mp.acos(mp.mpf(re) / 2))
            unit_circle_t.append(t)
        unit_circle_t = sorted(unit_circle_t)

        # Near-period-9 diagnostic from arg(theta_star).
        arg_over_pi = float(arg_theta / math.pi)
        delta9 = float(arg_theta - (4.0 * math.pi / 9.0))
        k_drift = float(math.pi / (2.0 * abs(delta9))) if delta9 != 0 else float("inf")

        # Cauchy remainder certificate via M_r on |theta|=r.
        r_used = float(args.radius_factor) * R_theta
        print("[sync-branch-radius] tracking analytic branch on |theta|=r", flush=True)
        Mr, _max_lam = _track_circle_Mr(
            r=r_used,
            nphi=int(args.nphi),
            radial_steps=int(args.radial_steps),
            dps=int(args.dps),
        )
        # Add a small safety margin.
        Mr_bound = float(Mr) * 1.01

        # Bound for |theta|<=0.5.
        theta_max = 0.5
        rem = Mr_bound * (theta_max**9) / (r_used**9) * (1.0 / (1.0 - theta_max / r_used))

        # Negative-carry cubic discriminant and radius.
        print("[sync-branch-radius] computing phi_minus discriminant and radius", flush=True)
        G = _phi_minus_cubic(lam, u)
        disc2 = sp.discriminant(sp.Poly(G, lam), lam)
        disc2 = _normalize_int_poly_u(disc2, u)
        disc2_poly = sp.Poly(disc2, u, domain=sp.ZZ)
        roots2 = sp.nroots(disc2_poly, n=int(args.dps), maxsteps=200)
        roots2_c: List[complex] = [complex(sp.N(r, int(args.dps))) for r in roots2]
        best_u2 = None
        best_th2 = None
        for uu in roots2_c:
            if abs(uu) == 0:
                continue
            th = _min_theta_distance(uu, max_k=8)
            if best_th2 is None or abs(th) < abs(best_th2):
                best_th2 = th
                best_u2 = uu
        assert best_u2 is not None and best_th2 is not None
        theta2 = best_th2
        u2 = best_u2
        if theta2.real < 0:
            # Prefer a representative with Re(theta)>=0.
            u2 = 1.0 / u2
            theta2 = _min_theta_distance(u2, max_k=8)
        R2 = float(abs(theta2))

        payload = BranchRadiusPayload(
            disc_u=str(disc),
            D_u=str(D),
            D_degree=deg,
            D_is_palindromic=bool(pal),
            D_is_squarefree=bool(D_squarefree),
            D_inv_x=str(Dinv_poly.as_expr()),
            D_inv_degree=int(Dinv_deg),
            nearest_u=f"{u_star.real:.10f}{u_star.imag:+.10f}i",
            nearest_u_inv=f"{u_inv.real:.10f}{u_inv.imag:+.10f}i",
            theta_star=f"{theta_star.real:.10f}{theta_star.imag:+.10f}i",
            R_theta=float(R_theta),
            p_star=int(_p_star_from_R_theta(R_theta)),
            arg_theta_star=float(arg_theta),
            arg_theta_star_over_pi=float(arg_over_pi),
            near_period_9_delta_rad=float(delta9),
            near_period_9_k_drift=float(k_drift),
            D_inv_real_roots_in_minus2_2=int(root_count_minus2_2),
            unit_circle_branch_angles_t=[float(t) for t in unit_circle_t],
            r_used=float(r_used),
            Mr_bound=float(Mr_bound),
            remainder_bound_theta_le_0_5=float(rem),
            phi_minus_disc_u=str(disc2),
            phi_minus_nearest_u=f"{u2.real:.10f}{u2.imag:+.10f}i",
            phi_minus_theta_star=f"{theta2.real:.10f}{theta2.imag:+.10f}i",
            phi_minus_R_theta=float(R2),
        )

        jout = Path(args.json_out)
        jout.parent.mkdir(parents=True, exist_ok=True)
        jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")

        # Build TeX snippet (Chinese, for the paper).
        def _poly_multiline_tex(expr: sp.Expr, var: sp.Symbol, *, max_line_len: int = 75) -> List[str]:
            """Format an integer polynomial as multiple TeX lines.

            The returned list is intended to be used inside an amsmath aligned block.
            """
            P = sp.Poly(sp.expand(expr), var, domain=sp.ZZ)
            terms = []
            for (e,), coeff in sorted(P.as_dict().items(), key=lambda kv: -int(kv[0][0])):
                coeff = sp.Integer(coeff)
                if coeff == 0:
                    continue
                if e == 0:
                    terms.append(coeff)
                else:
                    terms.append(coeff * (var ** int(e)))

            if not terms:
                return ["0"]

            parts: List[str] = []
            for idx, t in enumerate(terms):
                t = sp.expand(t)
                sign = -1 if t.could_extract_minus_sign() else 1
                t_abs = -t if sign < 0 else t
                tex = sp.latex(t_abs)
                if idx == 0:
                    parts.append(("- " + tex) if sign < 0 else tex)
                else:
                    parts.append(("- " + tex) if sign < 0 else ("+ " + tex))

            lines_out: List[str] = []
            cur = parts[0]
            for p in parts[1:]:
                if len(cur) + 1 + len(p) > max_line_len:
                    lines_out.append(cur)
                    cur = p
                else:
                    cur = cur + " " + p
            lines_out.append(cur)
            return lines_out

        u_tex = sp.Symbol("u")
        D_expr = sp.Poly(D, u_tex, domain=sp.ZZ).as_expr()
        disc_expr = sp.Poly(disc, u_tex, domain=sp.ZZ).as_expr()
        disc_lines = _poly_multiline_tex(disc_expr, u_tex)
        D_lines = _poly_multiline_tex(D_expr, u_tex)

        x_tex = sp.Symbol("x")
        Dinv_expr = sp.Poly(Dinv_poly.as_expr(), x_tex, domain=sp.ZZ).as_expr()
        Dinv_lines = _poly_multiline_tex(Dinv_expr, x_tex)

        disc2_expr = sp.Poly(disc2, u_tex, domain=sp.ZZ).as_expr()
        disc2_latex = sp.latex(disc2_expr)

        r_str = f"{r_used:.6f}"
        R_str = f"{R_theta:.10f}"
        Mr_str = f"{Mr_bound:.6f}"
        rem_str = f"{rem:.6e}"
        R2_str = f"{R2:.10f}"
        R_inv_sq_str = f"{1.0 / (R_theta * R_theta):.6f}"

        # Nearest conjugate pair (|u|<1) and reciprocal pair (|u|>1).
        u_small = u_inv
        if abs(u_small) > abs(u_star):
            u_small = u_star
        u_large = 1.0 / u_small
        u_small_re = u_small.real
        u_small_im = abs(u_small.imag)
        u_small_abs = abs(u_small)
        u_large_re = u_large.real
        u_large_im = abs(u_large.imag)
        u_large_abs = abs(u_large)
        u_small_pair = f"{u_small_re:.10f}\\pm {u_small_im:.10f}i"
        u_large_pair = f"{u_large_re:.10f}\\mp {u_large_im:.10f}i"
        u_small_abs_str = f"{u_small_abs:.7f}"
        u_large_abs_str = f"{u_large_abs:.7f}"
        theta_small_re = -abs(theta_star.real)
        theta_small_im = abs(theta_star.imag)
        theta_small_pair = f"{theta_small_re:.10f}\\pm {theta_small_im:.10f}i"
        two_psi_str = f"{2.0 * arg_theta:.10f}"

        tex_lines: List[str] = []
        tex_lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_output_potential_branch_radius_certificate.py")
        tex_lines.append("\\begin{proposition}[复参数分歧点的判别式刻画]\\label{prop:pressure-branchpoints-discriminant}")
        tex_lines.append("把 $F(\\lambda,u)\\in\\ZZ[u][\\lambda]$ 视为关于 $\\lambda$ 的代数方程，并在 $u\\in\\CC^\\times$ 上延拓其代数函数分支。")
        tex_lines.append("则 $\\lambda(u)$ 的分歧点恰对应 $\\lambda$ 变为重根，即存在 $(\\lambda,u)\\in\\CC\\times\\CC^\\times$ 使得")
        tex_lines.append("$$")
        tex_lines.append("F(\\lambda,u)=0,\\qquad \\partial_{\\lambda}F(\\lambda,u)=0.")
        tex_lines.append("$$")
        tex_lines.append("等价地，分歧点的 $u$-集合由关于 $\\lambda$ 的判别式零点给出；对本附录的六次 $F$，有完全显式分解")
        tex_lines.append("$$")
        tex_lines.append("\\begin{aligned}")
        if disc_lines:
            tex_lines.append("\\mathrm{Disc}_{\\lambda}(F)(u)&=" + disc_lines[0] + "\\\\")
            for ln in disc_lines[1:]:
                tex_lines.append("&" + ln + "\\\\")
        tex_lines.append("&=-u^{5}\\,D(u),")
        tex_lines.append("\\end{aligned}")
        tex_lines.append("$$")
        tex_lines.append("其中 $D(u)\\in\\ZZ[u]$ 为 $20$ 次回文多项式：")
        tex_lines.append("$$")
        tex_lines.append("\\begin{aligned}")
        if D_lines:
            if len(D_lines) == 1:
                tex_lines.append("D(u)&=" + D_lines[0] + ".")
            else:
                tex_lines.append("D(u)&=" + D_lines[0] + "\\\\")
                for ln in D_lines[1:-1]:
                    tex_lines.append("&" + ln + "\\\\")
                tex_lines.append("&" + D_lines[-1] + ".")
        tex_lines.append("\\end{aligned}")
        tex_lines.append("$$")
        tex_lines.append("\\end{proposition}")
        tex_lines.append("")
        tex_lines.append("\\begin{corollary}[回文判别式的 $10$ 次不变量降阶]\\label{cor:pressure-discriminant-invariant-reduction}")
        tex_lines.append("由于 $D(u)$ 为 $20$ 次回文多项式（$u^{20}D(1/u)=D(u)$），存在唯一 $D_{\\mathrm{inv}}(x)\\in\\ZZ[x]$（$\\deg=10$）使得")
        tex_lines.append("$$")
        tex_lines.append("D(u)=u^{10}\\,D_{\\mathrm{inv}}\\!\\left(u+u^{-1}\\right).")
        tex_lines.append("$$")
        tex_lines.append("写 $u=e^{\\theta}$，则 $u+u^{-1}=2\\cosh\\theta$，从而")
        tex_lines.append("$$")
        tex_lines.append("D(e^{\\theta})=e^{10\\theta}\\,D_{\\mathrm{inv}}(2\\cosh\\theta).")
        tex_lines.append("$$")
        tex_lines.append("因此除去平凡因子 $u^5$ 外，Perron 分支的有限分歧点由一元 $10$ 次方程 $D_{\\mathrm{inv}}(2\\cosh\\theta)=0$ 完全刻画；求最近分歧点可先解 $D_{\\mathrm{inv}}(x)=0$ 再用 $2\\cosh\\theta=x$ 的反双曲余弦映射选取 $|\\theta|$ 最小的 $2\\pi i\\ZZ$-lift。")
        tex_lines.append("对本核有完全显式的整数多项式")
        tex_lines.append("$$")
        tex_lines.append("\\begin{aligned}")
        if Dinv_lines:
            if len(Dinv_lines) == 1:
                tex_lines.append("D_{\\mathrm{inv}}(x)&=" + Dinv_lines[0] + ".")
            else:
                tex_lines.append("D_{\\mathrm{inv}}(x)&=" + Dinv_lines[0] + "\\\\")
                for ln in Dinv_lines[1:-1]:
                    tex_lines.append("&" + ln + "\\\\")
                tex_lines.append("&" + Dinv_lines[-1] + ".")
        tex_lines.append("\\end{aligned}")
        tex_lines.append("$$")
        tex_lines.append("并且若取完成化变量 $u=r^2,\\ s=r+r^{-1}$（命题 \\ref{prop:weighted-completion-Q}），则 $u+u^{-1}=s^2-2$，从而")
        tex_lines.append("$$")
        tex_lines.append("\\mathrm{Disc}_w\\bigl(\\widehat\\Delta(w,s)\\bigr)=D_{\\mathrm{inv}}(s^2-2),")
        tex_lines.append("$$")
        tex_lines.append("这与式 \\eqref{eq:sync_kernel_hatdelta_discriminant} 的 $20$ 次多项式完全一致。")
        tex_lines.append("\\end{corollary}")
        tex_lines.append("")
        tex_lines.append("\\begin{corollary}[单位圆扭曲上的三个本征分歧角]\\label{cor:pressure-unit-circle-branch-angles}")
        tex_lines.append("取 $u=e^{it}$（即 $\\theta=it$，$t\\in\\RR$），则 $u+u^{-1}=2\\cos t\\in[-2,2]$。因此单位圆上的分歧点与 $D_{\\mathrm{inv}}(x)$ 在区间 $[-2,2]$ 内的实根一一对应。")
        tex_lines.append(f"对本核，Sturm 计数给出 $D_{{\\mathrm{{inv}}}}$ 在 $[-2,2]$ 内恰有 {root_count_minus2_2} 个实根，故在一个周期 $t\\in(0,\\pi]$ 内恰有三个位于纯虚轴的分歧角（再加 $2\\pi\\ZZ$ 平移）：")
        tex_lines.append("$$")
        # angles: print in increasing order, aligned with Table tab_sync_kernel_hatdelta_branch_points
        if len(unit_circle_t) >= 3:
            t1, t2, t3 = unit_circle_t[:3]
            tex_lines.append(f"t_1\\approx {t1:.12f},\\qquad t_2\\approx {t2:.12f},\\qquad t_3\\approx {t3:.12f}.")
        else:
            tex_lines.append("\\text{（数值根略）}")
        tex_lines.append("$$")
        tex_lines.append("等价地，在完成化坐标 $s=r+r^{-1}=2\\cos(t/2)$ 下对应表 \\ref{tab:sync_kernel_hatdelta_branch_points} 所列的三个单位圆分歧点。")
        tex_lines.append("\\end{corollary}")
        tex_lines.append("")
        tex_lines.append("\\begin{corollary}[最近分歧点与 $\\theta$-解析半径]\\label{cor:pressure-analytic-radius}")
        tex_lines.append("以 $\\theta=\\log u$ 为局部坐标，并以 $\\lambda(1)=3$ 的 Perron 分支为基准进行解析延拓。")
        tex_lines.append(
            "令 $u_\\pm$ 为 $D(u)=0$ 的根中、使得 $|\\log u|$（在 $\\log u$ 的 $2\\pi i\\ZZ$ 选取中取最小模）最小的一对共轭根（取 $|u_\\pm|<1$ 的那支）。"
        )
        tex_lines.append("数值上可取")
        tex_lines.append("$$")
        tex_lines.append("\\begin{aligned}")
        tex_lines.append(
            f"u_\\pm&\\approx {u_small_pair}\\quad(|u_\\pm|\\approx {u_small_abs_str}),\\\\"
        )
        tex_lines.append(
            f"u_\\pm^{{-1}}&\\approx {u_large_pair}\\quad(|u_\\pm^{{-1}}|\\approx {u_large_abs_str}),"
        )
        tex_lines.append("\\end{aligned}")
        tex_lines.append("$$")
        tex_lines.append("并且相应的最近分歧点可取")
        tex_lines.append("$$")
        tex_lines.append(f"\\theta_\\pm:=\\log u_\\pm\\approx {theta_small_pair},\\qquad -\\theta_\\pm,")
        tex_lines.append("$$")
        tex_lines.append("取 $\\theta_\\star$ 为 $\\theta_\\pm$ 中满足 $\\Re\\theta_\\star\\ge 0,\\ \\Im\\theta_\\star\\ge 0$ 的代表。")
        tex_lines.append("从而 $\\theta=0$ 处解析芽的最大圆盘半径为")
        tex_lines.append("$$")
        tex_lines.append(f"\\boxed{{\\ R_\\theta:=|\\theta_\\star|\\approx {R_str}\\ }}.")
        tex_lines.append("$$")
        tex_lines.append("因此在 $|\\theta|<R_\\theta$ 内，$\\lambda(e^{\\theta})$ 与 $P(\\theta)=\\log\\lambda(e^{\\theta})$ 可作为单值解析函数延拓；并且在 $|\\theta|=R_\\theta$ 处发生代数分歧（分支点）。")
        tex_lines.append("\\end{corollary}")
        tex_lines.append("")
        two_pi_5 = 2.0 * math.pi / 5.0
        two_pi_6 = 2.0 * math.pi / 6.0
        two_pi_7 = 2.0 * math.pi / 7.0
        ratio6 = two_pi_6 / float(payload.R_theta)
        ratio7 = two_pi_7 / float(payload.R_theta)
        tex_lines.append("\\begin{corollary}[单位根扭曲的模数阈值（$p_\\star=6$）]\\label{cor:pressure-unit-root-modulus-threshold}")
        tex_lines.append(
            "对单位根扭曲 $u=\\omega_p=e^{2\\pi i/p}$，取 $\\theta=\\log u$ 的最小模 $2\\pi i\\ZZ$-lift，则 $|\\theta|=2\\pi/p$。"
            "因此以 $\\theta=0$ 为中心的局部 Taylor/累积展开在 $u=\\omega_p$ 处可作为收敛算法使用的必要条件是"
        )
        tex_lines.append("$$")
        tex_lines.append("\\frac{2\\pi}{p}<R_\\theta.")
        tex_lines.append("$$")
        tex_lines.append("由数值比较")
        tex_lines.append("$$")
        tex_lines.append(
            f"\\frac{{2\\pi}}{{5}}\\approx {two_pi_5:.12f}>R_\\theta,\\qquad "
            f"\\frac{{2\\pi}}{{6}}\\approx {two_pi_6:.12f}<R_\\theta,\\qquad "
            f"\\frac{{2\\pi}}{{7}}\\approx {two_pi_7:.12f}<R_\\theta,"
        )
        tex_lines.append("$$")
        tex_lines.append(
            f"并利用 $2\\pi/p$ 随 $p$ 单调递减，可得模数阈值 $p_\\star={payload.p_star}$："
            "$p\\le 5$ 必在解析域外，$p=6$ 处于贴边收敛区（$(2\\pi/6)/R_\\theta\\approx "
            f"{ratio6:.6f}$），而 $p\\ge 7$ 进入稳健收敛区（例如 $(2\\pi/7)/R_\\theta\\approx {ratio7:.6f}$）。"
        )
        tex_lines.append("\\end{corollary}")
        tex_lines.append("")
        tex_lines.append("\\begin{corollary}[Taylor 截断余项的 Cauchy 证书]\\label{cor:pressure-taylor-remainder-cauchy}")
        tex_lines.append("设 $T_8(\\theta)$ 为 $P(\\theta)$ 在 $\\theta=0$ 的 Taylor 多项式截断到 $\\theta^8$。取任意 $0<r<R_\\theta$ 并记")
        tex_lines.append("$$")
        tex_lines.append("M_r:=\\max_{|\\theta|=r}|P(\\theta)|.")
        tex_lines.append("$$")
        tex_lines.append("则对任意 $|\\theta|<r$ 有一致余项上界")
        tex_lines.append("$$")
        tex_lines.append(
            "\\boxed{\\ \\bigl|P(\\theta)-T_8(\\theta)\\bigr|"
            "\\le M_r\\cdot \\frac{|\\theta|^{9}}{r^{9}}\\cdot\\frac{1}{1-|\\theta|/r}\\ }."
        )
        tex_lines.append("$$")
        tex_lines.append(f"取 $r:={args.radius_factor}\\,R_\\theta\\approx {r_str}$ 并沿 $|\\theta|=r$ 对分支作连续数值跟踪（初值 $\\lambda(1)=3$），得到上界 $M_r\\le {Mr_str}$。")
        tex_lines.append("因此当 $|\\theta|\\le 0.5$ 时，有可审计余项界")
        tex_lines.append("$$")
        tex_lines.append(f"\\bigl|P(\\theta)-T_8(\\theta)\\bigr|\\le {rem_str}.")
        tex_lines.append("$$")
        tex_lines.append("\\end{corollary}")
        tex_lines.append("")
        tex_lines.append("\\begin{remark}[局部展开的有效域与最优截断尺度]\\label{rem:pressure-local-series-domain}")
        tex_lines.append(
            "由于 $R_\\theta$ 是 $\\theta=0$ 的真实解析半径，"
            "所有以 $P(\\theta)$ 的 Taylor 系数为核心的 CLT/Edgeworth/中偏差局部展开都必须满足 $|\\theta|<R_\\theta$。"
        )
        tex_lines.append("对任意 $0<r<R_\\theta$，Cauchy 估计给出一般系数界")
        tex_lines.append("$$")
        tex_lines.append(
            "|\\kappa_n|=|P^{(n)}(0)|\\le n!\\,\\frac{\\sup_{|\\theta|=r}|P(\\theta)|}{r^{n}},"
        )
        tex_lines.append("$$")
        tex_lines.append(
            "因此第 $n$ 项规模至多按 $(|\\theta|/r)^n$ 衰减。"
            "固定 $|\\theta|$ 时，可实现的最优截断阶由比值 $|\\theta|/R_\\theta$ 决定；"
            "当 $|\\theta|$ 接近 $R_\\theta$ 时，高阶项不可能稳定收敛。"
        )
        tex_lines.append("\\end{remark}")
        tex_lines.append("")
        tex_lines.append("\\begin{remark}[分歧半径的势指纹：与负携带势的对比]\\label{rem:pressure-radius-compare-phi-minus}")
        tex_lines.append("在附录 \\ref{app:vector-potential} 的负携带势实例中，主特征值满足三次方程")
        tex_lines.append("$$")
        tex_lines.append("\\lambda^3-(u+2)\\lambda^2+(u-2)\\lambda+3u=0,\\qquad u=e^{\\theta}.")
        tex_lines.append("$$")
        tex_lines.append("对该三次关于 $\\lambda$ 取判别式（忽略非零常数因子）得到分歧点集合由四次多项式")
        tex_lines.append("$$")
        tex_lines.append(disc2_latex + "=0")
        tex_lines.append("$$")
        tex_lines.append("刻画；其最近分歧点可取")
        tex_lines.append("$$")
        tex_lines.append(f"u_\\star^{{(-)}}\\approx {payload.phi_minus_nearest_u},\\qquad \\theta_\\star^{{(-)}}\\approx {payload.phi_minus_theta_star},")
        tex_lines.append("$$")
        tex_lines.append("从而对应解析半径")
        tex_lines.append("$$")
        tex_lines.append(f"R_\\theta^{{(-)}}:=|\\theta_\\star^{{(-)}}|\\approx {R2_str}.")
        tex_lines.append("$$")
        tex_lines.append("因此在“分歧半径”这一可计算的谱指纹下，负携带势的局部解析半径大于同步核输出位势，从而在相同的 $|\\theta|$ 尺度上可获得更强的统一余项控制（Cauchy 估计中的 $r^{-n}$ 衰减更快）。")
        tex_lines.append("\\end{remark}")
        tex_lines.append("")
        tex_lines.append("\\begin{remark}[高阶偶系数的振荡与最近复分歧角]\\label{rem:pressure-even-derivative-oscillation}")
        tex_lines.append("令 $f(\\theta):=P(\\theta)-\\theta/2-\\log 3$，则 $f$ 为偶函数且在 $|\\theta|<R_\\theta$ 内解析。")
        tex_lines.append("由最近分歧点 $\\theta_\\star$ 的几何位置，可用 Darboux 型系数转移（或等价的 Cauchy 系数积分主贡献）解释高阶偶系数的符号/振荡：")
        tex_lines.append("其主导模式由 $\\pm\\theta_\\star$ 及其共轭贡献叠加给出，故 $f^{(2k)}(0)$ 的符号可由")
        tex_lines.append("$\\cos\\bigl(2k\\arg(\\theta_\\star)+\\phi_0\\bigr)$ 型项控制（$\\phi_0$ 为分支点局部相位）。")
        tex_lines.append(
            f"在本核上 $\\arg(\\theta_\\star)\\approx {payload.arg_theta_star:.10f}$，"
            f"故 $2\\psi:=2\\arg(\\theta_\\star)\\approx {two_psi_str}$。"
        )
        tex_lines.append("进一步，由于 $\\gcd(D(u),D'(u))=1$，$D(u)$ 在 $\\CC$ 上无重根，因此每个有限分歧点都是简单谱碰撞并诱导平方根型 Puiseux 分歧。于是高阶偶导数具有通用包络指数 $k^{-3/2}$：存在常数 $C\\neq 0$ 使得（$k\\to\\infty$）")
        tex_lines.append("$$")
        tex_lines.append("f^{(2k)}(0)\\sim C\\,(2k)!\\,|\\theta_\\star|^{-2k}\\,k^{-3/2}\\cos\\bigl(2k\\arg(\\theta_\\star)+\\phi_0\\bigr).")
        tex_lines.append("$$")
        tex_lines.append(
            "因此偶阶累积量 $\\kappa_{2k}:=P^{(2k)}(0)=f^{(2k)}(0)$ 的符号不会稳定为纯交替，"
            "而必须呈现由 $\\psi$ 锁定的振荡相位。相应的比值检验为"
        )
        tex_lines.append("$$")
        tex_lines.append(
            "\\frac{\\kappa_{2k}}{(2k)(2k-1)\\,\\kappa_{2k-2}}"
            f"\\approx R_\\theta^{{-2}}\\,\\frac{{\\cos(2k\\psi+\\phi_0)}}{{\\cos(2(k-1)\\psi+\\phi_0)}}"
            f",\\qquad R_\\theta^{{-2}}\\approx {R_inv_sq_str}."
        )
        tex_lines.append("$$")
        tex_lines.append(
            f"并且 $\\arg(\\theta_\\star)/\\pi\\approx {payload.arg_theta_star_over_pi:.10f}\\approx 4/9$，"
            f"与 $4\\pi/9$ 的偏差 $\\Delta\\approx {payload.near_period_9_delta_rad:.6e}$（弧度）给出近 $9$ 周期的漂移尺度"
        )
        tex_lines.append("$$")
        tex_lines.append(f"k_\\mathrm{{drift}}\\sim \\frac{{\\pi}}{{2|\\Delta|}}\\approx {payload.near_period_9_k_drift:.3f}.")
        tex_lines.append("$$")
        tex_lines.append("\\end{remark}")

        tout = Path(args.tex_out)
        tout.parent.mkdir(parents=True, exist_ok=True)
        tout.write_text("\n".join(tex_lines) + "\n", encoding="utf-8")
    finally:
        prog.stop("done")


if __name__ == "__main__":
    main()

