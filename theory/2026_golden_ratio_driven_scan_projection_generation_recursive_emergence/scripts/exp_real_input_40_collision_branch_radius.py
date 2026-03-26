#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Branch points and analytic radius for the pure-collision cubic pressure P_2(theta).

We consider the cubic equation (in lambda, parameterized by u):
  f(lambda; u) = lambda^3 - 2 lambda^2 - (u+1) lambda + u = 0.

The algebraic branch points of lambda(u) occur exactly when f has a repeated root
in lambda, i.e. when the discriminant (in lambda) vanishes:
  Disc_lambda f(u) = 4 u^3 + 25 u^2 + 88 u + 8.

Writing u = exp(theta), the branch points in the theta-plane are the lattice:
  theta = log u_j + 2π i k,  k ∈ Z,
where u_j ranges over the three roots of Disc_lambda f(u)=0 and log is the complex
logarithm (principal branch).

We compute the roots u_j, their principal logs, and the analytic radius at theta=0:
  R_theta = min_j min_{k∈Z} |log u_j + 2π i k|.

Outputs:
  - artifacts/export/real_input_40_collision_branch_radius.json
  - sections/generated/eq_real_input_40_collision_branch_radius.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class RootDatum:
    u_re: str
    u_im: str
    log_re: str
    log_im: str
    k_nearest: int
    theta_nearest_re: str
    theta_nearest_im: str
    theta_nearest_abs: str


@dataclass(frozen=True)
class Payload:
    dps: int
    u0_re: str
    uplus_re: str
    uplus_im: str
    log_uplus_re: str
    log_uplus_im: str
    R_theta: str
    roots: List[RootDatum]


def _nearest_k(im: mp.mpf) -> int:
    """Return k that minimizes |im + 2πk| over integers k."""
    twopi = 2 * mp.pi
    # minimizer is nearest integer to -im/(2π)
    return int(mp.nint(-im / twopi))


def _fmt(x: mp.mpf | mp.mpc, nd: int) -> str:
    if isinstance(x, mp.mpc):
        raise TypeError("Use _fmt_re_im for complex numbers.")
    return mp.nstr(x, nd)


def _fmt_re_im(z: mp.mpc, nd: int) -> Tuple[str, str]:
    return mp.nstr(mp.re(z), nd), mp.nstr(mp.im(z), nd)


def main() -> None:
    t0 = time.time()
    ap = argparse.ArgumentParser(
        description="Branch points and analytic radius for the collision cubic pressure."
    )
    ap.add_argument("--dps", type=int, default=80, help="mpmath decimal precision.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_collision_branch_radius.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_real_input_40_collision_branch_radius.tex"),
    )
    args = ap.parse_args()

    dps = int(args.dps)
    if dps < 40:
        raise SystemExit("Require --dps >= 40 for stable root/log output.")
    mp.mp.dps = dps

    u = sp.Symbol("u")
    disc = 4 * u**3 + 25 * u**2 + 88 * u + 8
    poly = sp.Poly(disc, u)
    roots_sp = poly.nroots(n=dps)

    roots: List[mp.mpc] = []
    for r in roots_sp:
        rr = sp.re(r).evalf(dps)
        ri = sp.im(r).evalf(dps)
        roots.append(mp.mpc(mp.mpf(str(rr)), mp.mpf(str(ri))))

    # Identify real root u0 and conjugate pair u±.
    roots_sorted = sorted(roots, key=lambda z: (abs(mp.im(z)), mp.re(z)))
    u0 = roots_sorted[0]
    # Remaining two are conjugates (up to numerical noise); pick +Im as uplus.
    rest = roots_sorted[1:]
    if len(rest) != 2:
        raise RuntimeError("Unexpected number of roots for cubic discriminant.")
    uplus = rest[0] if mp.im(rest[0]) > mp.im(rest[1]) else rest[1]
    if mp.im(uplus) <= 0:
        raise RuntimeError("Failed to identify the positive-imag root.")

    # Logs and nearest lattice shifts.
    nd_out = 16
    payload_roots: List[RootDatum] = []
    R_theta = None
    log_uplus = mp.log(uplus)

    for z in roots:
        lg = mp.log(z)
        k = _nearest_k(mp.im(lg))
        theta = lg + 2j * mp.pi * k
        u_re, u_im = _fmt_re_im(z, nd_out)
        log_re, log_im = _fmt_re_im(lg, nd_out)
        th_re, th_im = _fmt_re_im(theta, nd_out)
        th_abs = _fmt(abs(theta), nd_out)
        payload_roots.append(
            RootDatum(
                u_re=u_re,
                u_im=u_im,
                log_re=log_re,
                log_im=log_im,
                k_nearest=int(k),
                theta_nearest_re=th_re,
                theta_nearest_im=th_im,
                theta_nearest_abs=th_abs,
            )
        )
        if R_theta is None or abs(theta) < R_theta:
            R_theta = abs(theta)

    if R_theta is None:
        raise RuntimeError("Failed to compute R_theta.")

    # Write JSON payload.
    u0_re, _ = _fmt_re_im(u0, nd_out)
    uplus_re, uplus_im = _fmt_re_im(uplus, nd_out)
    log_uplus_re, log_uplus_im = _fmt_re_im(log_uplus, nd_out)
    payload = Payload(
        dps=dps,
        u0_re=u0_re,
        uplus_re=uplus_re,
        uplus_im=uplus_im,
        log_uplus_re=log_uplus_re,
        log_uplus_im=log_uplus_im,
        R_theta=_fmt(R_theta, nd_out),
        roots=payload_roots,
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Write TeX snippet (numeric values only).
    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: list[str] = []
    lines.append("% Generated by scripts/exp_real_input_40_collision_branch_radius.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(f"u_0 &\\approx {u0_re},")
    lines.append("\\\\")
    lines.append(
        f"u_\\pm &\\approx {uplus_re} \\pm {uplus_im}\\,i,"
    )
    lines.append("\\\\")
    lines.append(
        f"\\log u_\\pm &\\approx {log_uplus_re} \\pm {log_uplus_im}\\,i,"
    )
    lines.append("\\\\")
    lines.append(f"R_\\theta &\\approx {_fmt(R_theta, nd_out)}.")
    lines.append("\\end{aligned}")
    lines.append("\\]")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")

    dt = time.time() - t0
    print(f"[collision-branch-radius] wrote {jout} and {tout} in {dt:.2f}s", flush=True)


if __name__ == "__main__":
    main()

