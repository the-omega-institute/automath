#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the diffusive sinc scaling limit at the double root y=0 for Z_m(y).

This script is English-only by repository convention.

We numerically audit the scaling statement (paper):

  (2/m) * Z_m( -u / m^2 )  ->  sinc( sqrt(u)/2 )

and we also report the same comparison under the exact normalization by
Z_m(0)=floor(m/2)+1:

  Z_m( -u / m^2 ) / Z_m(0)  ->  sinc( sqrt(u)/2 )

for u on a real grid (a compact subset of C), and we also locate the first few
scaled near-zero roots via u = -m^2 * y, comparing them to 4*pi^2*j^2.

Outputs (default):
  - artifacts/export/fold_zm_double_root_diffusive_sinc_limit_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import mpmath as mp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sinc(z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    if z == 0:
        return mp.mpf(1)
    return mp.sin(z) / z


def _target(u: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    # sinc(sqrt(u)/2) is an entire function of u; mpmath's principal sqrt is fine
    # for this numerical audit on R.
    return _sinc(mp.sqrt(u) / 2)


def _zm_eval(m: int, y: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    # Z_0..Z_3 match the paper's (Fold-derived) initial values.
    if m < 0:
        raise ValueError("m must be nonnegative")
    if m == 0:
        return mp.mpf(1)
    z0 = mp.mpf(1)
    z1 = mp.mpf(1) + y
    if m == 1:
        return z1
    z2 = mp.mpf(2) + mp.mpf(2) * y
    if m == 2:
        return z2
    z3 = mp.mpf(2) + mp.mpf(5) * y + y * y
    if m == 3:
        return z3
    # rolling recurrence
    for _k in range(4, m + 1):
        z4 = z3 + (mp.mpf(1) + mp.mpf(2) * y) * z2 - z1 - (y * (y + 1)) * z0
        z0, z1, z2, z3 = z1, z2, z3, z4
    return z3


def _scaled_f(m: int, u: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    y = -(u / (m * m))
    return (mp.mpf(2) / m) * _zm_eval(m, y)


def _zm0(m: int) -> mp.mpf:
    # Exact closed form (paper): Z_m(0) = floor(m/2) + 1.
    return mp.mpf((m // 2) + 1)


def _scaled_g(m: int, u: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    y = -(u / (m * m))
    return _zm_eval(m, y) / _zm0(m)


def _grid_max_error_pair(m: int, u_grid: List[mp.mpf]) -> Tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    max_err_f = mp.mpf(0)
    argmax_u_f = u_grid[0] if u_grid else mp.mpf(0)
    max_err_g = mp.mpf(0)
    argmax_u_g = u_grid[0] if u_grid else mp.mpf(0)
    for u in u_grid:
        err_f = abs(_scaled_f(m, u) - _target(u))
        if err_f > max_err_f:
            max_err_f = err_f
            argmax_u_f = u
        err_g = abs(_scaled_g(m, u) - _target(u))
        if err_g > max_err_g:
            max_err_g = err_g
            argmax_u_g = u
    return max_err_f, argmax_u_f, max_err_g, argmax_u_g


def _try_bracket_root(
    m: int,
    u0: mp.mpf,
    rel0: mp.mpf,
    rel_max: mp.mpf,
    n_expand: int,
) -> Optional[Tuple[mp.mpf, mp.mpf]]:
    # Try to find a sign-change bracket for f(u)=0 around u0 by expanding
    # a symmetric interval [u0*(1-rel), u0*(1+rel)].
    rel = rel0
    f = lambda uu: mp.re(_scaled_f(m, uu))  # should be real on real uu
    for _ in range(n_expand + 1):
        a = u0 * (1 - rel)
        b = u0 * (1 + rel)
        fa = f(a)
        fb = f(b)
        if fa == 0:
            return (a, a)
        if fb == 0:
            return (b, b)
        if fa * fb < 0:
            return (a, b)
        # expand
        if rel >= rel_max:
            break
        rel = min(rel_max, rel * mp.mpf("1.5"))
    return None


def _bisect_root(m: int, a: mp.mpf, b: mp.mpf, tol: mp.mpf) -> mp.mpf:
    f = lambda uu: mp.re(_scaled_f(m, uu))
    fa = f(a)
    fb = f(b)
    if a == b:
        return a
    if fa == 0:
        return a
    if fb == 0:
        return b
    if fa * fb > 0:
        raise ValueError("bisection requires a sign change")
    lo, hi = a, b
    flo, fhi = fa, fb
    for _ in range(400):
        mid = (lo + hi) / 2
        fmid = f(mid)
        if abs(fmid) <= tol or abs(hi - lo) <= tol:
            return mid
        if flo * fmid < 0:
            hi, fhi = mid, fmid
        else:
            lo, flo = mid, fmid
    return (lo + hi) / 2


def _scaled_root_u(m: int, j: int, tol: mp.mpf) -> Optional[mp.mpf]:
    u_star = mp.mpf(4) * (mp.pi**2) * (j * j)

    # First attempt: secant findroot near u_star.
    try:
        u1 = u_star * mp.mpf("0.97")
        u2 = u_star * mp.mpf("1.03")
        u_hat = mp.findroot(lambda uu: mp.re(_scaled_f(m, uu)), (u1, u2), tol=tol)
        if abs(mp.im(u_hat)) <= 10 * tol:
            return mp.re(u_hat)
    except Exception:
        pass

    # Fallback: bracket + bisection.
    br = _try_bracket_root(
        m=m,
        u0=u_star,
        rel0=mp.mpf("0.10"),
        rel_max=mp.mpf("0.80"),
        n_expand=10,
    )
    if br is None:
        return None
    a, b = br
    if a == b:
        return a
    try:
        return _bisect_root(m, a, b, tol=tol)
    except Exception:
        return None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=80)
    ap.add_argument("--m-values", type=str, default="80,120,200,320")
    ap.add_argument("--u-min", type=float, default=-10.0)
    ap.add_argument("--u-max", type=float, default=80.0)
    ap.add_argument("--u-grid-n", type=int, default=361)
    ap.add_argument("--j-max", type=int, default=2)
    args = ap.parse_args()

    mp.mp.dps = int(args.dps)
    tol = mp.mpf(10) ** (-(mp.mp.dps // 2))

    m_values = [int(x.strip()) for x in str(args.m_values).split(",") if x.strip()]
    if not m_values or any(m <= 0 for m in m_values):
        raise ValueError("--m-values must be a comma-separated list of positive integers")

    u_min = mp.mpf(str(args.u_min))
    u_max = mp.mpf(str(args.u_max))
    if u_max <= u_min:
        raise ValueError("--u-max must be greater than --u-min")
    u_grid_n = int(args.u_grid_n)
    if u_grid_n < 2:
        raise ValueError("--u-grid-n must be >= 2")

    t0 = time.time()

    # Real u-grid.
    u_grid = [u_min + (u_max - u_min) * (mp.mpf(i) / (u_grid_n - 1)) for i in range(u_grid_n)]

    grid_errors: List[Dict[str, object]] = []
    for m in m_values:
        max_err_f, argmax_u_f, max_err_g, argmax_u_g = _grid_max_error_pair(m, u_grid)
        grid_errors.append(
            {
                "m": m,
                "u_min": float(u_min),
                "u_max": float(u_max),
                "u_grid_n": u_grid_n,
                "max_abs_error_2_over_m": float(max_err_f),
                "argmax_u_2_over_m": float(argmax_u_f),
                "max_abs_error_norm_by_zm0": float(max_err_g),
                "argmax_u_norm_by_zm0": float(argmax_u_g),
            }
        )

    # Scaled near-zero roots (u = -m^2 y).
    roots: List[Dict[str, object]] = []
    for m in m_values:
        for j in range(1, int(args.j_max) + 1):
            u_star = mp.mpf(4) * (mp.pi**2) * (j * j)
            u_hat = _scaled_root_u(m, j, tol=tol)
            entry: Dict[str, object] = {"m": m, "j": j, "u_star": float(u_star)}
            if u_hat is None:
                entry["status"] = "fail"
            else:
                entry["status"] = "ok"
                entry["u_hat"] = float(u_hat)
                entry["abs_err_u"] = float(abs(u_hat - u_star))
                entry["y_hat"] = float(-(u_hat / (m * m)))
                entry["abs_f_at_u_hat"] = float(abs(_scaled_f(m, u_hat)))
                entry["abs_f_at_u_star"] = float(abs(_scaled_f(m, u_star)))
            roots.append(entry)

    payload: Dict[str, object] = {
        "script": Path(__file__).name,
        "mp_dps": mp.mp.dps,
        "t_wall_s": float(time.time() - t0),
        "grid_errors": grid_errors,
        "scaled_roots": roots,
        "notes": {
            "limit_target": "sinc(sqrt(u)/2)",
            "scaling": "evaluate Z_m at y=-u/m^2 and scale by 2/m",
            "scaling_alt": "evaluate Z_m at y=-u/m^2 and normalize by Z_m(0)=floor(m/2)+1",
            "root_scaling": "u = -m^2*y_root should approach 4*pi^2*j^2",
        },
    }

    out_json = export_dir() / "fold_zm_double_root_diffusive_sinc_limit_audit.json"
    _write_json(out_json, payload)
    print(f"[ok] wrote {out_json}")


if __name__ == "__main__":
    main()

