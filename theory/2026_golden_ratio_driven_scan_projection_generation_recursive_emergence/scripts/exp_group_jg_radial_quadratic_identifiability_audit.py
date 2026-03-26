#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit radial-quadratic identifiability for Joukowsky--Gödel ellipse readout.

This script audits identities stated in:
  sections/body/group_unification/subsubsec__group-unification-prime-register-fold-gap-ellipse.tex
  (input part: sections/body/group_unification/parts/subsubsec__group-jg-radial-quadratic-identifiability.tex)

Audits:
  - U_r = r^2 + r^{-2} + 2 cos(2Θ) and support I_r = [c(r)-2, c(r)+2]
  - Integer support separation: g_r >= 31/36 for r>=2
  - Bounded-noise threshold: σ < 31/72 keeps inflated supports disjoint
  - Extreme-value tail identity and inequalities used in the proof
  - Support separation implies KL divergence is infinite

Output:
  - artifacts/export/group_jg_radial_quadratic_identifiability_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _c(r: mp.mpf) -> mp.mpf:
    return r * r + (1 / (r * r))


def _I(r: mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
    c = _c(r)
    return c - 2, c + 2


def _g_int(r: int) -> mp.mpf:
    r1 = mp.mpf(r)
    lo_next = _I(r1 + 1)[0]
    hi = _I(r1)[1]
    return lo_next - hi


def _tail_prob_eps(eps: mp.mpf) -> mp.mpf:
    # P(V > 2-eps) for V=2cos Φ, Φ ~ Unif[0,2π)
    return (1 / mp.pi) * mp.acos(1 - eps / 2)


@dataclass(frozen=True)
class Payload:
    r_max_gap_check: int
    g2_value: float
    g_min_value: float
    g_min_arg_r: int
    g_lower_bound_value: float
    all_g_positive: bool
    noise_threshold_value: float
    inflated_disjoint_sigma: float
    inflated_disjoint_all_ok: bool
    eps_grid_n: int
    arccos_sqrt_ineq_all_ok: bool
    arccos_sqrt_ineq_min_slack: float
    tail_identity_max_abs_error: float
    tail_inequality_exp_all_ok: bool
    tail_inequality_exp_max_slack: float
    kl_support_separation_all_ok: bool
    elapsed_s: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit radial quadratic identifiability claims.")
    parser.add_argument("--r-max", type=int, default=5000, help="Max integer r for gap checks.")
    parser.add_argument("--eps-grid", type=int, default=4000, help="Grid size for epsilon inequality checks.")
    parser.add_argument("--sigma", type=float, default=0.21, help="Test sigma for inflated support disjointness.")
    args = parser.parse_args()

    t0 = time.time()
    mp.mp.dps = 80

    r_max = int(args.r_max)
    if r_max < 5:
        raise ValueError("--r-max must be >= 5")

    # Gap checks.
    g2 = _g_int(2)
    gmin = mp.mpf("1e9")
    argmin = 2
    all_pos = True
    for r in range(2, r_max + 1):
        g = _g_int(r)
        if g <= 0:
            all_pos = False
        if g < gmin:
            gmin = g
            argmin = r

    # Noise threshold: half of global lower bound.
    noise_thr = mp.mpf(31) / mp.mpf(72)

    sigma = mp.mpf(str(args.sigma))
    inflated_ok = True
    if sigma <= 0:
        raise ValueError("--sigma must be positive")
    # Check disjointness for a window of consecutive r.
    for r in range(2, min(r_max, 3000)):
        hi = _I(mp.mpf(r))[1] + sigma
        lo_next = _I(mp.mpf(r + 1))[0] - sigma
        if not (hi < lo_next):
            inflated_ok = False
            break

    # Inequality arccos(1-eps/2) >= sqrt(eps) for eps in (0,2].
    n_grid = int(args.eps_grid)
    if n_grid < 50:
        raise ValueError("--eps-grid must be >= 50")
    arccos_ok = True
    min_slack = mp.mpf("1e9")
    for k in range(1, n_grid + 1):
        eps = mp.mpf(2) * mp.mpf(k) / mp.mpf(n_grid)
        lhs = mp.acos(1 - eps / 2)
        rhs = mp.sqrt(eps)
        slack = lhs - rhs
        if slack < min_slack:
            min_slack = slack
        if slack < -mp.mpf("1e-40"):
            arccos_ok = False
            break

    # Tail identity and exponential inequality checks.
    # Identity: P(c-underline_c_n > eps) = (1 - p_eps)^n where p_eps = acos(1-eps/2)/pi.
    # Inequality: (1-x)^n <= exp(-n x).
    max_abs_err = mp.mpf("0")
    exp_ineq_ok = True
    exp_ineq_max_slack = mp.mpf("0")
    for n in [1, 2, 5, 10, 40, 100]:
        for k in range(1, 200):
            eps = mp.mpf(2) * mp.mpf(k) / mp.mpf(200)
            p = _tail_prob_eps(eps)
            exact = (1 - p) ** n
            # Self-consistency identity (no sampling): compare two equivalent expressions.
            alt = mp.e ** (n * mp.log(1 - p))
            err = abs(exact - alt)
            if err > max_abs_err:
                max_abs_err = err
            bound = mp.e ** (-n * p)
            slack = exact - bound
            if slack > exp_ineq_max_slack:
                exp_ineq_max_slack = slack
            if slack > mp.mpf("1e-60"):
                exp_ineq_ok = False

    # Support separation implies KL divergence is infinite: check disjointness of supports for r!=s.
    kl_ok = True
    for r in range(2, 120):
        Ir = _I(mp.mpf(r))
        for s in range(r + 1, 120):
            Is = _I(mp.mpf(s))
            if not (Ir[1] < Is[0] or Is[1] < Ir[0]):
                kl_ok = False
                break
        if not kl_ok:
            break

    payload = Payload(
        r_max_gap_check=r_max,
        g2_value=float(g2),
        g_min_value=float(gmin),
        g_min_arg_r=int(argmin),
        g_lower_bound_value=float(mp.mpf(31) / mp.mpf(36)),
        all_g_positive=bool(all_pos),
        noise_threshold_value=float(noise_thr),
        inflated_disjoint_sigma=float(sigma),
        inflated_disjoint_all_ok=bool(inflated_ok),
        eps_grid_n=n_grid,
        arccos_sqrt_ineq_all_ok=bool(arccos_ok),
        arccos_sqrt_ineq_min_slack=float(min_slack),
        tail_identity_max_abs_error=float(max_abs_err),
        tail_inequality_exp_all_ok=bool(exp_ineq_ok),
        tail_inequality_exp_max_slack=float(exp_ineq_max_slack),
        kl_support_separation_all_ok=bool(kl_ok),
        elapsed_s=float(time.time() - t0),
    )

    out = export_dir() / "group_jg_radial_quadratic_identifiability_audit.json"
    _write_json(out, asdict(payload))

    if not payload.all_g_positive:
        raise AssertionError("Found non-positive gap g_r in the audit window.")
    # The theorem claims g_r >= 31/36; validate with a small numerical tolerance.
    if payload.g_min_value + 1e-18 < payload.g_lower_bound_value:
        raise AssertionError("Gap lower bound violated in the audit window.")
    if not payload.inflated_disjoint_all_ok and sigma < noise_thr:
        raise AssertionError("Inflated supports overlapped below the stated threshold.")
    if not payload.arccos_sqrt_ineq_all_ok:
        raise AssertionError("arccos lower bound check failed on the epsilon grid.")
    if not payload.tail_inequality_exp_all_ok:
        raise AssertionError("Exponential inequality check failed.")
    if not payload.kl_support_separation_all_ok:
        raise AssertionError("Support separation check failed.")

    print(
        "[group-jg-radial-quadratic-identifiability] "
        f"gmin={payload.g_min_value:.12f} at r={payload.g_min_arg_r} "
        f"sigma_thr={payload.noise_threshold_value:.12f} "
        f"min_slack_arccos_sqrt={payload.arccos_sqrt_ineq_min_slack:.3e}",
        flush=True,
    )


if __name__ == "__main__":
    main()

