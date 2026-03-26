#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit frozen escort concentration, Mellin capacity identities, and core/full twists.

This script provides a deterministic audit for:
1. The finite-level escort concentration bound on the maximal-fiber layer.
2. The exact Mellin--Stieltjes identities linking moments, tail counts, and
   continuous capacity.
3. The equality rho_full = max(1, rho_core) for nontrivial root-of-unity twists
   in the real-input 40-state kernel.
"""

from __future__ import annotations

import json
import math
from collections import Counter
from typing import Dict, List, Sequence, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir
from common_phi_fold import fold_m, is_golden_legal


def _sp_str(expr: sp.Expr) -> str:
    return str(sp.simplify(expr))


def _mp_str(x: mp.mpf | mp.mpc, nd: int = 18) -> str:
    if isinstance(x, mp.mpc):
        sign = "+" if x.imag >= 0 else ""
        return f"{mp.nstr(x.real, nd)}{sign}{mp.nstr(x.imag, nd)}j"
    return mp.nstr(x, nd)


def _int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def _bits_to_key(bits: Sequence[int]) -> str:
    return "".join("1" if b else "0" for b in bits)


def _fiber_histogram(m: int) -> Dict[int, int]:
    fibers: Dict[str, int] = {}
    for idx in range(1 << m):
        micro = _int_to_bits(idx, m)
        x_bits = fold_m(micro)
        if not is_golden_legal(x_bits):
            raise RuntimeError("Fold_m produced an illegal golden word.")
        key = _bits_to_key(x_bits)
        fibers[key] = fibers.get(key, 0) + 1
    return dict(sorted(Counter(fibers.values()).items()))


def _tail_mellin_from_hist(hist: Dict[int, int], a: sp.Rational) -> Tuple[sp.Expr, sp.Expr, sp.Expr]:
    levels = sorted(hist)
    S_a = sum(sp.Integer(hist[d]) * sp.Integer(d) ** a for d in levels)

    tail_formula = sp.Integer(0)
    gap_formula = sp.Integer(0)
    prev = sp.Integer(0)

    for d in levels:
        d_sp = sp.Integer(d)
        tail_count = sum(hist[t] for t in levels if t >= d)
        tail_weight = sum(hist[t] * t for t in levels if t >= d)

        tail_formula += sp.Integer(tail_count) * (d_sp**a - prev**a)

        piece = (
            sp.Integer(tail_weight) / (a - 1) * (d_sp ** (a - 1) - prev ** (a - 1))
            - sp.Integer(tail_count) / a * (d_sp**a - prev**a)
        )
        gap_formula += a * (a - 1) * piece
        prev = d_sp

    return sp.simplify(S_a), sp.simplify(tail_formula), sp.simplify(gap_formula)


def _freeze_capacity_audit() -> Dict[str, object]:
    ms = [8, 10, 12, 14]
    escort_a = 6
    mellin_a = sp.Rational(5, 2)

    rows: List[Dict[str, object]] = []
    for m in ms:
        hist = _fiber_histogram(m)
        levels = sorted(hist)
        X = sum(hist.values())
        M = max(levels)
        K = hist[M]
        M2 = max([d for d in levels if d < M], default=1)

        total_micro = sum(d * hist[d] for d in levels)
        if total_micro != 1 << m:
            raise RuntimeError(f"Multiplicity sum mismatch at m={m}.")

        S_escort = mp.mpf("0")
        numer_max = mp.mpf("0")
        for d, count in hist.items():
            term = mp.mpf(count) * (mp.mpf(d) ** escort_a)
            S_escort += term
            if d == M:
                numer_max += term
        mass_max = numer_max / S_escort
        outside_mass = 1 - mass_max
        sharp_bound = mp.mpf(X - K) / mp.mpf(K) * (mp.mpf(M2) / mp.mpf(M)) ** escort_a
        simple_bound = mp.mpf(X) / mp.mpf(K) * (mp.mpf(M2) / mp.mpf(M)) ** escort_a

        S_a, tail_formula, gap_formula = _tail_mellin_from_hist(hist, mellin_a)

        alpha_m = mp.log(M) / m
        g_m = mp.log(K) / m
        x_m = mp.log(X) / m
        pressure_samples: List[Dict[str, object]] = []
        for a in [2, 4, 8]:
            S_int = mp.mpf(sum(hist[d] * (d**a) for d in levels))
            P_a = mp.log(S_int) / m
            pressure_samples.append(
                {
                    "a": a,
                    "P_a_over_m": _mp_str(P_a, 16),
                    "slope_proxy": _mp_str(P_a / a, 16),
                    "intercept_proxy": _mp_str(P_a - a * alpha_m, 16),
                    "alpha_m_plus_g_m_over_a": _mp_str(alpha_m + g_m / a, 16),
                    "alpha_m_plus_logX_over_a": _mp_str(alpha_m + x_m / a, 16),
                }
            )

        rows.append(
            {
                "m": m,
                "histogram": {str(k): int(v) for k, v in hist.items()},
                "X_m": X,
                "M_m": M,
                "K_m": K,
                "M_m_second": M2,
                "escort_a": escort_a,
                "escort_mass_max_layer": _mp_str(mass_max, 16),
                "escort_outside_mass": _mp_str(outside_mass, 16),
                "escort_sharp_bound": _mp_str(sharp_bound, 16),
                "escort_simple_bound": _mp_str(simple_bound, 16),
                "mellin_a": _sp_str(mellin_a),
                "moment_value": _sp_str(S_a),
                "tail_mellin_value": _sp_str(tail_formula),
                "capacity_gap_mellin_value": _sp_str(gap_formula),
                "tail_mellin_match": bool(sp.simplify(S_a - tail_formula) == 0),
                "capacity_gap_mellin_match": bool(sp.simplify(S_a - gap_formula) == 0),
                "pressure_samples": pressure_samples,
            }
        )

    return {"rows": rows}


def _delta_and_core_sympy() -> Tuple[sp.Symbol, sp.Symbol, sp.Expr, sp.Expr]:
    z, u = sp.symbols("z u")
    F = (
        sp.Integer(1)
        - z
        - 6 * u * z**2
        + 2 * u * z**3
        + (9 * u**2 - u) * z**4
        + (u - 3 * u**2) * z**5
        - (u**3 + 2 * u**2) * z**6
        + (4 * u**3 - 3 * u**2) * z**7
        + (u**3 - u**4) * z**8
    )
    Delta = sp.expand((1 - u * z**2) * F)
    return z, u, Delta, sp.expand(F)


def _roots_as_mpmath(poly: sp.Poly, dps: int) -> List[mp.mpc]:
    roots_sp = poly.nroots(n=dps, maxsteps=300)
    out: List[mp.mpc] = []
    for r in roots_sp:
        re = sp.N(sp.re(r), dps)
        im = sp.N(sp.im(r), dps)
        out.append(mp.mpc(mp.mpf(str(re)), mp.mpf(str(im))))
    return out


def _core_twist_audit() -> Dict[str, object]:
    mp.mp.dps = 80
    z, u, Delta, F = _delta_and_core_sympy()
    phi = (1 + mp.sqrt(5)) / 2
    lam = phi**2
    loglam = mp.log(lam)

    moduli = [2, 3, 4, 5, 6, 10]
    rows: List[Dict[str, object]] = []
    max_rho_error = mp.mpf("0")
    max_theta_error = mp.mpf("0")
    barrier_full: List[int] = []
    barrier_core: List[int] = []

    for m in moduli:
        theta_full_max = mp.ninf
        theta_core_max = mp.ninf
        row_entries: List[Dict[str, object]] = []

        for j in range(1, m):
            u0 = sp.exp(2 * sp.pi * sp.I * sp.Rational(j, m))

            full_poly = sp.Poly(Delta.subs(u, u0), z)
            core_poly = sp.Poly(F.subs(u, u0), z)
            full_roots = _roots_as_mpmath(full_poly, mp.mp.dps)
            core_roots = _roots_as_mpmath(core_poly, mp.mp.dps)

            rho_full = 1 / min(abs(root) for root in full_roots)
            rho_core = 1 / min(abs(root) for root in core_roots)
            rho_rhs = max(mp.mpf("1"), rho_core)

            theta_full = mp.log(rho_full) / loglam
            theta_core = mp.log(rho_core) / loglam
            theta_rhs = max(mp.mpf("0"), theta_core)

            rho_error = abs(rho_full - rho_rhs)
            theta_error = abs(theta_full - theta_rhs)
            max_rho_error = max(max_rho_error, rho_error)
            max_theta_error = max(max_theta_error, theta_error)

            theta_full_max = max(theta_full_max, theta_full)
            theta_core_max = max(theta_core_max, theta_core)

            row_entries.append(
                {
                    "j": j,
                    "rho_full": _mp_str(rho_full, 18),
                    "rho_core": _mp_str(rho_core, 18),
                    "rho_rhs_max_1_core": _mp_str(rho_rhs, 18),
                    "rho_error": _mp_str(rho_error, 8),
                    "theta_full": _mp_str(theta_full, 18),
                    "theta_core": _mp_str(theta_core, 18),
                    "theta_rhs_max_0_core": _mp_str(theta_rhs, 18),
                    "theta_error": _mp_str(theta_error, 8),
                    "sqrt_barrier_full": bool(theta_full > mp.mpf("0.5")),
                    "sqrt_barrier_core": bool(theta_core > mp.mpf("0.5")),
                }
            )

        if theta_full_max > mp.mpf("0.5"):
            barrier_full.append(m)
        if theta_core_max > mp.mpf("0.5"):
            barrier_core.append(m)

        rows.append(
            {
                "m": m,
                "theta_full_max": _mp_str(theta_full_max, 18),
                "theta_core_max": _mp_str(theta_core_max, 18),
                "entries": row_entries,
            }
        )

    return {
        "lambda": _mp_str(lam, 18),
        "rows": rows,
        "max_rho_error": _mp_str(max_rho_error, 8),
        "max_theta_error": _mp_str(max_theta_error, 8),
        "sqrt_barrier_full_moduli": barrier_full,
        "sqrt_barrier_core_moduli": barrier_core,
        "sqrt_barrier_sets_match": barrier_full == barrier_core,
    }


def main() -> None:
    payload = {
        "freeze_capacity_audit": _freeze_capacity_audit(),
        "core_twist_audit": _core_twist_audit(),
    }
    out_path = export_dir() / "xi_freezing_capacity_core_twist_audit.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[write] {out_path}")


if __name__ == "__main__":
    main()
