#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the explicit Chebyshev conjugacy for the Lee–Yang compression rational map a(y).

This script is English-only by repository convention.

We verify symbolically (over Q(sqrt(7))):
  - The closed-form derivative of a(y) and its critical points/values.
  - The identities
        a(y)-2 = 27 y(y-1)/(8 A(y)^3),
        a(y)+2 = P_LY(y)/(8 A(y)^3).
  - The explicit PGL2-conjugacy
        N(a(y)) = T3(M(y)),   where T3(s)=s^3-3s,
    with the fully explicit transforms M, N and M^{-1}.
  - The odd-normalization equivalent identity
        nu(a(y)) = T3(mu(y)),
        mu(y)=sqrt(7)(5-8y)/(7(2y+1)),
        nu(u)=sqrt(7)(288u-556)/49.
  - The discriminant factorization for the cubic inverse-image equation
        F_t(y) := Q(y) - 8 t A(y)^3,
    namely Disc_y(F_t) = -3^9 (2304 t^2 - 8896 t + 8549).
  - The Lee–Yang-root transport cubic in Chebyshev coordinate s:
        49 s^3 - 147 s + 1132 sqrt(7) = 0.
  - The square-descent generator resultant
        Res_y(P_LY(y), (5-8y)^2 - T(2y+1)^2)
        = 26244 (T^3 - 42T^2 + 441T - 1281424),
    together with its discriminant and index relation against Disc(K)=-999.

Outputs:
  - artifacts/export/fold_zm_leyang_compression_chebyshev_conjugacy_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class Payload:
    a_shift_identities_ok: bool
    derivative_ok: bool
    critical_values_ok: bool
    conjugacy_ok: bool
    odd_normalization_ok: bool
    minv_ok: bool
    discriminant_ok: bool
    nt_square_minus_4_ok: bool
    ply_root_transport_ok: bool
    square_descent_resultant_ok: bool
    square_descent_disc_ok: bool
    square_descent_index_ok: bool
    square_descent_index: int


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit Lee–Yang compression Chebyshev conjugacy and reduced discriminant."
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-leyang-compression-chebyshev] start", flush=True)

    y, t, s, u = sp.symbols("y t s u")
    sqrt7 = sp.sqrt(7)

    A = 1 + 2 * y
    Q = 16 + 69 * y + 219 * y**2 + 128 * y**3
    a = sp.simplify(Q / (8 * A**3))
    ply = 256 * y**3 + 411 * y**2 + 165 * y + 32

    a_shift_identities_ok = bool(
        sp.simplify(a - 2 - 27 * y * (y - 1) / (8 * A**3)) == 0
        and sp.simplify(a + 2 - ply / (8 * A**3)) == 0
    )
    if not a_shift_identities_ok:
        raise RuntimeError("Shift identities for a(y) with P_LY failed.")

    # --- derivative / critical values ---
    da = sp.simplify(sp.diff(a, y))
    da_expected = -sp.Rational(27, 8) * (2 * y**2 - 6 * y + 1) / (2 * y + 1) ** 4
    derivative_ok = bool(sp.simplify(da - da_expected) == 0)
    if not derivative_ok:
        raise RuntimeError(f"Unexpected derivative: got {da}, expected {da_expected}")

    y_plus = sp.simplify((3 + sqrt7) / 2)
    y_minus = sp.simplify((3 - sqrt7) / 2)
    a_plus = sp.simplify(a.subs(y, y_plus))
    a_minus = sp.simplify(a.subs(y, y_minus))
    a_plus_expected = sp.Rational(139, 72) + sp.Rational(7, 144) * sqrt7
    a_minus_expected = sp.Rational(139, 72) - sp.Rational(7, 144) * sqrt7
    critical_values_ok = bool(
        sp.simplify(a_plus - a_plus_expected) == 0 and sp.simplify(a_minus - a_minus_expected) == 0
    )
    if not critical_values_ok:
        raise RuntimeError(
            f"Unexpected critical values: a_plus={a_plus}, a_minus={a_minus},"
            f" expected {a_plus_expected}, {a_minus_expected}"
        )

    # --- explicit PGL2 conjugacy ---
    M = sp.simplify(sqrt7 * (8 * y - 5) / (7 * (2 * y + 1)))
    N_u = sp.simplify(sqrt7 * (556 - 288 * u) / 49)
    T3 = lambda z: z**3 - 3 * z
    conjugacy_ok = bool(sp.simplify(N_u.subs(u, a) - T3(M)) == 0)
    if not conjugacy_ok:
        raise RuntimeError("Conjugacy identity failed: N(a(y)) != T3(M(y)).")

    mu = sp.simplify(sqrt7 * (5 - 8 * y) / (7 * (2 * y + 1)))
    nu_u = sp.simplify(sqrt7 * (288 * u - 556) / 49)
    odd_normalization_ok = bool(sp.simplify(nu_u.subs(u, a) - T3(mu)) == 0)
    if not odd_normalization_ok:
        raise RuntimeError("Odd-normalization conjugacy failed: nu(a(y)) != T3(mu(y)).")

    Minv = sp.simplify((-7 * s - 5 * sqrt7) / (2 * (7 * s - 4 * sqrt7)))
    minv_ok = bool(sp.simplify(M.subs(y, Minv) - s) == 0)
    if not minv_ok:
        raise RuntimeError("Inverse check failed: M(M^{-1}(s)) != s.")

    # --- reduced discriminant for F_t(y) ---
    F = sp.expand(Q - 8 * t * A**3)
    polyF = sp.Poly(F, y)
    disc = sp.factor(sp.discriminant(polyF.as_expr(), y))
    disc_expected = -3**9 * (2304 * t**2 - 8896 * t + 8549)
    discriminant_ok = bool(sp.simplify(disc - disc_expected) == 0)
    if not discriminant_ok:
        raise RuntimeError(
            f"Unexpected Disc_y(F_t): got {disc}, expected {disc_expected}"
        )

    # --- N(t)^2 - 4 identity used in the discriminant reduction ---
    N_t = sp.simplify(N_u.subs(u, t))
    nt_square_minus_4_ok = bool(
        sp.simplify(
            N_t**2
            - 4
            - sp.Rational(36, 343) * (2304 * t**2 - 8896 * t + 8549)
        )
        == 0
    )
    if not nt_square_minus_4_ok:
        raise RuntimeError("Identity failed: N(t)^2 - 4 is not the expected scalar multiple.")

    # --- Lee–Yang root transport to Chebyshev coordinate ---
    beta, s_var, T_var = sp.symbols("beta s T")
    ply_beta = 256 * beta**3 + 411 * beta**2 + 165 * beta + 32
    mu_beta = sp.simplify(sqrt7 * (5 - 8 * beta) / (7 * (2 * beta + 1)))
    rel_mu_num = sp.together(s_var - mu_beta).as_numer_denom()[0]
    res_s = sp.expand(sp.resultant(ply_beta, rel_mu_num, beta))
    target_s = sp.expand(49 * s_var**3 - 147 * s_var + 1132 * sqrt7)
    q_s, r_s = (
        sp.Poly(res_s, s_var, extension=[sqrt7]).div(
            sp.Poly(target_s, s_var, extension=[sqrt7])
        )
    )
    ply_root_transport_ok = bool(r_s.as_expr() == 0 and q_s.degree() == 0)
    if not ply_root_transport_ok:
        raise RuntimeError(
            "Lee–Yang root transport cubic failed: resultant is not proportional to target cubic."
        )

    # --- square-descent monic generator and arithmetic audit ---
    rel_T_num = (5 - 8 * beta) ** 2 - T_var * (2 * beta + 1) ** 2
    res_T = sp.expand(sp.resultant(ply_beta, rel_T_num, beta))
    F_T = T_var**3 - 42 * T_var**2 + 441 * T_var - 1281424
    q_T, r_T = sp.Poly(res_T, T_var).div(sp.Poly(F_T, T_var))
    square_descent_resultant_ok = bool(r_T.as_expr() == 0 and q_T.degree() == 0)
    if not square_descent_resultant_ok:
        raise RuntimeError("Square-descent resultant failed for F(T).")

    disc_FT = int(sp.discriminant(F_T, T_var))
    disc_FT_expected = -(2**6) * (3**5) * (31**2) * 37 * (283**2)
    square_descent_disc_ok = bool(disc_FT == disc_FT_expected)
    if not square_descent_disc_ok:
        raise RuntimeError(
            f"Unexpected Disc(F): got {disc_FT}, expected {disc_FT_expected}"
        )

    disc_K = -999
    idx_sq = abs(disc_FT // disc_K)
    idx_val, idx_is_square = sp.integer_nthroot(idx_sq, 2)
    idx_expected = 2**3 * 3 * 31 * 283
    square_descent_index_ok = bool(idx_is_square and idx_val == idx_expected)
    if not square_descent_index_ok:
        raise RuntimeError(
            f"Unexpected index from discriminant ratio: got {idx_val}, expected {idx_expected}"
        )

    payload = Payload(
        a_shift_identities_ok=a_shift_identities_ok,
        derivative_ok=derivative_ok,
        critical_values_ok=critical_values_ok,
        conjugacy_ok=conjugacy_ok,
        odd_normalization_ok=odd_normalization_ok,
        minv_ok=minv_ok,
        discriminant_ok=discriminant_ok,
        nt_square_minus_4_ok=nt_square_minus_4_ok,
        ply_root_transport_ok=ply_root_transport_ok,
        square_descent_resultant_ok=square_descent_resultant_ok,
        square_descent_disc_ok=square_descent_disc_ok,
        square_descent_index_ok=square_descent_index_ok,
        square_descent_index=int(idx_val),
    )

    if not args.no_output:
        json_path = export_dir() / "fold_zm_leyang_compression_chebyshev_conjugacy_audit.json"
        _write_json(json_path, asdict(payload))

    dt = time.time() - t0
    print(f"[fold-zm-leyang-compression-chebyshev] ok elapsed_s={dt:.3f}", flush=True)


if __name__ == "__main__":
    main()

