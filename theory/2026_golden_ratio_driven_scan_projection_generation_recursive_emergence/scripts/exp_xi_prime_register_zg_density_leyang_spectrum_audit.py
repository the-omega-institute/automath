#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit Zeckendorf-Godel prime-code density and Lee-Yang spectral claims.

The script verifies, in exact/controlled numerical form:
  1) Delta_N closed form and finite-level tail inequality.
  2) Mertens-renormalized growth law for I_N.
  3) Weighted path hard-core polynomial P_N(t):
       - recurrence and coefficient construction,
       - all roots are simple negative reals (finite audit window),
       - consecutive-root interlacing (finite audit window),
       - Poisson-binomial factorization consistency.
  4) Spectral identities with weighted adjacency A_{N+1}:
       P_N(1) = |det(iI - A_{N+1})| = det(I + A_{N+1}^2)^{1/2}.
  5) Lee-Yang unit-circle lift via x = z + z^{-1} and
     Joukowsky transport to an ellipse.

Output:
  - artifacts/export/xi_prime_register_zg_density_leyang_spectrum_audit.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import mpmath as mp
import numpy as np
import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _first_n_primes(n: int) -> List[int]:
    out: List[int] = []
    p = 2
    while len(out) < n:
        if sp.isprime(p):
            out.append(p)
        p += 1
    return out


def _independent_set_sum_exact(primes: Sequence[int], n: int) -> sp.Rational:
    """Exact I_n by explicit sum over independent subsets of {1,...,n}."""
    total = sp.Rational(0)
    for mask in range(1 << n):
        ok = True
        weight = sp.Rational(1)
        for k in range(n):
            if (mask >> k) & 1:
                if k > 0 and ((mask >> (k - 1)) & 1):
                    ok = False
                    break
                weight *= sp.Rational(1, primes[k])
        if ok:
            total += weight
    return total


def _build_partition_recurrences_mp(primes: Sequence[int]) -> Tuple[List[mp.mpf], List[mp.mpf]]:
    """Return I_n (n=0..N) and delta_n (n=1..N) in mp precision."""
    i_vals: List[mp.mpf] = [mp.mpf("1")]
    for idx, p in enumerate(primes, start=1):
        if idx == 1:
            i_vals.append(mp.mpf("1") + mp.mpf(1) / p)
        else:
            i_vals.append(i_vals[idx - 1] + i_vals[idx - 2] / p)

    delta_vals: List[mp.mpf] = []
    euler_prod = mp.mpf("1")
    for idx, p in enumerate(primes, start=1):
        euler_prod *= 1 - mp.mpf(1) / p
        delta_vals.append(euler_prod * i_vals[idx])
    return i_vals, delta_vals


def _build_polynomials_q(primes: Sequence[int], n_max: int) -> Tuple[sp.Symbol, List[sp.Poly]]:
    t = sp.symbols("t")
    polys: List[sp.Poly] = [sp.Poly(1, t, domain=sp.QQ)]
    if n_max >= 1:
        polys.append(sp.Poly(1 + sp.Rational(1, primes[0]) * t, t, domain=sp.QQ))
    for n in range(2, n_max + 1):
        p_n = primes[n - 1]
        expr = polys[n - 1].as_expr() + sp.Rational(1, p_n) * t * polys[n - 2].as_expr()
        polys.append(sp.Poly(expr, t, domain=sp.QQ))
    return t, polys


def _roots_real_negative_simple(poly: sp.Poly) -> Tuple[bool, float, float]:
    roots = sp.nroots(poly.as_expr(), n=120, maxsteps=500)
    reals = sorted(float(sp.re(z)) for z in roots)
    max_im = max(abs(float(sp.im(z))) for z in roots) if roots else 0.0
    min_re = min(reals) if reals else 0.0
    if len(reals) <= 1:
        sep = 1.0
    else:
        sep = min(abs(reals[i + 1] - reals[i]) for i in range(len(reals) - 1))
    ok = bool(max_im < 1e-18 and all(x < 0.0 for x in reals) and sep > 1e-13)
    return ok, max_im, sep


def _interlace(a: Sequence[float], b: Sequence[float], eps: float = 1e-12) -> bool:
    """Strict interlacing for sorted ascending real roots."""
    m = len(a)
    n = len(b)
    if m == 0 or n == 0:
        return True
    if m == n:
        p1 = all(a[i] < b[i] - eps for i in range(m)) and all(
            b[i] < a[i + 1] - eps for i in range(m - 1)
        )
        p2 = all(b[i] < a[i] - eps for i in range(m)) and all(
            a[i] < b[i + 1] - eps for i in range(m - 1)
        )
        return bool(p1 or p2)
    if m == n + 1:
        return all(a[i] < b[i] - eps and b[i] < a[i + 1] - eps for i in range(n))
    if n == m + 1:
        return all(b[i] < a[i] - eps and a[i] < b[i + 1] - eps for i in range(m))
    return False


def _weighted_path_matrix(primes: Sequence[int], n: int) -> np.ndarray:
    """Build A_{n+1} for first n edge-weights w_k = p_k^{-1/2}."""
    m = n + 1
    a = np.zeros((m, m), dtype=float)
    for k in range(1, m):
        w = 1.0 / math.sqrt(float(primes[k - 1]))
        a[k - 1, k] = w
        a[k, k - 1] = w
    return a


@dataclass(frozen=True)
class Payload:
    n_primes_density: int
    delta_reference_n: int
    delta_reference_value: float
    delta_sequence_monotone_decreasing: bool
    recurrence_exact_small_window: bool
    finite_tail_bound_checks: int
    finite_tail_bound_all_ok: bool
    finite_tail_bound_max_slack: float
    positivity_lower_bound_truncated: float
    positivity_lower_bound_positive: bool
    mertens_ratio_n: int
    mertens_ratio_value: float
    mertens_target_constant: float
    mertens_relative_error: float
    lee_yang_root_window_nmax: int
    lee_yang_all_negative_simple: bool
    lee_yang_max_imag: float
    lee_yang_min_root_separation: float
    interlacing_window_nmax: int
    interlacing_all_ok: bool
    poisson_binomial_checks: int
    poisson_binomial_all_ok: bool
    spectral_radius_checks: int
    spectral_radius_all_ok: bool
    determinant_identity_checks: int
    determinant_identity_all_ok: bool
    determinant_identity_max_error: float
    joukowsky_transport_n: int
    joukowsky_max_ellipse_error: float
    elapsed_s: float


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit ZG density formulae and prime-weight Lee-Yang spectral identities."
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    parser.add_argument("--n-density", type=int, default=800, help="Prime cutoff for density recurrences.")
    parser.add_argument("--n-root-window", type=int, default=24, help="Root-audit window for P_N.")
    parser.add_argument("--n-interlace-window", type=int, default=10, help="Interlacing audit window.")
    args = parser.parse_args()

    t0 = time.time()
    mp.mp.dps = 100

    print("[zg-audit] phase=setup", flush=True)
    n_density = int(args.n_density)
    n_root_window = int(args.n_root_window)
    n_interlace_window = int(args.n_interlace_window)
    n_needed = max(n_density, n_root_window + 5, 40)
    primes = _first_n_primes(n_needed)

    print("[zg-audit] phase=density-recurrence", flush=True)
    i_vals_mp, delta_vals_mp = _build_partition_recurrences_mp(primes[:n_density])
    delta_monotone = all(
        delta_vals_mp[k] <= delta_vals_mp[k - 1] + mp.mpf("1e-80") for k in range(1, len(delta_vals_mp))
    )
    delta_ref = delta_vals_mp[-1]

    # Exact small-window verification of I_N via explicit independent-subset enumeration.
    recurrence_exact_ok = True
    for n in range(1, 11):
        i_enum = _independent_set_sum_exact(primes, n)
        if n == 1:
            i_rec = sp.Rational(1) + sp.Rational(1, primes[0])
        else:
            i0 = sp.Rational(1)
            i1 = sp.Rational(1) + sp.Rational(1, primes[0])
            for m in range(2, n + 1):
                i0, i1 = i1, i1 + sp.Rational(1, primes[m - 1]) * i0
            i_rec = i1
        if sp.simplify(i_enum - i_rec) != 0:
            recurrence_exact_ok = False
            break

    print("[zg-audit] phase=tail-bounds", flush=True)
    tail_ns = [10, 20, 40, 80, 120, 200, 300, 500]
    tail_ns = [n for n in tail_ns if n < n_density]
    finite_tail_ok = True
    finite_tail_max_slack = 0.0
    for n in tail_ns:
        err = delta_vals_mp[n - 1] - delta_ref
        ub1 = mp.fsum(mp.mpf(1) / (primes[j - 1] ** 2) for j in range(n + 1, n_density + 1))
        ub2 = mp.fsum(mp.mpf(1) / (primes[j - 1] * primes[j]) for j in range(n, n_density))
        ub = ub1 + ub2
        if err < -mp.mpf("1e-50") or err > ub + mp.mpf("1e-50"):
            finite_tail_ok = False
        slack = float(ub - err)
        if slack > finite_tail_max_slack:
            finite_tail_max_slack = slack

    # Positivity lower bound: truncated sums + integral tail majorant.
    p_last = primes[n_density - 1]
    s1 = mp.fsum(mp.mpf(1) / (p * p) for p in primes[:n_density])
    s2 = mp.fsum(mp.mpf(1) / (primes[k] * primes[k + 1]) for k in range(n_density - 1))
    positivity_lb = 1 - (s1 + mp.mpf(1) / p_last) - (s2 + mp.mpf(1) / p_last)
    positivity_ok = positivity_lb > 0

    print("[zg-audit] phase=mertens-renormalization", flush=True)
    n_mertens = n_density
    mertens_ratio = i_vals_mp[n_mertens] / mp.log(primes[n_mertens - 1])
    mertens_target = delta_ref * mp.e ** mp.euler
    mertens_rel_err = abs(mertens_ratio - mertens_target) / abs(mertens_target)

    print("[zg-audit] phase=polynomial-root-audit", flush=True)
    t_sym, polys = _build_polynomials_q(primes, n_root_window)
    roots_ok = True
    max_imag = 0.0
    min_sep = float("inf")
    for n in range(1, n_root_window + 1):
        ok_n, imag_n, sep_n = _roots_real_negative_simple(polys[n])
        roots_ok = roots_ok and ok_n
        max_imag = max(max_imag, imag_n)
        min_sep = min(min_sep, sep_n)

    print("[zg-audit] phase=interlacing-window", flush=True)
    interlacing_ok = True
    for n in range(2, n_interlace_window + 1):
        r_n = sorted(float(sp.re(z)) for z in sp.nroots(polys[n].as_expr(), n=120, maxsteps=500))
        r_nm1 = sorted(float(sp.re(z)) for z in sp.nroots(polys[n - 1].as_expr(), n=120, maxsteps=500))
        if not _interlace(r_n, r_nm1, eps=1e-12):
            interlacing_ok = False
            break

    print("[zg-audit] phase=poisson-binomial-factorization", flush=True)
    poisson_ok = True
    poisson_checks = 0
    test_t_values = [0.2, 1.0, 2.5]
    for n in [6, 10, 14, 18, n_root_window]:
        if n > n_root_window:
            continue
        roots = sorted(sp.nroots(polys[n].as_expr(), n=120, maxsteps=500), key=lambda z: float(sp.re(z)))
        alphas = [-float(sp.re(z)) for z in roots]
        if not all(a > 0 for a in alphas):
            poisson_ok = False
            continue
        for tv in test_t_values:
            lhs = float(polys[n].eval(t_sym, tv))
            rhs = 1.0
            for a in alphas:
                rhs *= 1.0 + tv / a
            if abs(lhs - rhs) > 5e-8:
                poisson_ok = False
            poisson_checks += 1

    print("[zg-audit] phase=spectral-determinant-identity", flush=True)
    spectral_ns = [8, 12, 16, 20, 24, 30]
    spectral_ns = [n for n in spectral_ns if n < n_density]
    spectral_ok = True
    det_ok = True
    det_max_err = 0.0
    sqrt2 = math.sqrt(2.0)
    for n in spectral_ns:
        a = _weighted_path_matrix(primes, n)
        eig = np.linalg.eigvalsh(a)
        if float(np.max(np.abs(eig))) > sqrt2 + 1e-12:
            spectral_ok = False

        p_n1 = float(i_vals_mp[n])  # P_N(1) = I_N
        d1 = abs(np.linalg.det(1j * np.eye(n + 1) - a))
        d2 = math.sqrt(float(np.linalg.det(np.eye(n + 1) + a @ a)))
        err = max(abs(p_n1 - d1), abs(p_n1 - d2), abs(d1 - d2))
        det_max_err = max(det_max_err, err)
        if err > 1e-8:
            det_ok = False

    print("[zg-audit] phase=joukowsky-transport", flush=True)
    n_jouk = min(24, n_density - 1)
    a_mat = _weighted_path_matrix(primes, n_jouk)
    eig = np.linalg.eigvalsh(a_mat)
    r = 1.3
    semi_a = r + 1.0 / r
    semi_b = abs(r - 1.0 / r)
    max_ellipse_err = 0.0
    for lam in eig:
        x = sqrt2 * float(lam)
        if abs(x) > 2.0:
            spectral_ok = False
            continue
        theta = math.acos(max(-1.0, min(1.0, x / 2.0)))
        z = complex(math.cos(theta), math.sin(theta))
        w = r * z + (1.0 / r) / z
        ellipse_err = abs((w.real * w.real) / (semi_a * semi_a) + (w.imag * w.imag) / (semi_b * semi_b) - 1.0)
        max_ellipse_err = max(max_ellipse_err, ellipse_err)

    payload = Payload(
        n_primes_density=n_density,
        delta_reference_n=n_density,
        delta_reference_value=float(delta_ref),
        delta_sequence_monotone_decreasing=bool(delta_monotone),
        recurrence_exact_small_window=bool(recurrence_exact_ok),
        finite_tail_bound_checks=len(tail_ns),
        finite_tail_bound_all_ok=bool(finite_tail_ok),
        finite_tail_bound_max_slack=float(finite_tail_max_slack),
        positivity_lower_bound_truncated=float(positivity_lb),
        positivity_lower_bound_positive=bool(positivity_ok),
        mertens_ratio_n=n_mertens,
        mertens_ratio_value=float(mertens_ratio),
        mertens_target_constant=float(mertens_target),
        mertens_relative_error=float(mertens_rel_err),
        lee_yang_root_window_nmax=n_root_window,
        lee_yang_all_negative_simple=bool(roots_ok),
        lee_yang_max_imag=float(max_imag),
        lee_yang_min_root_separation=float(min_sep if math.isfinite(min_sep) else 0.0),
        interlacing_window_nmax=n_interlace_window,
        interlacing_all_ok=bool(interlacing_ok),
        poisson_binomial_checks=poisson_checks,
        poisson_binomial_all_ok=bool(poisson_ok),
        spectral_radius_checks=len(spectral_ns),
        spectral_radius_all_ok=bool(spectral_ok),
        determinant_identity_checks=len(spectral_ns),
        determinant_identity_all_ok=bool(det_ok),
        determinant_identity_max_error=float(det_max_err),
        joukowsky_transport_n=n_jouk,
        joukowsky_max_ellipse_error=float(max_ellipse_err),
        elapsed_s=float(time.time() - t0),
    )

    if not payload.delta_sequence_monotone_decreasing:
        raise AssertionError("delta_N is not monotone nonincreasing in the audit window")
    if not payload.recurrence_exact_small_window:
        raise AssertionError("exact recurrence/enumeration identity failed")
    if not payload.finite_tail_bound_all_ok:
        raise AssertionError("finite tail bound checks failed")
    if not payload.positivity_lower_bound_positive:
        raise AssertionError("truncated positivity lower bound is nonpositive")
    if payload.mertens_relative_error > 0.03:
        raise AssertionError(
            f"Mertens renormalization relative error too large: {payload.mertens_relative_error:.6f}"
        )
    if not payload.lee_yang_all_negative_simple:
        raise AssertionError("Lee-Yang finite-window root negativity/simplicity check failed")
    if not payload.interlacing_all_ok:
        raise AssertionError("finite-window interlacing check failed")
    if not payload.poisson_binomial_all_ok:
        raise AssertionError("Poisson-binomial factorization numerical checks failed")
    if not payload.spectral_radius_all_ok:
        raise AssertionError("spectral radius bound check failed")
    if not payload.determinant_identity_all_ok:
        raise AssertionError("determinant identity check failed")
    if payload.joukowsky_max_ellipse_error > 1e-10:
        raise AssertionError("Joukowsky transport ellipse equation check failed")

    if not args.no_output:
        out = export_dir() / "xi_prime_register_zg_density_leyang_spectrum_audit.json"
        _write_json(out, asdict(payload))

    print(
        "[xi-prime-register-zg-density-leyang-spectrum] "
        f"delta_ref={payload.delta_reference_value:.12f} "
        f"tail_ok={payload.finite_tail_bound_all_ok} "
        f"roots_ok={payload.lee_yang_all_negative_simple} "
        f"interlace_ok={payload.interlacing_all_ok} "
        f"det_ok={payload.determinant_identity_all_ok} "
        f"elapsed_s={payload.elapsed_s:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()
