#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit q-expansion anchoring for the elliptic modular interface (37a1 / X0^+(37)).

This script is English-only by repository convention.

We work on the minimal integral model
    E0:  eta^2 + eta = x^3 - x,
and the weight function used in the paper's elliptic normalization
    y = eta + x^2.

We compute:
  - the Hecke/newform coefficients a_n (up to q_max) from the elliptic curve via
    point counts and multiplicativity (offline, no web dependency),
  - the truncated modular q-expansion of y(tau) at the cusp (q = e^{2π i τ}),
    using a formal-group logarithm/exponential computation,
  - the truncated newform expansion f(q) = sum_{n>=1} a_n q^n.

Outputs (default):
  - artifacts/export/fold_zm_elliptic_modular_y_qexp_audit.json
  - sections/generated/eq_fold_zm_elliptic_modular_y_qexp_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


# ----------------------------
# Power/Laurent series helpers
# ----------------------------

Series = Dict[int, Fraction]  # exp -> coeff


def _add(a: Series, b: Series, *, sign: int = 1) -> Series:
    out: Series = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, Fraction(0)) + sign * c
        if out[e] == 0:
            del out[e]
    return out


def _scale(a: Series, s: Fraction) -> Series:
    if s == 0:
        return {}
    return {e: c * s for e, c in a.items() if c * s != 0}


def _shift(a: Series, k: int) -> Series:
    return {e + k: c for e, c in a.items()}


def _trunc(a: Series, e_min: int, e_max: int) -> Series:
    return {e: c for e, c in a.items() if e_min <= e <= e_max and c != 0}


def _mul(a: Series, b: Series, e_min: int, e_max: int) -> Series:
    out: Series = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = ea + eb
            if e < e_min or e > e_max:
                continue
            out[e] = out.get(e, Fraction(0)) + ca * cb
    return {e: c for e, c in out.items() if c != 0}


def _pow_int(a: Series, n: int, e_min: int, e_max: int) -> Series:
    if n < 0:
        raise ValueError("negative exponent not supported here")
    if n == 0:
        return {0: Fraction(1)}
    r: Series = {0: Fraction(1)}
    x: Series = dict(a)
    k = n
    while k > 0:
        if k & 1:
            r = _mul(r, x, e_min, e_max)
        k //= 2
        if k:
            x = _mul(x, x, e_min, e_max)
    return r


def _deriv(a: Series, e_min: int, e_max: int) -> Series:
    out: Series = {}
    for e, c in a.items():
        if e == 0:
            continue
        ne = e - 1
        if e_min <= ne <= e_max:
            out[ne] = out.get(ne, Fraction(0)) + c * e
    return {e: c for e, c in out.items() if c != 0}


def _inv_power_series(a: Series, max_deg: int) -> Series:
    """Invert a power series with nonzero constant term (degrees 0..max_deg)."""
    a0 = a.get(0, Fraction(0))
    if a0 == 0:
        raise ValueError("non-invertible power series: constant term is 0")
    inv: Series = {0: Fraction(1) / a0}
    for n in range(1, max_deg + 1):
        s = Fraction(0)
        for i in range(1, n + 1):
            s += a.get(i, Fraction(0)) * inv.get(n - i, Fraction(0))
        inv[n] = -s / a0
        if inv[n] == 0:
            del inv[n]
    return inv


def _compose_power_series(A: Series, B: Series, max_deg: int) -> Series:
    """Compose power series A(t) with B(u): A(B(u)) mod u^{max_deg+1}.

    Assumes A has degrees >= 1 (no constant term required, but allowed) and B has no constant term.
    """
    out: Series = {}
    if not A:
        return out
    max_k = max(A.keys())
    B1 = _trunc(B, 0, max_deg)
    Bpow: Dict[int, Series] = {0: {0: Fraction(1)}, 1: B1}
    for k in range(2, max_k + 1):
        Bpow[k] = _mul(Bpow[k - 1], B1, 0, max_deg)
    for k, ak in A.items():
        if k == 0:
            out[0] = out.get(0, Fraction(0)) + ak
            continue
        pk = Bpow.get(k)
        if not pk:
            continue
        for e, c in pk.items():
            if e <= max_deg:
                out[e] = out.get(e, Fraction(0)) + ak * c
    return {e: c for e, c in out.items() if c != 0 and 0 <= e <= max_deg}


# ----------------------------
# Elliptic curve a_n coefficients (offline)
# ----------------------------


def _legendre_symbol(a: int, p: int) -> int:
    a %= p
    if a == 0:
        return 0
    x = pow(a, (p - 1) // 2, p)
    return -1 if x == p - 1 else 1


def _a_p_good_or_2(p: int) -> int:
    """Compute a_p = p+1-#E(F_p) for E0: eta^2+eta=x^3-x (p prime).

    For p=2 we brute force; for odd primes we use the quadratic discriminant count.
    """
    if p == 2:
        pts = 1
        for x in range(p):
            for y in range(p):
                if (y * y + y - (x * x * x - x)) % p == 0:
                    pts += 1
        return p + 1 - pts

    pts = 1  # point at infinity
    for x in range(p):
        rhs = (x * x * x - x) % p
        disc = (1 + 4 * rhs) % p
        pts += 1 + _legendre_symbol(disc, p)
    return p + 1 - pts


def _primes_upto(n: int) -> List[int]:
    ps: List[int] = []
    for k in range(2, n + 1):
        ok = True
        for p in ps:
            if p * p > k:
                break
            if k % p == 0:
                ok = False
                break
        if ok:
            ps.append(k)
    return ps


def compute_a_list(N: int) -> List[int]:
    """Return a_n for 0<=n<=N (a_0 unused, a_1=1) for E0: eta^2+eta=x^3-x."""
    if N < 1:
        raise ValueError("N must be >= 1")

    ps = _primes_upto(N)
    ap: Dict[int, int] = {}
    for p in ps:
        if p == 37:
            # 37a1 has nonsplit multiplicative reduction at 37, hence a_37 = -1.
            ap[p] = -1
        else:
            ap[p] = _a_p_good_or_2(p)

    # Cache for prime powers.
    apow: Dict[Tuple[int, int], int] = {(p, 0): 1 for p in ps}
    for p in ps:
        apow[(p, 1)] = ap[p]

    def a_prime_power(p: int, e: int) -> int:
        if (p, e) in apow:
            return apow[(p, e)]
        if p == 37:
            v = ap[p] ** e
        else:
            v = ap[p] * a_prime_power(p, e - 1) - p * a_prime_power(p, e - 2)
        apow[(p, e)] = v
        return v

    a = [0] * (N + 1)
    a[1] = 1
    for n in range(2, N + 1):
        m = n
        res = 1
        for p in ps:
            if p * p > m:
                break
            if m % p == 0:
                e = 0
                while m % p == 0:
                    m //= p
                    e += 1
                res *= a_prime_power(p, e)
        if m > 1:
            res *= a_prime_power(m, 1)
        a[n] = res
    return a


# ----------------------------
# Formal group computation for q-expansions
# ----------------------------


def compute_x_of_t(max_exp: int) -> Series:
    """Compute x(t) as a Laurent series for the local parameter t=-x/eta at O.

    We solve the identity induced by eta = -x/t and eta^2 + eta = x^3 - x.
    """
    x: Series = {-2: Fraction(1)}
    for m in range(-1, max_exp + 1):
        e_target = m - 2

        def E_coeff(u: Fraction) -> Fraction:
            xt: Series = dict(x)
            if u != 0:
                xt[m] = u
            else:
                xt.pop(m, None)

            e_min = -10
            x2 = _mul(xt, xt, e_min, e_target)
            term1 = x2
            term2 = _shift(xt, 1)  # x*t
            x3 = _mul(x2, xt, e_min, e_target - 2)
            term3 = _shift(x3, 2)  # x^3 * t^2
            term4 = _shift(xt, 2)  # x * t^2

            # E := x^2 - x t - x^3 t^2 + x t^2
            E = _add(term1, term2, sign=-1)
            E = _add(E, term3, sign=-1)
            E = _add(E, term4, sign=+1)
            return E.get(e_target, Fraction(0))

        b = E_coeff(Fraction(0))
        a_lin = E_coeff(Fraction(1)) - b
        if a_lin == 0:
            raise RuntimeError(f"no linear dependence at m={m}, e={e_target}")
        u = -b / a_lin
        if u != 0:
            x[m] = u
    return x


def compute_expE(series_deg: int) -> Tuple[Series, Series, Series]:
    """Return (x(t), eta(t), exp_E(u)) up to the requested series degree."""
    x_t = compute_x_of_t(series_deg)
    eta_t = _shift(_scale(x_t, Fraction(-1)), -1)  # eta = -x/t

    # omega = dx/(2eta+1) = g(t) dt, with g a power series.
    dx_dt = _deriv(x_t, -200, series_deg)
    D = _add(_scale(eta_t, Fraction(2)), {0: Fraction(1)})  # 2eta+1 (Laurent)

    # Shift by +3 to make numerator/denominator power series (since both have leading t^{-3}).
    num = _trunc(_shift(dx_dt, 3), 0, series_deg)
    den = _trunc(_shift(D, 3), 0, series_deg)
    den_inv = _inv_power_series(den, series_deg)
    g = _mul(num, den_inv, 0, series_deg)

    # log_E(t) = ∫ g(t) dt = t + O(t^2)
    logE: Series = {}
    for e, c in g.items():
        logE[e + 1] = logE.get(e + 1, Fraction(0)) + c / Fraction(e + 1)
    logE = _trunc(logE, 1, series_deg)
    if logE.get(1, Fraction(0)) != 1:
        raise RuntimeError("unexpected log_E leading coefficient")

    # exp_E(u): compositional inverse of log_E(t)
    expE: Series = {1: Fraction(1)}
    for n in range(2, series_deg + 1):
        composed = _compose_power_series(logE, expE, n)
        cn = composed.get(n, Fraction(0))
        if cn != 0:
            expE[n] = expE.get(n, Fraction(0)) - cn
    return x_t, eta_t, expE


def _format_q_series(coeffs: List[Tuple[int, int]], *, big_o_exp: int) -> str:
    # coeffs: list of (exp, coeff), exp can be negative.
    # We print in increasing exp order (more negative -> more positive) for display.
    parts: List[str] = []
    for exp, c in coeffs:
        if c == 0:
            continue
        sign = "+" if c > 0 else "-"
        a = abs(c)
        if not parts:
            sign = "-" if c < 0 else ""
        if exp == 0:
            term = f"{a}"
        elif exp == 1:
            term = "q" if a == 1 else f"{a}q"
        else:
            qpow = f"q^{{{exp}}}"
            if a == 1:
                term = qpow
            else:
                term = f"{a}{qpow}"
        parts.append(f"{sign}{term}")
    if not parts:
        parts = ["0"]
    return "".join(parts) + f"+O\\!\\left(q^{{{big_o_exp}}}\\right)"


def compute_weight_y_qexp(*, q_out: int, q_max: int, series_deg: int) -> Dict[str, object]:
    """Compute y(tau) = eta + x^2 q-expansion up to q^{q_out} (inclusive)."""
    if q_out < 0:
        raise ValueError("q_out must be nonnegative")
    if q_max < max(10, q_out + 6):
        raise ValueError("q_max too small for requested output")

    # Hecke/newform coefficients a_n (offline).
    a = compute_a_list(q_max)

    # Formal group exponential and x(t), eta(t).
    x_t, eta_t, expE = compute_expE(series_deg)

    # Modular logarithm L_mod(q) = - sum_{n>=1} a_n q^n / n
    # (the sign corresponds to the modular parametrization branch used in the manuscript).
    Lmod: Series = {n: Fraction(-a[n], n) for n in range(1, q_max + 1)}

    # t(q) = exp_E(L_mod(q))
    t_q = _compose_power_series(expE, Lmod, q_max)

    # U(q) = t(q)/q = 1 + ...
    U = _shift(t_q, -1)
    U_inv = _inv_power_series(_trunc(U, 0, q_max), q_max)

    def U_pow(e: int) -> Series:
        if e == 0:
            return {0: Fraction(1)}
        if e > 0:
            return _pow_int(_trunc(U, 0, q_max), e, 0, q_max)
        return _pow_int(U_inv, -e, 0, q_max)

    # Substitute t=q*U into Laurent series in t.
    q_keep_max = q_out + 5  # safety margin for x^2 -> y

    def compose_laurent_in_t(S: Series) -> Series:
        out: Series = {}
        for e_t, c in S.items():
            term = _shift(_scale(U_pow(e_t), c), e_t)  # q^{e_t} * U^{e_t}
            out = _add(out, _trunc(term, -50, q_keep_max))
        return out

    x_q = compose_laurent_in_t(x_t)
    eta_q = compose_laurent_in_t(eta_t)
    x2_q = _mul(x_q, x_q, -50, q_keep_max)
    y_q = _add(eta_q, x2_q)

    # Collect y coefficients for exponents -4..q_out.
    y_coeffs: List[Tuple[int, int]] = []
    for e in range(-4, q_out + 1):
        c = y_q.get(e, Fraction(0))
        if c.denominator != 1:
            raise RuntimeError(f"unexpected non-integer y coefficient at q^{e}: {c}")
        y_coeffs.append((e, int(c.numerator)))

    f_n_out = min(q_max, 7)
    f_coeffs: List[Tuple[int, int]] = [(n, int(a[n])) for n in range(1, f_n_out + 1)]

    return {
        "q_out": q_out,
        "q_max": q_max,
        "series_deg": series_deg,
        "a_n": {str(n): int(a[n]) for n in range(1, q_max + 1)},
        "y_coeffs": [{"exp": e, "coeff": c} for e, c in y_coeffs],
        "f_coeffs": [{"n": n, "a_n": an} for n, an in f_coeffs],
        "y_series_latex": _format_q_series(y_coeffs, big_o_exp=q_out + 1),
        "f_series_latex": _format_q_series(f_coeffs, big_o_exp=f_n_out + 1),
    }


def _sigma_k(n: int, k: int) -> int:
    s = 0
    d = 1
    while d * d <= n:
        if n % d == 0:
            s += d**k
            e = n // d
            if e != d:
                s += e**k
        d += 1
    return int(s)


def _invert_j_on_imag_axis(*, j_target: mp.mpf, dps: int = 80, n_terms: int = 80) -> tuple[mp.mpf, mp.mpf]:
    """Return (t,q) with tau=i*t in the SL2Z fundamental domain, such that j(i t)=j_target."""
    if dps < 50:
        raise ValueError("require dps >= 50 for stable inversion")
    if n_terms < 20:
        raise ValueError("require n_terms >= 20 for stable inversion")

    mp.mp.dps = int(dps)
    two_pi = mp.mpf(2) * mp.pi

    # Precompute divisor sums for E4/E6 q-expansions.
    sigma3 = [0] * (n_terms + 1)
    sigma5 = [0] * (n_terms + 1)
    for n in range(1, n_terms + 1):
        sigma3[n] = _sigma_k(n, 3)
        sigma5[n] = _sigma_k(n, 5)

    def j_it(t: mp.mpf) -> mp.mpf:
        q = mp.e ** (-two_pi * t)
        E4 = mp.mpf(1)
        E6 = mp.mpf(1)
        qn = q
        for n in range(1, n_terms + 1):
            E4 += mp.mpf(240) * sigma3[n] * qn
            E6 -= mp.mpf(504) * sigma5[n] * qn
            qn *= q
        E4_3 = E4**3
        return mp.mpf(1728) * E4_3 / (E4_3 - E6**2)

    # Fundamental-domain anchor: j(i)=1728. For real j_target>1728, the solution is unique on t>1.
    t_lo = mp.mpf(1)
    j_lo = j_it(t_lo)
    if not (j_lo < j_target):
        raise RuntimeError(f"expected j(i)=1728 < j_target, got j(i)={j_lo}")

    t_hi = mp.mpf(2)
    while j_it(t_hi) <= j_target:
        t_hi *= 2
        if t_hi > 64:
            raise RuntimeError("failed to bracket the j-inversion root on the imaginary axis")

    # Bisection (monotone on t>1).
    iters = 3 * dps + 10
    for _ in range(iters):
        t_mid = (t_lo + t_hi) / 2
        if j_it(t_mid) < j_target:
            t_lo = t_mid
        else:
            t_hi = t_mid

    t = (t_lo + t_hi) / 2
    q = mp.e ** (-two_pi * t)
    return t, q


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit modular q-expansion anchoring for y=eta+x^2 on 37a1 / X0^+(37).")
    parser.add_argument("--q-out", type=int, default=3, help="Max nonnegative q exponent to print for y(tau) (default: 3)")
    parser.add_argument("--q-max", type=int, default=50, help="Compute a_n and modular log up to this q exponent (default: 50)")
    parser.add_argument(
        "--series-deg",
        type=int,
        default=90,
        help="Internal formal-group series degree (default: 90)",
    )
    parser.add_argument("--tau-dps", type=int, default=80, help="Decimal digits for j-inversion on the imaginary axis (default: 80)")
    parser.add_argument("--j-terms", type=int, default=80, help="Number of q-terms for E4/E6 in j-inversion (default: 80)")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-elliptic-modular-y-qexp] start", flush=True)

    payload = compute_weight_y_qexp(q_out=args.q_out, q_max=args.q_max, series_deg=args.series_deg)

    # Invert j(E)=110592/37 in the SL2Z fundamental domain (tau is purely imaginary).
    j_target = mp.mpf(110592) / mp.mpf(37)
    t_im, q_at_tau = _invert_j_on_imag_axis(j_target=j_target, dps=int(args.tau_dps), n_terms=int(args.j_terms))
    payload.update(
        {
            "j_target": mp.nstr(j_target, 30),
            "tau_fundamental_domain": f"1j*{mp.nstr(t_im, 30)}",
            "tau_imag": mp.nstr(t_im, 30),
            "q_at_tau": mp.nstr(q_at_tau, 30),
        }
    )

    if not args.no_output:
        json_path = export_dir() / "fold_zm_elliptic_modular_y_qexp_audit.json"
        _write_json(json_path, payload)

        y_series = str(payload["y_series_latex"])
        f_series = str(payload["f_series_latex"])

        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_fold_zm_elliptic_modular_y_qexp_audit.py",
                "\\[",
                f"y(\\tau)={y_series}.",
                "\\]",
                "\\[",
                f"f(q)={f_series}.",
                "\\]",
                "",
            ]
        )
        tex_path = generated_dir() / "eq_fold_zm_elliptic_modular_y_qexp_audit.tex"
        _write_text(tex_path, tex)

    dt = time.time() - t0
    print(f"[fold-zm-elliptic-modular-y-qexp] ok elapsed_s={dt:.3f}", flush=True)


if __name__ == "__main__":
    main()

