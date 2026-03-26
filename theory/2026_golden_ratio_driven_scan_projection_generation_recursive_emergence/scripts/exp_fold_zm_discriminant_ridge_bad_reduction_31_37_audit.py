#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the semistable nodal reductions of the Lee--Yang discriminant ridge curve
at the bad odd primes p=31 and p=37.

Curve (genus 2, odd degree model):
  C: w^2 = f(y),   f(y) = -y(y-1) P_LY(y),
  P_LY(y)=256y^3+411y^2+165y+32.

At p in {31,37}, f has a unique double root y0 mod p, hence C/F_p has a single
ordinary double point (node). The normalization is an elliptic curve
  E_p: w'^2 = g_p(y) = f(y)/(y-y0)^2  in F_p[y].

We also certify the split/non-split type of the node via the square class of
g_p(y0), and compute #E_p(F_p), a_p(E_p), and #C(F_p).

This script is English-only by repository convention.

Outputs:
  - artifacts/export/fold_zm_discriminant_ridge_bad_reduction_31_37_audit.json
  - sections/generated/eq_fold_zm_discriminant_ridge_bad_reduction_31_37_audit.tex
"""

from __future__ import annotations

import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sym_int(a: int, p: int) -> int:
    """Representative in [-p//2, p//2]."""
    a %= p
    if a > p // 2:
        a -= p
    return int(a)


def _legendre_symbol(a: int, p: int) -> int:
    """Return (a/p) for odd prime p as -1,0,1."""
    a %= p
    if a == 0:
        return 0
    t = pow(a, (p - 1) // 2, p)
    return -1 if t == p - 1 else int(t)


def _is_square(a: int, p: int) -> bool:
    return _legendre_symbol(a, p) >= 0


def P_LY_int(y: int) -> int:
    y = int(y)
    return 256 * y**3 + 411 * y**2 + 165 * y + 32


def f_coeffs_Z() -> List[int]:
    # f(y) = -y(y-1)P_LY(y) = -256 y^5 -155 y^4 +246 y^3 +133 y^2 +32 y
    # Coeffs low-to-high degree.
    return [0, 32, 133, 246, -155, -256]


def _poly_eval(coeffs: List[int], x: int, p: int) -> int:
    """Evaluate polynomial sum coeffs[i]*x^i mod p."""
    x %= p
    acc = 0
    pow_x = 1
    for c in coeffs:
        acc = (acc + (c % p) * pow_x) % p
        pow_x = (pow_x * x) % p
    return int(acc)


def _poly_derivative(coeffs: List[int], p: int) -> List[int]:
    if len(coeffs) <= 1:
        return [0]
    out = []
    for i in range(1, len(coeffs)):
        out.append((i * coeffs[i]) % p)
    return out


def _poly_divmod_monic_quadratic(coeffs: List[int], y0: int, p: int) -> Tuple[List[int], List[int]]:
    """
    Divide f(y) by (y-y0)^2 = y^2 - 2y0 y + y0^2 over F_p.
    Return (quotient, remainder) as coefficient lists low-to-high.
    """
    # Ensure working modulo p.
    f = [c % p for c in coeffs]
    # divisor d(y)=y^2 + d1*y + d0 with d1=-2y0, d0=y0^2.
    d0 = (y0 * y0) % p
    d1 = (-2 * y0) % p

    # Long division for degrees: deg f = 5, deg d = 2, quotient deg 3.
    # Work with high-to-low for convenience.
    deg_f = len(f) - 1
    q = [0] * (deg_f - 2 + 1)  # degrees 0..3
    r = f[:]  # mutable remainder (low-to-high)

    def coeff_at(deg: int) -> int:
        return r[deg] if 0 <= deg < len(r) else 0

    # Since divisor is monic, leading term division is direct.
    for k in range(deg_f, 1, -1):
        # Determine q_{k-2} so that leading term cancels at degree k.
        lead = coeff_at(k) % p
        qdeg = k - 2
        q[qdeg] = lead
        # Subtract lead * y^{qdeg} * d(y) from r.
        # r_k -= lead*1, r_{k-1} -= lead*d1, r_{k-2} -= lead*d0.
        r[k] = (r[k] - lead) % p
        r[k - 1] = (r[k - 1] - lead * d1) % p
        r[k - 2] = (r[k - 2] - lead * d0) % p

    # Remainder is degree < 2: r0 + r1*y.
    rem = [r[0] % p, r[1] % p]
    # Trim quotient list to length 4.
    return ([q[i] % p for i in range(0, 4)], rem)


def _roots_and_mult(coeffs: List[int], p: int) -> Dict[int, int]:
    """Return root multiplicities for a degree<=5 poly over F_p via derivative test."""
    d = _poly_derivative(coeffs, p)
    mult: Dict[int, int] = {}
    for x in range(p):
        if _poly_eval(coeffs, x, p) == 0:
            # For our use, multiplicity is either 1 or 2.
            m = 2 if _poly_eval(d, x, p) == 0 else 1
            mult[int(x)] = m
    return mult


def _count_points_hyperelliptic_odd_degree(rhs_coeffs: List[int], p: int) -> int:
    """
    Count points on w^2 = rhs(y) over F_p for odd degree model (one point at infinity).
    Works also for nodal/singular fibers for counting F_p-rational solutions of the affine
    equation plus the unique point at infinity.
    """
    total = 1  # point at infinity
    for y in range(p):
        rhs = _poly_eval(rhs_coeffs, y, p)
        total += 1 + _legendre_symbol(rhs, p)
    return int(total)


@dataclass(frozen=True)
class PrimeReport:
    p: int
    y0_node: int
    f_lead: int
    f_factor_a: int
    f_factor_y0: int
    g_lead: int
    g_roots: List[int]
    eps: int
    g_at_node: int
    g_at_node_is_square: bool
    n_E_fp: int
    a_p_E: int
    n_C_fp: int
    j_E: int | None
    legendre_lambda: int | None
    lambda_sq_minus_lambda_plus_1: int | None


def _j_invariant_legendre(lambda_mod_p: int, p: int) -> int:
    lam = lambda_mod_p % p
    num = (1 - lam + lam * lam) % p
    if num == 0:
        return 0
    den = (lam * lam) % p
    den = (den * ((1 - lam) * (1 - lam) % p)) % p
    den_inv = pow(den, -1, p)
    j = (256 % p) * pow(num, 3, p) % p
    j = (j * den_inv) % p
    return int(j)


def audit_prime(p: int) -> PrimeReport:
    p = int(p)
    coeffs = f_coeffs_Z()

    mult = _roots_and_mult(coeffs, p)
    double_roots = [r for r, m in mult.items() if m == 2]
    if len(double_roots) != 1:
        raise RuntimeError(f"expected exactly one double root mod {p}, got {double_roots}")
    y0 = int(double_roots[0])

    q, rem = _poly_divmod_monic_quadratic(coeffs, y0, p)
    if rem[0] % p != 0 or rem[1] % p != 0:
        raise RuntimeError(f"nonzero remainder dividing by (y-{y0})^2 mod {p}: {rem}")

    # g(y) = quotient, degree 3.
    g_coeffs = q  # low-to-high degrees 0..3

    # Find roots of g in F_p.
    g_roots = [x for x in range(p) if _poly_eval(g_coeffs, x, p) == 0]
    if len(g_roots) != 3:
        raise RuntimeError(f"expected 3 distinct roots for g mod {p}, got {g_roots}")

    # Identify the nontrivial Legendre parameter lambda if roots contain 0 and 1.
    lam = None
    lam_check = None
    if 0 in g_roots and 1 in g_roots:
        others = [r for r in g_roots if r not in (0, 1)]
        if len(others) == 1:
            lam = int(others[0])
            lam_check = int((lam * lam - lam + 1) % p)

    # Leading coefficients (symmetric reps).
    f_lead = _sym_int(coeffs[-1], p)
    g_lead = _sym_int(g_coeffs[-1], p)

    # Determine eps via square class of g(y0).
    # Use the least nonnegative residue for reporting clarity.
    g_at_node = int(_poly_eval(g_coeffs, y0, p) % p)
    g_square = _is_square(g_at_node, p)
    eps = 1 if g_square else -1

    # Count points on E_p: w'^2 = g(y) (odd degree cubic => one infinity point).
    n_E = _count_points_hyperelliptic_odd_degree(g_coeffs, p)
    a_p = int(p + 1 - n_E)

    # Count points on C/F_p: w^2 = f(y) (odd degree 5 => one infinity point).
    n_C = _count_points_hyperelliptic_odd_degree([c % p for c in coeffs], p)

    # j invariant (only meaningful if we can read lambda).
    jE = _j_invariant_legendre(lam, p) if lam is not None else None

    # For reporting factorization, also record the simple root besides 0,1,y0 if present.
    simple_roots = [r for r, m in mult.items() if m == 1]
    # Expected: 0,1,alpha
    alpha = None
    if 0 in simple_roots and 1 in simple_roots:
        others = [r for r in simple_roots if r not in (0, 1)]
        if len(others) == 1:
            alpha = int(others[0])

    return PrimeReport(
        p=p,
        y0_node=y0,
        f_lead=f_lead,
        f_factor_a=int(alpha) if alpha is not None else -1,
        f_factor_y0=y0,
        g_lead=g_lead,
        g_roots=[int(r) for r in sorted(g_roots)],
        eps=eps,
        g_at_node=g_at_node,
        g_at_node_is_square=g_square,
        n_E_fp=n_E,
        a_p_E=a_p,
        n_C_fp=n_C,
        j_E=jE,
        legendre_lambda=lam,
        lambda_sq_minus_lambda_plus_1=lam_check,
    )


def _tex_factorization_f(rep: PrimeReport) -> str:
    p = rep.p
    c = rep.f_lead
    y0 = rep.y0_node
    a = rep.f_factor_a
    # Prefer displaying as y(y-1)(y-a)(y-y0)^2 when possible.
    if a >= 0:
        return rf"f(y)\equiv {c}\,y(y-1)(y-{a})(y-{y0})^{{2}}\pmod{{{p}}}"
    return rf"f(y)\equiv \text{{(unfactored)}}\pmod{{{p}}}"


def _tex_factorization_g(rep: PrimeReport) -> str:
    p = rep.p
    c = rep.g_lead
    roots = rep.g_roots
    if 0 in roots and 1 in roots and rep.legendre_lambda is not None:
        lam = rep.legendre_lambda
        return rf"E_{{{p}}}:\quad {{w'}}^2={c}\,y(y-1)(y-{lam})\qquad(\FF_{{{p}}})"
    # Generic fallback.
    return rf"E_{{{p}}}:\quad {{w'}}^2=\text{{(cubic)}}\qquad(\FF_{{{p}}})"


def render_tex(reports: List[PrimeReport]) -> str:
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_fold_zm_discriminant_ridge_bad_reduction_31_37_audit.py")
    lines.append(r"\[")
    lines.append(
        r"\mathcal C_{\mathrm{LY}}:\ w^{2}=-y(y-1)(256y^{3}+411y^{2}+165y+32)."
    )
    lines.append(r"\]")
    for rep in reports:
        p = rep.p
        lines.append(r"\[")
        lines.append(_tex_factorization_f(rep) + r".")
        lines.append(r"\]")
        lines.append(r"\[")
        lines.append(
            rf"\text{{node at }}(y,w)=({rep.y0_node},0),\qquad "
            rf"g({rep.y0_node})\equiv {rep.g_at_node}\ (\mathrm{{mod}}\ {p}),\qquad "
            rf"\varepsilon_{{{p}}}={rep.eps}."
        )
        lines.append(r"\]")
        lines.append(r"\[")
        lines.append(_tex_factorization_g(rep) + r".")
        lines.append(r"\]")
        lines.append(r"\[")
        lines.append(
            rf"\#E_{{{p}}}(\FF_{{{p}}})={rep.n_E_fp},\qquad a_{{{p}}}(E_{{{p}}})={rep.a_p_E},\qquad "
            rf"\#\mathcal C_{{\mathrm{{LY}}}}(\FF_{{{p}}})={rep.n_C_fp}."
        )
        lines.append(r"\]")
        if rep.j_E is not None:
            lines.append(r"\[")
            lines.append(
                rf"\lambda_{{{p}}}\equiv {rep.legendre_lambda}\ (\mathrm{{mod}}\ {p}),\qquad "
                rf"\lambda_{{{p}}}^2-\lambda_{{{p}}}+1\equiv {rep.lambda_sq_minus_lambda_plus_1}\ (\mathrm{{mod}}\ {p}),\qquad "
                rf"j(E_{{{p}}})\equiv {rep.j_E}\ (\mathrm{{mod}}\ {p})."
            )
            lines.append(r"\]")
    return "\n".join(lines) + "\n"


def main() -> None:
    t0 = time.time()
    primes = [31, 37]
    reports: List[PrimeReport] = []
    print("[audit] start bad reduction audit p=31,37", flush=True)
    for p in primes:
        print(f"[audit] analyzing p={p}", flush=True)
        reports.append(audit_prime(p))

    payload = {
        "curve": "w^2 = -y(y-1)P_LY(y), P_LY(y)=256y^3+411y^2+165y+32",
        "primes": primes,
        "reports": [asdict(r) for r in reports],
        "elapsed_s": time.time() - t0,
    }

    out_json = export_dir() / "fold_zm_discriminant_ridge_bad_reduction_31_37_audit.json"
    out_tex = generated_dir() / "eq_fold_zm_discriminant_ridge_bad_reduction_31_37_audit.tex"
    _write_json(out_json, payload)
    _write_text(out_tex, render_tex(reports))
    print(f"[audit] wrote {out_json}", flush=True)
    print(f"[audit] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

