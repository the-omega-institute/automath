#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Reproduce primitive orbit spectrum for the 10-state sync-kernel SFT.

Outputs:
- artifacts/export/sync_kernel_primitive_spectrum.json (default)
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import List, Tuple

from common_paths import export_dir
from common_phi_fold import Progress


STATES = [
    "000",
    "001",
    "002",
    "010",
    "100",
    "101",
    "0-12",
    "1-12",
    "01-1",
    "11-1",
]

B_MATRIX: List[List[int]] = [
    [1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    [1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
    [0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
]


def mat_mul(A: List[List[int]], B: List[List[int]]) -> List[List[int]]:
    n = len(A)
    m = len(B[0])
    p = len(B)
    out = [[0] * m for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for k in range(p):
            if Ai[k] == 0:
                continue
            aik = Ai[k]
            Bk = B[k]
            for j in range(m):
                out[i][j] += aik * Bk[j]
    return out


def mat_trace(A: List[List[int]]) -> int:
    return sum(A[i][i] for i in range(len(A)))


def mat_pow_traces(B: List[List[int]], n_max: int, prog: Progress) -> List[int]:
    if n_max <= 0:
        return []
    M = [row[:] for row in B]
    traces = []
    for n in range(1, n_max + 1):
        if n > 1:
            M = mat_mul(M, B)
        traces.append(mat_trace(M))
        prog.tick(f"trace n={n}/{n_max}")
    return traces


def mat_pow(B: List[List[int]], k: int, prog: Progress) -> List[List[int]]:
    if k <= 0:
        n = len(B)
        return [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    M = [row[:] for row in B]
    for step in range(2, k + 1):
        M = mat_mul(M, B)
        prog.tick(f"power k={step}/{k}")
    return M


def is_all_positive(A: List[List[int]]) -> bool:
    return all(x > 0 for row in A for x in row)


def mobius(n: int) -> int:
    if n == 1:
        return 1
    mu = 1
    p = 2
    nn = n
    while p * p <= nn:
        if nn % p == 0:
            nn //= p
            if nn % p == 0:
                return 0
            mu = -mu
        p += 1
    if nn > 1:
        mu = -mu
    return mu


def divisors(n: int) -> List[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def primitive_counts(traces: List[int], prog: Progress) -> List[int]:
    pvals: List[int] = []
    for n in range(1, len(traces) + 1):
        s = 0
        for d in divisors(n):
            s += mobius(d) * traces[n // d - 1]
        if s % n != 0:
            raise ValueError(f"non-integer p_n for n={n}: {s}/{n}")
        pvals.append(s // n)
        prog.tick(f"primitive n={n}/{len(traces)}")
    return pvals


def det_bareiss_int(M: List[List[int]]) -> int:
    A = [row[:] for row in M]
    n = len(A)
    det_sign = 1
    pivot_prev = 1
    for k in range(n - 1):
        pivot = A[k][k]
        if pivot == 0:
            swap = None
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    swap = i
                    break
            if swap is None:
                return 0
            A[k], A[swap] = A[swap], A[k]
            det_sign = -det_sign
            pivot = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * pivot - A[i][k] * A[k][j])
                if pivot_prev != 1:
                    A[i][j] //= pivot_prev
        pivot_prev = pivot
    return det_sign * A[n - 1][n - 1]


def poly_trim(poly: List[Fraction]) -> List[Fraction]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def poly_add(a: List[Fraction], b: List[Fraction]) -> List[Fraction]:
    n = max(len(a), len(b))
    out = [Fraction(0)] * n
    for i in range(n):
        if i < len(a):
            out[i] += a[i]
        if i < len(b):
            out[i] += b[i]
    return poly_trim(out)


def poly_mul(a: List[Fraction], b: List[Fraction]) -> List[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return poly_trim(out)


def poly_div(dividend: List[Fraction], divisor: List[Fraction]) -> Tuple[List[Fraction], List[Fraction]]:
    dividend = dividend[:]
    divisor = poly_trim(divisor[:])
    if len(divisor) == 1 and divisor[0] == 0:
        raise ZeroDivisionError("zero divisor")
    deg_d = len(dividend) - 1
    deg_s = len(divisor) - 1
    if deg_d < deg_s:
        return [Fraction(0)], dividend
    out = [Fraction(0)] * (deg_d - deg_s + 1)
    while deg_d >= deg_s and dividend != [Fraction(0)]:
        lead = dividend[-1] / divisor[-1]
        k = deg_d - deg_s
        out[k] = lead
        for i in range(deg_s + 1):
            dividend[k + i] -= lead * divisor[i]
        dividend = poly_trim(dividend)
        deg_d = len(dividend) - 1
    return poly_trim(out), poly_trim(dividend)


def lagrange_interpolate(points: List[Tuple[int, int]]) -> List[Fraction]:
    n = len(points)
    coeffs = [Fraction(0)] * n
    for i, (xi, yi) in enumerate(points):
        numer = [Fraction(1)]
        denom = Fraction(1)
        for j, (xj, _) in enumerate(points):
            if i == j:
                continue
            numer = poly_mul(numer, [Fraction(-xj), Fraction(1)])
            denom *= (xi - xj)
        term = [c * Fraction(yi, 1) / denom for c in numer]
        coeffs = poly_add(coeffs, term)
    return coeffs


def det_poly_coeffs(B: List[List[int]], prog: Progress) -> List[int]:
    n = len(B)
    points: List[Tuple[int, int]] = []
    for z in range(n + 1):
        M = [[(1 if i == j else 0) - z * B[i][j] for j in range(n)] for i in range(n)]
        det = det_bareiss_int(M)
        points.append((z, det))
        prog.tick(f"det sample z={z}/{n}")
    coeffs = lagrange_interpolate(points)
    out: List[int] = []
    for c in coeffs:
        if c.denominator != 1:
            raise ValueError(f"non-integer coeff: {c}")
        out.append(int(c))
    return out


def cubic_roots(a: float, b: float, c: float, d: float) -> List[complex]:
    """Solve cubic with real coefficients (robust for one real + two complex roots)."""
    if a == 0.0:
        raise ValueError("not a cubic")
    b /= a
    c /= a
    d /= a
    p = c - b * b / 3.0
    q = 2.0 * b * b * b / 27.0 - b * c / 3.0 + d
    delta = (q / 2.0) ** 2 + (p / 3.0) ** 3

    def real_cbrt(x: float) -> float:
        if x >= 0:
            return x ** (1.0 / 3.0)
        return -((-x) ** (1.0 / 3.0))

    shift = b / 3.0
    if delta >= 0:
        sqrt_delta = math.sqrt(delta)
        u = real_cbrt(-q / 2.0 + sqrt_delta)
        v = real_cbrt(-q / 2.0 - sqrt_delta)
        t = u + v
        x1 = t - shift
        real_part = -t / 2.0 - shift
        imag_part = (math.sqrt(3.0) / 2.0) * (u - v)
        x2 = complex(real_part, imag_part)
        x3 = complex(real_part, -imag_part)
        return [x1, x2, x3]

    r = math.sqrt(-(p**3) / 27.0)
    phi = math.acos(-q / (2.0 * r))
    t = 2.0 * math.sqrt(-p / 3.0)
    roots = []
    for k in range(3):
        roots.append(t * math.cos((phi + 2.0 * math.pi * k) / 3.0) - shift)
    return roots


def zeta_B(z: float) -> float:
    return 1.0 / ((z - 1.0) * (z + 1.0) * (3.0 * z - 1.0) * (z**3 - z**2 + z + 1.0))


def log_mertens_constant(max_m: int, tol: float, prog: Progress) -> Tuple[float, int]:
    z0 = 1.0 / 3.0
    f = (z0 - 1.0) * (z0 + 1.0) * (z0**3 - z0**2 + z0 + 1.0)
    C = -1.0 / f
    logM = math.log(C)
    small_hits = 0
    used = 1
    for m in range(2, max_m + 1):
        mu = mobius(m)
        if mu == 0:
            continue
        z_m = z0**m
        term = (mu / m) * math.log(zeta_B(z_m))
        logM += term
        used = m
        if abs(term) < tol:
            small_hits += 1
            if small_hits >= 6 and m > 20:
                break
        else:
            small_hits = 0
        prog.tick(f"logM m={m}/{max_m} term={term:.3e}")
    return logM, used


def residue_C_B() -> Tuple[Fraction, float]:
    z0 = Fraction(1, 3)
    g = (z0 - 1) * (z0 + 1) * (z0**3 - z0**2 + z0 + 1)
    C_frac = -Fraction(1, 1) / g
    return C_frac, float(C_frac)


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Reproduce sync-kernel primitive spectrum")
    parser.add_argument("--max-n", type=int, default=10, help="Max n for traces/primitive counts")
    parser.add_argument("--logm-max", type=int, default=200, help="Max m for log M_B series")
    parser.add_argument("--logm-tol", type=float, default=1e-14, help="Term cutoff for log M_B")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_primitive_spectrum.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="sync-kernel", every_seconds=20.0)

    print("[sync-kernel] start", flush=True)

    traces = mat_pow_traces(B_MATRIX, args.max_n, prog)
    pvals = primitive_counts(traces, prog)

    B5 = mat_pow(B_MATRIX, 5, prog)
    is_primitive = is_all_positive(B5)

    coeffs_int = det_poly_coeffs(B_MATRIX, prog)
    coeffs_frac = [Fraction(c) for c in coeffs_int]
    q1, r1 = poly_div(coeffs_frac, [Fraction(-1), Fraction(1)])  # (z-1)
    q2, r2 = poly_div(q1, [Fraction(1), Fraction(1)])  # (z+1)
    q3, r3 = poly_div(q2, [Fraction(-1), Fraction(3)])  # (3z-1)
    cubic_coeffs = [int(c) for c in q3]
    if r1 != [Fraction(0)] or r2 != [Fraction(0)] or r3 != [Fraction(0)]:
        raise ValueError("factorization failed")

    roots_z = cubic_roots(1.0, -1.0, 1.0, 1.0)
    eig_cubic = [1.0 / r for r in roots_z]
    rho = max(abs(x) for x in eig_cubic)

    C_frac, C = residue_C_B()
    logM, m_used = log_mertens_constant(args.logm_max, args.logm_tol, prog)
    M = math.exp(logM)
    pi_vals = []
    s = 0
    for v in pvals:
        s += v
        pi_vals.append(s)

    payload = {
        "states": STATES,
        "matrix_B": B_MATRIX,
        "det_poly_coeffs": coeffs_int,
        "det_factorization": {
            "linear": ["(z-1)", "(z+1)", "(3z-1)"],
            "cubic": [int(c) for c in cubic_coeffs],
        },
        "C_B": C,
        "C_B_fraction": f"{C_frac.numerator}/{C_frac.denominator}",
        "traces_a_n": traces,
        "primitive_p_n": pvals,
        "prime_counting_Pi_B": pi_vals,
        "prime_counting_Pi_B_N": pi_vals[-1] if pi_vals else 0,
        "pf_eigenvalue": 3.0,
        "rho_second_eigen_mod": rho,
        "log_M_B": logM,
        "M_B": M,
        "log_M_B_series_max_m": m_used,
        "B5_all_positive": is_primitive,
    }

    if not args.no_output:
        out_path = Path(args.output) if args.output else export_dir() / "sync_kernel_primitive_spectrum.json"
        write_json(out_path, payload)
        print(f"[sync-kernel] wrote {out_path}", flush=True)

    print("[sync-kernel] traces:", traces, flush=True)
    print("[sync-kernel] primitive:", pvals, flush=True)
    print(f"[sync-kernel] C_B = {C_frac} (~{C:.12g})", flush=True)
    if pi_vals:
        print(f"[sync-kernel] Pi_B({len(pi_vals)}) = {pi_vals[-1]}", flush=True)
    print(f"[sync-kernel] det coeffs: {coeffs_int}", flush=True)
    print(f"[sync-kernel] rho ~ {rho:.12g}", flush=True)
    print(f"[sync-kernel] log M_B ~ {logM:.16g}", flush=True)
    print(f"[sync-kernel] M_B ~ {M:.16g}", flush=True)
    print("[sync-kernel] done", flush=True)


if __name__ == "__main__":
    main()
