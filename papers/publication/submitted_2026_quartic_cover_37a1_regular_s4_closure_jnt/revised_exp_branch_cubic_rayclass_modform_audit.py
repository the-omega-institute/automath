#!/usr/bin/env python3
"""
Reproduce the class-group and Hecke-trace checks used in
`2026_branch_cubic_regular_s4_closure_prym_ray_class_arithmetic`.

The script records:
  - the powers of the ideal a = (2, tau - 1) in O_K, K = Q(sqrt(-111)),
  - the norm-form solutions showing that a^4 is not principal,
  - the root-count traces for the branch cubic c(y) and the maximal-order
    cubic u^3 - 9u^2 + 256 at good primes.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path

import sympy as sp
from sympy.matrices.normalforms import hermite_normal_form


def qmul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    """Multiply (x + y*tau)(u + v*tau), where tau^2 = tau - 28."""
    x1, y1 = a
    x2, y2 = b
    return (x1 * x2 - 28 * y1 * y2, x1 * y2 + x2 * y1 + y1 * y2)


def hnf_basis(cols: list[tuple[int, int]]) -> list[list[int]]:
    matrix = sp.Matrix([[c[0] for c in cols], [c[1] for c in cols]])
    hnf = hermite_normal_form(matrix)
    out: list[list[int]] = []
    for j in range(hnf.shape[1]):
        col = [int(hnf[0, j]), int(hnf[1, j])]
        if col != [0, 0]:
            out.append(col)
    return out


def ideal_mul(i_basis: list[list[int]], j_basis: list[list[int]]) -> list[list[int]]:
    cols: list[tuple[int, int]] = []
    for a0, a1 in i_basis:
        for b0, b1 in j_basis:
            cols.append(qmul((a0, a1), (b0, b1)))
    return hnf_basis(cols)


def principal_basis(alpha: tuple[int, int]) -> list[list[int]]:
    return hnf_basis([alpha, qmul(alpha, (0, 1))])


def norm(alpha: tuple[int, int]) -> int:
    x, y = alpha
    return x * x + x * y + 28 * y * y


def norm_solutions(target: int, bound: int = 500) -> list[list[int]]:
    sols: list[list[int]] = []
    for y in range(-bound, bound + 1):
        disc = 4 * target - 111 * y * y
        if disc < 0:
            continue
        root = isqrt(disc)
        if root * root != disc:
            continue
        for num in (-y + root, -y - root):
            if num % 2 == 0:
                x = num // 2
                if norm((x, y)) == target:
                    pair = [x, y]
                    if pair not in sols:
                        sols.append(pair)
    return sorted(sols)


def roots_mod(poly: callable, p: int) -> int:
    return sum(1 for a in range(p) if poly(a) % p == 0)


def main() -> None:
    ideal_a = [[2, 0], [-1, 1]]
    powers = {}
    current = ideal_a
    for n in range(1, 9):
        powers[str(n)] = current
        current = ideal_mul(current, ideal_a)

    norm16 = norm_solutions(16)
    principal_norm16 = {tuple(map(tuple, principal_basis(tuple(sol)))): sol for sol in norm16}

    branch_poly = lambda y: 256 * y * y * y + 411 * y * y + 165 * y + 32
    maximal_poly = lambda u: u * u * u - 9 * u * u + 256

    trace_data = []
    for p in list(sp.primerange(5, 101)):
        if p in (31, 37):
            continue
        branch_trace = roots_mod(branch_poly, p) - 1
        maximal_trace = roots_mod(maximal_poly, p) - 1
        trace_data.append(
            {
                "p": int(p),
                "trace_from_branch_cubic": int(branch_trace),
                "trace_from_maximal_order_cubic": int(maximal_trace),
            }
        )

    out = {
        "ideal_a_basis": ideal_a,
        "ideal_powers": powers,
        "norm16_solutions": norm16,
        "a4_is_principal": tuple(map(tuple, powers["4"])) in principal_norm16,
        "a8_principal_generator": [1, 3],
        "prime_trace_data": trace_data,
    }

    out_dir = Path(__file__).resolve().parents[1] / "artifacts" / "export"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "branch_cubic_rayclass_modform_audit.json"
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(out_path)


if __name__ == "__main__":
    main()
