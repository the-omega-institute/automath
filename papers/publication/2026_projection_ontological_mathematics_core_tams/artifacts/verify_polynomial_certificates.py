"""Verify modular and discriminant certificates for the displayed polynomials."""

from __future__ import annotations

import hashlib
import json
import platform
from pathlib import Path

import sympy as sp

from generate_sequence_data import RECURRENCES


X = sp.symbols("x")
CERTIFICATES = {
    9: ((11, (7,)), (17, (6, 1)), (13, (3, 2, 1, 1))),
    10: ((17, (9,)), (109, (8, 1)), (101, (5, 3, 1))),
    11: ((37, (9,)), (17, (8, 1)), (19, (5, 4))),
    12: ((29, (13,)), (17, (12, 1)), (97, (7, 6))),
    13: ((29, (11,)), (61, (10, 1)), (41, (7, 3, 1))),
    14: ((37, (13,)), (47, (12, 1)), (71, (7, 6))),
    15: ((17, (11,)), (127, (10, 1)), (37, (7, 4))),
    16: ((239, (13,)), (127, (12, 1)), (19, (7, 2, 2, 2))),
    17: ((31, (13,)), (59, (12, 1)), (23, (7, 6))),
}
LEGENDRE_PRIMES = (31, 37, 43, 61)
EXPECTED_LEGENDRE = {
    12: (-1, -1, 1, 1),
    13: (1, -1, 1, -1),
    14: (-1, 1, 1, 1),
    15: (-1, -1, -1, 1),
}


def polynomial(q: int) -> sp.Poly:
    coefficients = RECURRENCES[q][1]
    degree = len(coefficients)
    return sp.Poly(
        X**degree - sum(c * X ** (degree - i) for i, c in enumerate(coefficients, 1)),
        X,
        domain=sp.ZZ,
    )


def factorization(poly: sp.Poly, prime: int) -> tuple[list[int], list[dict[str, object]]]:
    reduced = sp.Poly(poly.as_expr(), X, modulus=prime)
    if sp.gcd(reduced, reduced.diff()).degree() != 0:
        raise AssertionError(f"ramified certificate prime {prime}")
    factors = sp.factor_list(reduced)[1]
    expanded = []
    records = []
    for factor, exponent in factors:
        expanded.extend([factor.degree()] * exponent)
        records.append({
            "coefficients": [int(value) % prime for value in factor.all_coeffs()],
            "degree": factor.degree(),
            "exponent": exponent,
        })
    return sorted(expanded, reverse=True), records


def rank_mod_two(rows: list[list[int]]) -> int:
    work = [row[:] for row in rows]
    rank = 0
    for column in range(len(work[0])):
        pivot = next((i for i in range(rank, len(work)) if work[i][column]), None)
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for i in range(len(work)):
            if i != rank and work[i][column]:
                work[i] = [a ^ b for a, b in zip(work[i], work[rank], strict=True)]
        rank += 1
    return rank


def main() -> None:
    rows = []
    for q, certificates in CERTIFICATES.items():
        poly = polynomial(q)
        certificate_rows = []
        for prime, expected_degrees in certificates:
            degrees, factors = factorization(poly, prime)
            assert degrees == sorted(expected_degrees, reverse=True)
            certificate_rows.append({"prime": prime, "degrees": degrees, "factors": factors})
        rows.append({
            "q": q,
            "polynomial_coefficients": [int(value) for value in poly.all_coeffs()],
            "discriminant": int(sp.discriminant(poly.as_expr(), X)),
            "modular_certificates": certificate_rows,
        })

    legendre_rows = []
    binary_rows = []
    by_q = {row["q"]: row for row in rows}
    for q, expected in EXPECTED_LEGENDRE.items():
        discriminant = by_q[q]["discriminant"]
        values = tuple(int(sp.legendre_symbol(discriminant, p)) for p in LEGENDRE_PRIMES)
        assert values == expected
        binary_rows.append([1 if value == -1 else 0 for value in values])
        legendre_rows.append({"q": q, "values": values})
    assert rank_mod_two(binary_rows) == 4

    payload = {
        "schema": 1,
        "environment": {"python": platform.python_version(), "sympy": sp.__version__},
        "polynomials": rows,
        "legendre_primes": LEGENDRE_PRIMES,
        "legendre_rows": legendre_rows,
        "binary_rank": 4,
        "status": "Certificates concern the displayed polynomials, not their identification as all-m minimal recurrences.",
    }
    output = Path(__file__).with_name("polynomial_certificates_q9_17.json")
    encoded = (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("ascii")
    output.write_bytes(encoded)
    print(f"verified_polynomials={len(rows)}")
    print("verified_modular_factorizations=27")
    print("verified_discriminant_binary_rank=4")
    print(f"wrote={output}")
    print(f"sha256={hashlib.sha256(encoded).hexdigest()}")


if __name__ == "__main__":
    main()
