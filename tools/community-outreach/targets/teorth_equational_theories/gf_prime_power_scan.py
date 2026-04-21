#!/usr/bin/env python3
"""Finite-field linear magma scan for teorth/equational_theories issue #418.

This script checks operations of the form

    x diamond y = a*x + b*y

over all prime-power fields of order at most 81.  It is intended as a
reproducible data artifact, not as a proof that larger fields cannot add more
separations.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
import urllib.request
from dataclasses import dataclass


ETP_COMMIT = "d69afe6eee96801b1cbfad2bfca18eb48a74fc2e"
BASE_URL = f"https://raw.githubusercontent.com/teorth/equational_theories/{ETP_COMMIT}"
VARS = ("x", "y", "z", "w", "u", "v")
VAR_INDEX = {var: i for i, var in enumerate(VARS)}

# Monic irreducible polynomials, constant coefficient first.
FIELD_MODULI = {
    (2, 1): [0, 1],
    (3, 1): [0, 1],
    (5, 1): [0, 1],
    (7, 1): [0, 1],
    (11, 1): [0, 1],
    (13, 1): [0, 1],
    (17, 1): [0, 1],
    (19, 1): [0, 1],
    (23, 1): [0, 1],
    (29, 1): [0, 1],
    (31, 1): [0, 1],
    (37, 1): [0, 1],
    (41, 1): [0, 1],
    (43, 1): [0, 1],
    (47, 1): [0, 1],
    (53, 1): [0, 1],
    (59, 1): [0, 1],
    (61, 1): [0, 1],
    (67, 1): [0, 1],
    (71, 1): [0, 1],
    (73, 1): [0, 1],
    (79, 1): [0, 1],
    (2, 2): [1, 1, 1],      # x^2 + x + 1
    (2, 3): [1, 1, 0, 1],   # x^3 + x + 1
    (2, 4): [1, 0, 0, 1, 1],      # x^4 + x^3 + 1
    (2, 5): [1, 0, 0, 1, 0, 1],   # x^5 + x^3 + 1
    (2, 6): [1, 0, 0, 0, 0, 1, 1],  # x^6 + x^5 + 1
    (3, 2): [1, 0, 1],      # x^2 + 1
    (3, 3): [1, 0, 2, 1],   # x^3 + 2*x^2 + 1
    (3, 4): [1, 0, 1, 1, 1],  # x^4 + x^3 + x^2 + 1
    (5, 2): [1, 1, 1],      # x^2 + x + 1
    (7, 2): [1, 0, 1],      # x^2 + 1
}


@dataclass(frozen=True)
class FieldSpec:
    q: int
    p: int
    degree: int


def fetch_json(path: str) -> object:
    with urllib.request.urlopen(f"{BASE_URL}/{path}", timeout=30) as response:
        return json.loads(response.read().decode("utf-8"))


def equation_id(name: str | None, equation_count: int) -> int | None:
    if name is None:
        return None
    match = re.fullmatch(r"Equation(\d+)", name)
    if match is None:
        return None
    number = int(match.group(1))
    if 1 <= number <= equation_count:
        return number
    return None


def int_to_coeffs(value: int, p: int, degree: int) -> list[int]:
    coeffs = []
    for _ in range(degree):
        coeffs.append(value % p)
        value //= p
    return coeffs


def coeffs_to_int(coeffs: list[int], p: int) -> int:
    value = 0
    scale = 1
    for coeff in coeffs:
        value += (coeff % p) * scale
        scale *= p
    return value


class FiniteField:
    def __init__(self, spec: FieldSpec) -> None:
        self.q = spec.q
        self.p = spec.p
        self.degree = spec.degree
        self.modulus = FIELD_MODULI[(spec.p, spec.degree)]
        coeffs = [int_to_coeffs(i, self.p, self.degree) for i in range(self.q)]
        self.add = [[0] * self.q for _ in range(self.q)]
        self.mul = [[0] * self.q for _ in range(self.q)]

        for a, ca in enumerate(coeffs):
            for b, cb in enumerate(coeffs):
                self.add[a][b] = coeffs_to_int(
                    [(ca[i] + cb[i]) % self.p for i in range(self.degree)],
                    self.p,
                )

                product = [0] * (2 * self.degree - 1)
                for i, x in enumerate(ca):
                    for j, y in enumerate(cb):
                        product[i + j] = (product[i + j] + x * y) % self.p

                for k in range(len(product) - 1, self.degree - 1, -1):
                    coeff = product[k] % self.p
                    if coeff:
                        for j, mod_coeff in enumerate(self.modulus[:-1]):
                            product[k - self.degree + j] = (
                                product[k - self.degree + j] - coeff * mod_coeff
                            ) % self.p
                self.mul[a][b] = coeffs_to_int(product[: self.degree], self.p)


class ModularRing:
    def __init__(self, modulus: int) -> None:
        self.q = modulus
        self.add = [[(a + b) % modulus for b in range(modulus)] for a in range(modulus)]
        self.mul = [[(a * b) % modulus for b in range(modulus)] for a in range(modulus)]


Poly = tuple[tuple[tuple[int, int], int], ...]
DiffVector = tuple[Poly, ...]


def add_poly(poly: dict[tuple[int, int], int], other: dict[tuple[int, int], int], scale: int = 1) -> dict[tuple[int, int], int]:
    result = dict(poly)
    for key, value in other.items():
        result[key] = result.get(key, 0) + scale * value
        if result[key] == 0:
            del result[key]
    return result


def shift_poly(poly: dict[tuple[int, int], int], da: int, db: int) -> dict[tuple[int, int], int]:
    return {(a_degree + da, b_degree + db): coeff for (a_degree, b_degree), coeff in poly.items()}


def canon_poly(poly: dict[tuple[int, int], int]) -> Poly:
    return tuple(sorted(poly.items()))


def term_polynomial_vector(tokens: tuple[str, ...]) -> list[dict[tuple[int, int], int]]:
    stack: list[list[dict[tuple[int, int], int]]] = []
    for token in tokens:
        if token == "+":
            right = stack.pop()
            left = stack.pop()
            stack.append(
                [
                    add_poly(shift_poly(left[i], 1, 0), shift_poly(right[i], 0, 1))
                    for i in range(len(VARS))
                ]
            )
        else:
            vector = [{} for _ in VARS]
            vector[VAR_INDEX[token]][(0, 0)] = 1
            stack.append(vector)
    return stack[0]


def equation_difference_vectors(
    equations: list[tuple[tuple[str, ...], tuple[str, ...], str]],
) -> list[DiffVector]:
    differences = []
    for lhs, rhs, _ in equations:
        lhs_vector = term_polynomial_vector(lhs)
        rhs_vector = term_polynomial_vector(rhs)
        differences.append(
            tuple(
                canon_poly(add_poly(lhs_vector[i], rhs_vector[i], -1))
                for i in range(len(VARS))
            )
        )
    return differences


def zero_bitset(poly: Poly, field: FiniteField, pairs: list[tuple[int, int]]) -> int:
    if not poly:
        return (1 << len(pairs)) - 1

    max_degree = max(max(a_degree, b_degree) for (a_degree, b_degree), _ in poly)
    powers = [[0] * field.q for _ in range(max_degree + 1)]
    for value in range(field.q):
        powers[0][value] = 1
    for degree in range(1, max_degree + 1):
        for value in range(field.q):
            powers[degree][value] = field.mul[powers[degree - 1][value]][value]

    bits = 0
    for index, (a, b) in enumerate(pairs):
        total = 0
        for (a_degree, b_degree), coeff in poly:
            scalar = coeff % field.p
            if scalar == 0:
                continue
            monomial = field.mul[powers[a_degree][a]][powers[b_degree][b]]
            total = field.add[total][field.mul[scalar][monomial]]
        if total == 0:
            bits |= 1 << index
    return bits


def coefficient_vector(tokens: tuple[str, ...], field: FiniteField, a: int, b: int) -> tuple[int, ...]:
    stack: list[tuple[int, ...]] = []
    for token in tokens:
        if token == "+":
            right = stack.pop()
            left = stack.pop()
            stack.append(
                tuple(
                    field.add[field.mul[a][left[i]]][field.mul[b][right[i]]]
                    for i in range(len(VARS))
                )
            )
        else:
            vector = [0] * len(VARS)
            vector[VAR_INDEX[token]] = 1
            stack.append(tuple(vector))
    return stack[0]


def residual_vector(
    equation: tuple[tuple[str, ...], tuple[str, ...], str],
    ring: ModularRing,
    a: int,
    b: int,
) -> tuple[int, ...]:
    lhs, rhs, _ = equation
    lhs_vector = coefficient_vector(lhs, ring, a, b)
    rhs_vector = coefficient_vector(rhs, ring, a, b)
    return tuple((left - right) % ring.q for left, right in zip(lhs_vector, rhs_vector))


def verify_z81_witnesses(
    equations: list[tuple[tuple[str, ...], tuple[str, ...], str]],
) -> list[dict[str, object]]:
    ring = ModularRing(81)
    checks = [
        {"a": 3, "b": 79, "satisfies": 3102, "refutes": 2936},
        {"a": 4, "b": 78, "satisfies": 412, "refutes": 617},
    ]
    results = []
    for check in checks:
        a = int(check["a"])
        b = int(check["b"])
        satisfies = int(check["satisfies"])
        refutes = int(check["refutes"])
        sat_residual = residual_vector(equations[satisfies - 1], ring, a, b)
        refute_residual = residual_vector(equations[refutes - 1], ring, a, b)
        results.append(
            {
                "modulus": 81,
                "a": a,
                "b": b,
                "satisfies": satisfies,
                "satisfies_text": equations[satisfies - 1][2],
                "satisfies_residual_lhs_minus_rhs": dict(zip(VARS, sat_residual)),
                "satisfies_verified": all(value == 0 for value in sat_residual),
                "refutes": refutes,
                "refutes_text": equations[refutes - 1][2],
                "refutes_residual_lhs_minus_rhs": dict(zip(VARS, refute_residual)),
                "refutes_verified": any(value != 0 for value in refute_residual),
            }
        )
    return results


def scan_field(
    spec: FieldSpec,
    equations: list[tuple[tuple[str, ...], tuple[str, ...], str]],
) -> tuple[FiniteField, dict[int, tuple[int, int]], int]:
    field = FiniteField(spec)
    equation_count = len(equations)
    pairs = [(a, b) for a in range(spec.q) for b in range(spec.q)]

    difference_vectors = equation_difference_vectors(equations)
    poly_index: dict[Poly, int] = {}
    polynomials: list[Poly] = []
    for vector in difference_vectors:
        for poly in vector:
            if poly not in poly_index:
                poly_index[poly] = len(polynomials)
                polynomials.append(poly)

    zero_sets = [zero_bitset(poly, field, pairs) for poly in polynomials]
    all_pairs = (1 << len(pairs)) - 1
    satisfied_by_pair = [0] * len(pairs)

    for index, vector in enumerate(difference_vectors):
        pair_bits = all_pairs
        for poly in vector:
            pair_bits &= zero_sets[poly_index[poly]]

        while pair_bits:
            low_bit = pair_bits & -pair_bits
            pair_index = low_bit.bit_length() - 1
            pair_bits -= low_bit
            satisfied_by_pair[pair_index] |= 1 << index

    patterns: dict[int, tuple[int, int]] = {}
    for pair_index, satisfied in enumerate(satisfied_by_pair):
        patterns.setdefault(satisfied, pairs[pair_index])

    all_equations = (1 << equation_count) - 1
    anti_implications = 0
    for satisfied in patterns:
        refuted = all_equations ^ satisfied
        bits = satisfied
        while bits:
            low_bit = bits & -bits
            index = low_bit.bit_length() - 1
            bits -= low_bit
            anti_implications |= refuted << (index * equation_count)

    return field, patterns, anti_implications


def first_pairs(bits: int, equation_count: int, limit: int) -> list[tuple[int, int]]:
    pairs = []
    while bits and len(pairs) < limit:
        low_bit = bits & -bits
        position = low_bit.bit_length() - 1
        bits -= low_bit
        pairs.append((position // equation_count + 1, position % equation_count + 1))
    return pairs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--example-limit", type=int, default=10)
    parser.add_argument(
        "--verify-z81-witnesses",
        action="store_true",
        help="verify the Z/81Z witness pairs cited in research.md",
    )
    args = parser.parse_args()

    raw_equations = fetch_json("tools/fme/src/eqdb.json")
    raw_unknowns = fetch_json("home_page/fme/unknowns.json")
    equations = [
        (tuple(item["lhs"]), tuple(item["rhs"]), item["eqn"])
        for item in raw_equations
    ]
    equation_count = len(equations)

    if args.verify_z81_witnesses:
        print(
            json.dumps(
                {
                    "etp_commit": ETP_COMMIT,
                    "z81_witnesses": verify_z81_witnesses(equations),
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    dashboard_unknowns = 0
    for item in raw_unknowns:
        lhs = equation_id(item.get("lhs"), equation_count)
        rhs = equation_id(item.get("rhs"), equation_count)
        if lhs is not None and rhs is not None:
            dashboard_unknowns |= 1 << ((lhs - 1) * equation_count + rhs - 1)

    prime_specs = [
        FieldSpec(q, q, 1)
        for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79)
    ]
    extension_specs = [
        FieldSpec(4, 2, 2),
        FieldSpec(8, 2, 3),
        FieldSpec(9, 3, 2),
        FieldSpec(16, 2, 4),
        FieldSpec(25, 5, 2),
        FieldSpec(27, 3, 3),
        FieldSpec(32, 2, 5),
        FieldSpec(49, 7, 2),
        FieldSpec(64, 2, 6),
        FieldSpec(81, 3, 4),
    ]

    prime_union = 0
    prime_summary = []
    for spec in prime_specs:
        _, patterns, anti_implications = scan_field(spec, equations)
        prime_union |= anti_implications
        prime_summary.append(
            {
                "q": spec.q,
                "patterns": len(patterns),
                "prime_union_anti_implications": prime_union.bit_count(),
            }
        )

    extension_union = 0
    extension_summary = []
    pattern_store: dict[int, dict[int, tuple[int, int]]] = {}
    for spec in extension_specs:
        field, patterns, anti_implications = scan_field(spec, equations)
        pattern_store[spec.q] = patterns
        extension_union |= anti_implications
        extension_summary.append(
            {
                "q": spec.q,
                "modulus": field.modulus,
                "patterns": len(patterns),
                "anti_implications": anti_implications.bit_count(),
                "new_vs_prime_fields_le_81": (anti_implications & ~prime_union).bit_count(),
                "dashboard_unknown_intersection": (anti_implications & dashboard_unknowns).bit_count(),
            }
        )

    new_extension_pairs = extension_union & ~prime_union
    examples = []
    for lhs, rhs in first_pairs(new_extension_pairs, equation_count, args.example_limit):
        witnesses = []
        for spec in extension_specs:
            for satisfied, coeffs in pattern_store[spec.q].items():
                if ((satisfied >> (lhs - 1)) & 1) and not ((satisfied >> (rhs - 1)) & 1):
                    witnesses.append({"q": spec.q, "a": coeffs[0], "b": coeffs[1]})
                    break
        examples.append(
            {
                "satisfies": lhs,
                "refutes": rhs,
                "witnesses": witnesses,
                "dashboard_unknown": bool(
                    (dashboard_unknowns >> ((lhs - 1) * equation_count + rhs - 1)) & 1
                ),
                "satisfies_text": equations[lhs - 1][2],
                "refutes_text": equations[rhs - 1][2],
            }
        )

    print(
        json.dumps(
            {
                "etp_commit": ETP_COMMIT,
                "equation_count": equation_count,
                "dashboard_unknown_count": dashboard_unknowns.bit_count(),
                "prime_fields_le_81": prime_summary,
                "prime_union_anti_implications": prime_union.bit_count(),
                "extension_fields": extension_summary,
                "extension_union_anti_implications": extension_union.bit_count(),
                "extension_new_vs_prime_fields_le_81": new_extension_pairs.bit_count(),
                "extension_dashboard_unknown_intersection": (extension_union & dashboard_unknowns).bit_count(),
                "examples_new_vs_prime_fields_le_81": examples,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
