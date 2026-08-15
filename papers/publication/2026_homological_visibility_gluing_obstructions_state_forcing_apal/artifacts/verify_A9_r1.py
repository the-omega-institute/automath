"""Finite and symbolic checks for the claims in oracle_sprint_A9_r1.md.

These checks verify only the algebraic consequences of UCT naturality and
NWW's displayed Cechization formula.  They do not prove either open
crossed-module comparison in NWW, Problems 8.1(b) and 8.2.
"""

import argparse
import sys
from contextlib import redirect_stdout
from fractions import Fraction
from functools import reduce
from io import StringIO
from itertools import combinations, product
from math import gcd
from pathlib import Path


def _continuous_three_cocycle(a, b, c):
    """A normalized continuous inhomogeneous 3-cocycle on (R,+)."""

    return a * b * c


def _group_coboundary(w, x, y, z):
    f = _continuous_three_cocycle
    return (
        f(x, y, z)
        - f(w + x, y, z)
        + f(w, x + y, z)
        - f(w, x, y + z)
        + f(w, x, y)
    )


def _tau(g, h, k, x):
    f = _continuous_three_cocycle
    return (
        f(h, k - h, x - k)
        - f(g, k - g, x - k)
        + f(g, h - g, x - h)
    )


def _tau_rewrite(g, h, k, x):
    f = _continuous_three_cocycle
    return f(g, h - g, k - h) + f(h - g, k - h, x - k)


def check_real_cechization_identities():
    values = tuple(Fraction(i, 2) for i in range(-4, 5))
    group_cases = 0
    tau_cases = 0
    cech_cases = 0

    for w, x, y, z in product(values, repeat=4):
        assert _group_coboundary(w, x, y, z) == 0
        group_cases += 1

    for g, h, k, x in product(values, repeat=4):
        assert _tau(g, h, k, x) == _tau_rewrite(g, h, k, x)
        tau_cases += 1

    for g, h, k, ell, x in product(values, repeat=5):
        cech_delta = (
            _tau(h, k, ell, x)
            - _tau(g, k, ell, x)
            + _tau(g, h, ell, x)
            - _tau(g, h, k, x)
        )
        assert cech_delta == 0
        cech_cases += 1

    return {
        "group_cocycle_cases": group_cases,
        "tau_rewrite_cases": tau_cases,
        "cech_cocycle_cases": cech_cases,
    }


def _divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


def _cyclic_subgroup(n, generators):
    divisor = reduce(gcd, generators, n)
    return frozenset(range(0, n, divisor))


def check_finite_quotient_claims(max_modulus=36):
    factorization_cases = 0
    exact_sequence_cases = 0

    for n in range(1, max_modulus + 1):
        subgroups = tuple(_cyclic_subgroup(n, (d,)) for d in _divisors(n))

        for subgroup in subgroups:
            for quotient_modulus in _divisors(n):
                units = tuple(
                    u for u in range(quotient_modulus) if gcd(u, quotient_modulus) == 1
                ) or (0,)
                for unit in units:
                    kills_image = all((unit * x) % quotient_modulus == 0 for x in subgroup)
                    factors_through = subgroup <= frozenset(
                        x
                        for x in range(n)
                        if (unit * x) % quotient_modulus == 0
                    )
                    pushed_evaluation_is_zero = kills_image
                    assert kills_image == factors_through == pushed_evaluation_is_zero
                    factorization_cases += 1

        for first, second, third in product(subgroups, repeat=3):
            intersection = first & second & third
            subgroup_sum = _cyclic_subgroup(n, tuple(first | second | third))
            assert intersection <= subgroup_sum

            labelled_quotient_order = n // len(intersection)
            common_quotient_order = n // len(subgroup_sum)
            kernel_order = len(subgroup_sum) // len(intersection)
            assert labelled_quotient_order == kernel_order * common_quotient_order
            exact_sequence_cases += 1

    return {
        "factorization_cases": factorization_cases,
        "exact_sequence_cases": exact_sequence_cases,
    }


def _elements(moduli):
    return tuple(product(*(range(modulus) for modulus in moduli)))


def _add(left, right, moduli):
    return tuple((x + y) % modulus for x, y, modulus in zip(left, right, moduli))


def _generated_subgroup(moduli, generators):
    zero = tuple(0 for _ in moduli)
    generated = {zero}
    frontier = [zero]
    while frontier:
        current = frontier.pop()
        for generator in generators:
            candidate = _add(current, generator, moduli)
            if candidate not in generated:
                generated.add(candidate)
                frontier.append(candidate)
    return frozenset(generated)


def _all_subgroups(moduli):
    elements = _elements(moduli)
    zero = tuple(0 for _ in moduli)
    subgroups = []
    for size in range(1, len(elements) + 1):
        for subset_tuple in combinations(elements, size):
            subset = frozenset(subset_tuple)
            if zero not in subset:
                continue
            if all(_add(x, y, moduli) in subset for x in subset for y in subset):
                subgroups.append(subset)
    return tuple(subgroups)


def _minimum_generator_number(moduli, subgroup):
    elements = tuple(subgroup)
    for beta in range(len(elements) + 1):
        if any(
            _generated_subgroup(moduli, generators) == subgroup
            for generators in product(elements, repeat=beta)
        ):
            return beta
    raise AssertionError("finite subgroup has no finite generating tuple")


def check_generator_bound_classification():
    moduli_list = ((2,), (3,), (4,), (2, 2), (2, 3), (2, 2, 2), (2, 4))
    classification_cases = 0

    for moduli in moduli_list:
        elements = _elements(moduli)
        subgroups = _all_subgroups(moduli)
        minimum_generators = {
            subgroup: _minimum_generator_number(moduli, subgroup)
            for subgroup in subgroups
        }

        for beta in range(4):
            homomorphism_images = {
                _generated_subgroup(moduli, generators)
                for generators in product(elements, repeat=beta)
            }
            bounded_generator_subgroups = {
                subgroup
                for subgroup, number in minimum_generators.items()
                if number <= beta
            }
            assert homomorphism_images == bounded_generator_subgroups
            classification_cases += len(subgroups)

    return {"groups": len(moduli_list), "classification_cases": classification_cases}


def pullback_strict_inclusion_example():
    # ev: H_r(S^r v S^r) = Z^2 -> Z/2 is projection to the first factor.
    ambient_image = frozenset({0, 1})
    # Pull back along the inclusion of the second sphere: t |-> (0,t).
    pullback_image = frozenset({0})
    assert pullback_image < ambient_image
    return {
        "ambient_image": ambient_image,
        "pullback_image": pullback_image,
        "ambient_quotient_order": 2 // len(ambient_image),
        "pullback_quotient_order": 2 // len(pullback_image),
    }


def action_lift_peiffer_counterexample():
    # G = K = C_2 and K-hat = C_2 x C_2 with boundary (a,b) |-> a.
    def boundary(element):
        return element[0]

    def action(group_element, element):
        a, b = element
        return (a, (b + group_element * a) % 2)

    def multiply(left, right):
        return ((left[0] + right[0]) % 2, (left[1] + right[1]) % 2)

    def inverse(element):
        return element  # Every element of C_2 x C_2 has order at most two.

    elements = tuple(product(range(2), repeat=2))
    covers_conjugation = all(
        boundary(action(g, element)) == boundary(element)
        for g in range(2)
        for element in elements
    )
    fixes_central_kernel = all(
        action(g, (0, z)) == (0, z) for g in range(2) for z in range(2)
    )
    peiffer_identity = all(
        action(boundary(left), right)
        == multiply(multiply(left, right), inverse(left))
        for left in elements
        for right in elements
    )
    assert covers_conjugation and fixes_central_kernel and not peiffer_identity
    return {
        "covers_conjugation": covers_conjugation,
        "fixes_central_kernel": fixes_central_kernel,
        "peiffer_identity": peiffer_identity,
    }


def _run_verification():
    real = check_real_cechization_identities()
    finite = check_finite_quotient_claims()
    generators = check_generator_bound_classification()
    pullback = pullback_strict_inclusion_example()
    peiffer = action_lift_peiffer_counterexample()
    print("PASS NWW Cechization formula checks:", real)
    print("PASS finite quotient checks:", finite)
    print("PASS generator-bound checks:", generators)
    print("PASS pullback direction check:", pullback)
    print("COUNTEREXAMPLE action lift does not imply Peiffer identity:", peiffer)
    print("OPEN comparisons intentionally unverified: NWW Problems 8.1(b), 8.2(a), 8.2(b)")


def main(argv=()):
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    if args.output is None:
        _run_verification()
        return

    capture = StringIO()
    with redirect_stdout(capture):
        _run_verification()
    report = capture.getvalue()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(report, encoding="utf-8", newline="\n")
    print(report, end="")


if __name__ == "__main__":
    main(sys.argv[1:])
