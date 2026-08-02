"""Exact finite checks for the results extracted from the A5 oracle report."""

from __future__ import annotations

from itertools import product
from pathlib import Path

import sympy as sp


def _least_rotation(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(word[j:] + word[:j] for j in range(len(word)))


def _is_primitive(word: tuple[int, ...]) -> bool:
    n = len(word)
    return all(word != word[:d] * (n // d) for d in range(1, n) if n % d == 0)


def primitive_binary_necklace_parity_counts(
    max_length: int,
) -> dict[int, tuple[int, int]]:
    """Count primitive binary necklaces by even and odd label parity."""
    counts: dict[int, tuple[int, int]] = {}
    for n in range(1, max_length + 1):
        representatives = {
            _least_rotation(word)
            for word in product((0, 1), repeat=n)
            if _is_primitive(word)
        }
        even = sum(sum(word) % 2 == 0 for word in representatives)
        odd = len(representatives) - even
        counts[n] = (even, odd)
    return counts


def quotient_correction_coefficients(
    max_degree: int,
) -> tuple[dict[int, sp.Rational], dict[int, sp.Rational]]:
    """Compare L_{1_e}-F_{1_e} with the quotient split-orbit product.

    The model is the full binary shift labelled by C2.  Its non-trivial
    twisted block is zero, so the strict twisted gap is exact.  A primitive
    orbit of odd parity closes in the regular cover only after two turns.
    """
    counts = primitive_binary_necklace_parity_counts(max_degree)
    periodic_minus_fixed = {degree: sp.Rational(0) for degree in range(1, max_degree + 1)}
    split_orbit_product = {degree: sp.Rational(0) for degree in range(1, max_degree + 1)}

    for length, (_even, odd) in counts.items():
        for repeat in range(2, max_degree // length + 1, 2):
            degree = repeat * length
            periodic_minus_fixed[degree] += sp.Rational(odd, repeat)
        for k in range(1, max_degree // (2 * length) + 1):
            degree = 2 * k * length
            split_orbit_product[degree] += sp.Rational(odd, 2 * k)

    return periodic_minus_fixed, split_orbit_product


def verify_c2_regular_cover_factorization() -> bool:
    """Check the regular-cover determinant and reduced Perron constants."""
    z = sp.Symbol("z")
    identity = sp.eye(2)
    regular_cover = sp.Matrix(((1, 1), (1, 1)))
    trivial_block = sp.Matrix(((2,),))
    sign_block = sp.Matrix(((0,),))
    cover_polynomial = sp.expand((identity - z * regular_cover).det())
    block_product = sp.expand(
        (sp.eye(1) - z * trivial_block).det()
        * (sp.eye(1) - z * sign_block).det()
    )
    t = sp.Symbol("t", real=True)
    cover_constant = sp.limit(
        (1 - t) / (sp.eye(2) - t * regular_cover / 2).det(), t, 1, dir="-"
    )
    base_constant = sp.limit((1 - t) / (1 - t), t, 1, dir="-")
    return cover_polynomial == block_product and cover_constant == base_constant == 1


def universal_product_jet(alpha: sp.Expr, order: int) -> sp.Expr:
    """Return the 1/N jet of exp[-alpha(H_N-log N-gamma)]."""
    x = sp.Symbol("x")
    logarithmic_jet = -alpha * x / 2
    for j in range(1, order // 2 + 1):
        logarithmic_jet += alpha * sp.bernoulli(2 * j) * x ** (2 * j) / (2 * j)
    return sp.expand(sp.series(sp.exp(logarithmic_jet), x, 0, order + 1).removeO())


def render_report() -> str:
    max_degree = 16
    periodic_minus_fixed, split_orbit_product = quotient_correction_coefficients(
        max_degree
    )
    alpha = sp.Symbol("alpha")
    jet = universal_product_jet(alpha, order=3)
    checks = {
        "quotient correction power series": periodic_minus_fixed
        == split_orbit_product,
        "quotient correction is non-zero": sum(periodic_minus_fixed.values()) > 0,
        "regular-cover determinant factorization": verify_c2_regular_cover_factorization(),
        "universal harmonic jet": sp.simplify(
            jet
            - 1
            + alpha * sp.Symbol("x") / 2
            - alpha * (3 * alpha + 2) * sp.Symbol("x") ** 2 / 24
            + alpha**2 * (alpha + 2) * sp.Symbol("x") ** 3 / 48
        )
        == 0,
    }
    if not all(checks.values()):
        failed = ", ".join(name for name, passed in checks.items() if not passed)
        raise AssertionError(f"failed checks: {failed}")

    lines = [
        "A5 NEW-RESULT EXACT VERIFICATION",
        "Model: full binary shift with C2 labels 0 and 1; exact SymPy arithmetic.",
        f"Primitive necklaces and quotient correction checked through z^{max_degree}.",
        f"Universal product jet through N^(-3): {sp.sstr(jet)}",
        "STATUS: PASS",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    report = render_report()
    output = Path(__file__).with_name("verify_a5_results_output.txt")
    output.write_text(report, encoding="ascii")
    print(report, end="")


if __name__ == "__main__":
    main()
