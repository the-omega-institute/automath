"""Verify the finite-group obstruction to a universal visible quotient."""

from __future__ import annotations

Element = tuple[int, int]


def add(x: Element, y: Element, n: int) -> Element:
    return ((x[0] + y[0]) % (n * n), (x[1] + y[1]) % n)


def scalar(k: int, x: Element, n: int) -> Element:
    return ((k * x[0]) % (n * n), (k * x[1]) % n)


def cyclic_subgroup(generator: Element, n: int) -> set[Element]:
    return {scalar(k, generator, n) for k in range(n * n)}


def n_multiples(n: int) -> set[Element]:
    return {scalar(n, (x, y), n) for x in range(n * n) for y in range(n)}


def subgroup_sum(left: set[Element], right: set[Element], n: int) -> set[Element]:
    return {add(x, y, n) for x in left for y in right}


def quotient_kills_extension_class(
    representative: Element, kernel: set[Element], n: int
) -> bool:
    """Test representative in kernel + nA, equivalent to vanishing in (A/N)/n(A/N)."""

    return representative in subgroup_sum(kernel, n_multiples(n), n)


def verify(n: int) -> None:
    if n < 2:
        raise ValueError("n must be at least 2")

    zero = (0, 0)
    representative = (0, 1)
    n0 = cyclic_subgroup((0, 1), n)
    n1 = cyclic_subgroup((n, 1), n)
    bad_kernel = cyclic_subgroup((1, 1), n)

    assert representative not in n_multiples(n), "the extension class must be nonzero"
    assert quotient_kills_extension_class(representative, n0, n)
    assert quotient_kills_extension_class(representative, n1, n)
    assert n0.intersection(n1) == {zero}
    assert not quotient_kills_extension_class(representative, {zero}, n)

    # Negative control: this nearby cyclic subgroup does not kill the class.
    assert not quotient_kills_extension_class(representative, bad_kernel, n)


def main() -> None:
    for n in range(2, 33):
        verify(n)
    print("verified the torsion obstruction for 2 <= n <= 32")


if __name__ == "__main__":
    main()
