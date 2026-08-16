"""Minimal exact replay of the Laurent constant-term recurrence.

Run from the paper root:

    python certificates/laurent_recurrence_minicheck.py
    python certificates/laurent_recurrence_minicheck.py 2 6
    python certificates/laurent_recurrence_minicheck.py 2,3,3

This is a compact independent audit of the deterministic recurrence in the
manuscript: it builds the all-sign Laurent coefficients q_{n,k}, iterates the
finite dictionary recurrence for C_j(s), and returns exact constant terms for
arbitrary requested rows.  With no row argument it checks the rows used through
total order eight.  It uses only Python standard-library exact rational
arithmetic.
"""

import argparse
from collections import defaultdict
from fractions import Fraction as F
from math import comb

Z, ONE, I = (F(0), F(0)), (F(1), F(0)), (F(0), F(1))
ROWS = [
    (2, 2), (2, 3), (2, 4), (3, 3), (2, 2, 2),
    (2, 5), (3, 4), (2, 2, 3),
    (2, 6), (3, 5), (4, 4), (2, 2, 4), (2, 3, 3), (2, 2, 2, 2),
]
EXPECTED = {
    (2, 2): (F(1, 4), 0), (2, 3): Z, (2, 4): (-F(1, 8), 0),
    (3, 3): (F(3, 16), 0), (2, 2, 2): (-F(3, 32), 0),
    (2, 5): Z, (3, 4): Z, (2, 2, 3): Z,
    (2, 6): (F(3, 64), 0), (3, 5): (-F(15, 128), 0),
    (4, 4): (F(5, 32), 0), (2, 2, 4): (F(3, 32), 0),
    (2, 3, 3): (-F(9, 128), 0), (2, 2, 2, 2): (F(9, 64), 0),
}


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(a, c):
    return a[0] * c, a[1] * c


def lam(n):
    if n % 2 == 0:
        return F((-1) ** (n // 2), 2**n), F(0)
    return scale((F(0), F(-1)), F((-1) ** ((n - 1) // 2), 2**n))


def eps(n, k):
    return 1 if n % 2 == 0 or k > 0 else -1


def q(n, k):
    return scale(lam(n), eps(n, k) * comb(n - 1, abs(k) - 1))


def constant_term(row):
    c = {0: ONE}
    for n in row:
        d = defaultdict(lambda: Z)
        for s, a in c.items():
            for k in list(range(-n, 0)) + list(range(1, n + 1)):
                d[s + k] = add(d[s + k], mul(a, q(n, k)))
        c = {s: a for s, a in d.items() if a != Z}
    return c.get(0, Z)


def integer_recurrence(row, weight):
    c = {0: 1}
    for n in row:
        d = defaultdict(int)
        for s, a in c.items():
            for k in list(range(-n, 0)) + list(range(1, n + 1)):
                d[s + k] += a * weight(n, k)
        c = {s: a for s, a in d.items() if a}
    return c.get(0, 0)


def fmt(z):
    re, im = z
    if im == 0:
        return str(re)
    if re == 0:
        return f"{im}i"
    sign = "+" if im > 0 else "-"
    return f"{re}{sign}{abs(im)}i"


def parse_rows(raw_rows):
    if not raw_rows:
        return []
    if len(raw_rows) == 1 and "," in raw_rows[0]:
        return [tuple(int(part) for part in raw_rows[0].split(",") if part)]
    return [tuple(int(part) for part in raw_rows)]


def print_row(row):
    value = constant_term(row)
    count = integer_recurrence(row, lambda n, k: 1)
    signed = integer_recurrence(row, lambda n, k: eps(n, k) * comb(n - 1, abs(k) - 1))
    print(f"{row!s:14s} |K|={count:2d} signed={signed:3d} J={fmt(value)}")


def main():
    parser = argparse.ArgumentParser(
        description="Exact rational Laurent constant-term recurrence."
    )
    parser.add_argument(
        "row",
        nargs="*",
        help="row as space-separated integers, or one comma-separated row such as 2,3,3",
    )
    args = parser.parse_args()
    requested = parse_rows(args.row)

    if requested:
        for row in requested:
            if not row or any(n <= 0 for n in row):
                raise SystemExit(f"invalid row: {row}")
            print_row(row)
        return

    for row in ROWS:
        value = constant_term(row)
        assert value == EXPECTED[row], f"{row}: got {value}, expected {EXPECTED[row]}"
        print_row(row)

    print("All Laurent recurrence rows through total order eight verified exactly.")


if __name__ == "__main__":
    main()
