#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Quadratic field from the discriminant of the A4 characteristic polynomial p_7(x),
and the class number of Q(sqrt{-985219}).

Context (paper-local):
  - In subsec__pom-s4.tex, the A4 collision kernel has characteristic polynomial
      p_7(x) = x^5 - 2 x^4 - 7 x^3 - 2 x + 2.
  - Its polynomial discriminant satisfies Disc_x(p_7) = -2^4 * 985219.
    The squarefree part (with sign) is therefore -985219, giving a canonical
    quadratic field Q(sqrt{-985219}) attached to the minimal recurrence at q=4.

This script:
  1) Computes Disc_x(p_7) exactly and extracts its squarefree part.
  2) Computes the class number h(Q(sqrt{-985219})) by enumerating reduced primitive
     positive definite binary quadratic forms of the fundamental discriminant.

Outputs:
  - artifacts/export/collision_kernel_A4_charpoly_quadratic_field_class_number.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _poly_p7() -> sp.Poly:
    x = sp.Symbol("x")
    p7 = x**5 - 2 * x**4 - 7 * x**3 - 2 * x + 2
    return sp.Poly(p7, x)


def _squarefree_part_from_factorint(fac: Dict[int, int]) -> int:
    out = 1
    for p, e in fac.items():
        if e % 2 == 1:
            out *= int(p)
    return int(out)


def _quadratic_field_fundamental_discriminant(squarefree_radicand: int) -> int:
    """
    For a squarefree integer n, return the (fundamental) discriminant of Q(sqrt{n}).
    """
    n = int(squarefree_radicand)
    # For n squarefree: Disc(Q(sqrt{n})) is n if n ≡ 1 (mod 4), else 4n.
    return n if (n % 4 == 1) else 4 * n


def _reduced_primitive_forms_negative_discriminant(D: int) -> List[Tuple[int, int, int]]:
    """
    Enumerate reduced primitive positive definite binary quadratic forms (a,b,c)
    of discriminant D<0.

    For negative fundamental discriminant D, the number of reduced primitive forms
    equals the class number h(D).
    """
    if D >= 0:
        raise ValueError("Expected a negative discriminant D<0.")
    if D % 4 not in (0, 1):
        raise ValueError("Expected a discriminant D congruent to 0 or 1 mod 4.")

    # Reduction bounds: for reduced positive definite forms, a <= sqrt(|D|/3).
    max_a = int(math.isqrt(abs(D) // 3 + 1))
    parity = D & 1  # b ≡ D (mod 2)

    forms: List[Tuple[int, int, int]] = []
    for a in range(1, max_a + 1):
        for b in range(-a, a + 1):
            if (b - parity) & 1:
                continue
            disc_term = b * b - D
            denom = 4 * a
            if disc_term % denom != 0:
                continue
            c = disc_term // denom

            # Reduced conditions: |b| <= a <= c, with tie-breaker.
            if abs(b) > a:
                continue
            if a > c:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue

            # Primitive (gcd=1).
            if math.gcd(a, math.gcd(b, c)) != 1:
                continue

            forms.append((a, b, c))

    return forms


@dataclass(frozen=True)
class Payload:
    # polynomial discriminant data
    disc_p7: str
    disc_p7_factorization: Dict[str, int]
    disc_p7_squarefree_part: int
    # quadratic field data
    quadratic_radicand: int
    quadratic_field_discriminant: int
    class_number: int
    class_number_factorization: Dict[str, int]
    reduced_forms: List[Tuple[int, int, int]]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compute Disc_x(p_7), its squarefree part, and h(Q(sqrt{-985219}))."
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_charpoly_quadratic_field_class_number.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    poly = _poly_p7()
    x = poly.gens[0]
    disc = sp.discriminant(poly, x)
    disc_int = int(disc)
    fac = sp.factorint(disc_int)
    sqfree = _squarefree_part_from_factorint(fac)

    n = int(sqfree)
    D = _quadratic_field_fundamental_discriminant(n)
    if D >= 0:
        raise RuntimeError(f"Expected an imaginary quadratic field discriminant, got D={D}.")

    forms = _reduced_primitive_forms_negative_discriminant(D)
    h = int(len(forms))
    h_fac = {str(int(p)): int(e) for p, e in sp.factorint(h).items()}

    payload = Payload(
        disc_p7=str(disc_int),
        disc_p7_factorization={str(int(p)): int(e) for p, e in fac.items()},
        disc_p7_squarefree_part=int(sqfree),
        quadratic_radicand=int(n),
        quadratic_field_discriminant=int(D),
        class_number=int(h),
        class_number_factorization=h_fac,
        reduced_forms=forms,
    )

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[A4-charpoly-quadratic-field-class-number] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

