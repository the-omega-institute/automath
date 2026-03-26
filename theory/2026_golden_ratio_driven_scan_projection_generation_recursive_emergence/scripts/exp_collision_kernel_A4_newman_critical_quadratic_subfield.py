#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Quadratic discriminant subfield of the A4 edge-weight RH threshold certificate P_4(t),
and the class number of Q(sqrt{-1151}).

Context (paper-local):
  - The edge-weight RH threshold t_* is certified by the degree-8 integer polynomial
    P_4(t) in sections/generated/eq_collision_kernel_A4_edge_weight_threshold.tex.
  - Its (polynomial) discriminant determines a canonical quadratic subfield of the
    splitting field via sqrt(Disc_t(P_4)).

This script:
  1) Computes Disc_t(P_4) exactly and extracts its squarefree part (should be -1151).
  2) Computes the class number h(Q(sqrt{-1151})) exactly by enumerating reduced
     primitive positive definite binary quadratic forms of discriminant -1151.

Outputs:
  - artifacts/export/collision_kernel_A4_newman_critical_quadratic_subfield.json
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


def _poly_P4() -> sp.Poly:
    t = sp.Symbol("t")
    P4 = (
        t**8
        - 10 * t**7
        + 72 * t**6
        - 24 * t**5
        - 1924 * t**4
        - 2904 * t**3
        + 1312 * t**2
        + 1464 * t
        - 1412
    )
    return sp.Poly(P4, t)


def _squarefree_part_from_factorint(fac: Dict[int, int]) -> int:
    out = 1
    for p, e in fac.items():
        if e % 2 == 1:
            out *= int(p)
    return int(out)


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
    # Use a safe integer bound.
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
    # P4 discriminant data
    disc_P4: str
    disc_P4_factorization: Dict[str, int]
    disc_P4_squarefree_part: int
    # quadratic field data
    quadratic_field_discriminant: int
    class_number: int
    is_prime_class_number: bool
    reduced_forms: List[Tuple[int, int, int]]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compute the discriminant quadratic subfield for P_4(t) and h(Q(sqrt{-1151}))."
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_newman_critical_quadratic_subfield.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    poly = _poly_P4()
    t = poly.gens[0]
    disc = sp.discriminant(poly, t)
    disc_int = int(disc)
    fac = sp.factorint(disc_int)
    sqfree = _squarefree_part_from_factorint(fac)

    D = -1151
    forms = _reduced_primitive_forms_negative_discriminant(D)
    h = len(forms)

    payload = Payload(
        disc_P4=str(disc_int),
        disc_P4_factorization={str(int(p)): int(e) for p, e in fac.items()},
        disc_P4_squarefree_part=int(sqfree),
        quadratic_field_discriminant=int(D),
        class_number=int(h),
        is_prime_class_number=sp.isprime(h) is True,
        reduced_forms=forms,
    )

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[A4-newman-critical-quadratic-subfield] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

