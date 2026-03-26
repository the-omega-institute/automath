#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit discriminant factorizations for the node-elimination quintic A5 and the secondary-degeneracy quintic Q5.

This script is English-only by repository convention.

We certify:
  - Disc(A5) factorization in Z.
  - Disc(Q5) factorization in Z (cross-check against the manuscript fingerprint).
  - The common squarefree kernel, hence the common quadratic discriminant subfield in the S5 splitting field.

Outputs:
  - artifacts/export/fold_zm_delta_a5_discriminant_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _squarefree_kernel(disc: int, fac: Dict[int, int]) -> int:
    """Return sf(disc) as a signed squarefree integer."""
    sf = -1 if disc < 0 else 1
    for p, e in fac.items():
        if e % 2 == 1:
            sf *= p
    return int(sf)


@dataclass(frozen=True)
class Payload:
    a5_coeffs_high_to_low: List[int]
    disc_a5: int
    disc_a5_factorization: Dict[int, int]
    sf_disc_a5: int
    q5_coeffs_high_to_low: List[int]
    disc_q5: int
    disc_q5_factorization: Dict[int, int]
    sf_disc_q5: int
    seconds: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Disc(A5), Disc(Q5), and their squarefree kernels.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-delta-a5-discriminant] start", flush=True)

    T = sp.Symbol("T")
    y = sp.Symbol("y")

    A5 = sp.Poly(
        4096 * T**5 - 47360 * T**4 + 186992 * T**3 - 231939 * T**2 - 200880 * T + 482112,
        T,
        domain=sp.ZZ,
    )
    Q5 = sp.Poly(
        4096 * y**5 + 5376 * y**4 - 464 * y**3 - 2749 * y**2 - 723 * y + 80,
        y,
        domain=sp.ZZ,
    )

    disc_a5 = int(sp.discriminant(A5.as_expr(), T))
    disc_q5 = int(sp.discriminant(Q5.as_expr(), y))
    fac_a5 = {int(p): int(e) for p, e in sp.factorint(abs(disc_a5)).items()}
    fac_q5 = {int(p): int(e) for p, e in sp.factorint(abs(disc_q5)).items()}

    sf_a5 = _squarefree_kernel(disc_a5, fac_a5)
    sf_q5 = _squarefree_kernel(disc_q5, fac_q5)

    seconds = time.time() - t0

    payload = Payload(
        a5_coeffs_high_to_low=[int(c) for c in A5.all_coeffs()],
        disc_a5=disc_a5,
        disc_a5_factorization=fac_a5,
        sf_disc_a5=sf_a5,
        q5_coeffs_high_to_low=[int(c) for c in Q5.all_coeffs()],
        disc_q5=disc_q5,
        disc_q5_factorization=fac_q5,
        sf_disc_q5=sf_q5,
        seconds=seconds,
    )

    # Expected fingerprints recorded in the manuscript.
    expected_a5 = {2: 42, 3: 11, 11: 2, 31: 1, 307: 2, 727: 1}
    expected_q5 = {2: 28, 3: 9, 11: 2, 31: 3, 727: 1}
    assert disc_a5 < 0 and disc_q5 < 0
    assert fac_a5 == expected_a5
    assert fac_q5 == expected_q5
    assert sf_a5 == -67611
    assert sf_q5 == -67611

    if not args.no_output:
        _write_json(export_dir() / "fold_zm_delta_a5_discriminant_audit.json", asdict(payload))

    print(f"[fold-zm-delta-a5-discriminant] ok seconds={seconds:.3f}", flush=True)


if __name__ == "__main__":
    main()

