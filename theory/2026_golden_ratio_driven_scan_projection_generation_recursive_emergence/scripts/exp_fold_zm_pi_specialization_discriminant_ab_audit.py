#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the rational specialization discriminant formula for the quartic Pi(lambda,y).

This script is English-only by repository convention.

We verify:
  - Disc_lambda(Pi(lambda,y)) = -y(y-1) P_LY(y),
    where P_LY(y) = 256 y^3 + 411 y^2 + 165 y + 32.
  - For y0=a/b (gcd(a,b)=1, b>0), the cleared-denominator quartic
        P_{a,b}(lambda) = b^2 * Pi(lambda, a/b)  in Z[lambda]
    has discriminant
        Disc_lambda(P_{a,b})
          = -a(a-b)(256a^3+411a^2 b+165 a b^2+32 b^3) * b^7.
  - Deterministic numeric spot checks on a set of (a,b) pairs.

Outputs:
  - artifacts/export/fold_zm_pi_specialization_discriminant_ab_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _deterministic_pairs(max_pairs: int) -> List[Tuple[int, int]]:
    pairs: List[Tuple[int, int]] = []
    # A deterministic enumeration (b>0) for reproducibility.
    for b in range(1, 60):
        for a in range(-60, 61):
            if math.gcd(a, b) != 1:
                continue
            pairs.append((a, b))
            if len(pairs) >= max_pairs:
                return pairs
    return pairs


@dataclass(frozen=True)
class Payload:
    disc_pi_ok: bool
    disc_ab_symbolic_ok: bool
    numeric_pairs_tested: int
    numeric_failures_head: List[Dict[str, object]]
    seconds: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit discriminant formula for P_{a,b}(lambda)=b^2*Pi(lambda,a/b).")
    parser.add_argument("--max-pairs", type=int, default=80, help="Max deterministic (a,b) pairs to test (default: 80).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-pi-specialization-disc-ab] start", flush=True)

    lam, y, a, b = sp.symbols("lam y a b")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32

    # --- Disc_lambda(Pi) ---
    disc_pi = sp.factor(sp.discriminant(Pi, lam))
    disc_pi_expected = -y * (y - 1) * P_LY
    disc_pi_ok = bool(sp.factor(disc_pi - disc_pi_expected) == 0)

    # --- Symbolic specialization formula via Disc scaling ---
    disc_ab_expected = -a * (a - b) * (256 * a**3 + 411 * a**2 * b + 165 * a * b**2 + 32 * b**3) * b**7
    disc_ab_from_disc_pi = sp.together((b**12) * disc_pi_expected.subs({y: a / b}))
    diff = sp.together(disc_ab_from_disc_pi - disc_ab_expected)
    num, den = diff.as_numer_denom()
    disc_ab_symbolic_ok = bool(sp.factor(num) == 0)

    # --- Deterministic numeric checks ---
    failures: List[Dict[str, object]] = []
    pairs = _deterministic_pairs(int(args.max_pairs))
    for aa, bb in pairs:
        y0 = sp.Rational(int(aa), int(bb))
        Pab = sp.expand((bb**2) * Pi.subs({y: y0}))
        disc_num = int(sp.discriminant(Pab, lam))
        disc_exp = int(disc_ab_expected.subs({a: int(aa), b: int(bb)}))
        if disc_num != disc_exp:
            failures.append(
                {
                    "a": int(aa),
                    "b": int(bb),
                    "disc_sympy": int(disc_num),
                    "disc_expected": int(disc_exp),
                }
            )
            if len(failures) >= 10:
                break

    dt = time.time() - t0
    payload = Payload(
        disc_pi_ok=bool(disc_pi_ok),
        disc_ab_symbolic_ok=bool(disc_ab_symbolic_ok),
        numeric_pairs_tested=int(len(pairs)),
        numeric_failures_head=failures,
        seconds=float(dt),
    )

    if not args.no_output:
        out = export_dir() / "fold_zm_pi_specialization_discriminant_ab_audit.json"
        _write_json(out, asdict(payload))
        print(f"[fold-zm-pi-specialization-disc-ab] wrote {out}", flush=True)

    print(
        "[fold-zm-pi-specialization-disc-ab] checks:"
        f" disc_pi={disc_pi_ok} disc_ab_symbolic={disc_ab_symbolic_ok} numeric_ok={len(failures)==0}"
        f" pairs={len(pairs)} seconds={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-pi-specialization-disc-ab] done", flush=True)


if __name__ == "__main__":
    main()

