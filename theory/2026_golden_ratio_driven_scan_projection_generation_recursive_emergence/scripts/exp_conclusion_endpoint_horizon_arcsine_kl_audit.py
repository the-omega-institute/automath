#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the closed-form KL divergence between arcsine endpoint-horizon densities.

We verify numerically:
  D_KL(f_a || f_b) = arcosh(b/a) = log((b + sqrt(b^2-a^2))/a),   0<a<=b,
where f_a(x) = 1_{|x|<a} / (pi * sqrt(a^2 - x^2)).

Output:
  - artifacts/export/conclusion_endpoint_horizon_arcsine_kl_audit.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _dkl_arcsine_numeric(a: mp.mpf, b: mp.mpf, U: mp.mpf) -> mp.mpf:
    """Compute D_KL(f_a || f_b) via a truncated u-substitution integral."""
    if not (a > 0 and b >= a):
        raise ValueError("Require 0<a<=b")
    if not (U > 0):
        raise ValueError("Require U>0")

    # Map u ∈ (-∞,∞) to θ ∈ (-π/2, π/2) via θ = (π/2) tanh u.
    # We integrate on [-U,U]; tails decay exponentially.
    def integrand_u(u: mp.mpf) -> mp.mpf:
        theta = (mp.pi / 2) * mp.tanh(u)
        s = mp.sin(theta)
        c = mp.cos(theta)
        jac = (mp.pi / 2) * (mp.sech(u) ** 2)
        return mp.log((b * b - a * a * s * s) / (a * a * c * c)) * jac

    return (mp.quad(integrand_u, [-U, U]) / (2 * mp.pi))


def _dkl_arcsine_closed(a: mp.mpf, b: mp.mpf) -> mp.mpf:
    return mp.acosh(b / a)


@dataclass(frozen=True)
class Payload:
    mp_dps: int
    test_pairs: List[Tuple[float, float]]
    max_abs_error: float
    mean_abs_error: float
    max_window_delta: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit KL closed form for arcsine endpoint-horizon densities.")
    parser.add_argument("--dps", type=int, default=120, help="mpmath decimal precision.")
    parser.add_argument("--U", type=str, default="12.0", help="Truncation window for u-integration.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    mp.mp.dps = int(args.dps)
    U = mp.mpf(str(args.U))

    # Deterministic test grid: include near-degenerate and separated scales.
    pairs = [
        (mp.mpf("1"), mp.mpf("1")),
        (mp.mpf("1"), mp.mpf("1.0001")),
        (mp.mpf("1"), mp.mpf("1.1")),
        (mp.mpf("1"), mp.mpf("2")),
        (mp.mpf("1"), mp.mpf("10")),
        (mp.mpf("0.3"), mp.mpf("0.9")),
        (mp.mpf("2.5"), mp.mpf("7.5")),
    ]

    errs: List[mp.mpf] = []
    window_deltas: List[mp.mpf] = []
    for a, b in pairs:
        d_u = _dkl_arcsine_numeric(a, b, U)
        d_u2 = _dkl_arcsine_numeric(a, b, U + 2)
        window_deltas.append(abs(d_u2 - d_u))
        d_num = d_u2
        d_cl = _dkl_arcsine_closed(a, b)
        errs.append(abs(d_num - d_cl))

    max_err = max(errs) if errs else mp.mpf("0")
    mean_err = (mp.fsum(errs) / len(errs)) if errs else mp.mpf("0")

    payload = Payload(
        mp_dps=int(args.dps),
        test_pairs=[(float(a), float(b)) for (a, b) in pairs],
        max_abs_error=float(max_err),
        mean_abs_error=float(mean_err),
        max_window_delta=float(max(window_deltas) if window_deltas else mp.mpf("0")),
    )

    # Conservative numerical thresholds (integration + truncation).
    if max_err > mp.mpf("1e-9"):
        raise AssertionError(f"max abs error too large: {max_err}")
    if payload.max_window_delta > 1e-8:
        raise AssertionError(f"window truncation delta too large: {payload.max_window_delta}")

    if not args.no_output:
        out = export_dir() / "conclusion_endpoint_horizon_arcsine_kl_audit.json"
        _write_json(out, asdict(payload))

    print(
        "[conclusion-endpoint-horizon-arcsine-kl-audit] "
        f"max_abs_error={payload.max_abs_error:.3e} mean_abs_error={payload.mean_abs_error:.3e}",
        flush=True,
    )


if __name__ == "__main__":
    main()

