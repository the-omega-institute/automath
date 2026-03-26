#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Verify and export the 2-parameter weighted determinant Delta(z;u,v) for real-input-40.

We weight:
  - collisions (d=2) via u = exp(theta_2),
  - output bit (e=1) via v = exp(theta_e),
and set theta_neg = 0.

Closed form (appendix):
  Δ(z;u,v) = det(I - z M_{u,v}) = (v z^2 - 1) * P8(z;u,v),
with P8(z;u,v) an explicit degree-8 polynomial in z over Z[u,v].

This script numerically checks det(I - z M_{u,v}) against the closed form on a small
set of (u,v,z) samples, and writes a JSON report.

Outputs (default):
- artifacts/export/sync_kernel_real_input_40_zeta_uv.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

import numpy as np

from common_paths import export_dir
from common_phi_fold import Progress
from exp_sync_kernel_real_input_40 import (
    build_kernel_edges,
    build_kernel_map,
    build_real_input_states,
    build_weighted_matrix,
)


@dataclass(frozen=True)
class Sample:
    u: float  # collision weight (d=2)
    v: float  # output weight (e=1)
    z: float


def _P8(z: float, u: float, v: float) -> float:
    z2 = z * z
    z3 = z2 * z
    z4 = z2 * z2
    z5 = z4 * z
    z6 = z3 * z3
    z7 = z6 * z
    z8 = z4 * z4
    return (
        (u * u * v**4 - u * u * v**3) * z8
        + (-u * u * v**3 - 3.0 * u * v**3 + 3.0 * u * v**2) * z7
        + (u * u * v**3 - u * u * v**2 + 3.0 * u * v**2) * z6
        + (u * u * v**2 + 4.0 * u * v**2 - u * v - 2.0 * v**2) * z5
        + (-3.0 * u * v**2 + u * v - 6.0 * v**2) * z4
        + (-u * v - v) * z3
        + (u * v + 5.0 * v) * z2
        + z
        - 1.0
    )


def delta_closed(z: float, u: float, v: float) -> float:
    return (v * z * z - 1.0) * _P8(z, u, v)


def det_numeric(M: np.ndarray, z: float) -> float:
    n = M.shape[0]
    sign, logabs = np.linalg.slogdet(np.eye(n) - z * M)
    if sign == 0:
        return 0.0
    return float(sign) * float(math.exp(float(logabs)))


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify Delta(z;u,v) for real-input-40 collision/output weighting")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_real_input_40_zeta_uv.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="real-input-40-zeta-uv", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    # Hand-picked stable samples (avoid z near poles; keep weights moderate).
    samples: List[Sample] = [
        Sample(u=0.7, v=0.8, z=0.06),
        Sample(u=0.7, v=1.3, z=0.05),
        Sample(u=1.0, v=0.9, z=0.07),
        Sample(u=1.4, v=1.2, z=0.05),
        Sample(u=1.7, v=1.7, z=0.04),
        Sample(u=2.2, v=0.8, z=0.06),
    ]

    rows: List[Dict[str, float]] = []
    max_abs = 0.0
    max_rel = 0.0

    for k, s in enumerate(samples, start=1):
        if s.u <= 0 or s.v <= 0:
            raise ValueError("u and v must be positive for the weighted kernel.")
        theta_e = math.log(s.v)  # v weights e=1
        theta_2 = math.log(s.u)  # u weights d=2
        M = build_weighted_matrix(theta_e, 0.0, theta_2, states, kernel_map)
        dn = det_numeric(M, s.z)
        dc = float(delta_closed(s.z, s.u, s.v))
        err = abs(dn - dc)
        rel = err / max(1.0, abs(dn))
        max_abs = max(max_abs, err)
        max_rel = max(max_rel, rel)
        rows.append(
            {
                "u": s.u,
                "v": s.v,
                "z": s.z,
                "det_numeric": dn,
                "delta_closed": dc,
                "abs_err": err,
                "rel_err": rel,
            }
        )
        prog.tick(f"sample {k}/{len(samples)}")

    payload: Dict[str, object] = {
        "formula": "Delta(z;u,v)=(v z^2-1)*P8(z;u,v) with P8 degree-8 polynomial (see appendix)",
        "samples": rows,
        "max_abs_err": max_abs,
        "max_rel_err": max_rel,
    }

    if not args.no_output:
        out = Path(args.output) if args.output else export_dir() / "sync_kernel_real_input_40_zeta_uv.json"
        write_json(out, payload)
        print(f"[real-input-40-zeta-uv] wrote {out}", flush=True)

    print(f"[real-input-40-zeta-uv] max_abs_err={max_abs:.3g} max_rel_err={max_rel:.3g}", flush=True)
    print("[real-input-40-zeta-uv] done", flush=True)


if __name__ == "__main__":
    main()

