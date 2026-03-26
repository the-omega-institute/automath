#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Verify and export the 1-parameter weighted determinant Delta(z,u) for real-input-40.

We weight only the output bit e via u = exp(theta_e), with theta_neg=theta_2=0.

This script numerically checks that:
  det(I - z M(u)) == Delta_closed(z,u)
for a small set of (u,z) samples, and writes a JSON report.

Outputs (default):
- artifacts/export/sync_kernel_real_input_40_zeta_u.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir
from common_phi_fold import Progress
from exp_sync_kernel_real_input_40 import build_kernel_edges, build_kernel_map, build_real_input_states, build_weighted_matrix


@dataclass(frozen=True)
class Sample:
    u: float
    z: float


def delta_closed(z: float, u: float) -> float:
    # Delta(z,u) = (1-uz^2) * Q(z,u)
    z2 = z * z
    z3 = z2 * z
    z4 = z2 * z2
    z5 = z4 * z
    z6 = z3 * z3
    z7 = z6 * z
    z8 = z4 * z4

    q = (
        1.0
        - z
        - 6.0 * u * z2
        + 2.0 * u * z3
        + (9.0 * u * u - u) * z4
        + (u - 3.0 * u * u) * z5
        - (u * u * u + 2.0 * u * u) * z6
        + (4.0 * u * u * u - 3.0 * u * u) * z7
        + (u * u * u - u * u * u * u) * z8
    )
    return (1.0 - u * z2) * q


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
    parser = argparse.ArgumentParser(description="Verify Delta(z,u) for real-input-40 output-bit weighting")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_real_input_40_zeta_u.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="real-input-40-zeta-u", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    # Hand-picked stable samples (avoid z near poles).
    samples: List[Sample] = [
        Sample(u=0.7, z=0.05),
        Sample(u=0.7, z=0.12),
        Sample(u=1.0, z=0.12),
        Sample(u=1.3, z=0.08),
        Sample(u=1.7, z=0.06),
        Sample(u=2.0, z=0.05),
    ]

    rows: List[Dict[str, float]] = []
    max_abs = 0.0
    max_rel = 0.0

    for k, s in enumerate(samples, start=1):
        theta_e = math.log(s.u)
        M = build_weighted_matrix(theta_e, 0.0, 0.0, states, kernel_map)
        dn = det_numeric(M, s.z)
        dc = float(delta_closed(s.z, s.u))
        err = abs(dn - dc)
        rel = err / max(1.0, abs(dn))
        max_abs = max(max_abs, err)
        max_rel = max(max_rel, rel)
        rows.append({"u": s.u, "z": s.z, "det_numeric": dn, "delta_closed": dc, "abs_err": err, "rel_err": rel})
        prog.tick(f"sample {k}/{len(samples)}")

    payload: Dict[str, object] = {
        "formula": "Delta(z,u)=(1-uz^2)*(1-z-6uz^2+2uz^3+(9u^2-u)z^4+(u-3u^2)z^5-(u^3+2u^2)z^6+(4u^3-3u^2)z^7+(u^3-u^4)z^8)",
        "samples": rows,
        "max_abs_err": max_abs,
        "max_rel_err": max_rel,
    }

    if not args.no_output:
        out = Path(args.output) if args.output else export_dir() / "sync_kernel_real_input_40_zeta_u.json"
        write_json(out, payload)
        print(f"[real-input-40-zeta-u] wrote {out}", flush=True)

    print(f"[real-input-40-zeta-u] max_abs_err={max_abs:.3g} max_rel_err={max_rel:.3g}", flush=True)
    print("[real-input-40-zeta-u] done", flush=True)


if __name__ == "__main__":
    main()

