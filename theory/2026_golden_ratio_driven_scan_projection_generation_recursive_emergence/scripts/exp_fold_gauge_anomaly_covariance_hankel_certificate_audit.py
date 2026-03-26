#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit distribution-moment representation and Hankel certificate at p=1/2.

We verify:
  - covariance closed form c_k (k>=1),
  - distribution nu = (1/8)delta_{1/2} + (7/648)delta_{-1/2} + (1/216)delta'_{-1/2}
    reproduces c_k moments,
  - det(H^(3)) = -1/2985984 and det(H^(4)) = 0 for H^(r)=(c_{i+j+1}).

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import paper_root, scripts_dir


def c_k(k: int) -> sp.Rational:
    if k < 1:
        raise ValueError("k must be >= 1")
    return sp.Rational(1, 2) ** k * (
        sp.Rational(1, 8)
        + (-1) ** k * (sp.Rational(7, 648) + sp.Rational(k, 108))
    )


def moment_nu(k: int) -> sp.Rational:
    """
    nu = a delta_{1/2} + b delta_{-1/2} + c delta'_{-1/2}.
    <delta_a, x^k> = a^k, <delta'_a, x^k> = -k a^{k-1}.
    """
    a = sp.Rational(1, 2)
    b = -sp.Rational(1, 2)
    w1 = sp.Rational(1, 8)
    w2 = sp.Rational(7, 648)
    w3 = sp.Rational(1, 216)
    return w1 * (a**k) + w2 * (b**k) + w3 * (-(k) * (b ** (k - 1)))


def hankel_det(r: int) -> sp.Rational:
    H = sp.Matrix([[c_k(i + j + 1) for j in range(r)] for i in range(r)])
    return sp.nsimplify(H.det())


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit p=1/2 covariance distribution and Hankel certificate.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "fold_gauge_anomaly_covariance_hankel_certificate_audit.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    # Moment checks for a reasonable range
    ks = list(range(1, 21))
    moment_ok = all(sp.simplify(c_k(k) - moment_nu(k)) == 0 for k in ks)

    det3 = hankel_det(3)
    det4 = hankel_det(4)

    out: Dict[str, object] = {
        "moment_check": {
            "k_range": ks,
            "ok": bool(moment_ok),
        },
        "hankel": {
            "det_H3": str(det3),
            "det_H4": str(det4),
        },
        "meta": {"script": Path(__file__).name, "scripts_dir": str(scripts_dir())},
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Hard assertions for pipeline gating
    assert moment_ok, "Distribution-moment representation failed on k=1..20"
    assert det3 == -sp.Rational(1, 2985984), "det(H^(3)) mismatch"
    assert det4 == 0, "det(H^(4)) expected 0"


if __name__ == "__main__":
    main()

