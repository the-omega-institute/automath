#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Hankel certificates for fold gauge anomaly mean/variance (exact).

We certify the two integer-normalized sequences appearing in the paper:

  B_int(m) := 2^{m+1} E[G_m]      (mean normalization),
  V(m)     := 2^{2m+2} Var(G_m]   (variance normalization).

Both are computed from the closed forms stated in:
  - subsubsec__fold-gauge-anomaly-uniform-baseline-finite-length-moment-closures.tex

We then compute exact Hankel witness determinants:
  det H^{(5)}_ell(B_int)  and  det H^{(13)}_ell(V),
verify the geometric scaling laws, and factor det H^{(13)}_0(V).

Outputs:
  - artifacts/export/fold_gauge_anomaly_hankel_mean_variance_certificates.json
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


def _barG(m: int) -> sp.Rational:
    mm = sp.Integer(m)
    return sp.simplify(
        sp.Rational(4, 9) * mm
        - sp.Rational(29, 54)
        + sp.Rational(5, 8) * sp.Rational(1, 2) ** mm
        + (sp.Rational(mm, 36) - sp.Rational(19, 216)) * (-sp.Rational(1, 2)) ** mm
    )


def _varG(m: int) -> sp.Rational:
    mm = sp.Integer(m)
    term1 = sp.Rational(118, 243) * mm - sp.Rational(635, 2916)
    term2 = (sp.Rational(43, 54) - sp.Rational(125, 144) * mm) * sp.Rational(1, 2) ** mm
    term3 = (
        -sp.Rational(1, 648) * mm**3
        + sp.Rational(1, 81) * mm**2
        + sp.Rational(173, 1296) * mm
        - sp.Rational(47, 162)
    ) * (-sp.Rational(1, 2)) ** mm
    term4 = (
        -sp.Rational(1, 1296) * mm**2
        + sp.Rational(19, 3888) * mm
        - sp.Rational(9293, 23328)
    ) * sp.Rational(1, 4) ** mm
    term5 = (-sp.Rational(5, 144) * mm + sp.Rational(95, 864)) * (-sp.Rational(1, 4)) ** mm
    return sp.simplify(term1 + term2 + term3 + term4 + term5)


def B_int(m: int) -> sp.Integer:
    v = sp.simplify((sp.Integer(2) ** (m + 1)) * _barG(m))
    if not v.is_Integer:
        raise AssertionError(f"B_int({m}) not integer: {v}")
    return sp.Integer(v)


def V(m: int) -> sp.Integer:
    v = sp.simplify((sp.Integer(4) ** (m + 1)) * _varG(m))
    if not v.is_Integer:
        raise AssertionError(f"V({m}) not integer: {v}")
    return sp.Integer(v)


def hankel_det(seq, size: int, ell: int) -> sp.Integer:
    H = sp.Matrix([[seq(ell + i + j) for j in range(size)] for i in range(size)])
    return sp.Integer(H.det())


def _to_factor_dict(d: Dict[sp.Integer, int]) -> Dict[str, int]:
    out: Dict[str, int] = {}
    for k, v in d.items():
        out[str(int(k))] = int(v)
    return out


def main() -> None:
    # Basic value tables (small prefix).
    B_vals: List[int] = [int(B_int(i)) for i in range(0, 15)]
    V_vals: List[int] = [int(V(i)) for i in range(0, 15)]

    det5_0 = hankel_det(B_int, size=5, ell=0)
    det5_1 = hankel_det(B_int, size=5, ell=1)
    det5_2 = hankel_det(B_int, size=5, ell=2)

    det13_0 = hankel_det(V, size=13, ell=0)
    det13_1 = hankel_det(V, size=13, ell=1)

    out = {
        "B_int_prefix": B_vals,
        "V_prefix": V_vals,
        "det_H5": {
            "det0": int(det5_0),
            "det1": int(det5_1),
            "det2": int(det5_2),
            "ratio_det1_det0": int(sp.simplify(sp.Rational(det5_1, det5_0))),
            "ratio_det2_det1": int(sp.simplify(sp.Rational(det5_2, det5_1))),
            "factor_det0": _to_factor_dict(sp.factorint(det5_0)),
        },
        "det_H13": {
            "det0": int(det13_0),
            "det1": int(det13_1),
            "ratio_det1_det0": int(sp.simplify(sp.Rational(det13_1, det13_0))),
            "factor_det0": _to_factor_dict(sp.factorint(det13_0)),
        },
    }

    out_path: Path = export_dir() / "fold_gauge_anomaly_hankel_mean_variance_certificates.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {out_path}")


if __name__ == "__main__":
    main()

