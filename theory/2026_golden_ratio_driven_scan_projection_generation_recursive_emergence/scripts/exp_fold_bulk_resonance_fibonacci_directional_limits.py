#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Directional limits for the bulk resonance ladder along Fibonacci-type recurrences.

We audit two explicit limit constants implied by the Fibonacci-directional factorization:

  C_phi(F_n) -> |cos(pi/sqrt(5))| * Π_{k=1}^∞ |cos(pi / (sqrt(5) * phi^k))|^2
  C_phi(L_n) -> Π_{k=1}^∞ |cos(pi * phi^{-k})|^2

Outputs:
  - artifacts/export/fold_bulk_resonance_fibonacci_directional_limits.json
  - sections/generated/eq_fold_bulk_resonance_fibonacci_directional_limits_numeric.tex
  - sections/generated/eq_fold_bulk_resonance_fib_luc_log_lower_bound_numeric.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI


SQRT5 = 5.0**0.5


def _tex_float(x: float, nd: int = 16) -> str:
    s = f"{x:.{nd}f}"
    s = s.rstrip("0").rstrip(".")
    if s == "-0":
        s = "0"
    return s


def _safe_log_abs_cos_pi(x: float) -> float:
    """Return log(|cos(pi * x)|) with basic safeguards."""
    c = abs(math.cos(math.pi * x))
    if c == 0.0:
        return float("-inf")
    return float(math.log(c))


def c_phi_fib_limit_partial(k_max: int) -> float:
    """Partial product for the Fibonacci-directional limit constant (k<=k_max)."""
    if k_max < 1:
        raise ValueError("k_max must be >= 1")
    alpha = 1.0 / SQRT5
    s = _safe_log_abs_cos_pi(alpha)  # |cos(pi/sqrt(5))|
    for k in range(1, k_max + 1):
        s += 2.0 * _safe_log_abs_cos_pi(alpha * (PHI ** (-k)))
    if math.isinf(s) and s < 0:
        return 0.0
    return float(math.exp(s))


def c_phi_luc_limit_partial(k_max: int) -> float:
    """Partial product for the Lucas-directional limit constant (k<=k_max)."""
    if k_max < 1:
        raise ValueError("k_max must be >= 1")
    s = 0.0
    for k in range(1, k_max + 1):
        s += 2.0 * _safe_log_abs_cos_pi(PHI ** (-k))
    if math.isinf(s) and s < 0:
        return 0.0
    return float(math.exp(s))


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit directional limit constants for C_phi(F_n) and C_phi(L_n) (LaTeX + JSON)."
    )
    parser.add_argument(
        "--k-max",
        type=int,
        default=200,
        help="Partial product cutoff K for k>=1 factors.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_bulk_resonance_fibonacci_directional_limits.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(
            generated_dir() / "eq_fold_bulk_resonance_fibonacci_directional_limits_numeric.tex"
        ),
        help="Output TeX equation fragment path.",
    )
    parser.add_argument(
        "--tex-log-lb-out",
        type=str,
        default=str(
            generated_dir() / "eq_fold_bulk_resonance_fib_luc_log_lower_bound_numeric.tex"
        ),
        help="Output TeX fragment for the strengthened logarithmic lower-bound constants.",
    )
    args = parser.parse_args()

    k_max = int(args.k_max)
    if k_max < 1:
        raise SystemExit("Require --k-max >= 1")

    # A few checkpoints to show convergence vs K.
    checkpoints = [1, 2, 3, 5, 10, 20, 50, 100, k_max]
    seen = set()
    checkpoints_uniq: List[int] = []
    for k in checkpoints:
        if 1 <= k <= k_max and k not in seen:
            checkpoints_uniq.append(int(k))
            seen.add(k)

    fib_vals: Dict[str, float] = {}
    luc_vals: Dict[str, float] = {}
    for k in checkpoints_uniq:
        fib_vals[str(k)] = float(c_phi_fib_limit_partial(k))
        luc_vals[str(k)] = float(c_phi_luc_limit_partial(k))

    C_fib = float(fib_vals[str(k_max)])
    C_luc = float(luc_vals[str(k_max)])
    log_phi = float(math.log(PHI))
    log_lower_bound_sum = float((C_fib * C_fib + C_luc * C_luc) / log_phi)
    log_lower_bound_sigma = float(2.0 * log_lower_bound_sum)

    payload: Dict[str, Any] = {
        "definition": {
            "phi": float(PHI),
            "C_phi_Fib": "|cos(pi/sqrt(5))| * prod_{k=1..inf} |cos(pi/(sqrt(5)*phi^k))|^2",
            "C_phi_Luc": "prod_{k=1..inf} |cos(pi*phi^{-k})|^2",
            "method": "partial_product_log_domain",
        },
        "partial_product": {
            "k_max": int(k_max),
            "checkpoints": checkpoints_uniq,
            "C_phi_Fib_at_K": fib_vals,
            "C_phi_Luc_at_K": luc_vals,
        },
        "approx": {
            "C_phi_Fib": float(C_fib),
            "C_phi_Luc": float(C_luc),
            "log_lower_bound_sum_constant": float(log_lower_bound_sum),
            "log_lower_bound_sigma_constant": float(log_lower_bound_sigma),
            "difference_Fib_minus_Luc": float(C_fib - C_luc),
            "ratio_Fib_over_Luc": float(C_fib / C_luc) if C_luc != 0.0 else float("inf"),
        },
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold_bulk_resonance_fibonacci_directional_limits.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(
        "C_{\\varphi,\\mathrm{Fib}}^{(\\le "
        + str(k_max)
        + ")}"
        + ":=\\Bigl|\\cos\\!\\Bigl(\\frac{\\pi}{\\sqrt5}\\Bigr)\\Bigr|"
        + "\\prod_{k=1}^{"
        + str(k_max)
        + "}\\Bigl|\\cos\\!\\Bigl(\\frac{\\pi}{\\sqrt5\\,\\varphi^{k}}\\Bigr)\\Bigr|^{2}"
        + f"&\\approx {_tex_float(C_fib, 16)},\\\\"
    )
    lines.append(
        "C_{\\varphi,\\mathrm{Luc}}^{(\\le "
        + str(k_max)
        + ")}"
        + ":=\\prod_{k=1}^{"
        + str(k_max)
        + "}\\Bigl|\\cos\\bigl(\\pi\\varphi^{-k}\\bigr)\\Bigr|^{2}"
        + f"&\\approx {_tex_float(C_luc, 16)}."
    )
    lines.append("\\end{aligned}")
    lines.append("\\]")

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")

    lines_log_lb: List[str] = []
    lines_log_lb.append("% AUTO-GENERATED by scripts/exp_fold_bulk_resonance_fibonacci_directional_limits.py")
    lines_log_lb.append("\\[")
    lines_log_lb.append("\\begin{aligned}")
    lines_log_lb.append(
        "\\frac{c_{\\mathrm{Fib}}^2+c_{\\mathrm{Luc}}^2}{\\log\\varphi}"
        + f"&\\approx {_tex_float(log_lower_bound_sum, 18)},\\\\"
    )
    lines_log_lb.append(
        "\\frac{2(c_{\\mathrm{Fib}}^2+c_{\\mathrm{Luc}}^2)}{\\log\\varphi}"
        + f"&\\approx {_tex_float(log_lower_bound_sigma, 18)}."
    )
    lines_log_lb.append("\\end{aligned}")
    lines_log_lb.append("\\]")

    tlog = Path(args.tex_log_lb_out)
    tlog.parent.mkdir(parents=True, exist_ok=True)
    tlog.write_text("\n".join(lines_log_lb) + "\n", encoding="utf-8")

    print(f"[fold-bulk-resonance-fib-directional-limits] wrote {jout}", flush=True)
    print(f"[fold-bulk-resonance-fib-directional-limits] wrote {tout}", flush=True)
    print(f"[fold-bulk-resonance-fib-directional-limits] wrote {tlog}", flush=True)


if __name__ == "__main__":
    main()

