#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Bulk resonance integer ladder C_phi(u) and partial Sigma_phi audits.

We study the integer-parametrized infinite products
  C_phi(u) := Π_{n=2}^∞ |cos(π u φ^{-n})|,  u ∈ Z,
which generalize the bulk resonance constant C_phi = C_phi(1).

This script evaluates truncated products (n<=N) in log domain, computes
partial sums
  Sigma_phi(U) := 1 + 2 Σ_{u=1}^U C_phi(u)^2
for selected checkpoints, and exports:
  - artifacts/export/fold_bulk_resonance_integer_ladder.json
  - sections/generated/eq_fold_bulk_resonance_integer_ladder_audit.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Dict, Iterable, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI


TWO_PI = 2.0 * math.pi


def _safe_log_abs_cos(x: float) -> float:
    """Return log(|cos(x)|) with basic numerical safeguards."""
    # Reduce argument to improve accuracy for large x.
    xr = math.remainder(x, TWO_PI)
    c = abs(math.cos(xr))
    if c == 0.0:
        return float("-inf")
    return math.log(c)


def log_c_phi_partial(u: int, n_max: int) -> float:
    """Compute log of the partial product Π_{n=2}^{n_max} |cos(π u φ^{-n})|."""
    if n_max < 2:
        raise ValueError("n_max must be >= 2")
    if u == 0:
        return 0.0
    s = 0.0
    for n in range(2, n_max + 1):
        x = math.pi * float(u) * (PHI ** (-n))
        t = _safe_log_abs_cos(x)
        if math.isinf(t) and t < 0:
            return float("-inf")
        s += t
    return float(s)


def c_phi_partial_from_log(logp: float) -> float:
    if math.isinf(logp) and logp < 0:
        return 0.0
    # Clamp extreme negatives to avoid underflow warnings.
    if logp < -750.0:
        return 0.0
    return float(math.exp(logp))


def _tex_float(x: float, nd: int = 16) -> str:
    s = f"{x:.{nd}f}"
    s = s.rstrip("0").rstrip(".")
    if s == "-0":
        s = "0"
    return s


def _default_checkpoints(u_max: int) -> List[int]:
    base = [1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1_000, 2_000, 5_000, 10_000]
    out = [u for u in base if u <= u_max]
    if u_max not in out:
        out.append(u_max)
    # Deduplicate while preserving order.
    seen = set()
    uniq: List[int] = []
    for u in out:
        if u not in seen:
            uniq.append(u)
            seen.add(u)
    return uniq


def _compute_sigma_checkpoints(
    n_max: int,
    u_max: int,
    checkpoints: Iterable[int],
) -> Tuple[Dict[int, float], Dict[int, float]]:
    """Return (C_phi_sq_prefix, Sigma_phi_at_checkpoints)."""
    checkpoints_sorted = sorted(set(int(u) for u in checkpoints))
    if not checkpoints_sorted:
        raise ValueError("checkpoints must be nonempty")
    if checkpoints_sorted[-1] > u_max:
        raise ValueError("all checkpoints must be <= u_max")

    # Prefix sums of C_phi(u)^2 for u=1..u_max.
    prefix: Dict[int, float] = {}
    sigma_at: Dict[int, float] = {}
    s = 0.0
    ck_idx = 0
    for u in range(1, u_max + 1):
        logc = log_c_phi_partial(u=u, n_max=n_max)
        c = c_phi_partial_from_log(logc)
        s += c * c
        if u in checkpoints_sorted:
            prefix[u] = s
            sigma_at[u] = 1.0 + 2.0 * s
            ck_idx += 1
            if ck_idx >= len(checkpoints_sorted):
                # All checkpoints reached; no need to continue.
                if u == checkpoints_sorted[-1]:
                    break
    return prefix, sigma_at


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compute C_phi(u) ladder (partial products) and Sigma_phi(U) partial sums (LaTeX + JSON)."
    )
    parser.add_argument(
        "--n-max",
        type=int,
        default=200,
        help="Partial product cutoff N (product starts at n=2).",
    )
    parser.add_argument(
        "--u-max",
        type=int,
        default=20000,
        help="Max integer u for Sigma_phi partial sums.",
    )
    parser.add_argument(
        "--store-u-max",
        type=int,
        default=30,
        help="Store C_phi(u) partial values for u<=store-u-max in outputs.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_bulk_resonance_integer_ladder.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_fold_bulk_resonance_integer_ladder_audit.tex"),
        help="Output TeX equation fragment path.",
    )
    args = parser.parse_args()

    n_max = int(args.n_max)
    u_max = int(args.u_max)
    store_u_max = int(args.store_u_max)
    if n_max < 2:
        raise SystemExit("Require --n-max >= 2")
    if u_max < 1:
        raise SystemExit("Require --u-max >= 1")
    if store_u_max < 0:
        raise SystemExit("Require --store-u-max >= 0")

    checkpoints = _default_checkpoints(u_max=u_max)
    _, sigma_at = _compute_sigma_checkpoints(
        n_max=n_max,
        u_max=u_max,
        checkpoints=checkpoints,
    )

    c_small: Dict[str, float] = {}
    logc_small: Dict[str, float] = {}
    for u in range(1, min(store_u_max, u_max) + 1):
        logc = log_c_phi_partial(u=u, n_max=n_max)
        c = c_phi_partial_from_log(logc)
        c_small[str(u)] = float(c)
        logc_small[str(u)] = float(logc) if not (math.isinf(logc) and logc < 0) else float("-inf")

    payload: Dict[str, Any] = {
        "definition": {
            "phi": float(PHI),
            "C_phi_u": "prod_{n=2..inf} |cos(pi * u * phi^{-n})|",
            "Sigma_phi_U": "1 + 2 * sum_{u=1..U} C_phi(u)^2",
            "method": "partial_product_log_domain",
        },
        "partial_product": {
            "n_max": n_max,
        },
        "sigma_partial": {
            "u_max": u_max,
            "checkpoints": checkpoints,
            "Sigma_phi_at_U": {str(U): float(sigma_at[U]) for U in checkpoints},
        },
        "C_phi_u_partial_small": {
            "u_max": min(store_u_max, u_max),
            "C_phi_u_partial": c_small,
            "log_C_phi_u_partial": logc_small,
        },
    }

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold_bulk_resonance_integer_ladder.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(
        "C_{\\varphi}(u)^{(\\le "
        + str(n_max)
        + ")}:=\\prod_{n=2}^{"
        + str(n_max)
        + "}\\bigl|\\cos(\\pi u\\,\\varphi^{-n})\\bigr|"
        + "\\qquad(u\\in\\ZZ),\\\\"
    )
    # Small ladder preview.
    if c_small:
        for u_str in list(c_small.keys())[: min(10, len(c_small))]:
            u = int(u_str)
            lines.append(f"C_{{\\varphi}}({u})^{{(\\le {n_max})}}&\\approx {_tex_float(c_small[u_str], 16)},\\\\")
    # Sigma checkpoints.
    lines.append(
        "\\Sigma_{\\varphi}^{(\\le "
        + str(u_max)
        + ")}:=1+2\\sum_{u=1}^{"
        + str(u_max)
        + "}\\bigl(C_{\\varphi}(u)^{(\\le "
        + str(n_max)
        + ")}\\bigr)^2,\\\\"
    )
    for U in checkpoints:
        lines.append(
            "\\Sigma_{\\varphi}^{(\\le "
            + str(U)
            + ")}"
            + f"&\\approx {_tex_float(sigma_at[U], 16)},\\\\"
        )
    if lines[-1].endswith("\\\\"):
        lines[-1] = lines[-1][:-2] + "."
    lines.append("\\end{aligned}")
    lines.append("\\]")

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"[fold-bulk-resonance-integer-ladder] wrote {jout}", flush=True)
    print(f"[fold-bulk-resonance-integer-ladder] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

