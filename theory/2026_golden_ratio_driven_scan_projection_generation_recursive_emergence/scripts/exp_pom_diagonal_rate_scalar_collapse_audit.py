#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the scalar-collapse parameterization (overlap amplitude A) and the scaling-duality
representation for the diagonal-coupling rate function R_w(delta).

This script is English-only by repository convention.

We numerically verify (for a fixed full-support example w):
  - For each kappa>0, the fixed point A = Phi_kappa(A) exists uniquely and yields a valid
    coupling P_kappa with marginals w and Z=1.
  - The map kappa -> delta(kappa) = 1 - sum_x P_kappa(x,x) is strictly decreasing.
  - For each delta in (0, delta0), solving the scalar-collapse yields (A,kappa,u) satisfying
      kappa = (1-A^2)/(A^2-delta)
    and the closed 1D rate formula
      R_w(delta) = 2 sum_x w log(u/w) + (1-delta) log(1+kappa).
  - The scaling-duality objective
      L(kappa) = 2H(w) - G_kappa(w) + (1-delta) log(1+kappa)
    is maximized at the kappa recovered from delta.

Outputs:
  - artifacts/export/pom_diagonal_rate_scalar_collapse_audit.json
  - sections/generated/eq_pom_diagonal_rate_scalar_collapse_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import mpmath as mp

from common_diagonal_rate import ScalarCollapseSolution, delta0_from_w, entropy, solve_A_for_kappa, solve_scalar_collapse
from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class KappaRow:
    kappa: str
    A: str
    delta: str


@dataclass(frozen=True)
class DeltaRow:
    delta_in: str
    A: str
    kappa: str
    delta_out: str
    R: str
    kappa_from_A_delta: str
    fixed_residual: str
    marginal_residual: str
    Z_residual: str
    dual_values: List[str]
    dual_kappas: List[str]


def _G_kappa_from_solution(w: List[mp.mpf], kappa: mp.mpf, A: mp.mpf, u: List[mp.mpf]) -> mp.mpf:
    # Canonical normalization (from fixed point): Z = (sum u)^2 + kappa sum u^2 = 1.
    # Then G_kappa(w) = log Z - 2 sum w log u = -2 sum w log u.
    return -2 * mp.fsum([wx * mp.log(ux) for wx, ux in zip(w, u)])


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit scalar-collapse parameterization for R_w(delta).")
    parser.add_argument("--dps", type=int, default=90, help="Decimal precision (default: 90).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 60:
        raise SystemExit("Require --dps >= 60 for stable outputs.")
    mp.mp.dps = dps

    t0 = time.time()
    print("[pom-diagonal-rate-scalar-collapse] start", flush=True)

    # Example full-support distribution (exact decimal sum=1).
    w = [mp.mpf("0.37"), mp.mpf("0.21"), mp.mpf("0.17"), mp.mpf("0.13"), mp.mpf("0.12")]
    d0 = delta0_from_w(w)

    # --- kappa -> delta monotone scan ---
    kappa_grid = [mp.mpf("1e-6"), mp.mpf("1e-3"), mp.mpf("1e-2"), mp.mpf("1e-1"), mp.mpf("1"), mp.mpf("10"), mp.mpf("1e3")]
    rows_k: List[KappaRow] = []
    deltas_scan: List[mp.mpf] = []
    for kk in kappa_grid:
        A, u = solve_A_for_kappa(w, kk, dps=dps)
        sum_u2 = mp.fsum([ux * ux for ux in u])
        delta_kk = mp.mpf(1) - (1 + kk) * sum_u2
        deltas_scan.append(delta_kk)
        rows_k.append(KappaRow(kappa=mp.nstr(kk, 25), A=mp.nstr(A, 25), delta=mp.nstr(delta_kk, 25)))

    monotone_ok = all(deltas_scan[i] > deltas_scan[i + 1] for i in range(len(deltas_scan) - 1))

    # --- delta -> (A,kappa,u) solve + dual checks ---
    delta_list = [mp.mpf("0.02"), mp.mpf("0.10"), mp.mpf("0.25")]
    rows_d: List[DeltaRow] = []
    H = entropy(w)

    for dd in delta_list:
        sol: ScalarCollapseSolution = solve_scalar_collapse(w, dd, dps=dps)
        k_from_A = (1 - sol.A * sol.A) / (sol.A * sol.A - sol.delta)
        Z_res = abs(sol.Z - 1)

        # Dual objective sampling around kappa*.
        dual_kappas: List[mp.mpf] = [sol.kappa / 4, sol.kappa / 2, sol.kappa, sol.kappa * 2, sol.kappa * 4]
        dual_values: List[mp.mpf] = []
        for kk in dual_kappas:
            A, u = solve_A_for_kappa(w, kk, dps=dps)
            G = _G_kappa_from_solution(w, kk, A, u)
            dual_values.append(2 * H - G + (1 - sol.delta) * mp.log(1 + kk))

        # Ensure maximum at the middle entry.
        dual_max_at_center = dual_values[2] >= max(dual_values[0], dual_values[1], dual_values[3], dual_values[4])

        rows_d.append(
            DeltaRow(
                delta_in=mp.nstr(dd, 25),
                A=mp.nstr(sol.A, 25),
                kappa=mp.nstr(sol.kappa, 25),
                delta_out=mp.nstr(sol.delta, 25),
                R=mp.nstr(sol.R, 25),
                kappa_from_A_delta=mp.nstr(k_from_A, 25),
                fixed_residual=mp.nstr(sol.max_fixed_point_residual, 10),
                marginal_residual=mp.nstr(sol.max_marginal_residual, 10),
                Z_residual=mp.nstr(Z_res, 10),
                dual_values=[mp.nstr(v, 25) for v in dual_values],
                dual_kappas=[mp.nstr(k, 25) for k in dual_kappas],
            )
        )

        if not dual_max_at_center:
            raise RuntimeError("Dual objective did not maximize at kappa*(delta) in the local sample.")

    payload = {
        "w": [mp.nstr(p, 25) for p in w],
        "delta0": mp.nstr(d0, 25),
        "kappa_scan": [asdict(r) for r in rows_k],
        "kappa_scan_monotone_decreasing_delta": bool(monotone_ok),
        "delta_solutions": [asdict(r) for r in rows_d],
    }

    if not args.no_output:
        out_json = export_dir() / "pom_diagonal_rate_scalar_collapse_audit.json"
        _write_json(out_json, payload)

        # TeX snippet: formulas + one numeric instantiation.
        ex = rows_d[0]
        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_pom_diagonal_rate_scalar_collapse_audit.py",
                "\\[",
                "u_{\\kappa,A}(x):=\\frac{\\sqrt{A^{2}+4\\kappa w(x)}-A}{2\\kappa},\\qquad A=\\sum_x u_{\\kappa,A}(x).",
                "\\]",
                "\\[",
                "R_w(\\delta)=2\\sum_x w(x)\\log\\frac{u(x)}{w(x)}+(1-\\delta)\\log(1+\\kappa),\\qquad \\kappa=\\frac{1-A^{2}}{A^{2}-\\delta}.",
                "\\]",
                "\\[",
                f"\\text{{Example: }}\\delta={ex.delta_in},\\ A\\approx {ex.A},\\ \\kappa\\approx {ex.kappa},\\ R_w(\\delta)\\approx {ex.R}.",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_pom_diagonal_rate_scalar_collapse_audit.tex"
        _write_text(out_tex, tex)

        print(f"[pom-diagonal-rate-scalar-collapse] wrote {out_json}", flush=True)
        print(f"[pom-diagonal-rate-scalar-collapse] wrote {out_tex}", flush=True)

    dt = time.time() - t0
    print(
        "[pom-diagonal-rate-scalar-collapse] checks:"
        f" monotone={monotone_ok} deltas={len(rows_d)} seconds={dt:.3f}",
        flush=True,
    )
    print("[pom-diagonal-rate-scalar-collapse] done", flush=True)


if __name__ == "__main__":
    main()

