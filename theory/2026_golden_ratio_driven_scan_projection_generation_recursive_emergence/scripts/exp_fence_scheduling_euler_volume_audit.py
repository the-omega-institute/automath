#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fence scheduling / Euler zigzag / volume audit.

We audit the fence poset Z_n (zigzag):
  1 < 2 > 3 < 4 > ...

Key identities audited on finite windows:
  - e(Z_n) (linear extensions) equals the Euler zigzag number E_n with EGF
        sec z + tan z = sum_{n>=0} E_n z^n / n!
  - vol(O(Z_n)) = e(Z_n) / n! (order polytope volume identity)
  - (1/n) log(E_n / n!) -> log(2/pi)

Outputs:
  - artifacts/export/fence_scheduling_euler_volume_audit.json
  - sections/generated/tab_fence_scheduling_euler_volume_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir, generated_dir


def euler_zigzag_numbers(n_max: int) -> List[int]:
    """Return [E_0,...,E_{n_max}] using the EGF sec z + tan z."""
    n_max = int(n_max)
    if n_max < 0:
        raise ValueError("n_max must be >= 0")
    z = sp.Symbol("z")
    expr = sp.sec(z) + sp.tan(z)
    ser = sp.series(expr, z, 0, n_max + 1).removeO().expand()
    out: List[int] = []
    for n in range(0, n_max + 1):
        coeff = sp.expand(ser).coeff(z, n)  # coefficient of z^n
        En = sp.factorial(n) * coeff
        En = sp.Integer(En)
        if En < 0:
            raise AssertionError("Euler number should be nonnegative")
        out.append(int(En))
    return out


def fence_pred_masks(n: int) -> List[int]:
    """Predecessor masks for Z_n on elements {0,...,n-1}."""
    n = int(n)
    pred = [0] * n
    for i in range(0, n - 1):
        a = i
        b = i + 1
        # In 1-based: if (i+1) is odd then (i+1) < (i+2), else (i+2) < (i+1).
        if (i + 1) % 2 == 1:
            # a < b
            pred[b] |= 1 << a
        else:
            # b < a
            pred[a] |= 1 << b
    return pred


def count_linear_extensions(pred: List[int]) -> int:
    """Count linear extensions by subset DP, O(n*2^n)."""
    n = len(pred)
    dp = [0] * (1 << n)
    dp[0] = 1
    for mask in range(1 << n):
        cur = dp[mask]
        if cur == 0:
            continue
        for i in range(n):
            if (mask >> i) & 1:
                continue
            if pred[i] & ~mask:
                continue
            dp[mask | (1 << i)] += cur
    return int(dp[(1 << n) - 1])


@dataclass(frozen=True)
class Row:
    n: int
    E_n: int
    e_linext: int
    vol: float
    log_density: float
    target: float
    abs_err: float
    ok: bool

    def to_dict(self) -> Dict[str, object]:
        return {
            "n": int(self.n),
            "E_n": int(self.E_n),
            "e_linext": int(self.e_linext),
            "vol": float(self.vol),
            "log_density": float(self.log_density),
            "target": float(self.target),
            "abs_err": float(self.abs_err),
            "ok": bool(self.ok),
        }


def write_table(rows: List[Row], out_path: Path, n_max: int) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        (
            "\\caption{锯齿调度/体积审计：对 $n\\le %d$，线性扩张数 $e(Z_n)$ 与 Euler 交错数 $E_n$ 一致（定理~\\ref{thm:pom-fence-maxchains-euler}），"
            "并给出 $\\frac{1}{n}\\log(E_n/n!)$ 向 $\\log(2/\\pi)$ 的收敛证书（定理~\\ref{thm:pom-fence-volume-log2pi}）。}"
        )
        % int(n_max)
    )
    lines.append("\\label{tab:fence_scheduling_euler_volume_audit}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$n$ & $E_n$ & $e(Z_n)$ & $E_n/n!$ & $\\frac{1}{n}\\log(E_n/n!)$ & $|\\Delta|$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        En = str(r.E_n)
        e = str(r.e_linext)
        vol = f"{r.vol:.10f}"
        dens = f"{r.log_density:.10f}"
        err = f"{r.abs_err:.2e}"
        lines.append(f"{r.n} & {En} & {e} & {vol} & {dens} & {err}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Audit Euler zigzag numbers vs fence linear extensions and volume density.")
    ap.add_argument("--n-max", type=int, default=12)
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fence_scheduling_euler_volume_audit.json"),
    )
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    n_max = int(args.n_max)
    if n_max < 1:
        raise SystemExit("Require --n-max >= 1")

    E = euler_zigzag_numbers(n_max)
    target = math.log(2.0 / math.pi)

    rows: List[Row] = []
    for n in range(1, n_max + 1):
        pred = fence_pred_masks(n)
        e_lin = count_linear_extensions(pred)
        En = int(E[n])
        if e_lin != En:
            raise AssertionError(f"e(Z_{n}) mismatch: dp={e_lin} vs E_n={En}")

        vol = En / math.factorial(n)
        log_density = (math.log(vol) / n) if n > 0 else 0.0
        abs_err = abs(log_density - target)

        rows.append(
            Row(
                n=n,
                E_n=En,
                e_linext=e_lin,
                vol=float(vol),
                log_density=float(log_density),
                target=float(target),
                abs_err=float(abs_err),
                ok=True,
            )
        )

    payload: Dict[str, object] = {
        "params": {"n_max": n_max, "target_log_2_over_pi": target},
        "rows": [r.to_dict() for r in rows],
    }

    json_out = Path(args.json_out)
    if not json_out.is_absolute():
        json_out = Path.cwd() / json_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    write_table(rows, out_path=(generated_dir() / "tab_fence_scheduling_euler_volume_audit.tex"), n_max=n_max)


if __name__ == "__main__":
    main()

