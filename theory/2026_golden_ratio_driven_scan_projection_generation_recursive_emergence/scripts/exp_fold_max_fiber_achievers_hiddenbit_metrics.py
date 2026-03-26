#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Derived hidden-bit metrics for max-fiber achievers of Fold_m.

Consumes the JSON output from:
  - exp_fold_max_fiber_achievers_bsplit.py

For each m, we compute (over maximizers x with d_m(x)=D_m):
  - p1 spectrum: p1(x) = d_{m,1}(x) / D_m
  - relative hidden-bit imbalance: Δ_m^(b) = max_x |d0-d1| / D_m
  - binary entropy spectrum: H_b(x) in bits

Outputs:
  - artifacts/export/fold_max_fiber_achievers_hiddenbit_metrics.json
  - sections/generated/tab_fold_max_fiber_achievers_hiddenbit_metrics.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, List, Tuple

from common_paths import export_dir, generated_dir


def _bin_entropy_bits(p: float) -> float:
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return -(p * math.log2(p) + (1.0 - p) * math.log2(1.0 - p))


def _format_set(vals: List[float], digits: int) -> str:
    # Deterministic, compact display for small spectra (typically size 1-3).
    vs = [float(v) for v in vals]
    vs.sort()
    body = ", ".join(f"{v:.{digits}f}" for v in vs)
    return f"$\\{{{body}\\}}$"


@dataclass(frozen=True)
class RowOut:
    m: int
    D: int
    kappa: int
    p1_values: List[float]
    delta_b: float
    Hb_values: List[float]


def write_table_tex(path: Path, rows: List[RowOut]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        "\\caption{Derived hidden-bit metrics for max-fiber achievers of Fold$_m$. "
        "We report the distinct $p_1=d_{m,1}/D_m$ values among maximizers, "
        "the relative imbalance $\\Delta_m^{(b)}=\\max_x |d_{m,0}-d_{m,1}|/D_m$, "
        "and the corresponding binary entropies $H_b$ in bits (rounded).}"
    )
    lines.append("\\label{tab:fold_max_fiber_achievers_hiddenbit_metrics}")
    lines.append("\\begin{tabular}{r r r l r l}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $D_m$ & $\\kappa_m^{\\mathrm{max}}$ & $p_1$ spectrum & "
        "$\\Delta_m^{(b)}$ & $H_b$ spectrum (bits)\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        p1s = _format_set(r.p1_values, digits=6)
        Hs = _format_set(r.Hb_values, digits=6)
        lines.append(f"{r.m} & {r.D} & {r.kappa} & {p1s} & {r.delta_b:.6f} & {Hs}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _load_json(path: Path) -> Dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or "rows" not in data:
        raise ValueError("unexpected JSON schema (expected dict with key 'rows')")
    return data


def main() -> None:
    parser = argparse.ArgumentParser(description="Derived hidden-bit metrics for max-fiber achievers (from bsplit JSON).")
    parser.add_argument("--m-min", type=int, default=2)
    parser.add_argument("--m-max", type=int, default=32)
    parser.add_argument(
        "--bsplit-json",
        type=str,
        default=str(export_dir() / "fold_max_fiber_achievers_bsplit.json"),
        help="Input JSON produced by exp_fold_max_fiber_achievers_bsplit.py",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_max_fiber_achievers_hiddenbit_metrics.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_max_fiber_achievers_hiddenbit_metrics.tex"),
    )
    args = parser.parse_args()

    if args.m_min < 2 or args.m_max < args.m_min:
        raise SystemExit("Require m_max >= m_min >= 2")

    jin = Path(args.bsplit_json)
    if not jin.exists():
        raise SystemExit(
            f"Missing input JSON: {jin}. Run exp_fold_max_fiber_achievers_bsplit.py first (or pass --bsplit-json)."
        )

    payload = _load_json(jin)
    rows_in = payload["rows"]
    if not isinstance(rows_in, list):
        raise ValueError("unexpected JSON schema: 'rows' must be a list")

    rows: List[RowOut] = []
    for r in rows_in:
        m = int(r["m"])
        if m < int(args.m_min) or m > int(args.m_max):
            continue
        D = int(r["D_closed"])
        kappa = int(r["kappa"])
        pair_mults = r["split_pair_mults"]
        if not isinstance(pair_mults, list):
            raise ValueError("unexpected JSON schema: split_pair_mults must be a list")

        p1_vals: List[float] = []
        Hb_vals: List[float] = []
        delta_b = 0.0

        for t in pair_mults:
            if not (isinstance(t, list) or isinstance(t, tuple)) or len(t) != 3:
                raise ValueError("unexpected split_pair_mults item (expected [d0,d1,mult])")
            d0, d1, _mult = (int(t[0]), int(t[1]), int(t[2]))
            p1 = float(d1) / float(D)
            p1_vals.append(p1)
            Hb_vals.append(_bin_entropy_bits(p1))
            delta_b = max(delta_b, abs(float(d0 - d1)) / float(D))

        # Deduplicate with a small rounding bucket to keep the display stable.
        def _uniq(vals: List[float], digits: int) -> List[float]:
            seen: Dict[int, float] = {}
            for v in vals:
                key = int(round(v * (10**digits)))
                seen[key] = v
            out = list(seen.values())
            out.sort()
            return out

        p1_unique = _uniq(p1_vals, digits=9)
        Hb_unique = _uniq(Hb_vals, digits=9)

        rows.append(
            RowOut(
                m=m,
                D=D,
                kappa=kappa,
                p1_values=p1_unique,
                delta_b=delta_b,
                Hb_values=Hb_unique,
            )
        )

    # Deterministic order
    rows.sort(key=lambda rr: rr.m)

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps(
            {
                "m_min": int(args.m_min),
                "m_max": int(args.m_max),
                "input_bsplit_json": str(jin),
                "rows": [asdict(r) for r in rows],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"[fold-max-fiber-hiddenbit-metrics] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[fold-max-fiber-hiddenbit-metrics] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

