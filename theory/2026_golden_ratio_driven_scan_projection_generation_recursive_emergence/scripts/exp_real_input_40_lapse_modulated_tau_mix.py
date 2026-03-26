#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Overhead-modulated mixing-time rescaling from twisted spectral gaps.

We take a precomputed twisted spectral gap (per internal step / proper-time tick):
  Delta := -log(rho/lambda),
  tau_mix := 1/Delta,
and apply an external-time rescaling proxy N = kappa0/kappa to convert to an external-time
rate in the simplest deterministic rescaling model:
  Delta_eff(x) = N(x) * Delta,
  tau_mix_eff(x) = tau_mix / N(x).

This script is intentionally *operational*: it does not recompute rho/lambda under a
changed kernel. It provides the deterministic rescaling interface that can be tested
once kappa(x) is instantiated by a routing / inverse-search cost model.

Inputs:
  - artifacts/export/real_input_40_rho_ppp_prime_scan.json  (default)

Outputs:
  - artifacts/export/real_input_40_lapse_modulated_tau_mix.json
  - sections/generated/tab_real_input_40_lapse_modulated_tau_mix.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, List, Sequence

from common_paths import export_dir, generated_dir, paper_root


def _load_json(rel: str) -> Dict[str, Any]:
    return json.loads((paper_root() / rel).read_text(encoding="utf-8"))


def _parse_float_list_csv(s: str) -> List[float]:
    out: List[float] = []
    for tok in str(s).split(","):
        t = tok.strip()
        if not t:
            continue
        out.append(float(t))
    # stable unique
    seen = set()
    uniq: List[float] = []
    for x in out:
        if x in seen:
            continue
        seen.add(x)
        uniq.append(x)
    return uniq


def _fmt(x: float) -> str:
    if math.isnan(x):
        return "\\mathrm{NaN}"
    if not math.isfinite(x):
        return "\\infty"
    return f"{x:.12f}"


@dataclass(frozen=True)
class Row:
    p: int
    rho_over_lambda: float
    Delta: float
    tau_mix: float
    kappa: float
    kappa0: float
    N: float
    Delta_eff: float
    tau_mix_eff: float


def main() -> None:
    ap = argparse.ArgumentParser(description="Lapse-modulated mixing-time rescaling table.")
    ap.add_argument(
        "--rho-json",
        type=str,
        default="artifacts/export/real_input_40_rho_ppp_prime_scan.json",
        help="Input JSON produced by exp_real_input_40_rho_ppp_prime_scan.py",
    )
    ap.add_argument(
        "--p-list",
        type=str,
        default="3,5,7,11,13",
        help="Comma-separated p values to include (must exist in rho-json).",
    )
    ap.add_argument(
        "--kappa-list",
        type=str,
        default="1,2,10,100",
        help="Comma-separated kappa values (background-dependent overhead proxies).",
    )
    ap.add_argument(
        "--kappa0",
        type=float,
        default=0.0,
        help="Reference kappa0. If <=0, we use min(kappa-list).",
    )
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_lapse_modulated_tau_mix.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_lapse_modulated_tau_mix.tex"),
    )
    args = ap.parse_args()

    rho = _load_json(str(args.rho_json))
    p_list = [int(x.strip()) for x in str(args.p_list).split(",") if x.strip()]
    kappas = _parse_float_list_csv(str(args.kappa_list))
    if not p_list:
        raise SystemExit("empty --p-list")
    if not kappas or any(k <= 0.0 for k in kappas):
        raise SystemExit("need positive --kappa-list values")

    kappa0 = float(args.kappa0)
    if kappa0 <= 0.0:
        kappa0 = float(min(kappas))

    rows_in = rho.get("rows", [])
    if not isinstance(rows_in, list):
        raise SystemExit("invalid rho-json: missing rows[]")

    by_p: Dict[int, Dict[str, Any]] = {}
    for r in rows_in:
        if not isinstance(r, dict):
            continue
        try:
            p = int(r.get("p"))
        except Exception:
            continue
        by_p[p] = r

    out_rows: List[Row] = []
    for p in p_list:
        if p not in by_p:
            raise SystemExit(f"missing p={p} in {args.rho_json}")
        rr = by_p[p]
        ratio = float(rr.get("rho_over_lambda"))
        Delta = float(rr.get("delta_minus_log_rho_over_lambda"))
        tau_mix = float("inf") if not (Delta > 0.0 and math.isfinite(Delta)) else float(1.0 / Delta)

        for kappa in kappas:
            N = float(kappa0) / float(kappa)
            Delta_eff = float(N) * float(Delta) if math.isfinite(Delta) else float("inf")
            tau_eff = float(tau_mix) / float(N) if (N > 0.0 and math.isfinite(tau_mix)) else float("inf")
            out_rows.append(
                Row(
                    p=int(p),
                    rho_over_lambda=float(ratio),
                    Delta=float(Delta),
                    tau_mix=float(tau_mix),
                    kappa=float(kappa),
                    kappa0=float(kappa0),
                    N=float(N),
                    Delta_eff=float(Delta_eff),
                    tau_mix_eff=float(tau_eff),
                )
            )

    # Stable sort: by p then kappa.
    out_rows.sort(key=lambda r: (r.p, r.kappa))

    payload = {
        "inputs": {"rho_json": str(args.rho_json)},
        "params": {"p_list": p_list, "kappa_list": kappas, "kappa0": kappa0},
        "rows": [asdict(r) for r in out_rows],
    }
    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[tau-mix-rescale] wrote {jout}", flush=True)

    # LaTeX table.
    tout = Path(str(args.tex_out))
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_real_input_40_lapse_modulated_tau_mix.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.15}")
    lines.append(
        "\\caption{Overhead-modulated mixing-time rescaling: given $\\Delta=-\\log(\\rho/\\lambda)$ and $\\tau_{\\mathrm{mix}}=1/\\Delta$ (internal steps), "
        "an external-time rescaling proxy $N=\\kappa_0/\\kappa$ yields $\\Delta_{\\mathrm{eff}}=N\\Delta$ and $\\tau_{\\mathrm{mix,eff}}=\\tau_{\\mathrm{mix}}/N$ (external time).}"
    )
    lines.append("\\label{tab:real-input-40-lapse-modulated-tau-mix}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$p$ & $\\rho/\\lambda$ & $\\Delta$ & $\\kappa$ & $N$ & $\\tau_{\\mathrm{mix,eff}}$\\\\")
    lines.append("\\midrule")
    for r in out_rows:
        lines.append(
            f"{r.p} & {_fmt(r.rho_over_lambda)} & {_fmt(r.Delta)} & {_fmt(r.kappa)} & {_fmt(r.N)} & {_fmt(r.tau_mix_eff)}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[tau-mix-rescale] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

