#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Large-modulus limit-law table for D(p) and sharp certificate bounds.

We define:
  D(p) := (1 - rho_{3,3,p}/lambda) * (p/(2π))^2 = kappa_p.
The paper predicts/derives:
  D(p) -> kappa_inf = sigma_xi^2/2  as p->∞.

We also compare to certificate bounds from the near-coboundary coloring defect summary:
  kappa_inf <= eps_pi^{(2)}/2,  and (coarse) eps/2.

Inputs:
  - artifacts/export/arity_335_n2_selection_law_primes.json
  - artifacts/export/arity_335_n2_master_curve.json   (for sigma^2 and kappa_inf)
  - sections/generated/tab_real_input_40_arity_dirichlet_mertens_335_N2_summary.tex (for eps, eps_pi^{(2)})

Outputs:
  - artifacts/export/arity_335_n2_limit_law.json
  - sections/generated/tab_real_input_40_arity_335_n2_limit_law.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir, paper_root


def _load(rel: str) -> dict:
    return json.loads((paper_root() / rel).read_text(encoding="utf-8"))


def _extract_eps(summary_tex_rel: str) -> Tuple[float, float]:
    txt = (paper_root() / summary_tex_rel).read_text(encoding="utf-8")
    eps = None
    eps2 = None
    for line in txt.splitlines():
        if eps is None and line.lstrip().startswith("\\varepsilon:="):
            j = line.find("\\lesssim")
            if j >= 0:
                tail = line[j + len("\\lesssim") :]
                m = re.search(r"([0-9.]+)", tail)
                if m:
                    eps = float(m.group(1))
        if eps2 is None and "\\varepsilon_\\pi^{(2)}" in line:
            j = line.find("\\approx")
            if j >= 0:
                tail = line[j + len("\\approx") :]
                m = re.search(r"([0-9.]+)", tail)
                if m:
                    eps2 = float(m.group(1))
        if eps is not None and eps2 is not None:
            break
    if eps is None:
        raise RuntimeError("could not extract epsilon from summary tex")
    if eps2 is None:
        raise RuntimeError("could not extract epsilon_pi^(2) from summary tex")
    return eps, eps2


def main() -> None:
    parser = argparse.ArgumentParser(description="Limit-law table for D(p) and certificate bounds.")
    parser.add_argument(
        "--selection-json",
        type=str,
        default="artifacts/export/arity_335_n2_selection_law_primes.json",
    )
    parser.add_argument(
        "--master-json",
        type=str,
        default="artifacts/export/arity_335_n2_master_curve.json",
    )
    parser.add_argument(
        "--summary-tex",
        type=str,
        default="sections/generated/tab_real_input_40_arity_dirichlet_mertens_335_N2_summary.tex",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_335_n2_limit_law.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_arity_335_n2_limit_law.tex"),
    )
    args = parser.parse_args()

    sel = _load(str(args.selection_json))
    master = _load(str(args.master_json))
    eps, eps2 = _extract_eps(str(args.summary_tex))

    kappa_inf = float(master["kappa_inf"])
    bound_eps2 = eps2 / 2.0
    bound_eps = eps / 2.0

    rows = []
    for r in sel["rows"]:
        p = int(r["p"])
        Dp = float(r["kappa_p"])  # equals D(p)
        rows.append(
            {
                "p": p,
                "D": Dp,
                "kappa_inf": kappa_inf,
                "abs_diff": abs(Dp - kappa_inf),
            }
        )

    payload: Dict[str, object] = {
        "p_list": [int(r["p"]) for r in sel["rows"]],
        "rows": rows,
        "kappa_inf": kappa_inf,
        "sigma2": float(master["pressure_P2"]),
        "eps": eps,
        "eps_pi_2": eps2,
        "bound_eps_over_2": bound_eps,
        "bound_epspi2_over_2": bound_eps2,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[limit-law] wrote {jout}", flush=True)

    # LaTeX table.
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Large-modulus limit law diagnostic for $D(p):=(1-\\rho_{3,3,p}/\\lambda)(p/2\\pi)^2=\\kappa_p$. "
        "We compare $D(p)$ against the variance-limit $\\kappa_\\infty=\\sigma_\\xi^2/2$ and certificate bounds "
        "$\\kappa_\\infty\\le \\varepsilon_\\pi^{(2)}/2$ (and coarse $\\varepsilon/2$).}"
    )
    lines.append("\\label{tab:real_input_40_arity_335_n2_limit_law}")
    lines.append("\\begin{tabular}{r r r r}")
    lines.append("\\toprule")
    lines.append("$p$ & $D(p)=\\kappa_p$ & $\\kappa_\\infty$ & $|D(p)-\\kappa_\\infty|$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r['p']} & {r['D']:.12f} & {kappa_inf:.12f} & {r['abs_diff']:.3e}\\\\"
        )
    lines.append("\\midrule")
    lines.append(f"$\\varepsilon/2$ & \\multicolumn{{3}}{{l}}{{{bound_eps:.12f}}}\\\\")
    lines.append(f"$\\varepsilon_\\pi^{{(2)}}/2$ & \\multicolumn{{3}}{{l}}{{{bound_eps2:.12f}}}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tex = Path(args.tex_out)
    tex.parent.mkdir(parents=True, exist_ok=True)
    tex.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[limit-law] wrote {tex}", flush=True)


if __name__ == "__main__":
    main()

